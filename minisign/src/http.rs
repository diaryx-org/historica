//! Signed requests over the platform's own HTTP: a fetch [`Source`], and the
//! token request.
//!
//! Historica's decision 0057 chose the stack a fetch rides on — `nyquest`,
//! pinned, which is WinRT, NSURLSession or libcurl underneath — and deferred
//! authentication to the transport. This is a transport with an answer: the
//! same source as historica's own, with an `Authorization` header from
//! [`crate::request`] on every request. Behind the `http` feature for 0057's
//! reason, which is a target with no such stack under it; the signing and the
//! check are in [`crate::request`] and need none of this.
//!
//! Two settings differ from historica's own source, and both follow from the
//! header.
//!
//! - **Redirects are not followed.** A signature names one host and one path,
//!   so it is worth nothing at the place a redirect points to, and following
//!   one would hand a live header to a host this command was never asked to
//!   talk to. A redirect is reported, and the person types the URL it names.
//! - **A signature is made per request, at the moment of the request.** A
//!   fetch of a large store runs longer than [`crate::request::DEFAULT_MAX_SKEW`],
//!   and a header made once at the start would be stale before the end.

use std::fmt;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use historica::store::{Source, Unreachable};
use minisign::SecretKey;

use crate::request::{RequestError, TOKEN_PATH, Target, sign_request};

/// What every request says it is.
const USER_AGENT: &str = concat!("historica-minisign/", env!("CARGO_PKG_VERSION"));

/// A published root on a server that wants to know who is reading, over the
/// platform's own HTTP.
///
/// `root` is the directory a manifest sits in, ending in `/`, and every path
/// a fetch asks for is resolved against it as decision 0052 says. Each request
/// is signed by `secret`.
pub struct SignedSource {
    client: nyquest::BlockingClient,
    root: Target,
    secret: SecretKey,
}

impl fmt::Debug for SignedSource {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // The secret key is left out, so a source in a log is not a key in one.
        f.debug_struct("SignedSource")
            .field("root", &self.root)
            .finish_non_exhaustive()
    }
}

impl SignedSource {
    /// A source reading below `root`, which ends in `/`.
    pub fn at(root: &str, secret: SecretKey) -> Result<Self, Unreachable> {
        let target = Target::of(root).map_err(Unreachable::saying)?;
        if !target.path.ends_with('/') || target.path.contains('?') {
            return Err(Unreachable::saying(format!(
                "`{root}` is not a directory: a published root ends in `/`, and \
                 every path a manifest names is put after it"
            )));
        }
        Ok(Self {
            client: client()?,
            root: target,
            secret,
        })
    }

    /// The path a request for `path`, as a manifest spells it, is sent to.
    ///
    /// Every byte that is not unreserved is escaped and `/` alone survives,
    /// as historica's own source does it (decision 0057): a manifest's paths
    /// are filenames, and a person may file their history under any name.
    pub fn request_path(&self, path: &str) -> String {
        format!("{}{}", self.root.path, escaped(path))
    }

    /// The `Authorization` header a `GET` of `path` would carry, made now.
    pub fn authorization(&self, path: &str) -> Result<String, RequestError> {
        sign_request(
            &self.secret,
            "GET",
            &self.root.host,
            &self.request_path(path),
            now().map_err(|because| RequestError::Minisign { because })?,
        )
    }
}

impl Source for SignedSource {
    fn get(&self, path: &str) -> Result<Option<Vec<u8>>, Unreachable> {
        let url = format!("{}{}", self.root.origin(), self.request_path(path));
        let header = self.authorization(path).map_err(Unreachable::saying)?;
        let response = self
            .client
            .request(nyquest::blocking::Request::get(url).with_header("Authorization", header))
            .map_err(said)?;
        let status = response.status();
        // The two ways a server says a file is not there, which decision 0048
        // makes an answer rather than a failure.
        if status.code() == 404 || status.code() == 410 {
            return Ok(None);
        }
        if !status.is_successful() {
            return Err(refused(status.code()));
        }
        response.bytes().map(Some).map_err(said)
    }
}

/// A short-lived token, as a hub mints one for a signed request.
///
/// # The contract a hub implements
///
/// `POST /api/auth/token` ([`TOKEN_PATH`]) on the hub's own origin, with an
/// empty body and an `Authorization` header from
/// [`crate::request::sign_request`] over that method, host and path. A hub
/// that takes the header answers `200` with a JSON object:
///
/// ```json
/// { "token": "…", "expires": "2026-10-20T18:05:00Z" }
/// ```
///
/// - `token` is printable ASCII with no space, which is what lets it be a
///   password in HTTP Basic and a line in git's credential protocol.
/// - `expires` is an RFC 3339 time with an offset (`Z` or `±hh:mm`),
///   fractional seconds allowed, after which the hub takes the token no more.
///
/// Every value in the object is a string. A key other than these two is
/// ignored, so a hub may add one; one of these two missing is a refusal. A hub
/// that does not take the header answers 401, and anything but a 2xx is a
/// [`TokenError::Refused`] carrying its status.
#[derive(Clone, PartialEq, Eq)]
pub struct Token {
    /// The token.
    pub token: String,
    /// When it stops working, as the hub wrote it.
    pub expires: String,
    /// The same moment, in seconds since the Unix epoch.
    pub expires_at: i64,
}

impl fmt::Debug for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // A token is a credential for as long as it lives; a log is longer.
        f.debug_struct("Token")
            .field("expires", &self.expires)
            .finish_non_exhaustive()
    }
}

impl Token {
    /// Read a hub's answer, holding it to the contract above.
    pub fn parse(body: &str) -> Result<Self, TokenError> {
        let fields = flat_object(body).ok_or(TokenError::Answer {
            because: "it is not a JSON object whose every value is a string",
        })?;
        let field = |name: &str| {
            fields
                .iter()
                .find(|(key, _)| key == name)
                .map(|(_, value)| value.clone())
        };
        let token = field("token").ok_or(TokenError::Answer {
            because: "it has no `token`",
        })?;
        if token.is_empty() || !token.bytes().all(|byte| (0x21..=0x7e).contains(&byte)) {
            return Err(TokenError::Answer {
                because: "its `token` is not printable ASCII without a space",
            });
        }
        let expires = field("expires").ok_or(TokenError::Answer {
            because: "it has no `expires`",
        })?;
        let expires_at = rfc3339(&expires).ok_or(TokenError::Answer {
            because: "its `expires` is not an RFC 3339 time with an offset",
        })?;
        Ok(Self {
            token,
            expires,
            expires_at,
        })
    }

    /// The token as JSON, in the shape the hub sent it.
    pub fn to_json(&self) -> String {
        format!(
            "{{\"token\":{},\"expires\":{}}}",
            json_string(&self.token),
            json_string(&self.expires)
        )
    }
}

/// Ask the hub at `hub` for a short-lived token, signing the request with
/// `secret`.
///
/// `hub` is the hub's origin, `https://hub.example.org`, with nothing after
/// it but an optional `/`: the token is minted at [`TOKEN_PATH`] on that
/// origin and nowhere else. [`Token`] states what the hub answers.
///
/// This is what a git credential helper is built on: `git clone` cannot sign
/// a request, so the helper gets a token here and hands it to git as a
/// password.
pub fn request_token(hub: &str, secret: &SecretKey) -> Result<Token, TokenError> {
    let target = Target::of(hub).map_err(TokenError::Request)?;
    if target.path != "/" {
        return Err(TokenError::Request(RequestError::Url {
            url: hub.to_owned(),
            because: "a hub is named by its origin alone, and the token is \
                      minted at /api/auth/token on it",
        }));
    }
    let time = now().map_err(|because| TokenError::Request(RequestError::Minisign { because }))?;
    let header = sign_request(secret, "POST", &target.host, TOKEN_PATH, time)
        .map_err(TokenError::Request)?;
    let client = client().map_err(TokenError::Unreachable)?;
    let url = format!("{}{TOKEN_PATH}", target.origin());
    let response = client
        .request(nyquest::blocking::Request::post(url).with_header("Authorization", header))
        .map_err(|error| TokenError::Unreachable(said(error)))?;
    let status = response.status();
    if !status.is_successful() {
        return Err(TokenError::Refused {
            status: status.code(),
        });
    }
    let body = response
        .text()
        .map_err(|error| TokenError::Unreachable(said(error)))?;
    Token::parse(&body)
}

/// Why no token came back.
#[derive(Debug)]
#[non_exhaustive]
pub enum TokenError {
    /// The request could not be signed, or the URL could not be signed for.
    Request(RequestError),
    /// The hub could not be reached at all.
    Unreachable(Unreachable),
    /// The hub answered, and not with a token.
    Refused {
        /// The status it answered with.
        status: u16,
    },
    /// The hub answered 2xx with something that is not the contract.
    Answer {
        /// What was wrong with it.
        because: &'static str,
    },
}

impl fmt::Display for TokenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Request(error) => error.fmt(f),
            Self::Unreachable(error) => error.fmt(f),
            Self::Refused { status: 401 } => f.write_str(
                "the hub answered 401: it does not take this key, or this \
                 machine's clock is minutes away from the hub's",
            ),
            Self::Refused { status } => write!(f, "the hub answered {status}"),
            Self::Answer { because } => write!(f, "the hub's answer is not a token: {because}"),
        }
    }
}

impl std::error::Error for TokenError {}

/// A client set as historica's own source sets one, and not following
/// redirects; the module says why.
fn client() -> Result<nyquest::BlockingClient, Unreachable> {
    // Registering the backend is what makes `nyquest` resolve to WinRT,
    // NSURLSession or libcurl. Registering twice is harmless.
    nyquest_preset::register();
    nyquest::ClientBuilder::default()
        .user_agent(USER_AGENT)
        .no_cookies()
        // Decision 0057: a cache that served the same manifest twice would
        // turn the one recoverable failure into the one unrecoverable one.
        .no_caching()
        .no_redirects()
        .request_timeout(Duration::from_secs(60))
        .build_blocking()
        .map_err(|error| Unreachable::saying(format!("no HTTP client: {error}")))
}

fn refused(code: u16) -> Unreachable {
    Unreachable::saying(match code {
        300..=399 => format!(
            "the server answered {code}, a redirect, which is not followed: the \
             request was signed for this URL and no other"
        ),
        401 | 403 => format!(
            "the server answered {code}: it does not take this key for this \
             copy, or this machine's clock is minutes away from the server's"
        ),
        _ => format!("the server answered {code}"),
    })
}

/// Seconds since the Unix epoch, now.
fn now() -> Result<u64, String> {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|since| since.as_secs())
        .map_err(|error| format!("the clock could not say when now is: {error}"))
}

/// What went wrong, as far down as the error chain goes; nyquest's own
/// message is a category, and what the platform said is underneath it.
fn said(error: nyquest::Error) -> Unreachable {
    let mut whole = error.to_string();
    let mut cause = std::error::Error::source(&error);
    while let Some(next) = cause {
        whole.push_str(&format!(": {next}"));
        cause = next.source();
    }
    Unreachable::saying(whole)
}

/// One manifest path, said as a URL path: historica's own escaping.
fn escaped(path: &str) -> String {
    let mut escaped = String::with_capacity(path.len());
    for byte in path.bytes() {
        match byte {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'-' | b'.' | b'_' | b'~' | b'/' => {
                escaped.push(byte as char);
            }
            other => escaped.push_str(&format!("%{other:02X}")),
        }
    }
    escaped
}

/// A JSON object whose every value is a string, as its pairs; `None` for
/// anything else.
///
/// Small on purpose. The token answer is two strings, and a JSON library for
/// it would be the largest dependency this feature adds after HTTP itself.
fn flat_object(text: &str) -> Option<Vec<(String, String)>> {
    let mut chars = text.trim().chars().peekable();
    let mut pairs = Vec::new();
    if chars.next()? != '{' {
        return None;
    }
    skip_space(&mut chars);
    if chars.peek() == Some(&'}') {
        chars.next();
    } else {
        loop {
            skip_space(&mut chars);
            let key = json_string_body(&mut chars)?;
            skip_space(&mut chars);
            if chars.next()? != ':' {
                return None;
            }
            skip_space(&mut chars);
            let value = json_string_body(&mut chars)?;
            pairs.push((key, value));
            skip_space(&mut chars);
            match chars.next()? {
                ',' => continue,
                '}' => break,
                _ => return None,
            }
        }
    }
    chars.next().is_none().then_some(pairs)
}

fn skip_space(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) {
    while chars
        .peek()
        .is_some_and(|c| matches!(c, ' ' | '\t' | '\n' | '\r'))
    {
        chars.next();
    }
}

/// One JSON string, its opening quote not yet read.
fn json_string_body(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) -> Option<String> {
    if chars.next()? != '"' {
        return None;
    }
    let mut out = String::new();
    loop {
        match chars.next()? {
            '"' => return Some(out),
            '\\' => match chars.next()? {
                '"' => out.push('"'),
                '\\' => out.push('\\'),
                '/' => out.push('/'),
                'b' => out.push('\u{8}'),
                'f' => out.push('\u{c}'),
                'n' => out.push('\n'),
                'r' => out.push('\r'),
                't' => out.push('\t'),
                'u' => {
                    let unit = hex4(chars)?;
                    let c = if (0xD800..0xDC00).contains(&unit) {
                        if chars.next()? != '\\' || chars.next()? != 'u' {
                            return None;
                        }
                        let low = hex4(chars)?;
                        if !(0xDC00..0xE000).contains(&low) {
                            return None;
                        }
                        char::from_u32(0x10000 + ((unit - 0xD800) << 10) + (low - 0xDC00))?
                    } else {
                        char::from_u32(unit)?
                    };
                    out.push(c);
                }
                _ => return None,
            },
            c if (c as u32) < 0x20 => return None,
            c => out.push(c),
        }
    }
}

fn hex4(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) -> Option<u32> {
    let mut unit = 0;
    for _ in 0..4 {
        unit = unit * 16 + chars.next()?.to_digit(16)?;
    }
    Some(unit)
}

/// A string as JSON writes one.
fn json_string(value: &str) -> String {
    let mut out = String::from("\"");
    for c in value.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// An RFC 3339 time with an offset, as seconds since the Unix epoch.
fn rfc3339(text: &str) -> Option<i64> {
    let bytes = text.as_bytes();
    let number = |range: std::ops::Range<usize>| -> Option<i64> {
        let digits = bytes.get(range)?;
        digits
            .iter()
            .all(u8::is_ascii_digit)
            .then(|| digits.iter().fold(0, |n, d| n * 10 + i64::from(d - b'0')))
    };
    if bytes.len() < 20
        || bytes[4] != b'-'
        || bytes[7] != b'-'
        || !matches!(bytes[10], b'T' | b't')
        || bytes[13] != b':'
        || bytes[16] != b':'
    {
        return None;
    }
    let (year, month, day) = (number(0..4)?, number(5..7)?, number(8..10)?);
    let (hour, minute, second) = (number(11..13)?, number(14..16)?, number(17..19)?);
    let mut at = 19;
    if bytes[at] == b'.' {
        at += 1;
        let start = at;
        while bytes.get(at).is_some_and(u8::is_ascii_digit) {
            at += 1;
        }
        if at == start {
            return None;
        }
    }
    let offset = match bytes.get(at..)? {
        b"Z" | b"z" => 0,
        [sign @ (b'+' | b'-'), _, _, b':', _, _] => {
            let hours = number(at + 1..at + 3)?;
            let minutes = number(at + 4..at + 6)?;
            if hours > 23 || minutes > 59 {
                return None;
            }
            let offset = hours * 3600 + minutes * 60;
            if *sign == b'-' { -offset } else { offset }
        }
        _ => return None,
    };
    let leap = year % 4 == 0 && (year % 100 != 0 || year % 400 == 0);
    let days_in_month = match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 if leap => 29,
        2 => 28,
        _ => return None,
    };
    // 60 is a leap second, which RFC 3339 allows and Unix time folds into the
    // next.
    if day < 1 || day > days_in_month || hour > 23 || minute > 59 || second > 60 {
        return None;
    }
    // Days from the civil date, after Howard Hinnant's algorithm.
    let y = if month <= 2 { year - 1 } else { year };
    let era = y.div_euclid(400);
    let yoe = y - era * 400;
    let mp = (month + 9) % 12;
    let doy = (153 * mp + 2) / 5 + day - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    let days = era * 146_097 + doe - 719_468;
    Some(days * 86_400 + hour * 3600 + minute * 60 + second - offset)
}

#[cfg(test)]
mod tests {
    use super::{Token, escaped, flat_object, rfc3339};

    #[test]
    fn a_hubs_answer_is_read_to_the_contract() {
        let token = Token::parse(
            "{ \"token\": \"hx_3f9a\\u0021\", \"expires\": \"2026-10-20T18:05:00Z\", \
             \"kind\": \"read\" }",
        )
        .expect("a token");
        assert_eq!(token.token, "hx_3f9a!");
        assert_eq!(token.expires, "2026-10-20T18:05:00Z");
        assert_eq!(token.expires_at, 1_792_519_500);
        assert_eq!(
            token.to_json(),
            "{\"token\":\"hx_3f9a!\",\"expires\":\"2026-10-20T18:05:00Z\"}"
        );
        assert!(!format!("{token:?}").contains("hx_3f9a"));

        for refused in [
            "",
            "[]",
            "{\"token\": \"a\"}",
            "{\"expires\": \"2026-10-20T18:05:00Z\"}",
            "{\"token\": \"a b\", \"expires\": \"2026-10-20T18:05:00Z\"}",
            "{\"token\": \"\", \"expires\": \"2026-10-20T18:05:00Z\"}",
            "{\"token\": \"a\", \"expires\": \"tomorrow\"}",
            "{\"token\": \"a\", \"expires\": 1792519500}",
            "{\"token\": \"a\", \"expires\": \"2026-10-20T18:05:00Z\"} trailing",
        ] {
            assert!(Token::parse(refused).is_err(), "`{refused}` was taken");
        }
    }

    #[test]
    fn a_flat_object_is_strings_and_nothing_else() {
        assert_eq!(flat_object("{}"), Some(Vec::new()));
        assert_eq!(
            flat_object("{\"a\":\"\\ud83d\\ude00\"}"),
            Some(vec![("a".to_owned(), "😀".to_owned())])
        );
        for refused in [
            "{",
            "{\"a\"}",
            "{\"a\":\"b\",}",
            "{\"a\":null}",
            "{\"a\":\"\n\"}",
        ] {
            assert_eq!(flat_object(refused), None, "`{refused}` was taken");
        }
    }

    #[test]
    fn an_rfc_3339_time_is_seconds_since_the_epoch() {
        assert_eq!(rfc3339("1970-01-01T00:00:00Z"), Some(0));
        assert_eq!(rfc3339("2026-10-20T12:05:00-06:00"), Some(1_792_519_500));
        assert_eq!(rfc3339("2026-10-20T18:05:00.123Z"), Some(1_792_519_500));
        assert_eq!(rfc3339("2000-02-29T00:00:00+00:00"), Some(951_782_400));
        for refused in [
            "2026-10-20 18:05:00Z",
            "2026-10-20T18:05:00",
            "2026-02-30T00:00:00Z",
            "2026-10-20T18:05:00.Z",
            "2026-10-20T24:00:00Z",
            "2026-10-20T18:05:00+0600",
        ] {
            assert_eq!(rfc3339(refused), None, "`{refused}` was taken");
        }
    }

    #[test]
    fn a_path_is_escaped_as_historica_escapes_it() {
        assert_eq!(
            escaped("store/history/revisions/2026-08/a second copy.ops.txt"),
            "store/history/revisions/2026-08/a%20second%20copy.ops.txt"
        );
        assert_eq!(escaped("history/notes/ré.txt"), "history/notes/r%C3%A9.txt");
    }
}
