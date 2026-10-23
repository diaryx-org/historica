//! A request signed by a device key, and the check a server makes of one.
//!
//! Historica's fetch has no authentication: decision 0057 defers it to the
//! transport, and a `Source` is where a host that has an answer gives it. The
//! forge proposal's answer is the device keys an account already holds, the
//! same minisign keys that sign claims. Each request carries
//!
//! ```text
//! Authorization: Minisign <key-id> <time> <signature>
//! ```
//!
//! and the server takes it from a key registered to someone allowed to read,
//! within a few minutes of the time it states.
//!
//! # What is signed
//!
//! Five lines, each ending in a newline, in this order and no other:
//!
//! ```text
//! historica-request-1
//! method GET
//! host hub.example.org
//! path /adam/notes/offer.txt
//! time 1760968324
//! ```
//!
//! [`signed_string`] writes it. The preamble carries its number for the
//! reason a claim's does: a later grammar is minted as `historica-request-2`
//! rather than by loosening this one. It also keeps a request signature apart
//! from every other thing a key signs. A claim begins `claim-`, a head
//! statement begins with its own preamble, and no byte string begins with
//! both, so a signature over one can never be passed off as a signature over
//! the other.
//!
//! - **method** is the request's method, in capitals: `GET`, `POST`.
//! - **host** is the URL's host, in lower case, with its port only when the
//!   port is not the scheme's own. That is what a browser's `URL.host` says,
//!   so a Cloudflare worker reads it from the request URL as it stands.
//! - **path** is the path and query exactly as the request line sends them,
//!   percent-escapes and all, beginning with `/`. Nothing is decoded or
//!   normalised on either side: the bytes on the wire are the bytes signed.
//! - **time** is seconds since the Unix epoch, in decimal.
//!
//! A request body is not signed. The only request with a body in mind is the
//! token request, which has none ([`TOKEN_PATH`]), and a read has none either.
//! A grammar that signs a body is a `historica-request-2`.
//!
//! # The header
//!
//! `<key-id>` is minisign's key ID: sixteen upper-case hexadecimal digits,
//! as `minisign.pub`'s comment prints it. `<time>` is the time line's value.
//! `<signature>` is a minisign signature made with an empty trusted comment,
//! with its two signatures put together: the 74 bytes of its signature line
//! followed by the 64 bytes of its global signature, in standard base64 with
//! no line breaks, 184 characters. A server that wants to check one with any
//! minisign verifier can rebuild the four-line file from those two halves and
//! `trusted comment: ` on its own.
//!
//! The ID rather than the whole public key, because the server already holds
//! every key it would accept and needs only to find one. It is not trusted:
//! [`verify_request`] looks the ID up, and the key it finds is what checks the
//! signature.
//!
//! # Replay
//!
//! A copied header reads one path on one host, by one method, for as long as
//! [`DEFAULT_MAX_SKEW`] leaves its time inside the window. For a read that is
//! the bytes the copier already saw go by. For a request with an effect — the
//! token request above all — it is one more of that effect, so a server should
//! refuse a header it has already accepted. The window is what makes that
//! cheap: a header older than the window is refused anyway, so the server has
//! to remember headers for the length of the window and no longer.

use std::fmt;
use std::str::FromStr;

use minisign_verify::{PublicKey, Signature};

use crate::base64;
use crate::claim::Key;

/// The first line of the signed string.
pub const PREAMBLE: &str = "historica-request-1";

/// The authentication scheme, the first word of the `Authorization` header.
pub const SCHEME: &str = "Minisign";

/// Where a hub mints a short-lived token for a signed request. The method is
/// `POST`, the body empty, and the response is the contract
/// `crate::http::Token` states.
pub const TOKEN_PATH: &str = "/api/auth/token";

/// How far the time a request states may be from the server's own, in
/// seconds, either way: five minutes.
///
/// The window has two jobs, and they pull opposite ways. It bounds how long a
/// copied header is worth anything, which wants it short. And it must cover
/// the honest disagreement between two clocks, which wants it long. A device
/// that keeps time by NTP is within a second or two; a laptop that has slept
/// for a week, or a phone that took its time from a network that was wrong,
/// can be a minute or more out. Five minutes takes all of those, and is what
/// Kerberos has used for decades for the same job. A header then lives at most
/// ten minutes from the moment it was made, which is the proposal's "a copied
/// header reads one path, for minutes".
///
/// The window is the same in both directions. A time ahead of the server is
/// refused at the same distance as one behind it, because a header stamped in
/// the future is one that stays good for longer than the window promises.
pub const DEFAULT_MAX_SKEW: u64 = 5 * 60;

/// The base64 characters of a header's signature: 138 bytes.
const SIGNATURE_CHARS: usize = 184;

/// The bytes of minisign's signature line: algorithm, key ID, signature.
const SIGNATURE_LINE_BYTES: usize = 74;

/// The algorithm a request signature is made with: Ed25519 over a BLAKE2b
/// hash of the message, minisign's default. The legacy `Ed`, over the message
/// itself, is refused, because nothing that makes these headers ever made one.
const PREHASHED: [u8; 2] = *b"ED";

/// What a minisign signature line says about the comment that is not signed.
/// Nothing reads it.
const UNTRUSTED_COMMENT: &str = "untrusted comment: historica-request-1";

/// A minisign key ID: the eight bytes that name a key, which every signature
/// it makes repeats.
///
/// Spelled as minisign spells it, sixteen upper-case hexadecimal digits of the
/// bytes read as a little-endian number, so the ID a person sees in
/// `minisign.pub`'s comment is the one a server is asked to look up.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct KeyId([u8; 8]);

impl KeyId {
    /// The ID's bytes, as a minisign key or signature holds them.
    pub fn bytes(&self) -> [u8; 8] {
        self.0
    }
}

impl From<[u8; 8]> for KeyId {
    fn from(bytes: [u8; 8]) -> Self {
        Self(bytes)
    }
}

impl fmt::Display for KeyId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:016X}", u64::from_le_bytes(self.0))
    }
}

impl FromStr for KeyId {
    type Err = Refusal;

    /// Sixteen upper-case hexadecimal digits, and nothing else: no `0x`, no
    /// lower case, no padding. One spelling, so one ID is never two.
    fn from_str(value: &str) -> Result<Self, Self::Err> {
        let malformed = || Refusal::Malformed {
            because: "a key ID is sixteen upper-case hexadecimal digits",
        };
        if value.len() != 16
            || !value
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'A'..=b'F').contains(&byte))
        {
            return Err(malformed());
        }
        let number = u64::from_str_radix(value, 16).map_err(|_| malformed())?;
        Ok(Self(number.to_le_bytes()))
    }
}

impl Key {
    /// This key's ID, which is what a request header names it by.
    pub fn id(&self) -> KeyId {
        // The text was decoded by minisign on the way in, so it is base64 of
        // the 42 bytes of an Ed25519 minisign key: two of algorithm, then the
        // eight of the ID.
        let bytes = base64::decode(self.as_str()).unwrap_or_default();
        let mut id = [0u8; 8];
        if let Some(found) = bytes.get(2..10) {
            id.copy_from_slice(found);
        }
        KeyId(id)
    }
}

/// The host and the path a URL's request would be signed over.
///
/// `https://Hub.Example.org:443/adam/notes/offer.txt?v=1#top` is host
/// `hub.example.org` and path `/adam/notes/offer.txt?v=1`: the host in lower
/// case and without the scheme's own port, the path and query as written, and
/// the fragment gone, since a fragment never leaves the client.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Target {
    /// `http` or `https`, in lower case.
    pub scheme: String,
    /// The host, as the signed string has it.
    pub host: String,
    /// The path and query, as the signed string has it.
    pub path: String,
}

impl Target {
    /// Read a URL. Only `http` and `https` are taken, and never a URL with a
    /// user or password in it, which would be a second credential riding
    /// beside this one.
    pub fn of(url: &str) -> Result<Self, RequestError> {
        let refuse = |because: &'static str| RequestError::Url {
            url: url.to_owned(),
            because,
        };
        let (scheme, rest) = url
            .split_once("://")
            .ok_or_else(|| refuse("it has no scheme"))?;
        let scheme = scheme.to_ascii_lowercase();
        let default_port = match scheme.as_str() {
            "https" => ":443",
            "http" => ":80",
            _ => return Err(refuse("it is not http or https")),
        };
        let rest = rest.split('#').next().unwrap_or_default();
        let end = rest.find(['/', '?']).unwrap_or(rest.len());
        let (authority, path) = rest.split_at(end);
        if authority.contains('@') {
            return Err(refuse("it names a user, and the key is the credential"));
        }
        let mut host = authority.to_ascii_lowercase();
        if host.ends_with(default_port) {
            host.truncate(host.len() - default_port.len());
        }
        let path = match path {
            "" => "/".to_owned(),
            query if query.starts_with('?') => format!("/{query}"),
            path => path.to_owned(),
        };
        check_host(&host)?;
        check_path(&path)?;
        Ok(Self { scheme, host, path })
    }

    /// The scheme and host, as a URL begins: `https://hub.example.org`.
    pub fn origin(&self) -> String {
        format!("{}://{}", self.scheme, self.host)
    }
}

/// The string a request signature is over. See the [module](self) for the
/// grammar, which this is the one writer of.
///
/// Refused where a field could not be read back unambiguously: a method that
/// is not capital letters, a host with anything but a host's characters, a
/// path that does not begin with `/` or holds a space or a control character.
/// A newline in any of them would be a way to write a second line.
pub fn signed_string(
    method: &str,
    host: &str,
    path: &str,
    time: u64,
) -> Result<String, RequestError> {
    check_method(method)?;
    check_host(host)?;
    check_path(path)?;
    Ok(format!(
        "{PREAMBLE}\nmethod {method}\nhost {host}\npath {path}\ntime {time}\n"
    ))
}

/// Sign a request, giving the value of its `Authorization` header.
///
/// `time` is seconds since the Unix epoch, and the caller's to give because
/// the caller is the one with a clock: a page in a browser has `Date.now()`
/// and no `SystemTime`.
#[cfg(feature = "sign")]
pub fn sign_request(
    secret: &minisign::SecretKey,
    method: &str,
    host: &str,
    path: &str,
    time: u64,
) -> Result<String, RequestError> {
    let message = signed_string(method, host, path, time)?;
    let minisign = |because: String| RequestError::Minisign { because };
    let signed = minisign::sign(None, secret, message.as_bytes(), Some(""), None)
        .map_err(|error| minisign(error.to_string()))?
        .into_string();
    // The four lines `minisign -Sm` would write; the second and fourth are the
    // two signatures, and the header carries those and nothing else.
    let mut lines = signed.lines();
    let (Some(_), Some(line), Some(_), Some(global)) =
        (lines.next(), lines.next(), lines.next(), lines.next())
    else {
        return Err(minisign("a signature that was not four lines".to_owned()));
    };
    let mut bytes = base64::decode(line).ok_or_else(|| minisign("a signature line".into()))?;
    bytes.extend(base64::decode(global).ok_or_else(|| minisign("a global signature".into()))?);
    if bytes.len() != SIGNATURE_LINE_BYTES + 64 {
        return Err(minisign("a signature of the wrong length".to_owned()));
    }
    let mut id = [0u8; 8];
    id.copy_from_slice(&bytes[2..10]);
    Ok(format!(
        "{SCHEME} {} {time} {}",
        KeyId(id),
        base64::encode(&bytes)
    ))
}

/// A header, read: who says they signed it, when, and the signature.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Authorization {
    /// The key the header names.
    pub key: KeyId,
    /// The time it states, in seconds since the Unix epoch.
    pub time: u64,
    signature: Vec<u8>,
}

impl FromStr for Authorization {
    type Err = Refusal;

    /// The header's value, read strictly: the scheme, then exactly one space
    /// between each of three fields, and nothing before or after.
    ///
    /// The scheme alone is compared without regard to case, because HTTP says
    /// a scheme is case-insensitive (RFC 9110, section 11.1) and a server
    /// that refused `minisign` would be refusing a header the standard calls
    /// the same one. Every field after it has one spelling.
    fn from_str(header: &str) -> Result<Self, Self::Err> {
        let malformed = |because: &'static str| Refusal::Malformed { because };
        let mut fields = header.split(' ');
        let (Some(scheme), Some(key), Some(time), Some(signature), None) = (
            fields.next(),
            fields.next(),
            fields.next(),
            fields.next(),
            fields.next(),
        ) else {
            return Err(malformed(
                "a header is `Minisign <key-id> <time> <signature>`, one space apart",
            ));
        };
        if !scheme.eq_ignore_ascii_case(SCHEME) {
            return Err(malformed("the scheme is not `Minisign`"));
        }
        let key: KeyId = key.parse()?;
        let time = parse_time(time).ok_or_else(|| {
            malformed("a time is seconds since the Unix epoch, in decimal, with no leading zero")
        })?;
        if signature.len() != SIGNATURE_CHARS {
            return Err(malformed("a signature is 184 characters of base64"));
        }
        let signature = base64::decode(signature)
            .ok_or_else(|| malformed("a signature is 184 characters of base64"))?;
        if signature[..2] != PREHASHED {
            return Err(malformed(
                "the signature is not minisign's prehashed Ed25519",
            ));
        }
        if signature[2..10] != key.0 {
            return Err(malformed(
                "the signature was made by a key the header does not name",
            ));
        }
        Ok(Self {
            key,
            time,
            signature,
        })
    }
}

impl Authorization {
    /// The signature, as the four lines of a minisign signature file.
    ///
    /// What lets a server check a header with any minisign verifier, the
    /// `minisign` command included: this file, and the signed string as the
    /// message. [`verify_request`] checks it so itself.
    pub fn to_minisig(&self) -> String {
        let (line, global) = self.signature.split_at(SIGNATURE_LINE_BYTES);
        format!(
            "{UNTRUSTED_COMMENT}\n{}\ntrusted comment: \n{}\n",
            base64::encode(line),
            base64::encode(global)
        )
    }
}

/// Check a request's `Authorization` header, as a server does, and say which
/// key signed it.
///
/// `method`, `host` and `path` are the request as the server received it,
/// spelled as the [module](self) says. `now` is the server's time in seconds
/// since the Unix epoch, and `max_skew` how far the header's time may be from
/// it either way; [`DEFAULT_MAX_SKEW`] says why five minutes. `lookup` finds
/// the public key with an ID, among the keys this server would accept at all,
/// and its answer is the whole of who is believed: a key it does not return is
/// refused however good the signature.
///
/// Stateless. A server that must not act twice on one header remembers the
/// headers it accepted for as long as `max_skew`, and refuses one it has seen.
pub fn verify_request(
    header: &str,
    method: &str,
    host: &str,
    path: &str,
    now: u64,
    max_skew: u64,
    lookup: impl FnOnce(&KeyId) -> Option<Key>,
) -> Result<KeyId, Refusal> {
    let authorization: Authorization = header.parse()?;
    let message =
        signed_string(method, host, path, authorization.time).map_err(Refusal::Request)?;

    // The clock first: it costs nothing, and a header outside the window is
    // refused without asking anyone about its key.
    if authorization.time > now.saturating_add(max_skew) {
        return Err(Refusal::Future {
            time: authorization.time,
            now,
        });
    }
    if authorization.time < now.saturating_sub(max_skew) {
        return Err(Refusal::Stale {
            time: authorization.time,
            now,
        });
    }

    let key = lookup(&authorization.key).ok_or(Refusal::UnknownKey {
        key: authorization.key,
    })?;
    if key.id() != authorization.key {
        return Err(Refusal::WrongKey {
            asked: authorization.key,
            found: key.id(),
        });
    }
    let public = PublicKey::from_base64(key.as_str()).map_err(|error| Refusal::Signature {
        because: error.to_string(),
    })?;
    let signature =
        Signature::decode(&authorization.to_minisig()).map_err(|error| Refusal::Signature {
            because: error.to_string(),
        })?;
    public
        .verify(message.as_bytes(), &signature, false)
        .map_err(|error| Refusal::Signature {
            because: error.to_string(),
        })?;
    Ok(authorization.key)
}

/// Seconds since the epoch, in one spelling: digits, no sign, no leading zero.
fn parse_time(text: &str) -> Option<u64> {
    if text.is_empty()
        || !text.bytes().all(|byte| byte.is_ascii_digit())
        || (text.len() > 1 && text.starts_with('0'))
    {
        return None;
    }
    text.parse().ok()
}

fn check_method(method: &str) -> Result<(), RequestError> {
    if method.is_empty() || !method.bytes().all(|byte| byte.is_ascii_uppercase()) {
        return Err(RequestError::Method {
            found: method.to_owned(),
        });
    }
    Ok(())
}

fn check_host(host: &str) -> Result<(), RequestError> {
    let allowed =
        |byte: u8| byte.is_ascii_lowercase() || byte.is_ascii_digit() || b"-.:[]".contains(&byte);
    if host.is_empty() || !host.bytes().all(allowed) {
        return Err(RequestError::Host {
            found: host.to_owned(),
        });
    }
    Ok(())
}

fn check_path(path: &str) -> Result<(), RequestError> {
    if !path.starts_with('/') || !path.bytes().all(|byte| (0x21..=0x7e).contains(&byte)) {
        return Err(RequestError::Path {
            found: path.to_owned(),
        });
    }
    Ok(())
}

/// Why a request could not be signed, or its fields could not be read.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum RequestError {
    /// A method that is not capital letters.
    Method {
        /// What it was.
        found: String,
    },
    /// A host with something other than a host's characters in it, or with
    /// upper case, which the signed string never holds.
    Host {
        /// What it was.
        found: String,
    },
    /// A path that does not begin with `/`, or holds a byte outside printable
    /// ASCII: a space, a control character, or anything not escaped.
    Path {
        /// What it was.
        found: String,
    },
    /// A URL this cannot sign a request to.
    Url {
        /// The URL.
        url: String,
        /// Why not.
        because: &'static str,
    },
    /// minisign refused.
    Minisign {
        /// What it said.
        because: String,
    },
}

impl fmt::Display for RequestError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Method { found } => write!(f, "`{found}` is not a method in capitals"),
            Self::Host { found } => write!(
                f,
                "`{found}` is not a host in lower case, with its port only where it is not the \
                 scheme's own"
            ),
            Self::Path { found } => write!(
                f,
                "`{found}` is not a path as a request line sends one: it begins with `/` and \
                 every byte that is not printable ASCII is escaped"
            ),
            Self::Url { url, because } => write!(f, "`{url}` cannot be signed for: {because}"),
            Self::Minisign { because } => write!(f, "minisign: {because}"),
        }
    }
}

impl std::error::Error for RequestError {}

/// Why a server refuses a signed request.
///
/// Every variant is a refusal and none is an excuse: a server answers each
/// one with 401 and the same body, and what this says is for its log.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum Refusal {
    /// The header is not one this grammar can read.
    Malformed {
        /// What was wrong with it.
        because: &'static str,
    },
    /// The request itself has a field the signed string cannot hold.
    Request(RequestError),
    /// The header's time is further behind the server's than the window.
    Stale {
        /// The time the header states.
        time: u64,
        /// The server's.
        now: u64,
    },
    /// The header's time is further ahead of the server's than the window.
    Future {
        /// The time the header states.
        time: u64,
        /// The server's.
        now: u64,
    },
    /// No key this server accepts has the ID the header names.
    UnknownKey {
        /// The ID.
        key: KeyId,
    },
    /// The lookup answered with a key whose ID is not the one asked about.
    WrongKey {
        /// The ID the header names.
        asked: KeyId,
        /// The ID of the key the lookup gave.
        found: KeyId,
    },
    /// The signature does not check under the key.
    Signature {
        /// What minisign said.
        because: String,
    },
}

impl fmt::Display for Refusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Malformed { because } => write!(f, "a malformed header: {because}"),
            Self::Request(error) => write!(f, "a request that cannot be signed for: {error}"),
            Self::Stale { time, now } => write!(
                f,
                "a header made at {time}, {} seconds before {now}, which is too long ago",
                now - time
            ),
            Self::Future { time, now } => write!(
                f,
                "a header made at {time}, {} seconds after {now}, which is too far ahead",
                time - now
            ),
            Self::UnknownKey { key } => write!(f, "no key here has the ID {key}"),
            Self::WrongKey { asked, found } => {
                write!(f, "asked for the key {asked}, and given the key {found}")
            }
            Self::Signature { because } => write!(f, "the signature does not check: {because}"),
        }
    }
}

impl std::error::Error for Refusal {}

#[cfg(test)]
mod tests {
    use super::{KeyId, Target, parse_time, signed_string};

    #[test]
    fn the_signed_string_is_five_lines() {
        assert_eq!(
            signed_string(
                "GET",
                "hub.example.org",
                "/adam/notes/offer.txt",
                1760968324
            )
            .expect("a request"),
            "historica-request-1\nmethod GET\nhost hub.example.org\npath \
             /adam/notes/offer.txt\ntime 1760968324\n"
        );
        for (method, host, path) in [
            ("get", "hub.example.org", "/"),
            ("GET\nmethod POST", "hub.example.org", "/"),
            ("GET", "Hub.example.org", "/"),
            ("GET", "hub.example.org\npath /x", "/"),
            ("GET", "", "/"),
            ("GET", "hub.example.org", "offer.txt"),
            ("GET", "hub.example.org", "/a b"),
            ("GET", "hub.example.org", "/a\nb"),
            ("GET", "hub.example.org", "/ré"),
        ] {
            assert!(
                signed_string(method, host, path, 0).is_err(),
                "{method:?} {host:?} {path:?} was signable"
            );
        }
    }

    #[test]
    fn a_url_gives_the_host_and_path_a_browser_would() {
        let target =
            Target::of("HTTPS://Hub.Example.org:443/adam/notes/offer.txt?v=1#top").expect("a URL");
        assert_eq!(target.scheme, "https");
        assert_eq!(target.host, "hub.example.org");
        assert_eq!(target.path, "/adam/notes/offer.txt?v=1");
        assert_eq!(target.origin(), "https://hub.example.org");

        let target = Target::of("http://localhost:8787").expect("a URL");
        assert_eq!(target.host, "localhost:8787");
        assert_eq!(target.path, "/");
        assert_eq!(Target::of("http://h:80?x").expect("a URL").path, "/?x");

        for refused in [
            "hub.example.org/offer.txt",
            "ftp://hub.example.org/offer.txt",
            "https://adam:secret@hub.example.org/",
            "https:///offer.txt",
        ] {
            assert!(Target::of(refused).is_err(), "`{refused}` was accepted");
        }
    }

    #[test]
    fn a_key_id_has_one_spelling() {
        let id: KeyId = "E7620F1842B4E81F".parse().expect("an ID");
        assert_eq!(id.to_string(), "E7620F1842B4E81F");
        assert_eq!(id.bytes(), [0x1F, 0xE8, 0xB4, 0x42, 0x18, 0x0F, 0x62, 0xE7]);
        for refused in [
            "e7620f1842b4e81f",
            "E7620F1842B4E81",
            "0xE7620F1842B4E8",
            "",
        ] {
            assert!(
                refused.parse::<KeyId>().is_err(),
                "`{refused}` was accepted"
            );
        }
    }

    #[test]
    fn a_time_has_one_spelling() {
        assert_eq!(parse_time("0"), Some(0));
        assert_eq!(parse_time("1760968324"), Some(1760968324));
        for refused in ["", "01", "+1", "-1", "1.0", " 1", "99999999999999999999"] {
            assert_eq!(parse_time(refused), None, "`{refused}` was accepted");
        }
    }
}
