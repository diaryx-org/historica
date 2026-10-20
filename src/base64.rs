//! Base64, the standard alphabet with padding, as minisign spells it.
//!
//! Written out rather than linked because the build that needs it is the one
//! that must stay cheapest: [`crate::request`] splits and joins a minisign
//! signature in a verifier built with no features, whose only dependency is
//! `minisign-verify`, and that crate keeps its own decoder private.
//!
//! Strict in the one way that matters for a credential: a string decodes to
//! exactly one byte sequence and a byte sequence encodes to exactly one
//! string. No whitespace, no missing padding, and no stray bits in the last
//! character, so two spellings of one signature cannot both be accepted.

const ALPHABET: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

/// `bytes`, encoded.
pub(crate) fn encode(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len().div_ceil(3) * 4);
    for chunk in bytes.chunks(3) {
        let b = [
            chunk[0],
            chunk.get(1).copied().unwrap_or(0),
            chunk.get(2).copied().unwrap_or(0),
        ];
        let n = (u32::from(b[0]) << 16) | (u32::from(b[1]) << 8) | u32::from(b[2]);
        for (index, shift) in [18, 12, 6, 0].into_iter().enumerate() {
            if index <= chunk.len() {
                out.push(ALPHABET[((n >> shift) & 63) as usize] as char);
            } else {
                out.push('=');
            }
        }
    }
    out
}

/// `text`, decoded, or `None` where it is not the one spelling [`encode`]
/// would have written.
pub(crate) fn decode(text: &str) -> Option<Vec<u8>> {
    let text = text.as_bytes();
    if !text.len().is_multiple_of(4) {
        return None;
    }
    let mut out = Vec::with_capacity(text.len() / 4 * 3);
    let chunks = text.len() / 4;
    for (number, chunk) in text.chunks(4).enumerate() {
        let last = number + 1 == chunks;
        let padding = chunk.iter().rev().take_while(|&&byte| byte == b'=').count();
        if padding > 2 || (padding > 0 && !last) {
            return None;
        }
        let mut n: u32 = 0;
        for &byte in &chunk[..4 - padding] {
            n = (n << 6) | u32::from(value(byte)?);
        }
        n <<= 6 * padding as u32;
        let decoded = [(n >> 16) as u8, (n >> 8) as u8, n as u8];
        let kept = 3 - padding;
        // The bits a padded quantum leaves over must be zero, or two strings
        // would decode to the same bytes.
        if decoded[kept..].iter().any(|&byte| byte != 0) {
            return None;
        }
        out.extend_from_slice(&decoded[..kept]);
    }
    Some(out)
}

fn value(byte: u8) -> Option<u8> {
    match byte {
        b'A'..=b'Z' => Some(byte - b'A'),
        b'a'..=b'z' => Some(byte - b'a' + 26),
        b'0'..=b'9' => Some(byte - b'0' + 52),
        b'+' => Some(62),
        b'/' => Some(63),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::{decode, encode};

    #[test]
    fn the_test_vectors_round_trip() {
        for (bytes, text) in [
            (&b""[..], ""),
            (b"f", "Zg=="),
            (b"fo", "Zm8="),
            (b"foo", "Zm9v"),
            (b"foob", "Zm9vYg=="),
            (b"fooba", "Zm9vYmE="),
            (b"foobar", "Zm9vYmFy"),
        ] {
            assert_eq!(encode(bytes), text);
            assert_eq!(decode(text).as_deref(), Some(bytes));
        }
    }

    #[test]
    fn a_second_spelling_is_refused() {
        for refused in ["Zg", "Zg=", "Zh==", "Zm9v\n", "Z===", "Zg==Zg==", "Zm9-"] {
            assert_eq!(decode(refused), None, "`{refused}` was accepted");
        }
    }
}
