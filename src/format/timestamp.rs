//! A timestamp with exactly one spelling.
//!
//! No timestamp participates in identity, causality, or ordering — decision
//! 0002 is emphatic about it — so this type exists to keep a *fact a person
//! cares about* from acquiring a second spelling, not to support arithmetic.
//! It holds the text it validated, which is what makes writing byte-exact.

use std::fmt;
use std::str::FromStr;

use super::error::{ParseError, ParseErrorKind};

/// An offset date-time, spelled `YYYY-MM-DDThh:mm:ss±hh:mm`.
///
/// Fractional seconds are not permitted, and neither is `Z`: one less spelling
/// to reproduce, and the offset is kept because "I wrote this at 9pm my time"
/// is the fact worth recording.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Timestamp(String);

/// Characters in a timestamp: `2025-08-19T00:47:11-06:00`.
const WIDTH: usize = 25;

impl Timestamp {
    /// Validate `value` as a timestamp, reporting against line `at`.
    pub(crate) fn parse(value: &str, at: usize) -> Result<Self, ParseError> {
        Self::check(value).map_err(|because| {
            ParseError::new(
                at,
                ParseErrorKind::MalformedTimestamp {
                    found: value.to_owned(),
                    because,
                },
            )
        })
    }

    fn check(value: &str) -> Result<Self, &'static str> {
        let bytes = value.as_bytes();
        if bytes.len() != WIDTH {
            return Err("it is the wrong length, or carries fractional seconds");
        }
        for (index, expected) in [
            (4, b'-'),
            (7, b'-'),
            (10, b'T'),
            (13, b':'),
            (16, b':'),
            (22, b':'),
        ] {
            if bytes[index] != expected {
                return Err("its separators are in the wrong places");
            }
        }
        let sign = bytes[19];
        if sign != b'+' && sign != b'-' {
            return Err("its offset needs a sign; `Z` is not a spelling this format has");
        }

        let number = |from: usize, to: usize| -> Result<u32, &'static str> {
            let slice = &value[from..to];
            if !slice.bytes().all(|b| b.is_ascii_digit()) {
                return Err("it holds something that is not a digit");
            }
            slice
                .parse()
                .map_err(|_| "it holds something that is not a digit")
        };

        let year = number(0, 4)?;
        let month = number(5, 7)?;
        let day = number(8, 10)?;
        let hour = number(11, 13)?;
        let minute = number(14, 16)?;
        let second = number(17, 19)?;
        let offset_hour = number(20, 22)?;
        let offset_minute = number(23, 25)?;

        if !(1..=12).contains(&month) {
            return Err("there is no such month");
        }
        if day < 1 || day > days_in_month(year, month) {
            return Err("there is no such day in that month");
        }
        if hour > 23 || minute > 59 || second > 59 {
            return Err("there is no such time of day");
        }
        if offset_hour > 23 || offset_minute > 59 {
            return Err("there is no such offset");
        }
        // RFC 3339 gives `-00:00` the distinct meaning "offset unknown", which
        // would be a second spelling of UTC that means something else.
        if sign == b'-' && offset_hour == 0 && offset_minute == 0 {
            return Err("`-00:00` means an unknown offset; write `+00:00` for UTC");
        }

        Ok(Self(value.to_owned()))
    }

    /// The timestamp as written.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// A timestamp that was not the one spelling this format has.
///
/// The parser reports the same fault with a line number attached; this is what
/// a caller outside a document gets — a writer checking its own clock, or a
/// test stating a time.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MalformedTimestamp {
    because: &'static str,
}

impl fmt::Display for MalformedTimestamp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "a timestamp is spelled `YYYY-MM-DDThh:mm:ss±hh:mm`, and {}",
            self.because
        )
    }
}

impl std::error::Error for MalformedTimestamp {}

impl FromStr for Timestamp {
    type Err = MalformedTimestamp;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        Self::check(value).map_err(|because| MalformedTimestamp { because })
    }
}

fn days_in_month(year: u32, month: u32) -> u32 {
    match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 if year.is_multiple_of(4) && (!year.is_multiple_of(100) || year.is_multiple_of(400)) => {
            29
        }
        2 => 28,
        _ => 0,
    }
}

impl fmt::Display for Timestamp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}
