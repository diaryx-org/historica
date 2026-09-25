//! What `unicode-normalization` knows, for `nfc.bend`: the tables it is
//! written from, and the normal form it is held to.
//!
//! `nfc_tables tables` asks the crate about every scalar value and prints
//! one line per fact, in code point order:
//!
//! - `c <x> <class>` for each character whose canonical combining class is
//!   not 0;
//! - `d <x> <y>..` for each character whose full canonical decomposition is
//!   not itself, Hangul syllables aside, which are arithmetic;
//! - `p <a> <b> <x>` for each pair `compose(a, b)` joins into `x`, Hangul
//!   aside again, in order of `a` and then `b`.
//!
//! and last `u <major>.<minor>.<update>`, the Unicode version. Every number
//! is hexadecimal. A pair is found by asking `compose` of every two
//! characters that decompose or appear in a decomposition: a primary
//! composite's two halves are each one or the other, so no pair is missed.
//!
//! `nfc_tables nfc` reads lines on standard input and prints, for each that
//! is not empty, its normal form C as the Rust tool computes it
//! (`historica::format::nfc` is `str::nfc` behind a quick check) and its
//! normal form D, each as code points in decimal, spaced, with a bar
//! between: what `nfc.bend`'s own `main` prints of the same lines.

use std::collections::BTreeSet;
use std::io::{BufRead as _, Write as _};

use unicode_normalization::char::{canonical_combining_class, compose, decompose_canonical};
use unicode_normalization::{UnicodeNormalization as _, UNICODE_VERSION};

fn hangul(c: char) -> bool {
    ('\u{AC00}'..='\u{D7A3}').contains(&c)
}

fn scalars() -> impl Iterator<Item = char> {
    (0u32..=0x10FFFF).filter_map(char::from_u32)
}

fn tables(out: &mut impl std::io::Write) -> std::io::Result<()> {
    for c in scalars() {
        let class = canonical_combining_class(c);
        if class != 0 {
            writeln!(out, "c {:x} {:x}", c as u32, class)?;
        }
    }
    let mut touched = BTreeSet::new();
    for c in scalars() {
        let mut parts = Vec::new();
        decompose_canonical(c, |d| parts.push(d));
        if hangul(c) {
            touched.insert(c);
            touched.extend(parts.iter().copied());
            continue;
        }
        if parts != [c] {
            touched.insert(c);
            touched.extend(parts.iter().copied());
            let spelled: Vec<String> = parts.iter().map(|d| format!("{:x}", *d as u32)).collect();
            writeln!(out, "d {:x} {}", c as u32, spelled.join(" "))?;
        }
    }
    for &a in &touched {
        for &b in &touched {
            if let Some(x) = compose(a, b) {
                if !hangul(x) {
                    writeln!(out, "p {:x} {:x} {:x}", a as u32, b as u32, x as u32)?;
                }
            }
        }
    }
    let (major, minor, update) = UNICODE_VERSION;
    writeln!(out, "u {major}.{minor}.{update}")
}

fn main() -> std::io::Result<()> {
    let stdout = std::io::stdout();
    let mut out = std::io::BufWriter::new(stdout.lock());
    match std::env::args().nth(1).as_deref() {
        Some("tables") => tables(&mut out)?,
        Some("nfc") => {
            let shown = |chars: &mut dyn Iterator<Item = char>| {
                chars.map(|c| (c as u32).to_string()).collect::<Vec<_>>().join(" ")
            };
            for line in std::io::stdin().lock().lines() {
                let line = line?;
                if line.is_empty() {
                    continue;
                }
                writeln!(out, "{}|{}", shown(&mut line.nfc()), shown(&mut line.nfd()))?;
            }
        }
        _ => {
            eprintln!("usage: nfc_tables tables | nfc_tables nfc < lines");
            std::process::exit(2);
        }
    }
    out.flush()
}
