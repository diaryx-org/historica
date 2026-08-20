//! The measurement behind decision 0009's choice of matcher.
//!
//! `docs/decisions/0009-diff.md` chooses `Algorithm::Histogram` on a small
//! margin, and a margin nobody can reproduce is an opinion. This generates
//! prose-shaped edits — paragraphs separated by blank lines, drawn from a small
//! vocabulary so that repeated lines are common — and compares every algorithm
//! `similar` offers on the same pairs.
//!
//! ```console
//! cargo run --release --example matchers
//! ```
//!
//! The generator is seeded, so the table in 0009 is the table this prints.
//! What matters is the operation count: every operation is a permanent event,
//! and a concurrent edit interleaves between operations rather than inside one.

use similar::{Algorithm, DiffOp, capture_diff_slices};

/// xorshift64*, so that a surprising result can be looked at again.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    fn below(&mut self, bound: usize) -> usize {
        (self.next() % bound as u64) as usize
    }
}

/// A file of paragraphs, each a few lines, each followed by a blank line.
fn prose(rng: &mut Rng, paragraphs: usize, vocabulary: usize) -> Vec<String> {
    let mut out = Vec::new();
    for _ in 0..paragraphs {
        for _ in 0..1 + rng.below(4) {
            out.push(format!("sentence {}", rng.below(vocabulary)));
        }
        out.push(String::new());
    }
    out
}

/// Edit it the way a person does: remove a run, add a paragraph, reword a line.
fn edit(rng: &mut Rng, file: &[String], edits: usize, vocabulary: usize) -> Vec<String> {
    let mut out = file.to_vec();
    for _ in 0..edits {
        if out.is_empty() {
            break;
        }
        let at = rng.below(out.len());
        match rng.below(3) {
            0 => {
                let run = 1 + rng.below(3.min(out.len() - at));
                out.drain(at..at + run);
            }
            1 => {
                let paragraph = prose(rng, 1, vocabulary);
                out.splice(at..at, paragraph);
            }
            _ => out[at] = format!("sentence {}", rng.below(vocabulary)),
        }
    }
    out
}

fn main() {
    const ROUNDS: usize = 3000;
    let algorithms = [
        Algorithm::Myers,
        Algorithm::RawMyers,
        Algorithm::Patience,
        Algorithm::Histogram,
        Algorithm::Hunt,
    ];

    let mut rng = Rng(0x1234_5678_9abc_def0);
    let mut differs = vec![0usize; algorithms.len()];
    let mut operations = vec![0usize; algorithms.len()];
    let mut items = vec![0usize; algorithms.len()];

    for _ in 0..ROUNDS {
        let vocabulary = 3 + rng.below(20);
        let paragraphs = 2 + rng.below(12);
        let parent = prose(&mut rng, paragraphs, vocabulary);
        let edits = 1 + rng.below(5);
        let child = edit(&mut rng, &parent, edits, vocabulary);

        let scripts: Vec<Vec<DiffOp>> = algorithms
            .iter()
            .map(|algorithm| capture_diff_slices(*algorithm, &parent, &child))
            .collect();

        for (index, script) in scripts.iter().enumerate() {
            if *script != scripts[0] {
                differs[index] += 1;
            }
            operations[index] += script
                .iter()
                .filter(|operation| !matches!(operation, DiffOp::Equal { .. }))
                .count();
            items[index] += script
                .iter()
                .map(|operation| match operation {
                    DiffOp::Equal { .. } => 0,
                    DiffOp::Delete { old_len, .. } => *old_len,
                    DiffOp::Insert { new_len, .. } => *new_len,
                    DiffOp::Replace {
                        old_len, new_len, ..
                    } => old_len + new_len,
                })
                .sum::<usize>();
        }
    }

    println!("{ROUNDS} random prose edits, compared against Myers:\n");
    println!("| Algorithm | Differs from Myers | Operations | Items touched |");
    println!("| --- | --- | --- | --- |");
    for (index, algorithm) in algorithms.iter().enumerate() {
        let percentage = 100.0 * differs[index] as f64 / ROUNDS as f64;
        let differs = if index == 0 {
            "—".to_owned()
        } else {
            format!("{percentage:.1}%")
        };
        println!(
            "| {algorithm:?} | {differs} | {} | {} |",
            operations[index], items[index]
        );
    }
}
