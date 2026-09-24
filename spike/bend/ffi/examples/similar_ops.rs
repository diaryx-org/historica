//! What `similar` makes of each pair `check.py` hands it: one case a line,
//! `old|new`, each side's items separated by spaces, and back one line of
//! operations a case — `capture_diff_slices(Algorithm::Histogram, ..)`, the
//! call `historica::diff` makes, or Myers where the old side begins `M:` —
//! spelled `E<old>,<new>,<len>`,
//! `D<old>,<len>,<new>`, `I<old>,<new>,<len>` and
//! `R<old>,<old len>,<new>,<new len>`.

use std::io::Read as _;

use similar::{Algorithm, DiffOp, capture_diff_slices};

fn main() {
    let mut input = String::new();
    std::io::stdin().read_to_string(&mut input).expect("cases on stdin");
    for case in input.lines() {
        let (old, new) = case.split_once('|').expect("a case is `old|new`");
        // `M:` asks for Myers, which is what `diff` draws a line's emphasis with.
        let (algorithm, old) = match old.strip_prefix("M:") {
            Some(old) => (Algorithm::Myers, old),
            None => (Algorithm::Histogram, old),
        };
        let old: Vec<&str> = old.split(' ').filter(|item| !item.is_empty()).collect();
        let new: Vec<&str> = new.split(' ').filter(|item| !item.is_empty()).collect();
        let spelled: Vec<String> = capture_diff_slices(algorithm, &old, &new)
            .into_iter()
            .map(|operation| match operation {
                DiffOp::Equal { old_index, new_index, len } => format!("E{old_index},{new_index},{len}"),
                DiffOp::Delete { old_index, old_len, new_index } => format!("D{old_index},{old_len},{new_index}"),
                DiffOp::Insert { old_index, new_index, new_len } => format!("I{old_index},{new_index},{new_len}"),
                DiffOp::Replace { old_index, old_len, new_index, new_len } => {
                    format!("R{old_index},{old_len},{new_index},{new_len}")
                }
            })
            .collect();
        println!("{}", spelled.join(" "));
    }
}
