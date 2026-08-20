//! Showing a person where concurrent work met, so they can settle it.
//!
//! Specified by `docs/decisions/0012-conflicts.md`. Nothing here is recorded
//! and nothing here is stored: a conflict is a function of the graph, so the
//! two heads *are* the conflict, and this is the view of it a person edits.
//!
//! The rendering labels each run inside a contested span with the revision
//! that wrote it, which a three-way tool cannot do and this one gets free —
//! item *i* of revision *R* is named `(R, i)`, and [`crate::merge`] returns
//! those origins.

use crate::core::RevisionId;
use crate::merge::{Contest, Merged};

/// Digest characters a marker line carries.
const MARK: usize = 8;

/// The merged file as a person should see it, contested spans fenced.
///
/// A file with nothing contested renders as itself, byte for byte, which is
/// what makes this safe to write into a working copy unconditionally.
pub fn render(merged: &Merged) -> String {
    let items = merged.state.items();
    let mut out = String::new();
    let mut position = 0;

    // Adjacent contests are one fence. The merge reports a span per run, since
    // a run is what its author wrote, but a person looking at two runs that
    // meet is looking at one disagreement.
    let spans = coalesce(merged);

    for span in spans {
        if span.at < position {
            continue;
        }
        for item in &items[position..span.at.min(items.len())] {
            push(&mut out, &item.text, item.terminated);
        }
        position = span.at;

        if span.len == 0 {
            // A contest over items that are gone: one revision removed what
            // another wrote beside. There is no text to fence, so the line
            // itself is the whole of it, and deleting it is the resolution.
            out.push_str(&format!(
                "vvv historica: {} removed what was written here; delete this line ^^^\n",
                named(&span.revisions)
            ));
            continue;
        }

        let end = (span.at + span.len).min(items.len());
        let mut run: Option<RevisionId> = None;
        for (index, item) in items[span.at..end].iter().enumerate() {
            let origin = merged.origins.get(span.at + index).copied();
            if origin != run {
                if let Some(origin) = origin {
                    out.push_str(&format!(
                        "vvv historica: {} wrote vvv\n",
                        origin.abbreviate(MARK)
                    ));
                }
                run = origin;
            }
            push(&mut out, &item.text, item.terminated);
        }
        out.push_str("^^^ historica: resolve, then delete these lines ^^^\n");
        position = end;
    }

    for item in &items[position.min(items.len())..] {
        push(&mut out, &item.text, item.terminated);
    }
    out
}

/// One region a person is asked to look at.
struct Span {
    at: usize,
    len: usize,
    revisions: Vec<RevisionId>,
}

/// The contested spans, with the ones that touch joined into one.
fn coalesce(merged: &Merged) -> Vec<Span> {
    let mut spans: Vec<Span> = Vec::new();
    for contest in &merged.contested {
        // Decision 0012: two branches disagreeing about a final newline is not
        // a span anybody can mark up. It is reported and not rendered.
        if contest.kind == Contest::Terminator {
            continue;
        }
        match spans.last_mut() {
            Some(held) if contest.len > 0 && held.len > 0 && held.at + held.len == contest.at => {
                held.len += contest.len;
                held.revisions.extend(contest.revisions.iter().copied());
            }
            _ => spans.push(Span {
                at: contest.at,
                len: contest.len,
                revisions: contest.revisions.clone(),
            }),
        }
    }
    spans
}

/// Every line a rendering of this merge would write on its own account.
///
/// What `record` refuses to accept, per line rather than per span: a person
/// can edit inside a fence and leave it standing.
pub fn markers(merged: &Merged) -> Vec<String> {
    let rendered = render(merged);
    let plain = merged.state.text();
    rendered
        .lines()
        .filter(|line| is_marker(line))
        .filter(|line| !plain.lines().any(|held| held == *line))
        .map(str::to_owned)
        .collect()
}

/// The marker lines still standing in `text`.
///
/// Scoped to a merge record, which is what lets a document *about* merge
/// markers be ordinary content the rest of the time.
pub fn unresolved(merged: &Merged, text: &str) -> Vec<String> {
    let standing: Vec<String> = markers(merged);
    text.lines()
        .filter(|line| standing.iter().any(|marker| marker == line))
        .map(str::to_owned)
        .collect()
}

/// Whether a line is one this module writes.
fn is_marker(line: &str) -> bool {
    (line.starts_with("vvv historica: ") && line.ends_with("vvv"))
        || (line.starts_with("vvv historica: ") && line.ends_with("^^^"))
        || line.starts_with("^^^ historica: ")
}

/// The revisions that met, abbreviated and joined for a person to read.
fn named(revisions: &[RevisionId]) -> String {
    if revisions.is_empty() {
        return "concurrent work".to_owned();
    }
    revisions
        .iter()
        .map(|revision| revision.abbreviate(MARK))
        .collect::<Vec<_>>()
        .join(" and ")
}

fn push(out: &mut String, text: &str, terminated: bool) {
    out.push_str(text);
    if terminated {
        out.push('\n');
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::merge::Contested;
    use crate::replay::State;

    fn revision(byte: u8) -> RevisionId {
        let mut bytes = [0u8; 32];
        bytes[0] = byte;
        RevisionId::from_bytes(bytes)
    }

    fn merged(text: &str, origins: &[u8], contested: Vec<Contested>) -> Merged {
        Merged {
            state: State::from_text(text),
            origins: origins.iter().map(|byte| revision(*byte)).collect(),
            contested,
        }
    }

    #[test]
    fn a_file_with_nothing_contested_renders_as_itself() {
        let merged = merged("one\ntwo\n", &[1, 1], Vec::new());
        assert_eq!(render(&merged), "one\ntwo\n");
        assert!(markers(&merged).is_empty());
    }

    #[test]
    fn a_contested_span_is_fenced_and_labelled_by_who_wrote_each_run() {
        let merged = merged(
            "one\nmine\ntheirs\nlast\n",
            &[1, 2, 3, 1],
            vec![Contested {
                at: 1,
                len: 2,
                revisions: vec![revision(2), revision(3)],
                kind: Contest::Insertion,
            }],
        );
        assert_eq!(
            render(&merged),
            "one\n\
             vvv historica: 02000000 wrote vvv\n\
             mine\n\
             vvv historica: 03000000 wrote vvv\n\
             theirs\n\
             ^^^ historica: resolve, then delete these lines ^^^\n\
             last\n"
        );
    }

    #[test]
    fn a_contest_over_items_that_are_gone_is_one_line_to_delete() {
        let merged = merged(
            "one\n",
            &[1],
            vec![Contested {
                at: 0,
                len: 0,
                revisions: vec![revision(2), revision(3)],
                kind: Contest::Deletion,
            }],
        );
        let rendered = render(&merged);
        assert!(rendered.starts_with("vvv historica: 02000000 and 03000000 removed"));
        assert!(rendered.ends_with("one\n"));
    }

    #[test]
    fn a_terminator_contest_is_reported_and_not_rendered() {
        let merged = merged(
            "one\ntwo\n",
            &[1, 1],
            vec![Contested {
                at: 0,
                len: 1,
                revisions: Vec::new(),
                kind: Contest::Terminator,
            }],
        );
        assert_eq!(render(&merged), "one\ntwo\n");
    }

    #[test]
    fn a_marker_a_person_left_standing_is_found_and_one_they_wrote_is_not() {
        let merged = merged(
            "one\nmine\ntheirs\n",
            &[1, 2, 3],
            vec![Contested {
                at: 1,
                len: 2,
                revisions: vec![revision(2), revision(3)],
                kind: Contest::Insertion,
            }],
        );

        let half_fixed = "one\nvvv historica: 02000000 wrote vvv\nmine and theirs\n";
        assert_eq!(unresolved(&merged, half_fixed).len(), 1);

        // A document about merge markers is ordinary content: nothing here
        // rendered these, so nothing refuses them.
        let prose = "one\nA fence reads `vvv historica: 0badbeef wrote vvv`.\n";
        assert!(unresolved(&merged, prose).is_empty());
    }
}
