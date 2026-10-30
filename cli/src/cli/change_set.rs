//! `change-set`: proposing a line of work beside the history, and deciding it.
//!
//! Decision 0090. The library holds the whole of what a change set is. This
//! is the spelling a person types: a list, one change set shown, and the four
//! acts. Recording a step is `record --onto change-sets/<id>`, and the merge
//! an acceptance names is `record --merge change-sets/<id>`, because each is
//! a record like any other.

use std::io::Write as _;
use std::path::{Path, PathBuf};

use historica::change_set::{
    self, CHANGE_SETS, ChangeSet, Declining, Part, Proposing, State, tip_name,
};
use historica::core::ChangeId;
use historica::record::{Clock as _, Platform, identity};
use historica::store::Store;

use super::record::{from_an_editor, warn_about_the_clock};
use super::{Failure, printing, target};

/// `change-set [list | show <id> | propose | submit <id> | accept <id>
/// [<merge>] | decline <id>]`.
pub fn change_set(base: &Path, root: PathBuf, arguments: Vec<String>) -> Result<u8, Failure> {
    let mut arguments = arguments.into_iter();
    let verb = arguments.next().unwrap_or_else(|| "list".to_owned());
    let rest: Vec<String> = arguments.collect();
    match verb.as_str() {
        "list" => list(root, rest),
        "show" => show(root, rest),
        "propose" => propose(base, root, rest),
        "submit" => submit(root, rest),
        "accept" => accept(root, rest),
        "decline" => decline(base, root, rest),
        other => Err(Failure::usage(format!(
            "`change-set {other}` is not a thing a change set does; it takes \
             list, show, propose, submit, accept, or decline"
        ))),
    }
}

/// The change set a person named: its id, a prefix of it, or its bookmark.
fn named(store: &Store, spelling: &str) -> Result<ChangeId, Failure> {
    let spelling = spelling
        .strip_prefix(CHANGE_SETS)
        .and_then(|rest| rest.strip_prefix('/'))
        .unwrap_or(spelling);
    let matching: Vec<ChangeId> = store
        .names()
        .keys()
        .filter_map(|name| match Part::of(name) {
            Some(Part::Tip(id)) if id.to_string().starts_with(spelling) => Some(id),
            _ => None,
        })
        .collect();
    match matching.as_slice() {
        _ if spelling.is_empty() => Err(Failure::usage("a change set cannot be empty")),
        [one] => Ok(*one),
        [] => Err(Failure::error(format!(
            "there is no change set `{spelling}` here; `historica change-set` lists them"
        ))),
        several => Err(Failure::error(format!(
            "`{spelling}` begins {} change sets' ids; type more of it",
            several.len()
        ))),
    }
}

/// One argument, the change set, and nothing else.
fn one(verb: &str, rest: &[String]) -> Result<String, Failure> {
    match rest {
        [one] => Ok(one.clone()),
        [] => Err(Failure::usage(format!(
            "`change-set {verb}` wants the change set"
        ))),
        [_, extra, ..] => Err(Failure::usage(format!(
            "`change-set {verb}` takes one change set, and `{extra}` is a second"
        ))),
    }
}

/// `-m <message>` among the rest, and what is left.
fn message_and(rest: Vec<String>) -> Result<(Option<String>, Vec<String>), Failure> {
    let mut message = None;
    let mut left = Vec::new();
    let mut rest = rest.into_iter();
    while let Some(argument) = rest.next() {
        match argument.as_str() {
            "-m" | "--message" => {
                message = Some(
                    rest.next()
                        .ok_or_else(|| Failure::usage("`-m` wants a value"))?,
                );
            }
            _ => left.push(argument),
        }
    }
    Ok((message, left))
}

fn failed(error: change_set::ChangeSetError) -> Failure {
    Failure::error(error)
}

/// One line per change set, newest first.
fn list(root: PathBuf, rest: Vec<String>) -> Result<u8, Failure> {
    if let Some(extra) = rest.first() {
        return Err(Failure::usage(format!(
            "`change-set list` takes no arguments, and `{extra}` is one"
        )));
    }
    let store = super::cache::open(&root)?;
    let change_sets = store.change_sets()?;
    printing(|out| {
        for change_set in &change_sets {
            let steps = change_set.steps.len();
            writeln!(
                out,
                "{}  {:<9}  {} step{}  {}  {}",
                change_set.id.abbreviate(12),
                change_set.state().as_str(),
                steps,
                if steps == 1 { "" } else { "s" },
                change_set.author,
                change_set.title,
            )?;
        }
        Ok(())
    })
}

/// Everything one change set says.
fn show(root: PathBuf, rest: Vec<String>) -> Result<u8, Failure> {
    let spelling = one("show", &rest)?;
    let store = super::cache::open(&root)?;
    let id = named(&store, &spelling)?;
    let change_set = store.change_set(&id).map_err(failed)?;
    let messages: Vec<(String, String)> = change_set
        .steps
        .iter()
        .map(|step| {
            let message = store
                .revision(step)
                .map(|revision| revision.message.lines().next().unwrap_or("").to_owned())
                .unwrap_or_default();
            (step.abbreviate(12), message)
        })
        .collect();
    printing(|out| {
        writeln!(out, "change set {}", tip_name(&change_set.id))?;
        writeln!(out, "title      {}", change_set.title)?;
        writeln!(out, "author     {}", change_set.author)?;
        writeln!(out, "created    {}", change_set.created)?;
        writeln!(out, "state      {}", change_set.state())?;
        for base in &change_set.base {
            writeln!(out, "base       {}", base.abbreviate(12))?;
        }
        writeln!(out, "opening    {}", change_set.opening.abbreviate(12))?;
        for (step, message) in &messages {
            writeln!(out, "step       {step}  {message}")?;
        }
        writeln!(out, "tip        {}", change_set.tip.abbreviate(12))?;
        for step in &change_set.after {
            writeln!(
                out,
                "after      {}  recorded before its decision was heard of, and not part of it",
                step.abbreviate(12)
            )?;
        }
        for (label, fact) in [
            ("submitted", change_set.submitted),
            ("accepted", change_set.accepted),
            ("declined", change_set.declined),
        ] {
            if let Some(revision) = fact {
                writeln!(out, "{label:<10} {}", revision.abbreviate(12))?;
            }
        }
        if !change_set.description.is_empty() {
            writeln!(out)?;
            writeln!(out, "{}", change_set.description)?;
        }
        Ok(())
    })
}

/// `propose [-m <title>] [--on <target>]`: an opening on the head, or on
/// what `--on` names.
fn propose(base: &Path, root: PathBuf, rest: Vec<String>) -> Result<u8, Failure> {
    let (message, rest) = message_and(rest)?;
    let mut on = None;
    let mut rest = rest.into_iter();
    while let Some(argument) = rest.next() {
        match argument.as_str() {
            "--on" => {
                on = Some(
                    rest.next()
                        .ok_or_else(|| Failure::usage("`--on` wants a target"))?,
                );
            }
            other => {
                return Err(Failure::usage(format!(
                    "`{other}` is not an argument `change-set propose` takes"
                )));
            }
        }
    }
    let mut store = super::cache::open(&root)?;
    let repository = root
        .parent()
        .ok_or_else(|| Failure::error("this store has no repository around it"))?
        .to_path_buf();
    let on = match on {
        Some(spelling) => vec![target::resolve(&store, &spelling)?],
        None => target::the_head(&store)?.into_iter().collect(),
    };
    let author = identity::author_for(&repository).map_err(Failure::error)?;
    let mut platform = Platform;
    let when = platform.now().map_err(Failure::error)?;
    warn_about_the_clock(&store, &when);
    let message = match message {
        Some(message) => message,
        None => from_an_editor(base)?,
    };
    let proposed = change_set::propose(
        &mut store,
        &Proposing {
            on,
            author,
            when,
            message,
            extensions: Default::default(),
        },
        &mut platform,
    )
    .map_err(failed)?;
    printing(|out| {
        writeln!(out, "proposed {}: \"{}\"", proposed.name(), proposed.title)?;
        writeln!(
            out,
            "record its steps with `historica record --onto {}`",
            proposed.name()
        )
    })
}

fn submit(root: PathBuf, rest: Vec<String>) -> Result<u8, Failure> {
    let spelling = one("submit", &rest)?;
    let mut store = super::cache::open(&root)?;
    let id = named(&store, &spelling)?;
    let submitted = change_set::submit(&mut store, &id).map_err(failed)?;
    printing(|out| {
        writeln!(
            out,
            "submitted {} at {}",
            submitted.name(),
            submitted.tip.abbreviate(12)
        )
    })
}

/// `accept <id> [<merge>]`: name the merge that took the line in. With no
/// merge named, the one merge in the store naming the tip.
fn accept(root: PathBuf, rest: Vec<String>) -> Result<u8, Failure> {
    let (spelling, merge) = match rest.as_slice() {
        [spelling] => (spelling.clone(), None),
        [spelling, merge] => (spelling.clone(), Some(merge.clone())),
        [] => return Err(Failure::usage("`change-set accept` wants the change set")),
        [_, _, extra, ..] => {
            return Err(Failure::usage(format!(
                "`change-set accept` takes a change set and a merge, and `{extra}` is a third"
            )));
        }
    };
    let mut store = super::cache::open(&root)?;
    let id = named(&store, &spelling)?;
    let acceptance = match merge {
        Some(merge) => target::resolve(&store, &merge)?,
        None => {
            let candidates = store.acceptances(&id).map_err(failed)?;
            match candidates.as_slice() {
                [one] => *one,
                [] => {
                    let tip = tip_name(&id);
                    return Err(Failure::error(format!(
                        "nothing here merges {tip} yet: accepting is a merge, so \
                         `historica update {tip}`, then `historica record --onto \
                         <your head> --merge {tip}`, then accept again"
                    )));
                }
                several => {
                    return Err(Failure::error(format!(
                        "{} merges name {}'s tip; say which one accepts it:\n{}",
                        several.len(),
                        tip_name(&id),
                        target::listed(several.iter().map(|id| id.abbreviate(12)))
                    )));
                }
            }
        }
    };
    let accepted = change_set::accept(&mut store, &id, acceptance).map_err(failed)?;
    printing(|out| report(out, &accepted, State::Accepted))
}

/// `decline <id> [-m <why>]`: one tombstone over the opening and every step.
fn decline(base: &Path, root: PathBuf, rest: Vec<String>) -> Result<u8, Failure> {
    let (message, rest) = message_and(rest)?;
    let spelling = one("decline", &rest)?;
    let mut store = super::cache::open(&root)?;
    let repository = root
        .parent()
        .ok_or_else(|| Failure::error("this store has no repository around it"))?
        .to_path_buf();
    let id = named(&store, &spelling)?;
    let author = identity::author_for(&repository).map_err(Failure::error)?;
    let mut platform = Platform;
    let when = platform.now().map_err(Failure::error)?;
    let message = match message {
        Some(message) => message,
        None => from_an_editor(base)?,
    };
    let declined = change_set::decline(
        &mut store,
        &id,
        &Declining {
            author,
            when,
            message,
        },
        &mut platform,
    )
    .map_err(failed)?;
    printing(|out| report(out, &declined, State::Declined))
}

fn report(
    out: &mut impl std::io::Write,
    change_set: &ChangeSet,
    state: State,
) -> std::io::Result<()> {
    let by = match state {
        State::Accepted => change_set.accepted,
        _ => change_set.declined,
    };
    writeln!(
        out,
        "{state} {}: \"{}\"{}",
        change_set.name(),
        change_set.title,
        by.map(|revision| format!(", by {}", revision.abbreviate(12)))
            .unwrap_or_default()
    )
}
