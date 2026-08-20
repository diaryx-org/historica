//! `record` and `identity`: the two commands that write on a person's behalf.

use std::fs;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;

use historica::record::{
    Clock, Platform, Recording, identity, plan as plan_for, record as record_revision,
};
use historica::store::Store;
use historica::working::Working;

use super::{Failure, printing, target};

/// `record [-m <message>] [--onto <target>] [--move <old>=<new>] [--dry-run]`.
pub fn record(base: &Path, root: PathBuf, arguments: Vec<String>) -> Result<u8, Failure> {
    let mut message: Option<String> = None;
    let mut onto: Option<String> = None;
    let mut moves: Vec<(String, String)> = Vec::new();
    let mut dry_run = false;

    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        let mut value = |flag: &str| {
            arguments
                .next()
                .ok_or_else(|| Failure::usage(format!("`{flag}` wants a value")))
        };
        match argument.as_str() {
            "-m" | "--message" => message = Some(value("-m")?),
            "--onto" => onto = Some(value("--onto")?),
            "--move" => {
                let stated = value("--move")?;
                let (from, to) = stated
                    .split_once('=')
                    .ok_or_else(|| Failure::usage("`--move` is spelled `--move <old>=<new>`"))?;
                moves.push((from.to_owned(), to.to_owned()));
            }
            "-n" | "--dry-run" => dry_run = true,
            other => {
                return Err(Failure::usage(format!(
                    "`{other}` is not an argument `record` takes"
                )));
            }
        }
    }

    let mut store = Store::open(&root)?;
    let repository = root
        .parent()
        .ok_or_else(|| Failure::error("this store has no repository around it"))?
        .to_path_buf();

    // Decision 0011: the head is the position, and several heads mean a person
    // should be choosing rather than a tool.
    let parent = match onto {
        Some(spelling) => Some(target::resolve(&store, &spelling)?),
        None => heads(&store)?,
    };

    for (from, to) in &moves {
        perform(&repository, from, to)?;
    }

    let working = Working::read(&repository, store.skipped()).map_err(Failure::error)?;
    let mut platform = Platform;

    if dry_run {
        let plan =
            plan_for(&store, &working, parent, &moves, &mut platform).map_err(Failure::error)?;
        if plan.is_empty() {
            return printing(|out| writeln!(out, "nothing here differs from what is recorded"));
        }
        return printing(|out| {
            for (fact, path) in plan.facts() {
                writeln!(out, "{fact:<7} {path}")?;
            }
            Ok(())
        });
    }

    let author = identity::author_for(&repository).map_err(Failure::error)?;
    let when = platform.now().map_err(Failure::error)?;
    warn_about_the_clock(&store, &when);

    let message = match message {
        Some(message) => message,
        None => from_an_editor(base)?,
    };

    let recorded = record_revision(
        &mut store,
        &working,
        &Recording {
            onto: parent,
            author,
            when,
            message,
            moves,
        },
        &mut platform,
    )
    .map_err(Failure::error)?;

    printing(|out| {
        for (fact, path) in recorded.plan.facts() {
            writeln!(out, "{fact:<7} {path}")?;
        }
        writeln!(
            out,
            "recorded {} as {}",
            recorded.change.abbreviate(8),
            recorded.revision.abbreviate(12)
        )?;
        for name in &recorded.advanced {
            writeln!(out, "{name} -> {}", recorded.change.abbreviate(8))?;
        }
        if recorded.plan.parent.is_none() {
            writeln!(out, "this is a root: it has no parent")?;
        }
        Ok(())
    })
}

/// `identity <author>` — write the line a refusal to record asks for.
pub fn set_identity(arguments: Vec<String>) -> Result<u8, Failure> {
    let mut arguments = arguments.into_iter();
    let author = arguments
        .next()
        .ok_or_else(|| Failure::usage("`identity` wants a name, as `Name <you@example.com>`"))?;
    if let Some(extra) = arguments.next() {
        return Err(Failure::usage(format!(
            "`identity` takes one name, and `{extra}` is a second"
        )));
    }

    let path = identity::identity_path().ok_or_else(|| {
        Failure::error("this platform has no configuration directory to write to")
    })?;
    if let Some(directory) = path.parent() {
        fs::create_dir_all(directory)
            .map_err(|error| Failure::error(format!("{}: {error}", directory.display())))?;
    }
    if path.exists() {
        return Err(Failure::error(format!(
            "{} already exists; edit it rather than having it rewritten",
            path.display()
        )));
    }
    fs::write(&path, format!("author {author}\n"))
        .map_err(|error| Failure::error(format!("{}: {error}", path.display())))?;

    printing(|out| writeln!(out, "wrote {}", path.display()))
}

/// The one head to record against, or a refusal naming the choice.
fn heads(store: &Store) -> Result<Option<historica::core::RevisionId>, Failure> {
    let heads = store.history().heads();
    match heads.len() {
        0 => Ok(None),
        1 => Ok(heads.into_iter().next()),
        several => Err(Failure::error(format!(
            "this store has {several} heads, so nothing here is `the` latest; \
             name one with --onto:{}",
            heads
                .iter()
                .map(|head| format!("\n  {}", head.abbreviate(12)))
                .collect::<String>()
        ))),
    }
}

/// Perform a stated rename, in whichever state the folder is in.
///
/// Decision 0011: the flag works whether a person reached for `mv` first or
/// not, which is the only way a flag like this survives contact with how
/// people actually work.
fn perform(repository: &Path, from: &str, to: &str) -> Result<(), Failure> {
    let (old, new) = (repository.join(from), repository.join(to));
    match (old.exists(), new.exists()) {
        (true, false) => {
            if let Some(directory) = new.parent() {
                fs::create_dir_all(directory)
                    .map_err(|error| Failure::error(format!("{}: {error}", directory.display())))?;
            }
            fs::rename(&old, &new)
                .map_err(|error| Failure::error(format!("{from} -> {to}: {error}")))
        }
        (false, true) => Ok(()),
        (true, true) => Err(Failure::error(format!(
            "`{from}` and `{to}` are both here, so which one is the file is not \
             something to guess at"
        ))),
        (false, false) => Err(Failure::error(format!(
            "neither `{from}` nor `{to}` is here"
        ))),
    }
}

/// The message, from the editor a person has already chosen.
///
/// The template is empty and nothing is stripped: decision 0011 refuses to
/// interpret a body 0002 promises never to interpret, and a journal entry
/// beginning with a Markdown heading is the case that would lose its first
/// line.
fn from_an_editor(base: &Path) -> Result<String, Failure> {
    let Some(editor) = std::env::var_os("VISUAL")
        .or_else(|| std::env::var_os("EDITOR"))
        .filter(|editor| !editor.is_empty())
    else {
        return Err(Failure::usage(
            "no $VISUAL or $EDITOR here; say what this records with -m",
        ));
    };

    let path = std::env::temp_dir().join("historica-message");
    fs::write(&path, "").map_err(|error| Failure::error(format!("{}: {error}", path.display())))?;

    let status = Command::new(&editor)
        .arg(&path)
        .current_dir(base)
        .status()
        .map_err(|error| Failure::error(format!("{}: {error}", Path::new(&editor).display())))?;
    if !status.success() {
        return Err(Failure::error("the editor stopped without saving"));
    }

    let message = fs::read_to_string(&path)
        .map_err(|error| Failure::error(format!("{}: {error}", path.display())))?;
    let _ = fs::remove_file(&path);
    Ok(message)
}

/// Say something when this machine's clock disagrees with the store.
///
/// Decision 0010: the failure worth catching is the machine that says 1970,
/// because 0005 copies that into every later revision of the change. The
/// comparison is the front end's, on the same terms as `log`'s tie-break.
fn warn_about_the_clock(store: &Store, now: &historica::format::Timestamp) {
    let Some(newest) = store
        .iter()
        .map(|(_, document)| document.when.clone())
        .max_by_key(|when| instant(when.as_str()))
    else {
        return;
    };
    if instant(now.as_str()) < instant(newest.as_str()) {
        eprintln!(
            "historica: this machine's clock reads {now}, and this store already \
             holds work recorded at {newest}"
        );
    }
}

/// A timestamp as an instant, for a comparison presentation is allowed to make.
fn instant(spelled: &str) -> i128 {
    spelled
        .parse::<jiff::Timestamp>()
        .map(|instant| instant.as_nanosecond())
        .unwrap_or(i128::MIN)
}
