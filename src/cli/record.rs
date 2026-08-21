//! `record` and `identity`: the two commands that write on a person's behalf.

use std::collections::BTreeMap;
use std::fs;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;

use historica::conflict;
use historica::core::{FileId, RevisionId};
use historica::record::{
    Amendment, Clock, Platform, Recording, amend as amend_revision, amendment_plan, identity,
    plan as plan_for, record as record_revision,
};
use historica::store::Store;
use historica::tree::{Kind, TreeContest};
use historica::working::Working;

use super::{Failure, printing, render, target};

/// `record [-m <message>] [--onto <target>] [--move <old>=<new>] [--dry-run]`.
pub fn record(base: &Path, root: PathBuf, arguments: Vec<String>) -> Result<u8, Failure> {
    let mut message: Option<String> = None;
    let mut onto: Option<String> = None;
    let mut joining: Vec<String> = Vec::new();
    let mut moves: Vec<(String, String)> = Vec::new();
    let mut at: Vec<(FileId, String)> = Vec::new();
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
            "--merge" => joining.push(value("--merge")?),
            "--at" => {
                let stated = value("--at")?;
                let (file, path) = stated
                    .split_once('=')
                    .ok_or_else(|| Failure::usage("`--at` is spelled `--at <file>=<path>`"))?;
                let file = file
                    .parse::<FileId>()
                    .map_err(|_| Failure::usage(format!("`{file}` is not a file identifier")))?;
                at.push((file, path.to_owned()));
            }
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
    // should be choosing rather than a tool. 0015 moved the rule to `target`,
    // so `status` derives the same position this does.
    let parents = target::parents(&store, onto.as_deref(), &joining)?;

    for (from, to) in &moves {
        perform(&repository, from, to)?;
    }

    let working = Working::read(&repository, store.skipped()).map_err(Failure::error)?;
    let mut platform = Platform;

    let recording = |author: String, when, message| Recording {
        parents: parents.clone(),
        author,
        when,
        message,
        moves: moves.clone(),
        at: at.clone(),
    };

    if dry_run {
        let asked = recording(String::new(), placeholder(), String::new());
        let plan = plan_for(&store, &working, &asked, &mut platform).map_err(Failure::error)?;
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
        &recording(author, when, message),
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
        if recorded.plan.parents.is_empty() {
            writeln!(out, "this is a root: it has no parent")?;
        }
        if recorded.plan.parents.len() > 1 {
            writeln!(
                out,
                "this joins {} lines of work",
                recorded.plan.parents.len()
            )?;
        }
        Ok(())
    })
}

/// `amend [<target>] [-m <message>] [--move <old>=<new>] [--dry-run]`.
///
/// Decision 0023: the head, rewritten as the folder now stands. Everything
/// that describes the work is the amended revision's and everything the folder
/// says is worked out again, so the only thing this command has to be given is
/// a message — and only where the person wants a different one.
pub fn amend(root: PathBuf, arguments: Vec<String>) -> Result<u8, Failure> {
    let mut message: Option<String> = None;
    let mut moves: Vec<(String, String)> = Vec::new();
    let mut named: Option<String> = None;
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
            "--move" => {
                let stated = value("--move")?;
                let (from, to) = stated
                    .split_once('=')
                    .ok_or_else(|| Failure::usage("`--move` is spelled `--move <old>=<new>`"))?;
                moves.push((from.to_owned(), to.to_owned()));
            }
            "-n" | "--dry-run" => dry_run = true,
            other if other.starts_with('-') => {
                return Err(Failure::usage(format!(
                    "`{other}` is not an argument `amend` takes"
                )));
            }
            other if named.is_none() => named = Some(other.to_owned()),
            other => {
                return Err(Failure::usage(format!(
                    "`amend` rewrites one revision, and `{other}` is a second"
                )));
            }
        }
    }

    let mut store = Store::open(&root)?;
    let repository = root
        .parent()
        .ok_or_else(|| Failure::error("this store has no repository around it"))?
        .to_path_buf();

    let revision = match &named {
        Some(spelling) => target::resolve(&store, spelling)?,
        None => target::the_head(&store)?.ok_or_else(|| {
            Failure::error("this store holds no revisions yet, so there is nothing to rewrite")
        })?,
    };

    for (from, to) in &moves {
        perform(&repository, from, to)?;
    }

    let working = Working::read(&repository, store.skipped()).map_err(Failure::error)?;
    let mut platform = Platform;

    if dry_run {
        let asked = Amendment {
            revision,
            message: message.clone(),
            reviser: String::new(),
            revised: placeholder(),
            moves: moves.clone(),
        };
        let plan =
            amendment_plan(&store, &working, &asked, &mut platform).map_err(Failure::error)?;
        return printing(|out| {
            for (fact, path) in plan.facts() {
                writeln!(out, "{fact:<7} {path}")?;
            }
            // Every fact the amendment would state, and not "nothing here
            // differs": an amendment restates the whole of what its
            // predecessor said, so an unchanged folder is a full plan rather
            // than an empty one — and an amendment that would change nothing
            // at all is a refusal by then, not a line of a report.
            writeln!(out, "this would supersede {}", revision.abbreviate(12))
        });
    }

    let reviser = identity::author_for(&repository).map_err(Failure::error)?;
    let revised = platform.now().map_err(Failure::error)?;
    warn_about_the_clock(&store, &revised);

    let amendment = Amendment {
        revision,
        message,
        reviser,
        revised,
        moves,
    };
    let amended =
        amend_revision(&mut store, &working, &amendment, &mut platform).map_err(Failure::error)?;

    printing(|out| {
        for (fact, path) in amended.plan.facts() {
            writeln!(out, "{fact:<7} {path}")?;
        }
        writeln!(
            out,
            "amended {} as {}",
            amended.change.abbreviate(8),
            amended.revision.abbreviate(12)
        )?;
        // Decision 0013: there is no operation log here, so the revision this
        // replaced is the record of what the work was before. Printing its
        // digest is what makes the undo something a person can still type.
        writeln!(
            out,
            "it supersedes {}, which is still here",
            amended.superseded.abbreviate(12)
        )
    })
}

/// `merge <target>` — write what two lines of work say together.
///
/// Decision 0012: nothing conflicted is recorded and nothing is remembered.
/// This renders the merge into the folder and prints the command that records
/// it, so the pending merge lives in the person's terminal.
pub fn merge(root: PathBuf, arguments: Vec<String>) -> Result<u8, Failure> {
    let spellings: Vec<String> = arguments;
    if spellings.is_empty() {
        return Err(Failure::usage("`merge` wants the work to join"));
    }

    let store = Store::open(&root)?;
    let repository = root
        .parent()
        .ok_or_else(|| Failure::error("this store has no repository around it"))?
        .to_path_buf();

    let mut heads: Vec<RevisionId> = Vec::new();
    for spelling in &spellings {
        let head = target::resolve(&store, spelling)?;
        if !heads.contains(&head) {
            heads.push(head);
        }
    }
    let standing = target::current_heads(&store);
    if heads.len() == 1
        && let Some(mine) = standing.iter().next().copied()
        && standing.len() == 1
        && !heads.contains(&mine)
    {
        heads.push(mine);
    }
    if heads.len() < 2 {
        return Err(Failure::error(
            "merging is joining two lines of work; name the other one too",
        ));
    }
    heads.sort();

    let merged = store.merged_tree_of(&heads).map_err(Failure::error)?;
    let mut said = Vec::new();
    let mut contested = 0usize;

    // A path two files claim cannot be a folder's truth: one keeps the path
    // and the other is written beside it under a rendered name, which `--at`
    // then settles. Decision 0008 forbids the format inventing either.
    let mut beside: BTreeMap<FileId, String> = BTreeMap::new();
    for contest in &merged.contested {
        said.push(render::contest_line(contest));
        if let TreeContest::Path { path, files } = contest {
            for file in files.iter().skip(1) {
                beside.insert(*file, format!("{path} (historica: {})", file.abbreviate(8)));
            }
        }
    }

    for (file, entry) in merged.tree.entries() {
        let at = beside.get(file).map_or(entry.path.as_str(), String::as_str);
        let on_disk = repository.join(at);

        // Decision 0017: a file of bytes has no lines to mark up, so a
        // contested one is reported and the folder is left exactly as it is.
        // The tool cannot tell a resolution from an oversight here, and saying
        // so is better than pretending otherwise.
        let rendered = match entry.kind {
            Kind::Whole => {
                let Some(payload) = entry.payload else {
                    contested += 1;
                    said.push(format!(
                        "left {at} alone: it is contested and holds no lines"
                    ));
                    for (revision, _) in contested_payloads(&merged.contested, file) {
                        said.push(format!("  historica cat {} {at}", revision.abbreviate(8)));
                    }
                    continue;
                };
                let bytes = store
                    .payload(&payload)
                    .map_err(Failure::error)?
                    .ok_or_else(|| {
                        Failure::error(format!("this store does not hold the content {payload}"))
                    })?;
                if let Ok(held) = fs::read(&on_disk)
                    && held != bytes
                    && !heads.iter().any(|head| {
                        store
                            .content_at(head, file)
                            .is_ok_and(|content| content.bytes() == held)
                    })
                {
                    said.push(format!(
                        "left {at} alone: it holds work nothing has recorded"
                    ));
                    continue;
                }
                bytes
            }
            Kind::Lines => {
                let content = store
                    .merged_content_of(&heads, file)
                    .map_err(Failure::error)?;
                let rendered = conflict::render(&content);
                if !content.contested.is_empty() {
                    contested += 1;
                }
                if let Ok(held) = fs::read_to_string(&on_disk)
                    && held != rendered
                    && held != content.state.text()
                    && !recorded_anywhere(&store, &heads, file, &held)
                {
                    // Neither version nor the rendering, and no head holds it:
                    // this is work nobody has recorded, and a merge that
                    // overwrote it would lose it.
                    said.push(format!(
                        "left {at} alone: it holds work nothing has recorded"
                    ));
                    continue;
                }
                rendered.into_bytes()
            }
        };

        if let Some(directory) = on_disk.parent() {
            fs::create_dir_all(directory)
                .map_err(|error| Failure::error(format!("{}: {error}", directory.display())))?;
        }
        fs::write(&on_disk, &rendered).map_err(|error| Failure::error(format!("{at}: {error}")))?;
    }

    printing(|out| {
        for line in &said {
            writeln!(out, "{line}")?;
        }
        if contested == 0 {
            writeln!(out, "nothing is contested; record it with:")?;
        } else {
            writeln!(
                out,
                "{contested} file{} work that met; resolve it, delete the lines \
                 historica wrote, and record it with:",
                if contested == 1 { " holds" } else { "s hold" }
            )?;
        }
        writeln!(
            out,
            "  historica record{} -m <message>",
            spellings
                .iter()
                .map(|spelling| format!(" --merge {spelling}"))
                .collect::<String>()
        )
    })
}

/// The revisions that each stated one contested file's whole content.
fn contested_payloads(contested: &[TreeContest], file: &FileId) -> Vec<(RevisionId, RevisionId)> {
    contested
        .iter()
        .find_map(|contest| match contest {
            TreeContest::Content {
                file: contested,
                payloads,
            } if contested == file => Some(payloads.clone()),
            _ => None,
        })
        .unwrap_or_default()
}

/// Whether some head already holds exactly this text for this file.
///
/// What distinguishes "the folder is where I left it" from "the folder holds
/// something nobody has recorded", which is the only thing a merge must not
/// overwrite.
fn recorded_anywhere(store: &Store, heads: &[RevisionId], file: &FileId, held: &str) -> bool {
    heads.iter().any(|head| {
        store
            .merged_content_of(&[*head], file)
            .is_ok_and(|content| content.state.text() == held)
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

/// A timestamp for a plan nobody records, since a plan states no time.
fn placeholder() -> historica::format::Timestamp {
    "0001-01-01T00:00:00+00:00"
        .parse()
        .expect("a timestamp this crate wrote")
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
