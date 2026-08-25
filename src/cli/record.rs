//! `record` and `identity`: the two commands that write on a person's behalf.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;

use historica::conflict;
use historica::core::{FileId, RevisionId};
use historica::format::{self, Mode};
use historica::fs::{Disk, Filesystem as _};
use historica::record::{
    Abandoning, Amendment, Clock, Platform, Recording, Restriction, abandon as abandon_revision,
    abandonment_plan, amend as amend_revision, amendment_plan, check_restriction, identity,
    plan as plan_for, record as record_revision,
};
use historica::store::Store;
use historica::tree::{Kind, TreeContest};
use historica::working::Working;

use super::{Failure, printing, render, target};

/// `record [<path>...] [-m <message>] [--onto <target>] [--move <old>=<new>]
/// [--dry-run]`.
///
/// A path narrows what is surveyed and nothing else: the files left out are
/// not compared with the tree, so this records an observed state as much as
/// the unrestricted command does. There is still no index — nothing here is
/// remembered past the end of the command.
pub fn record(base: &Path, root: PathBuf, arguments: Vec<String>) -> Result<u8, Failure> {
    let mut message: Option<String> = None;
    let mut onto: Option<String> = None;
    let mut joining: Vec<String> = Vec::new();
    let mut moves: Vec<(String, String)> = Vec::new();
    // Held as typed until the store is open: decision 0024 lets `--at` name a
    // file bookmark, and a bookmark is a file in the store rather than a
    // spelling that can be parsed on its own.
    let mut at: Vec<(String, String)> = Vec::new();
    let mut accepted: BTreeSet<String> = BTreeSet::new();
    let mut named: BTreeSet<String> = BTreeSet::new();
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
            "--accept" => {
                accepted.insert(value("--accept")?);
            }
            "--at" => {
                let stated = value("--at")?;
                let (file, path) = stated
                    .split_once('=')
                    .ok_or_else(|| Failure::usage("`--at` is spelled `--at <file>=<path>`"))?;
                at.push((file.to_owned(), format::nfc(path).into_owned()));
            }
            "--move" => {
                let stated = value("--move")?;
                let (from, to) = stated
                    .split_once('=')
                    .ok_or_else(|| Failure::usage("`--move` is spelled `--move <old>=<new>`"))?;
                moves.push((format::nfc(from).into_owned(), format::nfc(to).into_owned()));
            }
            "-n" | "--dry-run" => dry_run = true,
            other if other.starts_with('-') => {
                return Err(Failure::usage(format!(
                    "`{other}` is not an argument `record` takes"
                )));
            }
            // A path, relative to the repository, spelled as `--move` and
            // `--at` already spell one. A trailing slash is the way a person
            // says directory and their shell says it for them.
            other => {
                let path = format::nfc(other.trim_end_matches('/')).into_owned();
                if path.is_empty() {
                    return Err(Failure::usage(
                        "`record` takes the paths to record, and an empty one \
                         names nothing",
                    ));
                }
                named.insert(path);
            }
        }
    }
    let only = if named.is_empty() {
        Restriction::Everything
    } else {
        Restriction::Paths(named)
    };

    let mut store = Store::open(&root)?;
    let repository = root
        .parent()
        .ok_or_else(|| Failure::error("this store has no repository around it"))?
        .to_path_buf();

    let at: Vec<(FileId, String)> = at
        .into_iter()
        .map(|(file, path)| Ok((target::file_by_name(&store, &file)?, path)))
        .collect::<Result<_, Failure>>()?;

    // Decision 0011: the head is the position, and several heads mean a person
    // should be choosing rather than a tool. 0015 moved the rule to `target`,
    // so `status` derives the same position this does.
    let parents = target::parents(&store, onto.as_deref(), &joining)?;

    let recording = |author: String, when, message| Recording {
        parents: parents.clone(),
        author,
        when,
        message,
        moves: moves.clone(),
        at: at.clone(),
        accepted: accepted.clone(),
        only: only.clone(),
    };

    // What a restriction refuses outright, asked before the rename below
    // rearranges the folder: a refusal that had moved a file on its way to
    // saying no is a refusal that did something.
    check_restriction(&recording(String::new(), placeholder(), String::new()))
        .map_err(Failure::error)?;

    for (from, to) in &moves {
        perform(&repository, from, to)?;
    }

    let working = Working::read(&repository, store.skipped()).map_err(Failure::error)?;
    let mut platform = Platform;

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
                moves.push((format::nfc(from).into_owned(), format::nfc(to).into_owned()));
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

/// `abandon <target> [-m <message>] [--dry-run]`.
///
/// Decision 0013: supersession by a revision of a newly minted change, which
/// records nothing and explains everything. The message is the one this
/// format requires, so with no `-m` the editor opens exactly as `record`'s
/// does — and an empty message is a refusal rather than a tombstone.
pub fn abandon(base: &Path, root: PathBuf, arguments: Vec<String>) -> Result<u8, Failure> {
    let mut message: Option<String> = None;
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
            "-n" | "--dry-run" => dry_run = true,
            other if other.starts_with('-') => {
                return Err(Failure::usage(format!(
                    "`{other}` is not an argument `abandon` takes"
                )));
            }
            other if named.is_none() => named = Some(other.to_owned()),
            other => {
                return Err(Failure::usage(format!(
                    "`abandon` abandons one run of work, and `{other}` is a second"
                )));
            }
        }
    }
    let Some(spelling) = named else {
        return Err(Failure::usage(
            "`abandon` wants the revision to abandon; it and everything \
             standing on it go",
        ));
    };

    let mut store = Store::open(&root)?;
    let repository = root
        .parent()
        .ok_or_else(|| Failure::error("this store has no repository around it"))?
        .to_path_buf();
    let revision = target::resolve(&store, &spelling)?;

    if dry_run {
        let run = abandonment_plan(&store, &revision).map_err(Failure::error)?;
        return printing(|out| {
            for id in &run {
                writeln!(out, "would abandon {}", target::spelled(&store, id))?;
            }
            writeln!(
                out,
                "a tombstone would supersede {}, and its message is required",
                if run.len() == 1 {
                    "this revision".to_owned()
                } else {
                    format!("these {} revisions", run.len())
                }
            )
        });
    }

    let author = identity::author_for(&repository).map_err(Failure::error)?;
    let mut platform = Platform;
    let when = platform.now().map_err(Failure::error)?;
    warn_about_the_clock(&store, &when);

    let message = match message {
        Some(message) => message,
        None => from_an_editor(base)?,
    };

    let abandoning = Abandoning {
        revision,
        author,
        when,
        message,
    };
    let abandoned =
        abandon_revision(&mut store, &abandoning, &mut platform).map_err(Failure::error)?;

    printing(|out| {
        for id in &abandoned.superseded {
            writeln!(out, "abandoned {}", id.abbreviate(12))?;
        }
        writeln!(
            out,
            "the tombstone is {} ({})",
            abandoned.revision.abbreviate(12),
            abandoned.change.abbreviate(8)
        )?;
        for name in &abandoned.advanced {
            writeln!(out, "{name} -> {}", abandoned.change.abbreviate(8))?;
        }
        // Decision 0013: abandoning is the graph and pruning is disk, and a
        // person should hear the difference from the command that sits on it.
        writeln!(
            out,
            "what it supersedes is still here; `historica prune` is what removes it"
        )
    })
}

/// `carry [<target>] [--dry-run]`.
///
/// Decision 0059: restate work standing on a rewritten revision against the
/// rewrite. Everything derives from what the store holds — no clock, no
/// random source, no author — which is what lets two replicas repairing one
/// history write byte-identical files. With no target it finds every
/// revision `check`'s note would name, and finding none is the ordinary
/// answer rather than a refusal.
pub fn carry(root: PathBuf, arguments: Vec<String>) -> Result<u8, Failure> {
    let mut named: Option<String> = None;
    let mut dry_run = false;
    for argument in arguments {
        match argument.as_str() {
            "-n" | "--dry-run" => dry_run = true,
            other if other.starts_with('-') => {
                return Err(Failure::usage(format!(
                    "`{other}` is not an argument `carry` takes"
                )));
            }
            other if named.is_none() => named = Some(other.to_owned()),
            other => {
                return Err(Failure::usage(format!(
                    "`carry` carries one line of work, and `{other}` is a second"
                )));
            }
        }
    }

    let mut store = Store::open(&root)?;
    let target = match &named {
        Some(spelling) => Some(target::resolve(&store, spelling)?),
        None => None,
    };

    let planned = if dry_run {
        historica::record::carry::plan(&store, target.as_ref()).map_err(Failure::error)?
    } else {
        historica::record::carry::carry(&mut store, target.as_ref()).map_err(Failure::error)?
    };

    printing(|out| {
        if planned.is_empty() {
            return writeln!(
                out,
                "nothing stands on a rewritten revision; there is nothing to carry"
            );
        }
        let mut restated = false;
        for step in &planned.steps {
            writeln!(
                out,
                "{} {} as {}, onto {}",
                if dry_run { "would carry" } else { "carried" },
                step.predecessor.abbreviate(12),
                step.revision.abbreviate(12),
                step.onto
                    .iter()
                    .map(|id| id.abbreviate(12))
                    .collect::<Vec<_>>()
                    .join(" and ")
            )?;
            for path in &step.restated {
                writeln!(out, "  restated {path}")?;
            }
            restated |= !step.restated.is_empty();
        }
        if !dry_run {
            // Decision 0013's reason, one command over: the superseded
            // revisions are the record of what the work was, and prune is
            // the command that empties it.
            writeln!(
                out,
                "what was carried is still here, superseded; `historica prune` \
                 is what removes it"
            )?;
            if restated {
                writeln!(
                    out,
                    "the folder is unchanged; `historica update` makes it hold \
                     the carried head"
                )?;
            }
        }
        Ok(())
    })
}

/// `merge [<target>...]` — write what two lines of work say together.
///
/// Decision 0012: nothing conflicted is recorded and nothing is remembered.
/// This renders the merge into the folder and prints the command that records
/// it, so the pending merge lives in the person's terminal.
///
/// One rule decides what is joined: **what is named, and every head that is
/// not**. Divergence is the state this command exists for, and in it the store
/// already knows both answers — so naming one head is enough, and naming none
/// is enough when divergence is the whole of what there is to join. A target
/// that is not a head is still joined to every head, which is how a person
/// merges a line of work they had abandoned the tip of.
pub fn merge(root: PathBuf, arguments: Vec<String>) -> Result<u8, Failure> {
    let spellings: Vec<String> = arguments;

    let store = Store::open(&root)?;
    let repository = root
        .parent()
        .ok_or_else(|| Failure::error("this store has no repository around it"))?
        .to_path_buf();

    let mut heads: Vec<RevisionId> = Vec::new();
    // What a person typed for each head they typed, so the command printed at
    // the end says their bookmark back to them rather than a digest they now
    // have to match up. A head they did not name has no such spelling.
    let mut as_typed: BTreeMap<RevisionId, String> = BTreeMap::new();
    for spelling in &spellings {
        let head = target::resolve(&store, spelling)?;
        as_typed.entry(head).or_insert_with(|| spelling.clone());
        if !heads.contains(&head) {
            heads.push(head);
        }
    }
    let standing = target::current_heads(&store);
    for head in &standing {
        if !heads.contains(head) {
            heads.push(*head);
        }
    }
    if heads.len() < 2 {
        return Err(Failure::error(
            "merging is joining two lines of work, and this store has one; \
             name the other, or record on both sides first",
        ));
    }
    heads.sort();

    // Decision 0023, amended: supersession is a statement about one change's
    // revisions and does not travel along parent edges, so a head can stand on
    // a revision somebody has since rewritten. Merging it is not merging
    // concurrent work. A rewrite mints its own items for lines its predecessor
    // already minted, so both sides hold the same lines under different names
    // and every one of them arrives here contested — which reads, in the
    // folder, as the other side having retyped work that was already there.
    // Saying so before the markers is the difference between a person
    // resolving a conflict and a person deleting their own work to be rid of
    // one. `check` says it too; this is the command where they meet it.
    let mut said = Vec::new();
    let withdrawn = store.history().superseded();
    if !withdrawn.is_empty() {
        for (id, document) in store.reachable_from(&heads).map_err(Failure::error)? {
            if withdrawn.contains(&id) {
                continue;
            }
            for parent in document.parents.iter().filter(|p| withdrawn.contains(p)) {
                said.push(format!(
                    "{} stands on {}, which something rewrote; what meets below \
                     may be that rewrite rather than work done twice",
                    id.abbreviate(8),
                    parent.abbreviate(8)
                ));
            }
        }
    }

    let merged = store.merged_tree_of(&heads).map_err(Failure::error)?;
    let mut contested = 0usize;

    // A path two files claim cannot be a folder's truth: one keeps the path
    // and the other is written beside it under a rendered name, which `--at`
    // then settles. Decision 0008 forbids the format inventing either.
    let mut beside: BTreeMap<FileId, String> = BTreeMap::new();
    for contest in &merged.contested {
        said.push(render::contest_line(contest));
        if let TreeContest::Path { path, files } = contest {
            for file in files.iter().skip(1) {
                beside.insert(*file, beside_name(path, file));
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
        // Decision 0040, on decision 0034's reason: the folder is what
        // `record --merge` surveys, so a link laid down pointing the old way
        // would be recorded as a retarget nobody made — undoing one side of
        // the merge as part of joining the work that contained it.
        if entry.kind == Kind::Link {
            let Some(target) = entry
                .target
                .as_ref()
                .and_then(|target| historica::update::materialise(&merged.tree, at, target))
            else {
                said.push(format!("left {at} alone: it is a link naming nowhere"));
                continue;
            };
            match Disk.link_target(&on_disk) {
                Ok(None) => {
                    said.push(format!(
                        "left {at} alone: this folder cannot hold a symbolic link"
                    ));
                }
                Ok(Some(held)) if held == target => {}
                Ok(_) | Err(_) => {
                    if let Some(directory) = on_disk.parent() {
                        fs::create_dir_all(directory).map_err(|error| {
                            Failure::error(format!("{}: {error}", directory.display()))
                        })?;
                    }
                    Disk.set_link(&on_disk, &target)
                        .map_err(|error| Failure::error(format!("{at}: {error}")))?;
                    said.push(format!("pointed {at} at {target}"));
                }
            }
            continue;
        }

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
            Kind::Link => unreachable!("a link was laid down above"),
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
        // Decision 0034: the folder is what `record --merge` surveys, so a
        // merged file laid down with the wrong bit would be recorded as a mode
        // change nobody made — undoing the chmod one side of the merge
        // performed, silently, as part of joining the work that contained it.
        if let Ok(Some(held)) = Disk.executable(&on_disk)
            && Mode::of(held) != entry.mode
        {
            Disk.set_executable(&on_disk, entry.mode.is_executable())
                .map_err(|error| Failure::error(format!("{at}: {error}")))?;
            said.push(format!("made {at} {}", entry.mode));
        }
    }

    // Decision 0012: a path two files claim is settled by `--at` and by
    // nothing else, so a command printed without one is a command that
    // refuses. The paths are the ones this merge just wrote beside, which
    // makes following it record the folder exactly as it now stands. Each
    // pair is quoted because a rendered name has a space in it by
    // construction, and the identifier is spelled in full because `--at`
    // names a file against a survey rather than against a revision, and so
    // takes no abbreviation.
    let settling: String = beside
        .iter()
        .map(|(file, path)| format!(" --at \"{file}={path}\""))
        .collect();

    printing(|out| {
        for line in &said {
            writeln!(out, "{line}")?;
        }
        if !beside.is_empty() {
            writeln!(
                out,
                "a path two files claim is settled below by where this merge \
                 wrote them; type other paths there if you would rather"
            )?;
        }
        if contested > 0 {
            writeln!(
                out,
                "{contested} file{} work that met; resolve it, delete the lines \
                 historica wrote, and record it with:",
                if contested == 1 { " holds" } else { "s hold" }
            )?;
        } else if beside.is_empty() {
            writeln!(out, "nothing is contested; record it with:")?;
        } else {
            writeln!(out, "no lines met; record it with:")?;
        }
        // Every head this merge joined, not only the ones named: `record`
        // derives nothing here, so a command that left one out would record a
        // different merge from the one just rendered into the folder.
        writeln!(
            out,
            "  historica record{}{settling} -m <message>",
            heads
                .iter()
                .map(|head| {
                    let spelling = as_typed
                        .get(head)
                        .cloned()
                        .unwrap_or_else(|| head.abbreviate(12));
                    format!(" --merge {spelling}")
                })
                .collect::<String>()
        )
    })
}

/// The name a file is written under beside a path another file keeps.
///
/// Two files claiming one path is a state 0008 lets a merge produce and
/// forbids the format resolving on its own, so one keeps the path and the
/// other is written beside it under a name whose reason a person can read.
/// Two rules shape how it is spelled.
///
/// The marker carries no colon. `:` is a character NTFS and exFAT refuse in a
/// name, so the older spelling could not be written at all on Windows or onto
/// a removable drive — on the one path where a merge has to write a second
/// file in order to make any progress at all.
///
/// And it goes *before* the final extension, because 0020's point is that the
/// file a person double-clicks opens in the editor they already have, and a
/// marker after `.txt` takes that away.
fn beside_name(path: &str, file: &FileId) -> String {
    let marker = format!("(historica {})", file.abbreviate(8));
    let (directory, name) = match path.rsplit_once('/') {
        Some((directory, name)) => (&path[..directory.len() + 1], name),
        None => ("", path),
    };
    match name.rsplit_once('.') {
        // A leading dot is the whole of a name like `.env` rather than an
        // extension in front of an empty one.
        Some((stem, extension)) if !stem.is_empty() => {
            format!("{directory}{stem} {marker}.{extension}")
        }
        _ => format!("{directory}{name} {marker}"),
    }
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
        .filter_map(Result::ok)
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
