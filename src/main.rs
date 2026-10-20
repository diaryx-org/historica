//! The command line: one conversion, stated plainly.

use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use historica::store::Store;
use historica::wrote::{Line, Statement};
use historica_git::{export, import};

fn main() -> ExitCode {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    match run(&arguments.iter().map(String::as_str).collect::<Vec<_>>()) {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("historica-git: {message}");
            ExitCode::FAILURE
        }
    }
}

fn run(arguments: &[&str]) -> Result<(), String> {
    match arguments {
        [] | ["-h" | "--help" | "help"] => {
            print!("{USAGE}");
            Ok(())
        }
        ["-V" | "--version"] => {
            println!("historica-git {}", env!("CARGO_PKG_VERSION"));
            Ok(())
        }
        ["import", repository, folder] => convert(repository, folder),
        ["import", ..] => Err(format!(
            "`import` takes a repository and a folder to make\n\n{USAGE}"
        )),
        ["write", "--wrote", statement] => after(statement, None),
        ["write", "--wrote", statement, folder, repository] => {
            after(statement, Some((folder, repository)))
        }
        ["write", folder, repository] => write(folder, repository),
        ["write", ..] => Err(format!(
            "`write` takes a store and a repository to make\n\n{USAGE}"
        )),
        ["colocate", directory] => colocate(directory),
        ["colocate", ..] => Err(format!(
            "`colocate` takes one directory holding a repository or a store\n\n{USAGE}"
        )),
        [command, ..] => Err(format!("unknown command `{command}`\n\n{USAGE}")),
    }
}

fn colocate(directory: &str) -> Result<(), String> {
    let at = PathBuf::from(directory);
    let has_git = at.join(".git").exists();
    let has_store = at.join("history").exists();
    match (has_git, has_store) {
        (true, false) => convert(directory, directory),
        (false, true) | (true, true) => write(directory, directory),
        (false, false) => Err(format!(
            "{} holds neither a git repository nor a Historica store; `git init` \
             or `historica init` starts one",
            at.display()
        )),
    }
}

fn convert(repository: &str, folder: &str) -> Result<(), String> {
    let repository = PathBuf::from(repository);
    let folder = PathBuf::from(folder);
    let report =
        import::from_repository(&repository, &folder).map_err(|error| error.to_string())?;

    println!(
        "read {} commits, recorded {} revisions in {}",
        report.commits,
        report.revisions,
        folder.join("history").display()
    );
    if report.held > 0 {
        println!(
            "{} of them the store already held, and were recognised rather than \
             converted again",
            report.held
        );
    }
    if !report.bookmarks.is_empty() {
        println!("\nbookmarks:");
        for bookmark in &report.bookmarks {
            println!("  - {bookmark}");
        }
    }
    if !report.moved.is_empty() {
        println!("\nbookmarks moved to where git has the branch:");
        for bookmark in &report.moved {
            println!("  - {bookmark}");
        }
    }
    if !report.removed.is_empty() {
        println!("\nbookmarks removed, because git deleted the branch:");
        for bookmark in &report.removed {
            println!("  - {bookmark}");
        }
    }
    if report.behind {
        println!(
            "\nthe folder was left as it was; `historica update` is what brings it \
             forward"
        );
    }
    say(&report.uncarried, standing(report.onto, &report.standing));
    Ok(())
}

/// Decision 0004: `write`, not `export`. Historica's decision 0042 gives
/// `export` to a copy of a store to take away, and one binary cannot use the
/// word for two things without the collision landing in the reader's head.
fn write(folder: &str, repository: &str) -> Result<(), String> {
    let folder = PathBuf::from(folder);
    let repository = PathBuf::from(repository);
    let report = export::to_repository(&folder, &repository).map_err(|error| error.to_string())?;

    println!(
        "read {} revisions, wrote {} commits in {}",
        report.revisions,
        report.commits,
        repository.display()
    );
    if report.reused > 0 {
        println!(
            "{} the repository already held, and were named rather than written again",
            report.reused
        );
    }
    if !report.references.is_empty() {
        println!("\nrefs:");
        for reference in &report.references {
            println!("  - {reference}");
        }
    }
    if !report.deleted.is_empty() {
        println!("\nrefs deleted, because the store no longer names them:");
        for reference in &report.deleted {
            println!("  - {reference}");
        }
    }
    if let Some(branch) = &report.branch {
        match report.onto {
            true => println!("\nthe working tree was brought up to {branch}"),
            false => println!("\nchecked out {branch}"),
        }
    }
    held_back(&report.held_back);
    say(&report.uncarried, standing(report.onto, &report.standing));
    Ok(())
}

/// Decision 0009: the run after a historica command, which reads what the
/// command said it wrote and keeps the repository current.
///
/// A statement that says nothing was written is the case this exists for,
/// and it costs reading standard input: nothing is opened and nothing is
/// printed. So is no statement at all — a command that stopped before it
/// printed one wrote nothing, and its own exit status says why.
fn after(statement: &str, at: Option<(&str, &str)>) -> Result<(), String> {
    let text = match statement {
        "-" => {
            let mut text = String::new();
            std::io::stdin()
                .read_to_string(&mut text)
                .map_err(|error| format!("standard input: {error}"))?;
            text
        }
        path => std::fs::read_to_string(path).map_err(|error| format!("{path}: {error}"))?,
    };
    if text.is_empty() {
        return Ok(());
    }
    let wrote: Statement = text.parse().map_err(|error| {
        format!(
            "{error}\n\nnothing was written to git, because a statement this build \
             does not read is discarded whole; `historica-git write` without \
             `--wrote` brings the repository current"
        )
    })?;
    if wrote.is_empty() {
        return Ok(());
    }
    let (folder, repository) = match at {
        Some((folder, repository)) => (PathBuf::from(folder), PathBuf::from(repository)),
        None => {
            let store = Store::discover(".").map_err(|error| error.to_string())?;
            let folder = store
                .root()
                .parent()
                .map(Path::to_path_buf)
                .ok_or("the store has no folder around it")?;
            (folder.clone(), folder)
        }
    };
    let Some(report) =
        export::after(&wrote, &folder, &repository).map_err(|error| error.to_string())?
    else {
        return Ok(());
    };

    println!("historica wrote {}", told(&wrote));
    let mut git = Vec::new();
    match report.commits {
        0 => {}
        1 => git.push("wrote 1 commit".to_owned()),
        n => git.push(format!("wrote {n} commits")),
    }
    if !report.references.is_empty() {
        git.push(format!("moved {}", report.references.join(", ")));
    }
    if !report.deleted.is_empty() {
        git.push(format!("deleted {}", report.deleted.join(", ")));
    }
    match git.is_empty() {
        true => println!("git had all of it already"),
        false => println!("git: {}", git.join("; ")),
    }
    held_back(&report.held_back);
    // What git cannot hold about this run's revisions is counted, and where
    // to read it said. What is true of every run is not: decision 0010, and
    // the whole write that made the repository already said it.
    let notes = report.uncarried.len();
    if notes > 0 {
        println!(
            "{notes} {} on what git cannot hold; `historica-git write {} {}` {}",
            if notes == 1 { "note" } else { "notes" },
            folder.display(),
            repository.display(),
            if notes == 1 { "says it" } else { "lists them" },
        );
    }
    Ok(())
}

/// What a statement says, briefly, for the person whose command printed it
/// instead of its own sentences.
fn told(wrote: &Statement) -> String {
    let mut parts = Vec::new();
    for kind in ["revision", "name", "unname", "gone"] {
        let said: Vec<String> = wrote
            .lines()
            .filter(|line| line.kind() == kind)
            .map(|line| match line {
                Line::Revision(id) | Line::Gone(id) => id.abbreviate(12),
                Line::Name(name) | Line::Unname(name) => name.clone(),
            })
            .collect();
        match said.len() {
            0 => {}
            1..=3 => parts.push(format!("{kind} {}", said.join(", "))),
            n => parts.push(format!("{n} {kind} lines")),
        }
    }
    parts.join("; ")
}

/// Decision 0008: a ref something else moved is said and not followed, and
/// that is a statement about where git is rather than about what it can hold.
fn held_back(lines: &[String]) {
    if lines.is_empty() {
        return;
    }
    println!("\ngit is not where the store is:");
    for line in lines {
        println!("  - {line}");
    }
}

/// Decision 0001: a conversion states what it could not carry, because the
/// person holding the result otherwise believes it is the thing it came from.
fn say(uncarried: &[String], standing: &[String]) {
    if uncarried.is_empty() && standing.is_empty() {
        return;
    }
    println!("\nwhat did not cross:");
    for line in uncarried.iter().chain(standing) {
        println!("  - {line}");
    }
}

/// Decision 0010: what did not cross on every run is said by a whole
/// conversion, and a run onto what it made before leaves it out.
fn standing(onto: bool, standing: &[String]) -> &[String] {
    if onto { &[] } else { standing }
}

const USAGE: &str = "\
historica-git converts between git repositories and Historica stores.

usage: historica-git <command>

commands:

  import <repository> <folder>   convert <repository> into the store at <folder>
  write  <folder> <repository>   write the store at <folder> out as a git repository
  write  --wrote <statement> [<folder> <repository>]
                                 keep the repository current after a historica
                                 command, given what `--fields` said it wrote
                                 (`-` is standard input). with no directories,
                                 the store is found from here and the
                                 repository is the one beside it
  colocate <directory>           keep a store and its git projection together

A target that is empty or absent gets a whole conversion. A folder already
holding a store, or a directory already holding a repository, gets what the
other side has gained since — decision 0007 — and nothing of a person's is
touched: a second import writes into `history/` and leaves the folder for
`historica update`, and a second write moves only refs this tool made or git
left where it found them. Anything else in the way is refused. `git` must be
on PATH, which decision 0002 makes this tool's one dependency.

`write --wrote` is for running after every historica command that writes:

  historica record -m 'note' --fields | historica-git write --wrote -

A statement with no lines does nothing at all, without opening the store; one
that names anything brings the repository up to date. It never makes a
repository, and a statement naming a revision this store does not hold is
refused, since it is about another store.
";
