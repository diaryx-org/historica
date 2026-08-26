//! Cutting a release, as one program.
//!
//! historica releases on a tag: pushing `vX.Y.Z` starts `release.yml`, which
//! cuts the GitHub release and writes its body from the changelog. Everything
//! before that push is mechanical and easy to get half-right by hand — the
//! version lives in the manifest and the lockfile both, and the changelog's
//! unreleased region has to be cut into a released section — so it lives here
//! instead:
//!
//!     cargo xtask version                 what the repository calls itself
//!     cargo xtask bump <patch|minor|major|X.Y.Z[-pre]>
//!     cargo xtask changelog [--write|--check]
//!     cargo xtask release <patch|minor|major|X.Y.Z[-pre]> [--push] [--no-verify]
//!     cargo xtask release-notes [tag]
//!
//! A version may carry a pre-release: `1.0.0-rc.1` is how a major goes out to
//! be tried before it is promised. Only a literal spec can name one — see
//! [`Version::bump`] — and `release.yml` cuts such a tag as a GitHub
//! pre-release rather than as the repository's latest.
//!
//! `release` stops at the tag unless it is given `--push`. That asymmetry is the
//! whole safety model: every step before the push is a local commit that can be
//! amended or thrown away, and the push is the one that puts a version number
//! somewhere other people can see it. So the push is asked for explicitly, each
//! time, and the default run prints the two commands it did not run.
//!
//! `release-notes` is what `release.yml` invokes, so the release workflow holds
//! no more knowledge about this repository than the CI workflow does: it asks
//! the program.

use std::cmp::Ordering;
use std::fmt;

use crate::{Result, Sh};

/// The changelog, and the config that generates half of it.
const CHANGELOG: &str = "docs/CHANGELOG.md";
const CLIFF_CONFIG: &str = ".config/cliff.toml";

/// The front end's manifest, which carries the one version requirement that
/// does not inherit from `[workspace.package]` — see [`set_requirement`].
const CLI_MANIFEST: &str = "cli/Cargo.toml";

/// The generated region inside `## Unreleased`. Only the bytes between these
/// two lines are ever rewritten; a handwritten release intro lives below the
/// end marker, in the released section, where regeneration cannot reach it.
const BEGIN: &str = "<!-- git-cliff:begin — generated; edits here are overwritten -->";
const END: &str = "<!-- git-cliff:end -->";
/// What the region says when there is nothing unreleased — the normal state
/// immediately after a release.
const EMPTY_REGION: &str = "_No commits since the last tag._";

/// Where a reader is sent for the rest of the history, from a release body.
const REPO: &str = "https://github.com/diaryx-org/historica";

// ---------------------------------------------------------------------------
// Versions
// ---------------------------------------------------------------------------

/// A semver version: the triple, and the pre-release identifiers after it.
///
/// Build metadata (`+…`) stays deliberately unparsed rather than silently
/// dropped — a version this cannot read is a version it must not rewrite — and
/// historica has never had a use for it. Pre-releases it does have a use for:
/// `1.0.0-rc.1` is how a major goes out to be tried before it is promised.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Version {
    major: u64,
    minor: u64,
    patch: u64,
    /// What lies between the `-` and the end, stored as written: `Some("rc.1")`
    /// for `1.0.0-rc.1`, and `None` for a version that promises something.
    pre: Option<String>,
}

impl Version {
    fn parse(text: &str) -> Result<Self> {
        let text = text.trim();
        let unreadable = || format!("`{text}` is not an x.y.z or x.y.z-pre version");

        if text.contains('+') {
            return Err(format!(
                "{}\nhint: build metadata is not used here, and a version this cannot read \
                 is one it must not rewrite",
                unreadable()
            ));
        }

        let (triple, pre) = match text.split_once('-') {
            Some((triple, pre)) => (triple, Some(pre)),
            None => (text, None),
        };

        let mut parts = triple.split('.');
        let mut next = || -> Result<u64> {
            parts
                .next()
                .and_then(|p| p.parse().ok())
                .ok_or_else(&unreadable)
        };
        let version = Version {
            major: next()?,
            minor: next()?,
            patch: next()?,
            pre: pre.map(str::to_owned),
        };
        if parts.next().is_some() {
            return Err(unreadable());
        }
        match &version.pre {
            Some(pre) if !is_prerelease(pre) => Err(format!(
                "`{pre}` is not a pre-release: dot-separated identifiers of `[0-9A-Za-z-]`, \
                 numeric ones without leading zeros\n\
                 hint: `rc.1`, not `rc.01`"
            )),
            _ => Ok(version),
        }
    }

    /// `patch`, `minor`, `major`, or a literal version to move to.
    ///
    /// `floor` is what the result has to be ahead of — see [`floor`]. A release
    /// that goes backwards is a typo every time, and the tag it would cut is the
    /// one thing that cannot be taken back.
    ///
    /// The three keywords refuse to run from a pre-release, because there is no
    /// answer they could give that is not a guess: from `1.0.0-rc.1`, `patch`
    /// reads as `1.0.1` and means `1.0.0` to the person finishing the release.
    /// The way out of a pre-release is to say where it goes.
    fn bump(&self, spec: &str, floor: &Version) -> Result<Self> {
        let next = match spec {
            "patch" | "minor" | "major" if self.pre.is_some() => {
                return Err(format!(
                    "`{spec}` has no meaning from the pre-release {self}\n\
                     hint: name the version — {}.{}.{} finishes this pre-release, and \
                     another pre-release carries it on",
                    self.major, self.minor, self.patch
                ));
            }
            "patch" => Version {
                major: self.major,
                minor: self.minor,
                patch: self.patch + 1,
                pre: None,
            },
            "minor" => Version {
                major: self.major,
                minor: self.minor + 1,
                patch: 0,
                pre: None,
            },
            "major" => Version {
                major: self.major + 1,
                minor: 0,
                patch: 0,
                pre: None,
            },
            literal => Version::parse(literal)?,
        };

        if &next <= floor {
            return Err(format!(
                "{next} is not ahead of {floor}\n\
                 hint: releases only move forward — a tag that has been pushed is one \
                 other people have already fetched",
            ));
        }
        Ok(next)
    }
}

/// SemVer's rule for what may follow the `-`: one or more dot-separated
/// identifiers, each non-empty and drawn from `[0-9A-Za-z-]`, and a numeric one
/// written without leading zeros — `rc.1`, never `rc.01`, since those two would
/// compare as different pre-releases while reading as the same intent.
fn is_prerelease(text: &str) -> bool {
    let numeric = |id: &str| id.bytes().all(|b| b.is_ascii_digit());
    !text.is_empty()
        && text.split('.').all(|id| {
            !id.is_empty()
                && id.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-')
                && !(numeric(id) && id.len() > 1 && id.starts_with('0'))
        })
}

/// SemVer precedence, which is not the derived order.
///
/// The triple decides first. Where two triples are equal, the version *with* a
/// pre-release ranks **below** the one without, because `1.0.0-rc.1` comes
/// before `1.0.0` — the opposite of what `#[derive(Ord)]` would make of an
/// `Option`, which is why this is written out rather than derived.
impl Ord for Version {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.major, self.minor, self.patch)
            .cmp(&(other.major, other.minor, other.patch))
            .then_with(|| match (&self.pre, &other.pre) {
                (None, None) => Ordering::Equal,
                (None, Some(_)) => Ordering::Greater,
                (Some(_), None) => Ordering::Less,
                (Some(ours), Some(theirs)) => precedence(ours, theirs),
            })
    }
}

impl PartialOrd for Version {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Two pre-releases, compared identifier by identifier: numeric ones as numbers,
/// anything else as ASCII text, and a numeric identifier ranking below an
/// alphanumeric one. Where one side runs out with everything equal so far, the
/// shorter ranks lower — `rc` before `rc.1`.
///
/// This is what the dot in `rc.1` buys. Undotted, `rc1` is a single alphanumeric
/// identifier compared as text, and `rc10` would sort *before* `rc9`.
fn precedence(ours: &str, theirs: &str) -> Ordering {
    for (ours, theirs) in ours.split('.').zip(theirs.split('.')) {
        let ordering = match (ours.parse::<u64>(), theirs.parse::<u64>()) {
            (Ok(ours), Ok(theirs)) => ours.cmp(&theirs),
            (Ok(_), Err(_)) => Ordering::Less,
            (Err(_), Ok(_)) => Ordering::Greater,
            (Err(_), Err(_)) => ours.cmp(theirs),
        };
        if ordering != Ordering::Equal {
            return ordering;
        }
    }
    ours.split('.').count().cmp(&theirs.split('.').count())
}

impl fmt::Display for Version {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}.{}", self.major, self.minor, self.patch)?;
        match &self.pre {
            Some(pre) => write!(f, "-{pre}"),
            None => Ok(()),
        }
    }
}

/// What a new version has to be ahead of: the newest tag, or the manifest where
/// there is no tag at all.
///
/// Not the manifest itself, which is the obvious choice and the wrong one. The
/// manifest can sit ahead of every tag — bumped in the tree, not yet cut — and
/// such a version has never been a release. What cannot be taken back is the
/// tag, so the tag is what the floor is made of; re-aiming an untagged `1.0.0`
/// at `1.0.0-rc.1` is not a release going backwards, it is a plan changing.
fn floor(sh: &Sh, current: &Version) -> Result<Version> {
    Ok(tags(sh)?
        .iter()
        .filter_map(|tag| Version::parse(tag.strip_prefix('v')?).ok())
        .max()
        .unwrap_or_else(|| current.clone()))
}

/// `workspace.package.version` — the version the package inherits, and the one
/// the release workflow compares the tag against.
fn workspace_version(sh: &Sh) -> Result<Version> {
    let manifest = sh.read("Cargo.toml")?;
    let line = manifest
        .lines()
        .find(|line| line.starts_with("version = \""))
        .ok_or_else(|| "no `version` in [workspace.package]".to_string())?;
    Version::parse(line.split('"').nth(1).unwrap_or_default())
}

pub fn print_version(sh: &Sh) -> Result<()> {
    println!("{}", workspace_version(sh)?);
    Ok(())
}

/// Move the repository to `next`.
///
/// Two rewrites — `[workspace.package] version` and the front end's requirement
/// on the library — and then the lockfile, which records the members' own
/// versions and so moves with them. `--workspace` touches nothing else: a
/// release is not the moment to pick up a new upstream dependency.
///
/// The count is checked rather than assumed. `[package]` inherits the value with
/// `version.workspace = true`, so exactly one line in the manifest holds it; a
/// second one would mean the two could disagree, and rewriting only the first
/// would ship the disagreement.
fn set_version(sh: &Sh, next: &Version) -> Result<()> {
    let manifest = sh.read("Cargo.toml")?;
    let mut out = String::with_capacity(manifest.len());
    let mut found = 0;

    for line in manifest.lines() {
        if line.starts_with("version = \"") {
            out.push_str(&format!("version = \"{next}\""));
            found += 1;
        } else {
            out.push_str(line);
        }
        out.push('\n');
    }

    if found != 1 {
        return Err(format!(
            "expected exactly one `version = \"…\"` line in Cargo.toml, found {found}"
        ));
    }
    sh.write("Cargo.toml", &out)?;
    println!("Cargo.toml -> {next}");

    set_requirement(sh, next)?;
    sh.cargo(&["update", "--workspace", "--quiet"])
}

/// Point `cli/Cargo.toml`'s `historica` requirement at `next`, in full.
///
/// The front end depends on the library by version as well as by path, because
/// the version is what publishing needs and the path is what builds. That one
/// requirement inherits nothing, so it has to be moved here — and it is written
/// out in full rather than left at a `"1.0"` that covers the majority of
/// releases, because the exception is exactly the case this whole file just
/// learned: a caret requirement does not match a pre-release, so `cargo publish
/// -p historica-cli` beside a `1.0.0-rc.1` library would go asking crates.io
/// for a `1.0.x` nobody ever released. In full it is right either way —
/// `"1.0.0"` is the same caret requirement `"1.0"` was, and `"1.0.0-rc.1"` is
/// the one that matches the pre-release.
fn set_requirement(sh: &Sh, next: &Version) -> Result<()> {
    let manifest = sh.read(CLI_MANIFEST)?;
    let mut out = String::with_capacity(manifest.len());
    let mut found = 0;

    for line in manifest.lines() {
        match requirement(line) {
            Some(old) => {
                out.push_str(&line.replacen(
                    &format!("version = \"{old}\""),
                    &format!("version = \"{next}\""),
                    1,
                ));
                found += 1;
            }
            None => out.push_str(line),
        }
        out.push('\n');
    }

    if found != 1 {
        return Err(format!(
            "expected exactly one `historica = {{ version = \"…\"` line in {CLI_MANIFEST}, \
             found {found}"
        ));
    }
    sh.write(CLI_MANIFEST, &out)?;
    println!("{CLI_MANIFEST} -> historica {next}");
    Ok(())
}

/// The version `historica = { version = "…", … }` asks for, from the line that
/// asks for it — and `None` from every other line. Shared with the test in
/// `main.rs` that checks the committed manifests agree.
pub fn requirement(line: &str) -> Option<&str> {
    line.trim_start()
        .strip_prefix("historica = {")?
        .split("version = \"")
        .nth(1)?
        .split('"')
        .next()
}

pub fn bump(sh: &Sh, spec: &str) -> Result<()> {
    let current = workspace_version(sh)?;
    let next = current.bump(spec, &floor(sh, &current)?)?;
    println!("{current} -> {next}");
    set_version(sh, &next)
}

// ---------------------------------------------------------------------------
// The changelog
// ---------------------------------------------------------------------------

/// The unreleased commits, rendered by git-cliff through `.config/cliff.toml`.
///
/// git-cliff exits non-zero when there is nothing unreleased, which is a normal
/// state right after a tag rather than a failure — hence the placeholder rather
/// than an error.
fn generated(sh: &Sh) -> Result<String> {
    sh.require(
        "git-cliff",
        "nix profile install nixpkgs#git-cliff, or cargo install git-cliff",
    )?;
    let rendered = sh
        .capture(
            "git-cliff",
            &["--config", CLIFF_CONFIG, "--unreleased", "--strip", "all"],
        )
        .unwrap_or_default();
    let body = rendered.trim();
    Ok(if body.is_empty() {
        EMPTY_REGION.to_string()
    } else {
        body.to_string()
    })
}

/// The commits a tag covers, rendered the same way the unreleased region is.
///
/// The range starts at the previous tag, or — for the first tag ever — at the
/// repository's root commit, which is the closest thing to "before everything"
/// that git-cliff will accept as a range.
fn tagged(sh: &Sh, previous: Option<&str>, tag: &str) -> Result<String> {
    let root;
    let start = match previous {
        Some(previous) => previous,
        None => {
            root = sh.capture("git", &["rev-list", "--max-parents=0", "HEAD"])?;
            root.trim()
        }
    };
    let rendered = sh
        .capture(
            "git-cliff",
            &[
                "--config",
                CLIFF_CONFIG,
                "--strip",
                "all",
                &format!("{start}..{tag}"),
            ],
        )
        .unwrap_or_default();
    let body = rendered.trim();
    Ok(if body.is_empty() {
        "_Nothing recorded._".to_string()
    } else {
        body.to_string()
    })
}

/// Every `v*` tag, oldest first — the same pattern `.config/cliff.toml` sections
/// history by.
///
/// Ordered here rather than by `git --sort=v:refname`, which places `v1.0.0-rc.1`
/// *after* `v1.0.0` unless the repository configures `versionsort.suffix` for
/// every suffix it might ever use. This order decides which commits each
/// changelog section covers, so a pre-release sorted into the wrong place would
/// hand a section a range belonging to its own successor.
///
/// A tag the parse cannot read sorts below every tag it can and keeps git's own
/// relative order: the list still has to be total, and a name outside the scheme
/// has no better answer than the one git gives.
fn tags(sh: &Sh) -> Result<Vec<String>> {
    let mut tags: Vec<String> = sh
        .capture("git", &["tag", "--list", "v[0-9]*"])?
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .map(str::to_owned)
        .collect();
    tags.sort_by_cached_key(|tag| Version::parse(tag.trim_start_matches('v')).ok());
    Ok(tags)
}

/// Tags with no section of their own, rendered and dated, newest first.
///
/// A tag can appear after the fact — cut long after the commits it names, once
/// the release it stood for had already happened — and without this, those
/// commits would simply leave the file: no longer unreleased, and in no section
/// either. So the tag list, not the last write, decides what the changelog owes.
fn missing_sections(sh: &Sh, text: &str) -> Result<Vec<String>> {
    let tags = tags(sh)?;
    let mut sections = Vec::new();
    for (index, tag) in tags.iter().enumerate() {
        if text
            .lines()
            .any(|line| section_tag(line) == Some(tag.as_str()))
        {
            continue;
        }
        let previous = index.checked_sub(1).map(|i| tags[i].as_str());
        let body = tagged(sh, previous, tag)?;
        let date = sh.capture("git", &["log", "-1", "--format=%cs", tag])?;
        sections.push(format!("## {tag} — {}\n\n{body}\n", date.trim()));
    }
    Ok(sections)
}

/// `## v0.2.0 — 2026-08-21` -> `v0.2.0`, and anything else -> `None`.
fn section_tag(line: &str) -> Option<&str> {
    let rest = line.strip_prefix("## ")?;
    let tag = rest.split_whitespace().next()?;
    tag.strip_prefix('v')
        .filter(|version| version.starts_with(|c: char| c.is_ascii_digit()))
        .map(|_| tag)
}

/// Put sections in their place: newest first, and an older one folded in above
/// the first section it outranks rather than appended to the end.
fn insert_sections(text: &str, sections: Vec<String>) -> String {
    if sections.is_empty() {
        return text.to_string();
    }
    let order = |tag: &str| Version::parse(tag.trim_start_matches('v')).ok();

    let mut out = String::with_capacity(text.len());
    let mut pending: Vec<String> = sections;
    for line in text.lines() {
        if let Some(tag) = section_tag(line)
            && let Some(here) = order(tag)
        {
            // Everything newer than the section starting on this line goes in
            // ahead of it.
            let (newer, rest): (Vec<String>, Vec<String>) = pending.into_iter().partition(|s| {
                section_tag(s.lines().next().unwrap_or_default())
                    .and_then(order)
                    .is_some_and(|candidate| candidate > here)
            });
            for section in newer {
                out.push_str(&section);
                out.push('\n');
            }
            pending = rest;
        }
        out.push_str(line);
        out.push('\n');
    }
    // Whatever is older than every section already in the file lands at the end.
    for section in pending {
        out.push_str(&section);
        out.push('\n');
    }
    out
}

fn region(body: &str) -> String {
    format!("{BEGIN}\n\n{body}\n\n{END}")
}

/// Replace the marked region, and optionally drop a fresh released section in
/// immediately below it. Everything above `## Unreleased` and every released
/// section below is left byte-for-byte alone.
fn rewrite(text: &str, body: &str, released: Option<&str>) -> Result<String> {
    for marker in [BEGIN, END] {
        if !text.lines().any(|line| line == marker) {
            return Err(format!("marker not found in {CHANGELOG}:\n  {marker}"));
        }
    }

    let mut out = String::with_capacity(text.len());
    let mut skipping = false;
    for line in text.lines() {
        if line == BEGIN {
            out.push_str(&region(body));
            out.push('\n');
            skipping = true;
        } else if line == END {
            skipping = false;
            if let Some(section) = released {
                out.push('\n');
                out.push_str(section);
                out.push('\n');
            }
        } else if !skipping {
            out.push_str(line);
            out.push('\n');
        }
    }
    Ok(out)
}

/// `cargo xtask changelog [--write|--check]` — print, splice, or verify.
pub fn changelog(sh: &Sh, args: &[&str]) -> Result<()> {
    let mode = match args {
        [] => "print",
        ["--write"] => "write",
        ["--check"] => "check",
        _ => return Err("usage: cargo xtask changelog [--write|--check]".into()),
    };

    let body = generated(sh)?;
    if mode == "print" {
        println!("{}", region(&body));
        return Ok(());
    }

    let current = sh.read(CHANGELOG)?;
    // Two jobs, because a tag can arrive after the commits it names: refresh the
    // unreleased region, and give any tag still without a section one.
    let missing = missing_sections(sh, &current)?;
    let named: Vec<String> = missing
        .iter()
        .filter_map(|s| section_tag(s.lines().next().unwrap_or_default()).map(str::to_owned))
        .collect();
    let spliced = insert_sections(&rewrite(&current, &body, None)?, missing);

    if mode == "check" {
        if !named.is_empty() {
            return Err(format!(
                "{CHANGELOG} has no section for {}\nhint: run `cargo xtask changelog --write`",
                named.join(", ")
            ));
        }
        if spliced != current {
            return Err(format!(
                "{CHANGELOG}'s generated region is stale\nhint: run `cargo xtask changelog --write`"
            ));
        }
        println!("{CHANGELOG}'s generated region is up to date");
        return Ok(());
    }

    sh.write(CHANGELOG, &spliced)?;
    for tag in &named {
        println!("{CHANGELOG} -> new section `## {tag}`");
    }
    println!("wrote {CHANGELOG}");
    Ok(())
}

/// One release's section of the changelog, without its heading — the body of a
/// GitHub release, for the notes job in `release.yml`.
///
/// Read from `docs/CHANGELOG.md` rather than rendered from the commits, and
/// deliberately: the tag's tree already carries the section `release` cut, so
/// the notes a reader finds on the release page are byte-identical to the ones
/// the repository ships, and the runner needs no git-cliff to produce them.
pub fn release_notes(sh: &Sh, tag: Option<&str>) -> Result<()> {
    let tag = match tag {
        Some(tag) => tag.to_string(),
        None => format!("v{}", workspace_version(sh)?),
    };
    let changelog = sh.read(CHANGELOG)?;
    let body = section(&changelog, &tag).ok_or_else(|| {
        format!(
            "{CHANGELOG} has no section for {tag}\n\
             hint: `cargo xtask changelog --write`, commit, and re-run — a tag whose \
             changelog section is missing is a tag cut without one"
        )
    })?;

    println!("{body}");
    println!(
        "\n---\n\n\
         Every change in this release and the ones before it: \
         [docs/CHANGELOG.md]({REPO}/blob/{tag}/docs/CHANGELOG.md)."
    );
    Ok(())
}

/// The lines under `## <tag> — …`, up to the next `##` heading. A `###` group
/// heading is part of the section, so the search is for that heading level
/// exactly — and so a handwritten release intro, which sits directly under the
/// heading, comes along with the generated groups.
fn section(changelog: &str, tag: &str) -> Option<String> {
    let mut lines = changelog
        .lines()
        .skip_while(|line| section_tag(line) != Some(tag));
    lines.next()?;
    let body: Vec<&str> = lines.take_while(|line| !line.starts_with("## ")).collect();
    Some(body.join("\n").trim().to_string())
}

/// Turn the unreleased region into a released section headed `## vX.Y.Z — date`,
/// and reset the region. Called by `release`, between the version bump and the
/// commit, so the release commit carries both.
fn cut_changelog(sh: &Sh, version: &Version) -> Result<()> {
    let body = generated(sh)?;
    let date = sh.capture("date", &["+%Y-%m-%d"])?.trim().to_string();
    let released = format!("## v{version} — {date}\n\n{body}\n");
    let current = sh.read(CHANGELOG)?;
    let cut = rewrite(&current, EMPTY_REGION, Some(&released))?;
    sh.write(CHANGELOG, &cut)?;
    println!("{CHANGELOG} -> new section `## v{version} — {date}`");
    Ok(())
}

// ---------------------------------------------------------------------------
// Releasing
// ---------------------------------------------------------------------------

/// `cargo xtask release <patch|minor|major|X.Y.Z> [--push] [--no-verify]`.
///
/// Bump, regenerate, commit, tag — and push only when asked. What the push
/// starts is worth stating plainly: `release.yml` cuts a GitHub release at that
/// tag and writes its body from the changelog section this command just wrote.
/// A release can be deleted, but a tag other people have already fetched cannot
/// be taken back from them.
pub fn release(sh: &Sh, spec: &str, args: &[&str]) -> Result<()> {
    let (mut push, mut verify) = (false, true);
    for arg in args {
        match *arg {
            "--push" => push = true,
            "--no-verify" => verify = false,
            other => {
                return Err(format!(
                    "unknown option `{other}`\n\
                     usage: cargo xtask release <patch|minor|major|X.Y.Z[-pre]> [--push] \
                     [--no-verify]"
                ));
            }
        }
    }

    let current = workspace_version(sh)?;
    let next = current.bump(spec, &floor(sh, &current)?)?;
    let tag = format!("v{next}");

    // Everything that can say "no" says it before anything is written. A
    // half-applied release is a working tree to untangle by hand, and the whole
    // point of this command is not doing that.
    preflight(sh, &tag)?;

    if verify {
        println!("\n\x1b[1m━━ CI ━━\x1b[0m");
        crate::ci(sh)?;
    } else {
        println!("skipping CI (--no-verify)");
    }

    println!("\n\x1b[1m━━ {current} -> {next} ━━\x1b[0m");
    set_version(sh, &next)?;
    cut_changelog(sh, &next)?;

    // Only the four files a release moves, named explicitly: whatever else is
    // in the tree stays out of the release commit.
    sh.run(
        "git",
        &["add", "Cargo.toml", CLI_MANIFEST, "Cargo.lock", CHANGELOG],
    )?;
    sh.run("git", &["commit", "-m", &format!("chore: bump to {next}")])?;
    // Annotated: the release workflow reads `github.ref_name`, and
    // `git describe` wants an object to read.
    sh.run("git", &["tag", "-a", &tag, "-m", &tag])?;

    let branch = sh.capture("git", &["rev-parse", "--abbrev-ref", "HEAD"])?;
    let branch = branch.trim().to_string();

    // What a pre-release does differently, said once, where it is about to
    // matter: GitHub will not call it Latest, and a caller has to ask for it by
    // name because a caret requirement does not reach a pre-release.
    let kind = match next.pre {
        Some(_) => format!(
            "\n{tag} is a pre-release. GitHub marks it as one rather than Latest, and a\n\
             caller has to name it exactly — `historica = \"{next}\"` — because `\"1.0\"`\n\
             and every other caret requirement passes a pre-release by.\n"
        ),
        None => String::new(),
    };

    if !push {
        println!(
            "\n\x1b[32m{tag} is committed and tagged locally.\x1b[0m\n\n\
             Nothing has left this machine. To release:\n\n    \
             git push origin {branch}\n    \
             git push origin {tag}\n\n\
             The tag is what publishes: `release.yml` cuts the GitHub release at {tag}\n\
             and writes its body from the changelog section above.\n\
             {kind}\n\
             To undo locally instead: git tag -d {tag} && git reset --hard HEAD~1\n"
        );
        return Ok(());
    }

    sh.run("git", &["push", "origin", &branch])?;
    sh.run("git", &["push", "origin", &tag])?;
    println!("\n\x1b[32m{tag} pushed.\x1b[0m The release is running:\n    {REPO}/actions\n");
    Ok(())
}

/// Refuse a release that is already doomed: dirty tree, wrong branch, a tag that
/// exists, or no git-cliff to write the changelog with.
fn preflight(sh: &Sh, tag: &str) -> Result<()> {
    sh.require(
        "git-cliff",
        "nix profile install nixpkgs#git-cliff, or cargo install git-cliff",
    )?;

    if !sh
        .capture("git", &["status", "--porcelain"])?
        .trim()
        .is_empty()
    {
        return Err(
            "the working tree is dirty — commit or stash first, so the release commit holds \
             only the version bump and the changelog"
                .into(),
        );
    }

    let branch = sh.capture("git", &["rev-parse", "--abbrev-ref", "HEAD"])?;
    if branch.trim() != "main" {
        return Err(format!(
            "on branch `{}`, and historica releases from `main`",
            branch.trim()
        ));
    }

    if !sh
        .capture("git", &["tag", "--list", tag])?
        .trim()
        .is_empty()
    {
        return Err(format!("tag {tag} already exists locally"));
    }
    if !sh
        .capture("git", &["ls-remote", "--tags", "origin", tag])?
        .trim()
        .is_empty()
    {
        return Err(format!("tag {tag} already exists on origin"));
    }

    // A release cut on a stale main is a release missing commits. Fetch is
    // advisory — a laptop offline enough to fail it can still cut the local
    // commit and push later.
    if sh
        .capture("git", &["fetch", "--quiet", "origin", "main"])
        .is_ok()
    {
        let behind = sh.capture("git", &["rev-list", "--count", "HEAD..origin/main"])?;
        if behind.trim() != "0" {
            return Err(format!(
                "main is {} commits behind origin/main — pull first",
                behind.trim()
            ));
        }
    } else {
        println!("warning: could not reach origin; releasing against the local main");
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v(version: &str) -> Version {
        Version::parse(version).unwrap()
    }

    #[test]
    fn versions_move_forward_only() {
        let current = v("0.1.0");
        // The ordinary case: the manifest and the newest tag are the same
        // version, so the floor is the version being bumped from.
        let bump = |spec| current.bump(spec, &current);
        assert_eq!(bump("patch").unwrap().to_string(), "0.1.1");
        assert_eq!(bump("minor").unwrap().to_string(), "0.2.0");
        assert_eq!(bump("major").unwrap().to_string(), "1.0.0");
        assert_eq!(bump("0.9.3").unwrap().to_string(), "0.9.3");
        assert_eq!(bump("0.1.1-rc.1").unwrap().to_string(), "0.1.1-rc.1");
        assert!(bump("0.0.9").is_err(), "a release cannot go back");
        assert!(bump("0.1.0").is_err(), "nor stand still");
        assert!(bump("0.1").is_err());
        assert!(
            bump("0.1.0-rc.1").is_err(),
            "a pre-release of the current version is behind it, not ahead"
        );
    }

    /// A version is read whole or refused whole — the pre-release is never
    /// quietly truncated away, since a truncated version is one `set_version`
    /// would write back as a different release than the one asked for.
    #[test]
    fn a_version_is_read_whole_or_not_at_all() {
        for text in ["1.0.0", "1.0.0-rc.1", "1.0.0-alpha.1.2", "1.0.0-x-y-z.0"] {
            assert_eq!(v(text).to_string(), text, "round trip");
        }
        for text in [
            "1.0",     // not a triple
            "1.0.0.0", // nor four of them
            "1.0.0-",  // an empty pre-release
            "1.0.0-rc..1",
            "1.0.0-rc.01", // a leading zero makes two spellings of one number
            "1.0.0-rc!",   // outside the identifier alphabet
            "1.0.0+build", // build metadata, deliberately unread
            "v1.0.0",      // the tag, not the version
        ] {
            assert!(Version::parse(text).is_err(), "`{text}` should not parse");
        }
    }

    /// The precedence chain from the SemVer specification itself, plus the step
    /// that matters most here: a pre-release ranks below the release it leads to.
    #[test]
    fn a_prerelease_ranks_below_the_release_it_leads_to() {
        let chain = [
            "1.0.0-alpha",
            "1.0.0-alpha.1",
            "1.0.0-alpha.beta",
            "1.0.0-beta",
            "1.0.0-beta.2",
            "1.0.0-beta.11",
            "1.0.0-rc.1",
            "1.0.0",
            "1.0.1-rc.1",
            "1.0.1",
        ];
        for pair in chain.windows(2) {
            assert!(v(pair[0]) < v(pair[1]), "{} < {}", pair[0], pair[1]);
        }
        assert_eq!(v("1.0.0-rc.1"), v("1.0.0-rc.1"));
    }

    /// Why the dot is not decoration: dotted, `1` and `9` and `10` are numbers
    /// and compare as numbers. Undotted they are part of one text identifier,
    /// and `rc10` sorts before `rc9` — a tenth release candidate that ranks
    /// below the ninth, and a `--verify-tag` failure long after the mistake.
    #[test]
    fn the_dot_in_rc_1_is_what_orders_the_tenth_after_the_ninth() {
        assert!(v("1.0.0-rc.9") < v("1.0.0-rc.10"));
        assert!(v("1.0.0-rc10") < v("1.0.0-rc9"), "the trap being avoided");
    }

    /// From a pre-release the three keywords have no non-guessed answer, so they
    /// decline and say what to type instead.
    #[test]
    fn keyword_bumps_decline_to_guess_from_a_prerelease() {
        let current = v("1.0.0-rc.1");
        let floor = v("0.2.0");
        for spec in ["patch", "minor", "major"] {
            let error = current.bump(spec, &floor).unwrap_err();
            assert!(error.contains("1.0.0"), "names the way out: {error}");
        }
        // The two literals it points at both work.
        assert_eq!(current.bump("1.0.0", &floor).unwrap().to_string(), "1.0.0");
        assert_eq!(
            current.bump("1.0.0-rc.2", &floor).unwrap().to_string(),
            "1.0.0-rc.2"
        );
    }

    /// The floor is the newest tag rather than the manifest, so a version that
    /// was bumped in the tree and never cut can still be re-aimed at a
    /// pre-release — while anything at or below a tag someone could have fetched
    /// is still refused.
    #[test]
    fn an_untagged_manifest_version_can_be_re_aimed() {
        let current = v("1.0.0");
        let tagged = v("0.2.0");
        assert_eq!(
            current.bump("1.0.0-rc.1", &tagged).unwrap().to_string(),
            "1.0.0-rc.1",
            "1.0.0 was never tagged, so aiming below it is a plan changing",
        );
        assert!(current.bump("0.2.0", &tagged).is_err(), "the tag itself");
        assert!(current.bump("0.1.9", &tagged).is_err(), "and below it");
    }

    /// The one requirement that does not inherit the workspace version, found by
    /// the same reader that rewrites it — and found on that line only.
    #[test]
    fn the_cli_requirement_is_read_from_its_own_line() {
        assert_eq!(
            requirement(r#"historica = { version = "1.0.0-rc.1", path = ".." }"#),
            Some("1.0.0-rc.1"),
        );
        assert_eq!(
            requirement(r#"  historica = { version = "1.0" }"#),
            Some("1.0")
        );
        assert_eq!(requirement(r#"jiff = { version = "0.2" }"#), None);
        assert_eq!(requirement("historica = { path = \"..\" }"), None);
        assert_eq!(requirement("# historica = { version = \"1.0\" }"), None);
    }

    /// The bump rewrites one line, and the manifest has to be the shape that
    /// makes that safe: the version stated once, in `[workspace.package]`, and
    /// inherited by `[package]` rather than repeated there.
    #[test]
    fn the_manifest_states_its_version_exactly_once() {
        let sh = Sh::new();
        let manifest = sh.read("Cargo.toml").unwrap();
        assert_eq!(
            manifest
                .lines()
                .filter(|line| line.starts_with("version = \""))
                .count(),
            1,
        );
        assert!(manifest.contains("version.workspace = true"));
        // And that line is the one `cargo xtask version` reads.
        let version = workspace_version(&sh).unwrap();
        assert!(manifest.contains(&format!("version = \"{version}\"")));
    }

    /// The splice touches the region and nothing else — not the prose above it,
    /// and not a single released section below.
    #[test]
    fn rewriting_leaves_everything_outside_the_region_alone() {
        let text = format!(
            "# Changelog\n\nprose\n\n## Unreleased\n\n{BEGIN}\n\nold\n\n{END}\n\n## v0.1.0 — 2026-08-07\n\nkept\n"
        );
        let refreshed = rewrite(&text, "new", None).unwrap();
        assert!(refreshed.contains("\nnew\n") && !refreshed.contains("\nold\n"));
        assert!(refreshed.contains("# Changelog\n\nprose"));
        assert!(refreshed.ends_with("## v0.1.0 — 2026-08-07\n\nkept\n"));

        let cut = rewrite(&text, EMPTY_REGION, Some("## v0.2.0 — 2026-08-21\n\nnew\n")).unwrap();
        let released = cut.find("## v0.2.0").unwrap();
        assert!(
            released > cut.find(END).unwrap(),
            "released sections go below the region"
        );
        assert!(
            released < cut.find("## v0.1.0").unwrap(),
            "newest release first"
        );
        assert!(cut.contains(EMPTY_REGION));
    }

    /// A tag section is recognised by its heading and nothing else, so that a
    /// handwritten intro under one is never mistaken for a heading — and a
    /// heading that is prose (`## Unreleased`) is never mistaken for a tag.
    #[test]
    fn tag_headings_are_told_from_prose_ones() {
        assert_eq!(section_tag("## v0.1.0 — 2026-08-21"), Some("v0.1.0"));
        assert_eq!(section_tag("## v0.1.0"), Some("v0.1.0"));
        assert_eq!(section_tag("## Unreleased"), None);
        assert_eq!(section_tag("## verify the build"), None);
        assert_eq!(section_tag("### Added"), None);
        assert_eq!(section_tag("- **cli** — ## v1.0.0 in a bullet"), None);
    }

    /// A tag can be cut long after the commits it names, so a backfilled section
    /// has to land in version order rather than on top.
    #[test]
    fn backfilled_sections_land_in_version_order() {
        let text = "## v0.6.0 — c\n\nsix\n\n## v0.4.0 — a\n\nfour\n";
        let merged = insert_sections(
            text,
            vec![
                "## v0.5.0 — b\n\nfive\n".to_string(),
                "## v0.3.0 — z\n\nthree\n".to_string(),
            ],
        );
        let order: Vec<&str> = merged.lines().filter_map(section_tag).collect();
        assert_eq!(order, ["v0.6.0", "v0.5.0", "v0.4.0", "v0.3.0"]);
        // Nothing already in the file is rewritten on the way past.
        for kept in ["six", "four"] {
            assert_eq!(merged.matches(kept).count(), 1);
        }
    }

    #[test]
    fn nothing_missing_leaves_the_file_untouched() {
        let text = "## v0.6.0 — c\n\nsix\n";
        assert_eq!(insert_sections(text, vec![]), text);
    }

    /// The release body is a slice of the changelog, so the slice has to end
    /// where the next release begins — and not at a group heading inside it.
    #[test]
    fn a_release_section_stops_at_the_next_release() {
        let changelog = "\
# Changelog

## Unreleased

nothing

## v0.2.0 — 2026-08-21

An intro, handwritten.

### Added

- a thing

## v0.1.0 — 2026-08-06

### Added

- an older thing
";
        let body = section(changelog, "v0.2.0").unwrap();
        assert!(body.starts_with("An intro, handwritten."), "{body}");
        assert!(body.contains("### Added") && body.contains("- a thing"));
        assert!(
            !body.contains("older"),
            "the next release is not part of it"
        );
        assert!(!body.contains("## v0.1.0"));

        assert_eq!(
            section(changelog, "v0.1.0").unwrap(),
            "### Added\n\n- an older thing"
        );
        assert_eq!(section(changelog, "v9.9.9"), None, "a tag with no section");
    }

    #[test]
    fn rewriting_a_changelog_without_markers_is_an_error() {
        assert!(rewrite("# Changelog\n", "new", None).is_err());
    }

    /// The markers are the whole contract between this file and the changelog:
    /// if the committed file loses one, every `--write` and `--check` fails.
    #[test]
    fn the_committed_changelog_has_its_markers() {
        let text = Sh::new().read(CHANGELOG).unwrap();
        for marker in [BEGIN, END] {
            assert!(
                text.lines().any(|line| line == marker),
                "{CHANGELOG} is missing `{marker}`",
            );
        }
    }
}
