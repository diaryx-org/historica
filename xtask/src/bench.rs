//! `cargo xtask bench`: what the commands cost, on a store built to order.
//!
//! Not a CI job. A timing that fails a build on a shared runner is a timing
//! nobody trusts, and these numbers exist to be compared against each other —
//! before a change and after it, on one machine — rather than against a
//! threshold. So this lives beside the jobs rather than in [`JOBS`], for the
//! reason releasing does.
//!
//! [`JOBS`]: crate::JOBS
//!
//! The store is synthetic and stated in one line: so many files, so many
//! revisions, so many lines each, one line of each file rewritten per
//! revision. That shape is the one the reading commands are linear in — a
//! history is walked per file, and a file is replayed per revision — so it is
//! the shape a change to materialising has to be measured against. It is
//! deliberately *not* a real repository: real ones differ from each other more
//! than they differ from this, and a number that moves for reasons the flags
//! do not name is not a measurement.
//!
//! Every command is run several times and the fastest run is reported, which
//! is the usual way to read a timing that has a machine's other work mixed
//! into it: the noise only ever adds.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

use crate::{Result, Sh};

/// How big a store to build, and how hard to time it.
struct Shape {
    files: usize,
    revisions: usize,
    lines: usize,
    runs: usize,
}

impl Default for Shape {
    /// Big enough that the walk dominates process startup, small enough that
    /// the whole job is under a minute.
    fn default() -> Self {
        Shape {
            files: 30,
            revisions: 120,
            lines: 400,
            runs: 5,
        }
    }
}

impl Shape {
    /// Read `files=30 revisions=120 lines=400 runs=5`, in any order, any
    /// subset. Named rather than positional because four bare numbers on a
    /// command line are four chances to mean the wrong one.
    fn parse(args: &[&str]) -> Result<Self> {
        let mut shape = Shape::default();
        for arg in args {
            let (key, value) = arg
                .split_once('=')
                .ok_or_else(|| format!("`{arg}` is not `<setting>=<number>`\n\n{}", usage()))?;
            let number: usize = value
                .parse()
                .map_err(|_| format!("`{value}` is not a number\n\n{}", usage()))?;
            if number == 0 {
                return Err(format!("`{key}` must be more than zero"));
            }
            match key {
                "files" => shape.files = number,
                "revisions" => shape.revisions = number,
                "lines" => shape.lines = number,
                "runs" => shape.runs = number,
                _ => return Err(format!("unknown setting `{key}`\n\n{}", usage())),
            }
        }
        Ok(shape)
    }

    /// How many revisions the store ends up holding: the import, and one per
    /// round of edits.
    fn recorded(&self) -> usize {
        self.revisions + 1
    }
}

pub fn usage() -> String {
    "usage: cargo xtask bench [files=N] [revisions=N] [lines=N] [runs=N]\n\n  \
     files=30        how many files the store holds\n  \
     revisions=120   how many rounds of edits to record\n  \
     lines=400       how many lines each file starts with\n  \
     runs=5          how many times to time each command\n"
        .to_owned()
}

/// Build the binary, build a store with it, and time the reading commands.
pub fn bench(sh: &Sh, args: &[&str]) -> Result<()> {
    let shape = Shape::parse(args)?;

    // Release, because a debug build measures the borrow checker's opinion of
    // the code rather than the code.
    sh.cargo(&["build", "--release"])?;
    let binary = sh.root.join("target/release/historica");
    if !binary.exists() {
        return Err(format!("no binary at {}", binary.display()));
    }

    let store = Bench::new(&binary, &shape)?;
    println!(
        "\n\x1b[1m━━ a store of {} files × {} revisions × {} lines ━━\x1b[0m",
        shape.files,
        shape.recorded(),
        shape.lines
    );
    store.build()?;

    let head = store.head()?;
    let path = "f1.txt";
    let commands: [(&str, Vec<&str>); 6] = [
        ("log", vec!["log"]),
        ("files <head>", vec!["files", &head]),
        ("cat <head> f1.txt", vec!["cat", &head, path]),
        ("status", vec!["status"]),
        ("update --dry-run", vec!["update", "--dry-run"]),
        ("check", vec!["check"]),
    ];

    // Twice, because the question this exists to answer is what `cache/` is
    // worth. Emptied first so the cold column is honestly cold — decision 0035
    // makes that a supported thing to do to a store, which is the other half
    // of what is being demonstrated. The commands then fill it as they go,
    // exactly as they would for anybody, and the warm column is the second
    // time each one is asked.
    let mut cold = Vec::new();
    for (label, arguments) in &commands {
        cold.push(store.time(label, arguments, shape.runs, Cache::Cleared)?);
    }
    let mut warm = Vec::new();
    for (label, arguments) in &commands {
        warm.push(store.time(label, arguments, shape.runs, Cache::Kept)?);
    }
    let held = store.cache_size()?;

    println!("  {:<24}{}", "store on disk", store.size()?);
    println!("  {:<24}{held}", "cache after one pass");
    println!("  {:<24}{}\n", "fastest of", shape.runs);
    println!("  {:<24}{:>12}{:>12}", "", "no cache", "cached");
    for ((label, without), (_, with)) in cold.iter().zip(&warm) {
        println!(
            "  {label:<24}{:>9.1} ms{:>9.1} ms",
            without.as_secs_f64() * 1000.0,
            with.as_secs_f64() * 1000.0
        );
    }
    println!();
    Ok(())
}

/// Whether a run gets to keep what the run before it cached.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Cache {
    /// Emptied before every run: what a first reader pays.
    Cleared,
    /// Left alone: what every reader after the first pays.
    Kept,
}

/// A generated store, and the binary that reads it.
struct Bench<'a> {
    binary: &'a Path,
    root: PathBuf,
    shape: &'a Shape,
}

impl<'a> Bench<'a> {
    fn new(binary: &'a Path, shape: &'a Shape) -> Result<Self> {
        // Under the temp directory rather than the workspace: nothing here is
        // a build artifact, and a 15 MB store under `target/` is one `cargo
        // clean` away from being a surprise either way.
        let root = std::env::temp_dir().join("historica-bench");
        if root.exists() {
            std::fs::remove_dir_all(&root)
                .map_err(|e| format!("could not clear {}: {e}", root.display()))?;
        }
        std::fs::create_dir_all(&root)
            .map_err(|e| format!("could not create {}: {e}", root.display()))?;
        Ok(Bench {
            binary,
            root,
            shape,
        })
    }

    /// Write the files, then record them once per round of edits.
    ///
    /// Recording is the slow half by a wide margin and is not what is being
    /// measured, so it prints its progress: a job that looks hung for a minute
    /// is a job people stop running.
    fn build(&self) -> Result<()> {
        self.run(&["init"])?;
        for file in 1..=self.shape.files {
            self.write(file, |line| format!("file {file} line {line}\n"))?;
        }
        self.run(&["record", "-m", "the import"])?;

        let mut done = 0;
        for revision in 1..=self.shape.revisions {
            for file in 1..=self.shape.files {
                // One line per file per revision, at a position that moves, so
                // the operation documents are small and spread through the
                // file rather than piling up at one end.
                let touched = (revision * 7) % self.shape.lines + 1;
                self.write(file, |line| {
                    if line == touched {
                        format!("file {file} line {line} rewritten at {revision}\n")
                    } else {
                        format!("file {file} line {line}\n")
                    }
                })?;
            }
            self.run(&["record", "-m", &format!("revision {revision}")])?;
            done += 1;
            if done % 20 == 0 && done != self.shape.revisions {
                print!("\r  recorded {done}/{} revisions", self.shape.revisions);
                use std::io::Write as _;
                let _ = std::io::stdout().flush();
            }
        }
        println!(
            "\r  recorded {done}/{} revisions        ",
            self.shape.revisions
        );
        Ok(())
    }

    fn write(&self, file: usize, line: impl Fn(usize) -> String) -> Result<()> {
        let mut text = String::new();
        for number in 1..=self.shape.lines {
            text.push_str(&line(number));
        }
        let path = self.root.join(format!("f{file}.txt"));
        std::fs::write(&path, text).map_err(|e| format!("could not write {}: {e}", path.display()))
    }

    /// Empty `cache/`, as a person is entitled to.
    fn clear_cache(&self) -> Result<()> {
        let directory = self.root.join("history/cache");
        let Ok(entries) = std::fs::read_dir(&directory) else {
            return Ok(());
        };
        for entry in entries {
            let path = entry
                .map_err(|e| format!("could not read an entry: {e}"))?
                .path();
            if path.is_file() {
                std::fs::remove_file(&path)
                    .map_err(|e| format!("could not remove {}: {e}", path.display()))?;
            }
        }
        Ok(())
    }

    /// How much disk `cache/` is using.
    fn cache_size(&self) -> Result<String> {
        Self::shown(Self::bytes_under(&self.root.join("history/cache"))?)
    }

    /// The store's size, as `du -sh` would say it — the cache excluded, since
    /// it is reported beside this rather than folded into it.
    fn size(&self) -> Result<String> {
        let history = self.root.join("history");
        let bytes = Self::bytes_under(&history)? - Self::bytes_under(&history.join("cache"))?;
        Self::shown(bytes)
    }

    /// Every byte of every file under one directory, at any depth.
    fn bytes_under(directory: &Path) -> Result<u64> {
        let Ok(entries) = std::fs::read_dir(directory) else {
            return Ok(0);
        };
        let mut total = 0;
        for entry in entries {
            let entry = entry.map_err(|e| format!("could not read an entry: {e}"))?;
            let kind = entry
                .file_type()
                .map_err(|e| format!("could not stat {}: {e}", entry.path().display()))?;
            if kind.is_dir() {
                total += Self::bytes_under(&entry.path())?;
            } else if kind.is_file() {
                total += entry.metadata().map(|m| m.len()).unwrap_or(0);
            }
        }
        Ok(total)
    }

    fn shown(bytes: u64) -> Result<String> {
        Ok(if bytes >= 1 << 20 {
            format!("{:.1} MB", bytes as f64 / (1u64 << 20) as f64)
        } else {
            format!("{:.1} kB", bytes as f64 / 1024.0)
        })
    }

    /// The head revision's name, which is the first word `log` prints.
    fn head(&self) -> Result<String> {
        let output = self.output(&["log"])?;
        output
            .split_whitespace()
            .next()
            .map(str::to_owned)
            .ok_or_else(|| "`log` said nothing, so there is no head to ask about".to_owned())
    }

    /// The fastest of `runs` runs of one command.
    ///
    /// Emptying `cache/` between runs rather than once before them is the
    /// whole of what makes the cold column cold: the first run fills it, and
    /// the fastest of the rest would otherwise be a cached run wearing the
    /// other column's label.
    fn time(
        &self,
        label: &'static str,
        args: &[&str],
        runs: usize,
        cache: Cache,
    ) -> Result<(&'static str, Duration)> {
        let mut best = Duration::MAX;
        for _ in 0..runs {
            if cache == Cache::Cleared {
                self.clear_cache()?;
            }
            let start = Instant::now();
            self.run(args)?;
            best = best.min(start.elapsed());
        }
        Ok((label, best))
    }

    fn run(&self, args: &[&str]) -> Result<()> {
        self.output(args).map(|_| ())
    }

    /// Run the binary in the store and hand back its stdout.
    ///
    /// Output is captured rather than inherited so that writing a page of
    /// `status` to a terminal is not part of what is being timed.
    fn output(&self, args: &[&str]) -> Result<String> {
        let output = Command::new(self.binary)
            .args(args)
            .current_dir(&self.root)
            .output()
            .map_err(|e| format!("could not run the binary: {e}"))?;
        if !output.status.success() {
            return Err(format!(
                "`historica {}` failed ({})\n{}",
                args.join(" "),
                output.status,
                String::from_utf8_lossy(&output.stderr).trim()
            ));
        }
        Ok(String::from_utf8_lossy(&output.stdout).into_owned())
    }
}
