//! Historica's command-line front end.
//!
//! Decision 0006 calls `init`, `check`, and `arrange` "the first commands
//! owed"; decision 0003 calls that kind of work "interface work — owed to
//! users, not to correctness". Everything here is that: the commands read the
//! readable files and render them, and the only ones that write are the three
//! whose writing is specified — `init` makes the layout, `arrange` renames
//! presentation, `name` moves a bookmark.
//!
//! Nothing here decides anything the library has not decided already. Where a
//! history is concurrent and merging is not built, the command says so in the
//! library's own words rather than picking an order.

mod cli;

use std::process::ExitCode;

fn main() -> ExitCode {
    match cli::run(std::env::args().skip(1)) {
        Ok(code) => ExitCode::from(code),
        Err(failure) => {
            if let Some(message) = failure.message() {
                eprintln!("historica: {message}");
            }
            if failure.wants_usage() {
                eprintln!();
                eprint!("{}", cli::usage());
            }
            ExitCode::from(failure.code())
        }
    }
}
