//! What can go wrong, and the one rule about which of it is an error.
//!
//! A remark arrives in somebody else's chain, written by somebody else's
//! program, and the reader who fetched it cannot mend any of it. So the
//! errors here are about *this* side: a name that cannot be a directory, a
//! store that will not open, a document this crate was told to read as a
//! remark and could not. A document in a fetched chain that merely happens
//! not to be a remark is not an error and never reaches this type — it is
//! passed over, because that is what a document that is not a remark is.

use std::fmt;

/// The result of anything in this crate that can fail.
pub type Result<T> = std::result::Result<T, Error>;

/// What went wrong.
#[derive(Debug)]
#[non_exhaustive]
pub enum Error {
    /// The filesystem said no.
    Io(std::io::Error),
    /// Historica said no — opening a store, fetching from a source,
    /// reading a tree. Carried as text because what a caller does with it
    /// is print it: this crate adds nothing to historica's own account of
    /// what happened, and wrapping the error type would make every caller
    /// depend on historica to match on it.
    History(String),
    /// A name that was about to become a path segment and cannot be one.
    Name(String),
    /// A document this was asked to read as a remark, that is not one — an
    /// unknown motivation, a target the caller's own check refused. Not
    /// what a document with no `target` at all gets; that is an ordinary
    /// document and reads as `Ok(None)`.
    Unreadable(String),
    /// fig could not read or write the metadata block.
    Metadata(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Io(e) => write!(f, "{e}"),
            Error::History(e) => write!(f, "{e}"),
            Error::Name(e) => write!(f, "{e}"),
            Error::Unreadable(e) => write!(f, "{e}"),
            Error::Metadata(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Error::Io(e) => Some(e),
            _ => None,
        }
    }
}

impl From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Self {
        Error::Io(e)
    }
}

impl From<fig::Error> for Error {
    fn from(e: fig::Error) -> Self {
        Error::Metadata(e.to_string())
    }
}

/// Historica's errors, folded to text. Written as a helper rather than a
/// `From` impl because historica has several error types and they share no
/// trait this crate could name once.
#[cfg(feature = "layer")]
pub(crate) fn history<E: fmt::Display>(e: E) -> Error {
    Error::History(e.to_string())
}
