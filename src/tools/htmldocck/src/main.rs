//! HtmlDocCk is a test framework for rustdoc's HTML backend.
#![allow(dead_code, unused_variables)] // FIXME

use std::process::ExitCode;

mod cache;
mod check;
mod config;
mod error;
mod parse;

fn main() -> ExitCode {
    let result = error::DiagCtxt::scope(|dcx| {
        let args: Vec<_> = std::env::args().collect();
        let config = config::Config::parse(&args, dcx)?;

        // FIXME: better error message
        let template = std::fs::read_to_string(&config.template)
            .map_err(|error| dcx.emit_noloc(&format!("failed to read file: {error}")))?;

        let commands = parse::commands(&template, dcx);

        let mut cache = cache::Cache::new(&config.doc_dir);
        commands.into_iter().try_for_each(|command| command.run(&mut cache, dcx))
    });

    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(()) => ExitCode::FAILURE,
    }
}

/// A check command.
#[derive(Debug)] // FIXME: temporary
struct Command {
    kind: CommandKind,
    negated: bool,
    // FIXME: better repr for location info
    lineno: usize,
    line: String,
}

/// The kind of check command.
#[derive(Debug)] // FIXME: temporary
enum CommandKind {
    /// `@has <PATH>`.
    HasFile { path: String },
    /// `@has-dir <PATH>`.
    HasDir { path: String },
    /// `@has <PATH> <XPATH> <TEXT>`.
    Has { path: String, xpath: String, text: String },
    /// `@hasraw <PATH> <TEXT>`.
    HasRaw { path: String, text: String },
    /// `@matches <PATH> <XPATH> <PATTERN>`.
    Matches { path: String, xpath: String, pattern: String },
    /// `@matchesraw <PATH> <PATTERN>`.
    MatchesRaw { path: String, pattern: String },
    /// `@count <PATH> <XPATH> [<TEXT>] <COUNT>`.
    // FIXME: don't use `usize` for robustness!
    Count { path: String, xpath: String, text: Option<String>, count: usize },
    /// `@files <PATH> <ARRAY>`.
    Files { path: String, files: String },
    /// `@snapshot <NAME> <PATH> <XPATH>`.
    Snapshot { name: String, path: String, xpath: String },
}

impl CommandKind {
    /// Whether this kind of command may be negated with `!`.
    fn may_be_negated(&self) -> bool {
        // We match exhaustively to get a compile error if we add a new kind of command.
        match self {
            Self::Has { .. }
            | Self::HasFile { .. }
            | Self::HasDir { .. }
            | Self::HasRaw { .. }
            | Self::Matches { .. }
            | Self::MatchesRaw { .. }
            | Self::Count { .. }
            | Self::Snapshot { .. } => true,
            Self::Files { .. } => false,
        }
    }
}
