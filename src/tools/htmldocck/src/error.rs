use std::ops::Range;

use unicode_width::UnicodeWidthStr;

pub(crate) struct DiagCtxt {
    count: usize,
}

impl DiagCtxt {
    pub(crate) fn scope(run: impl FnOnce(&mut Self) -> Result<(), ()>) -> Result<(), ()> {
        let mut dcx = Self::new();
        let result = run(&mut dcx);
        dcx.summarize();
        match result {
            Ok(()) if dcx.is_empty() => Ok(()),
            _ => Err(()),
        }
    }

    fn new() -> Self {
        Self { count: 0 }
    }

    fn is_empty(&self) -> bool {
        self.count == 0
    }

    // FIXME: proper API, name
    pub(crate) fn emit_noloc(&mut self, message: &str) {
        // FIXME: use proper coloring library
        eprintln!("\x1b[31merror\x1b[0m: {message}");
        self.count += 1;
    }

    // FIXME: proper API
    pub(crate) fn emit<'a>(
        &mut self,
        message: &str,
        line: &str,
        location: impl Into<Location>,
        help: impl Into<Option<&'a str>>,
    ) {
        self._emit(message, line, location.into(), help.into())
    }

    fn _emit(&mut self, message: &str, line: &str, location: Location, help: Option<&str>) {
        // FIXME: use proper coloring library
        eprintln!("\x1b[31merror\x1b[0m: {message}");
        eprintln!("\x1b[1;36m{} | \x1b[0m{line}", location.lineno);
        if let Some(range) = location.range {
            let underline_offset = line[..range.start].width();
            let underline_length = line[range].width();
            eprintln!(
                "\x1b[1;36m{}   \x1b[0m\x1b[31m{}{}{}\x1b[0m",
                " ".repeat(location.lineno.ilog10() as usize + 1),
                " ".repeat(underline_offset),
                "^".repeat(underline_length),
                // FIXME: get rid of format here
                help.map(|help| format!(" help: {help}")).unwrap_or_default(),
            );
        }
        self.count += 1;
    }

    fn summarize(&self) {
        if self.is_empty() {
            return;
        }

        eprintln!();
        eprintln!("encountered {} error{}", self.count, if self.count == 1 { "" } else { "s" },);
    }
}

pub(crate) struct Location {
    /// The one-based line number.
    pub(crate) lineno: usize,
    // FIXME: docs
    // FIXME: check if we actually want Option<_> here
    pub(crate) range: Option<Range<usize>>,
}

// FIXME: check if we want to keep this
impl From<usize> for Location {
    fn from(lineno: usize) -> Self {
        Self { lineno, range: None }
    }
}

// FIXME: check if we want to keep this (this way)
impl From<(usize, Range<usize>)> for Location {
    fn from((lineno, range): (usize, Range<usize>)) -> Self {
        Self { lineno, range: Some(range) }
    }
}
