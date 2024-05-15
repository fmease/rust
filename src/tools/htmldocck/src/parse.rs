use std::sync::OnceLock;

use crate::error::DiagCtxt;
use crate::{Command, CommandKind};

/// Parse all commands inside of the given template.
// FIXME: Add comment that this doesn't conflict with the ui_test-style compiletest directives
pub(crate) fn commands(template: &str, dcx: &mut DiagCtxt) -> Vec<Command> {
    // FIXME: Add comment that we do not respect Rust syntax for simplicity of implementation.

    // FIXME: port behavior of "concat_multi_lines(template)"
    // FIXME: or `.split('\n')`?
    template
        .lines()
        .enumerate()
        .filter_map(|(index, line)| Command::parse(line, index + 1, dcx).ok())
        .collect()
}

impl Command {
    fn parse(line: &str, lineno: usize, dcx: &mut DiagCtxt) -> Result<Self, ()> {
        let captures = pattern().captures(line).ok_or(())?;

        let args = captures.name(group::ARGUMENTS).unwrap();
        let args = shlex::split(args.as_str()).ok_or_else(|| {
            // Unfortunately, `shlex` doesn't provide us with the precise cause of failure.
            // Nor does it provide the location of the erroneous string it encountered.
            // Therefore we can't easily reconstruct this piece of information ourselves and
            // we have no option but to emit a vague error for an imprecise location.
            dcx.emit(
                "command arguments are not properly terminated or escaped",
                line,
                (lineno, args.range()),
                None,
            );
        })?;

        let name = captures.name(group::NAME).unwrap();
        let kind = CommandKind::parse(name, &args, line, lineno, dcx)?;

        let negated = if let Some(negation) = captures.name(group::NEGATION) {
            if !kind.may_be_negated() {
                dcx.emit(
                    &format!("command `{}` may not be negated", name.as_str()),
                    line,
                    (lineno, negation.range()),
                    "remove the `!`",
                );
                return Err(());
            }

            true
        } else {
            false
        };

        if let Some(misplaced_negation) = captures.name(group::NEGATION_MISPLACED) {
            // FIXME: better message
            dcx.emit(
                "misplaced negation `!`",
                line,
                (lineno, misplaced_negation.range()),
                if negated && kind.may_be_negated() {
                    "move the `!` after the `@`"
                } else {
                    // FIXME: more context
                    "remove the `!`"
                },
            );
            return Err(());
        }

        // FIXME: avoid to_owned
        Ok(Self { kind, negated, lineno, line: line.to_owned() })
    }
}

impl CommandKind {
    // FIXME: improve signature
    fn parse(
        name: regex::Match<'_>,
        args: &[String],
        line: &str,
        lineno: usize,
        dcx: &mut DiagCtxt,
    ) -> Result<Self, ()> {
        // FIXME: avoid cloning by try_into'ing the args into arrays and moving the Strings
        // or by draining the Vec & using Iterator::next
        // FIXME: Add comment "unfortunately, `shlex` doesn't yield slices, only owned stuff"
        // FIXME: parse `XPath`s here and provide beautiful errs with location info
        // FIXME: parse regexs here and provide pretty errs with location info
        Ok(match name.as_str() {
            "has" => match args {
                [path] => Self::HasFile { path: path.clone() },
                [path, xpath, text] => {
                    Self::Has { path: path.clone(), xpath: xpath.clone(), text: text.clone() }
                }
                args => panic!("arg mismatch: expected 1 | 3, got {}", args.len()), // FIXME
            },
            "hasraw" => match args {
                [path, text] => Self::HasRaw { path: path.clone(), text: text.clone() },
                args => panic!("arg mismatch: expected 2, got {}", args.len()), // FIXME
            },
            "matches" => match args {
                [path, xpath, pattern] => Self::Matches {
                    path: path.clone(),
                    xpath: xpath.clone(),
                    pattern: pattern.clone(),
                },
                args => panic!("arg mismatch: expected 3, got {}", args.len()), // FIXME
            },
            "matchesraw" => match args {
                [path, pattern] => {
                    Self::MatchesRaw { path: path.clone(), pattern: pattern.clone() }
                }
                args => panic!("arg mismatch: expected 2, got {}", args.len()), // FIXME
            },
            "files" => match args {
                [path, files] => Self::Files { path: path.clone(), files: files.clone() },
                args => panic!("arg mismatch: expected 2, got {}", args.len()), // FIXME
            },
            // FIXME: proper number parsing
            "count" => match args {
                [path, xpath, count] => Self::Count {
                    path: path.clone(),
                    xpath: xpath.clone(),
                    text: None,
                    count: count.parse().unwrap(),
                },
                [path, xpath, text, count] => Self::Count {
                    path: path.clone(),
                    xpath: xpath.clone(),
                    text: Some(text.clone()),
                    count: count.parse().unwrap(),
                },
                args => panic!("arg mismatch: expected 3 | 4, got {}", args.len()), // FIXME
            },
            "snapshot" => match args {
                [name, path, xpath] => {
                    Self::Snapshot { name: name.clone(), path: path.clone(), xpath: xpath.clone() }
                }
                args => panic!("arg mismatch: expected 3, got {}", args.len()), // FIXME
            },
            "has-dir" => match args {
                [path] => Self::HasDir { path: path.clone() },
                args => panic!("arg mismatch: expected 1, got {}", args.len()), // FIXME
            },
            _ => {
                // FIXME: Suggest potential typo candidates.
                // FIXME: Suggest "escaping" via non-whitespace char like backslash
                // FIXME: Note that it's parsed as a HtmlDocCk command, not as a ui_test-style compiletest directive
                dcx.emit(
                    &format!("unrecognized command `{}`", name.as_str()),
                    line,
                    (lineno, name.range()),
                    None,
                );
                return Err(());
            }
        })
    }
}

fn pattern() -> &'static regex::Regex {
    // FIXME: `LazyLock` once on beta
    static PATTERN: OnceLock<regex::Regex> = OnceLock::new();
    PATTERN.get_or_init(|| {
        use group::*;

        regex::RegexBuilder::new(&format!(
            r#"
            \s(?P<{NEGATION_MISPLACED}>!)?@(?P<{NEGATION}>!)?
            (?P<{NAME}>[A-Za-z]+(?:-[A-Za-z]+)*)
            (?P<{ARGUMENTS}>.*)$
            "#
        ))
        .ignore_whitespace(true)
        .unicode(true)
        .build()
        .unwrap()
    })
}

/// Regular expression capture groups.
mod group {
    pub(super) const ARGUMENTS: &str = "args";
    pub(super) const NAME: &str = "name";
    pub(super) const NEGATION_MISPLACED: &str = "prebang";
    pub(super) const NEGATION: &str = "postbang";
}
