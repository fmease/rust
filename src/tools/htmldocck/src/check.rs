use crate::cache::Cache;
use crate::error::DiagCtxt;
use crate::{Command, CommandKind};

impl Command {
    // FIXME: implement all checks!
    // FIXME: move regex parsing etc. into the parser maybe
    pub(crate) fn run(self, cache: &mut Cache<'_>, dcx: &mut DiagCtxt) -> Result<(), ()> {
        let result = self.kind.run(cache, dcx)?;

        if result == self.negated {
            // FIXME: better diag incl. location
            dcx.emit_noloc("check failed");
            return Err(());
        }

        Ok(())
    }
}

impl CommandKind {
    #[allow(unused_variables)] // FIXME: temporary
    fn run(self, cache: &mut Cache<'_>, dcx: &mut DiagCtxt) -> Result<bool, ()> {
        Ok(match self {
            Self::HasFile { path } => cache.has(path, dcx)?, // FIXME: check if it's actually a file
            Self::HasDir { path } => cache.has(path, dcx)?, // FIXME: check if it's actually a directory
            Self::Has { path, xpath, text } => {
                let data = cache.load(path, dcx)?;
                true // FIXME
            }
            Self::HasRaw { path, text } => {
                let data = cache.load(path, dcx)?;

                if text.is_empty() {
                    true
                } else {
                    let text = channel_url::instantiate(&text, dcx)?;
                    let text = text.replace(|c: char| c.is_ascii_whitespace(), " ");
                    let data = data.replace(|c: char| c.is_ascii_whitespace(), " ");

                    data.contains(&text)
                }
            }
            Self::Matches { path, xpath, pattern } => {
                let data = cache.load(path, dcx)?;
                true // FIXME
            }
            Self::MatchesRaw { path, pattern } => {
                let data = cache.load(path, dcx)?;
                let pattern = channel_url::instantiate(&pattern, dcx)?;

                if pattern.is_empty() {
                    true
                } else {
                    let Ok(pattern) = regex::RegexBuilder::new(&pattern)
                        .unicode(true)
                        // FIXME: better diagnostic incl. location
                        .build()
                        .map_err(|error| dcx.emit_noloc(&format!("malformed regex: {error}")))
                    else {
                        return Err(());
                    };

                    pattern.is_match(data)
                }
            }
            Self::Count { path, xpath, text, count } => {
                let data = cache.load(path, dcx)?;
                true // FIXME
            }
            Self::Files { path, files } => {
                let data = cache.load(path, dcx)?;
                true // FIXME
            }
            Self::Snapshot { name, path, xpath } => {
                let data = cache.load(path, dcx)?;
                true // FIXME
            }
        })
    }
}

mod channel_url {
    use std::{borrow::Cow, sync::OnceLock};

    use crate::error::DiagCtxt;

    const PLACEHOLDER: &str = "{{channel}}";

    pub(super) fn instantiate<'a>(input: &'a str, dcx: &mut DiagCtxt) -> Result<Cow<'a, str>, ()> {
        let Some(channel_url) = channel_url(dcx)? else { return Ok(input.into()) };
        Ok(input.replace(PLACEHOLDER, channel_url).into())
    }

    #[allow(dead_code)] // FIXME temporary
    pub(super) fn anonymize<'a>(input: &'a str, dcx: &'_ mut DiagCtxt) -> Result<Cow<'a, str>, ()> {
        let Some(channel_url) = channel_url(dcx)? else { return Ok(input.into()) };
        Ok(input.replace(channel_url, PLACEHOLDER).into())
    }

    fn channel_url(dcx: &mut DiagCtxt) -> Result<Option<&'static str>, ()> {
        static CHANNEL_URL: OnceLock<Option<String>> = OnceLock::new();

        // FIXME: Use `get_or_try_init` here (instead of `get`→`set`→`get`) if/once stabilized (on beta).

        if let Some(channel_url) = CHANNEL_URL.get() {
            return Ok(channel_url.as_deref());
        }

        const KEY: &str = "DOC_RUST_LANG_ORG_CHANNEL";

        let channel_url = match std::env::var(KEY) {
            Ok(url) => Some(url),
            // FIXME: should we make the channel mandatory instead?
            Err(std::env::VarError::NotPresent) => None,
            Err(std::env::VarError::NotUnicode(var)) => {
                // FIXME: better diag
                // FIXME: Use `OsStr::display` (instead of `to_string_lossy`) if/once stabilized (on beta).
                dcx.emit_noloc(&format!(
                    "env var `{KEY}` is not valid UTF-8: `{}`",
                    var.to_string_lossy()
                ));
                return Err(());
            }
        };

        // unwrap: The static item is locally scoped and no other thread tries to initialize it.
        CHANNEL_URL.set(channel_url).unwrap();
        // unwrap: Initialized above.
        Ok(CHANNEL_URL.get().unwrap().as_deref())
    }
}
