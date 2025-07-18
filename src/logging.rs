use logforth::color::LevelColor;
use logforth::filter::EnvFilter;
use logforth::{Layout, append};

#[derive(Debug, Clone, Copy)]
struct MinimalLogforthLayout;

impl Layout for MinimalLogforthLayout {
    fn format(
        &self,
        record: &log::Record,
        _: &[Box<dyn logforth::Diagnostic>],
    ) -> anyhow::Result<Vec<u8>> {
        let colors = LevelColor::default();
        let level = colors.colorize_record_level(false, record.level());
        let message = record.args();
        Ok(format!("{level:>5} {message}").into_bytes())
    }
}

pub fn enable_logforth() {
    __enable_logforth(append::Stderr::default().with_layout(MinimalLogforthLayout));
}

pub fn enable_logforth_stderr() {
    __enable_logforth(append::Stderr::default());
}

fn __enable_logforth<T: logforth::Append>(layout: T) {
    logforth::builder()
        .dispatch(|d| d.filter(EnvFilter::from_default_env()).append(layout))
        .apply();
}
