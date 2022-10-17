pub type Result<T = (), E = RunError> = core::result::Result<T, E>;

#[derive(Clone, Debug)]
pub struct RunError {
    pub line: usize,
    pub offset: usize,
    pub message: String,
    pub where_: String,
}

impl RunError {
    pub fn new(line: usize, offset: usize, message: impl Into<String>) -> Self {
        Self::with_where(line, offset, message, String::new())
    }

    pub fn with_where(
        line: usize,
        offset: usize,
        message: impl Into<String>,
        where_: impl Into<String>,
    ) -> Self {
        Self {
            line,
            offset,
            message: message.into(),
            where_: where_.into(),
        }
    }
}

impl core::fmt::Display for RunError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if f.alternate() {
            writeln!(f, "{0:~<start$}{0:^<1}", "", start = self.offset)?;
        }
        write!(
            f,
            "[line {}, offset {}] Error{}: {}",
            self.line, self.offset, self.where_, self.message
        )
    }
}

impl std::error::Error for RunError {}
