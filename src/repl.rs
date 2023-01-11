pub use std::io::Result;
use std::{
    borrow::Cow,
    env,
    io::{self, ErrorKind},
    string::ToString,
};

use chrono::Utc;
use clap::{Arg, ArgMatches, Command};
use core::ops::{ControlFlow, Deref, DerefMut, Index};
use crossterm::style::Color;
use crox::{CroxError, CroxErrorKind, TokenType};
use directories::ProjectDirs;
use reedline::{
    default_emacs_keybindings, ColumnarMenu, DefaultHinter, EditCommand, Emacs, KeyCode,
    KeyModifiers, PromptEditMode, PromptHistorySearch, PromptHistorySearchStatus, PromptViMode,
    Reedline, ReedlineEvent, ReedlineMenu, SearchDirection, SearchQuery, Signal, Span,
    SqliteBackedHistory, Suggestion, ValidationResult,
};

use crate::frontend::{Config, Frontend};

pub struct Repl {
    line_editor: Changeable<Reedline>,
    prompt: Prompt,
    validator_enabled: bool,
    clear_history_at_end: bool,
    command: Command,
    config: SetConfig,
    frontend_config: Option<Config>,
    frontend: Frontend,
}

impl Repl {
    pub fn run() -> Result<()> {
        println!("Type :help for a list of available commands or :exit to exit the shell.");

        let mut line_editor = Self::new()?;
        loop {
            let sig = line_editor.read_line()?;
            if sig.handle()?.is_break() {
                break;
            }
        }

        Ok(())
    }

    fn new() -> Result<Self> {
        fn commands() -> Command {
            make_cmd(
                env!("CARGO_PKG_NAME"),
                Commands::values().iter().map(|sub| sub.cmd(None)),
            )
            .disable_colored_help(true)
            .disable_help_flag(true)
            .disable_help_subcommand(true)
            .disable_version_flag(true)
            .no_binary_name(true)
            .display_name("")
        }

        fn line_editor(command: &Command) -> Result<Reedline> {
            let history = Repl::create_history()?;

            let edit_mode = {
                let mut keybindings = default_emacs_keybindings();
                keybindings.add_binding(
                    KeyModifiers::NONE,
                    KeyCode::Tab,
                    ReedlineEvent::UntilFound(vec![
                        ReedlineEvent::MenuNext,
                        ReedlineEvent::Menu("completion_menu".to_string()),
                    ]),
                );
                keybindings.add_binding(
                    KeyModifiers::ALT,
                    KeyCode::Enter,
                    ReedlineEvent::Edit(vec![EditCommand::InsertNewline]),
                );
                keybindings.add_binding(KeyModifiers::SHIFT, KeyCode::Enter, ReedlineEvent::Enter);
                Emacs::new(keybindings)
            };

            let completer = Completer::new(command);
            let completion_menu = ColumnarMenu::default().with_name("completion_menu");
            let hinter = DefaultHinter::default().with_style(nu_ansi_term::Style::new().dimmed());
            let validator = Validator;

            let line_editor = Reedline::create()
                .with_ansi_colors(true)
                .with_edit_mode(Box::new(edit_mode))
                .with_history(Box::new(history))
                .with_completer(Box::new(completer))
                .with_menu(ReedlineMenu::EngineCompleter(Box::new(completion_menu)))
                .with_hinter(Box::new(hinter))
                .with_validator(Box::new(validator))
                .with_quick_completions(true)
                .with_partial_completions(true);

            Ok(line_editor)
        }
        let command = commands();
        let frontend = Frontend::new();

        let line_editor = line_editor(&command)?;
        let line_editor = Changeable::new(line_editor);

        Ok(Self {
            line_editor,
            prompt: Prompt,
            validator_enabled: true,
            clear_history_at_end: false,
            config: SetConfig::default(),
            frontend_config: None,
            command,
            frontend,
        })
    }

    fn read_line(&mut self) -> Result<LineCommand<'_>> {
        let sig = self.line_editor.read_line(&self.prompt)?;

        // record start time of this command, so that we can calculate the duration in Drop
        let _item = self.line_editor.update_last_command_context(&|mut item| {
            item.start_timestamp = Some(Utc::now());
            item
        });

        Ok(LineCommand::new(self, sig))
    }

    fn run_frontend(&self, query: &str) {
        self.frontend
            .run(io::stdout(), io::stderr(), query, self.frontend_config);
    }

    fn handle_command(&mut self, command: &str) -> Result<ControlFlow<()>> {
        let args = command
            .split_ascii_whitespace()
            .map(str::trim)
            .filter(|s| !s.is_empty())
            .collect::<Vec<_>>();

        let matches = self.command.try_get_matches_from_mut(args);
        match matches {
            Ok(matches) => match Commands::matches(&matches) {
                Ok((cmd, matches)) => match cmd {
                    Commands::Exit => return Ok(ControlFlow::Break(())),
                    Commands::Help => {
                        let help_cmd = self
                            .command
                            .find_subcommand_mut(":help")
                            .expect("The :help command should exist");

                        Self::print_help(help_cmd, matches.subcommand())?;
                    }
                    Commands::Clear => match ClearCommand::matches(matches) {
                        Ok((ClearCommand::Screen, _)) | Err(CommandMatchError::NoSubcommand) => {
                            self.clear_screen()?;
                        }
                        Ok((ClearCommand::Config, _)) => self.clear_config(),
                        Ok((ClearCommand::History, _)) => self.clear_history(),
                        Ok((ClearCommand::Scrollback, _)) => self.clear_scrollback()?,
                        Err(CommandMatchError::NoMatch(_)) => self.print_main_help()?,
                    },
                    Commands::Config => match ConfigCommand::matches(matches) {
                        Ok((ConfigCommand::Show, _)) | Err(CommandMatchError::NoSubcommand) => {
                            self.show_config();
                        }
                        Ok((ConfigCommand::Clear, _)) => {
                            self.clear_config();
                            self.show_config();
                        }
                        Ok((ConfigCommand::Set, matches)) => {
                            self.set_config(&ConfigCommand::get_config(matches));
                            self.show_config();
                        }
                        Err(CommandMatchError::NoMatch(_)) => self.print_main_help()?,
                    },
                    Commands::AutoNewLine => self.toggle_validator(),
                    Commands::History => self.print_history()?,
                    Commands::Vars => self.frontend.print_vars(io::stdout()),
                },
                Err(_) => self.print_main_help()?,
            },
            Err(e) => e.print()?,
        }

        Ok(ControlFlow::Continue(()))
    }

    fn print_help(command: &mut Command, sub_command: Option<(&str, &ArgMatches)>) -> Result<()> {
        match sub_command {
            Some((cmd, matches)) => match command.find_subcommand_mut(cmd) {
                Some(sub) => Self::print_help(sub, matches.subcommand())?,
                None => println!("Unknown subcommand: {cmd}"),
            },
            None => Self::print_help_for(command)?,
        }

        Ok(())
    }

    fn print_main_help(&mut self) -> Result<()> {
        Self::print_help_for(&mut self.command)
    }

    fn print_help_for(command: &mut Command) -> Result<()> {
        command.write_long_help(&mut std::io::stdout().lock())
    }

    fn print_history(&self) -> Result<()> {
        let history = self
            .line_editor
            .history()
            .search(SearchQuery::everything(SearchDirection::Forward))
            .map_err(|e| io::Error::new(ErrorKind::Other, e))?;

        for entry in history {
            if let Some(duration) = entry.duration {
                println!("({duration:?})\t{}", entry.command_line);
            } else {
                println!("\t{}", entry.command_line);
            }
        }

        Ok(())
    }

    fn clear_history(&mut self) {
        self.clear_history_at_end = true;
    }

    fn toggle_validator(&mut self) {
        if self.validator_enabled {
            self.validator_enabled = false;
            self.line_editor.modify(Reedline::disable_validator);
            println!("Auto newline disabled.");
            println!("You can enter newlines by using ALT+Enter.");
        } else {
            self.validator_enabled = true;
            let validator = Box::new(Validator);
            self.line_editor.modify(|le| le.with_validator(validator));
            println!("Auto newline enabled.");
        }
    }

    fn show_config(&self) {
        let mut dc = None::<Config>;

        for (config, configured) in self.config.0 {
            let name = config.name();
            configured.map_or_else(
                || {
                    let dc = dc.get_or_insert_with(Config::default);
                    let default_value = *config.config_field(dc);
                    println!("{name}: {default_value} (default)");
                },
                |value| println!("{name}: {value} (configured)"),
            );
        }
    }

    fn set_config(&mut self, config: &SetConfig) {
        let set_config = SetConfig::new(|opt| config[opt].or(self.config[opt]));
        self.inner_set_configs(set_config);
    }

    fn clear_config(&mut self) {
        self.inner_set_configs(SetConfig::default());
    }

    fn inner_set_configs(&mut self, set_config: SetConfig) {
        let mut config = None::<Config>;
        for (option, configured) in set_config.0 {
            if let Some(value) = configured {
                let config = config.get_or_insert_with(Config::default);
                let config = option.config_field(config);
                *config = value;
            }
        }

        self.config = set_config;
        self.frontend_config = config;
    }

    fn clear_screen(&mut self) -> Result<()> {
        self.line_editor.clear_screen()?;
        Ok(())
    }

    fn clear_scrollback(&mut self) -> Result<()> {
        self.line_editor.clear_scrollback()?;
        Ok(())
    }

    fn create_history() -> Result<SqliteBackedHistory> {
        const APPLICATION: &str = env!("CARGO_PKG_NAME");

        let history = ProjectDirs::from("io", "knutwalker", APPLICATION).ok_or_else(|| {
            io::Error::new(
                ErrorKind::Other,
                format!("Could not find project directories for {APPLICATION}"),
            )
        })?;

        let history = history.data_dir().join(format!("{APPLICATION}.history"));

        SqliteBackedHistory::with_file(history.clone()).map_err(|e| {
            io::Error::new(
                ErrorKind::Other,
                format!(
                    "Could not open history file at {}: {}",
                    history.display(),
                    e
                ),
            )
        })
    }
}

impl Drop for Repl {
    fn drop(&mut self) {
        if self.clear_history_at_end {
            if let Ok(mut history) = Self::create_history() {
                use reedline::History;

                history
                    .search(SearchQuery::everything(SearchDirection::Backward))
                    .unwrap_or_default()
                    .into_iter()
                    .filter_map(|e| e.id)
                    .for_each(|id| {
                        let _item = history.delete(id);
                    });
            }
        }
    }
}

struct LineCommand<'a> {
    line_editor: &'a mut Repl,
    signal: Signal,
}

impl<'a> LineCommand<'a> {
    fn new(line_editor: &'a mut Repl, signal: Signal) -> Self {
        Self {
            line_editor,
            signal,
        }
    }

    fn handle(self) -> Result<ControlFlow<()>> {
        match &self.signal {
            Signal::Success(buffer) => {
                let buffer = buffer.trim_start();
                if buffer.starts_with(':') {
                    let ctrl = self.line_editor.handle_command(buffer)?;
                    return Ok(ctrl);
                }
                if !buffer.is_empty() {
                    self.line_editor.run_frontend(buffer);
                }
            }
            Signal::CtrlD => return Ok(ControlFlow::Break(())),
            Signal::CtrlC => println!("Interrupted. Type :exit to exit the shell."),
        }

        Ok(ControlFlow::Continue(()))
    }
}

impl Drop for LineCommand<'_> {
    fn drop(&mut self) {
        // record duration of last command, ignore if there wasn't one
        let _item = self
            .line_editor
            .line_editor
            .update_last_command_context(&|mut item| {
                item.duration = item
                    .start_timestamp
                    .map(|start| Utc::now() - start)
                    .and_then(|d| d.to_std().ok());
                item
            });
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Commands {
    Exit,
    Help,
    Clear,
    History,
    Config,
    AutoNewLine,
    Vars,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum ClearCommand {
    Config,
    History,
    Scrollback,
    Screen,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum ConfigCommand {
    Show,
    Clear,
    Set,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(u8)]
enum ConfigOption {
    Ast,
    Timings,
}

trait CommandValues: Sized {
    fn values() -> &'static [Self];

    fn name(self) -> &'static str;

    fn matches(
        matches: &ArgMatches,
    ) -> std::result::Result<(Self, &ArgMatches), CommandMatchError<'_>>
    where
        Self: Copy + 'static,
    {
        let (sub, matches) = matches
            .subcommand()
            .ok_or(CommandMatchError::NoSubcommand)?;
        Self::values()
            .iter()
            .find_map(|&cmd| (cmd.name() == sub).then_some((cmd, matches)))
            .ok_or(CommandMatchError::NoMatch(sub))
    }
}

fn make_cmd<T>(name: &'static str, subs: T) -> Command
where
    T: Iterator<Item = Command> + ExactSizeIterator,
{
    const HELP_TEMPLATE: &str = "{before-help}{name}\n{about}{options}{after-help}\n";

    const HELP_TEMPLATE_WITH_SUB: &str = concat!(
        "{before-help}{name}\n",
        "{about-with-newline}\n",
        "Available Commands:\n",
        "{subcommands}{after-help}\n",
    );

    let cmd = Command::new(name)
        .subcommand_help_heading("Available Commands")
        .help_template(if subs.len() == 0 {
            HELP_TEMPLATE
        } else {
            HELP_TEMPLATE_WITH_SUB
        })
        .after_long_help(concat!(
            "For help on a specific command type:\n",
            "    :help command\n",
            "Use up and down arrows to access statement history.",
        ));

    subs.fold(cmd, Command::subcommand)
}

impl CommandValues for Commands {
    fn values() -> &'static [Self] {
        &[
            Self::Exit,
            Self::Help,
            Self::Clear,
            Self::History,
            Self::Config,
            Self::AutoNewLine,
            Self::Vars,
        ]
    }

    fn name(self) -> &'static str {
        match self {
            Self::Exit => ":exit",
            Self::Help => ":help",
            Self::Clear => ":clear",
            Self::History => ":history",
            Self::Config => ":config",
            Self::AutoNewLine => ":auto-newline",
            Self::Vars => ":vars",
        }
    }
}

impl Commands {
    const fn about(self) -> &'static str {
        match self {
            Self::Exit => "Exit the shell",
            Self::Help => "Show all available commands",
            Self::Clear => "Clear the screen (default) or the scrollback buffer or the history",
            Self::History => "Print a list of the last commands executed",
            Self::Config => "Manage the current REPL configuration",
            Self::AutoNewLine => "Toggle automatic insertion of newlines",
            Self::Vars => "Show the current variables of this session",
        }
    }

    fn sub_commands(self, prefix: Option<&str>) -> Vec<Command> {
        match self {
            Self::Help => {
                let prefix = ":help";

                Self::values()
                    .iter()
                    .filter(|x| **x != self)
                    .map(|cmd| {
                        cmd.cmd(Some(prefix))
                            .name(cmd.name().trim_start_matches(':'))
                            .display_name(format!(":help {}", cmd.name().trim_start_matches(':')))
                    })
                    .collect()
            }

            Self::Clear => ClearCommand::values()
                .iter()
                .map(|cmd| {
                    let name = prefix.map_or_else(
                        || format!(":clear {}", cmd.name()),
                        |prefix| format!("{prefix} clear {}", cmd.name()),
                    );
                    make_cmd(cmd.name(), std::iter::empty())
                        .about(cmd.about())
                        .display_name(name)
                })
                .collect(),

            Self::Config => ConfigCommand::values()
                .iter()
                .map(|cmd| {
                    let name = prefix.map_or_else(
                        || format!(":config {}", cmd.name()),
                        |prefix| format!("{prefix} config {}", cmd.name()),
                    );
                    cmd.add_args(
                        make_cmd(cmd.name(), std::iter::empty())
                            .about(cmd.about())
                            .display_name(name),
                    )
                })
                .collect(),

            _ => Vec::new(),
        }
    }

    fn cmd(self, prefix: Option<&str>) -> Command {
        make_cmd(self.name(), self.sub_commands(prefix).into_iter()).about(self.about())
    }
}

impl CommandValues for ClearCommand {
    fn values() -> &'static [Self] {
        &[Self::History, Self::Scrollback, Self::Screen, Self::Config]
    }

    fn name(self) -> &'static str {
        match self {
            Self::Config => "config",
            Self::History => "history",
            Self::Scrollback => "scrollback",
            Self::Screen => "screen",
        }
    }
}

impl ClearCommand {
    const fn about(self) -> &'static str {
        match self {
            Self::Config => "Clear the current configuration",
            Self::History => {
                "Clear the history. It will only be cleared at the end of the session."
            }
            Self::Scrollback => "Clear the scrollback buffer",
            Self::Screen => "Clear the screen",
        }
    }
}

impl CommandValues for ConfigCommand {
    fn values() -> &'static [Self] {
        &[Self::Show, Self::Clear, Self::Set]
    }

    fn name(self) -> &'static str {
        match self {
            Self::Show => "show",
            Self::Clear => "clear",
            Self::Set => "set",
        }
    }
}

impl ConfigCommand {
    const fn about(self) -> &'static str {
        match self {
            Self::Show => "Show the current configuration",
            Self::Clear => "Clear the current configuration",
            Self::Set => "Set configuration values",
        }
    }

    fn add_args(self, cmd: Command) -> Command {
        match self {
            Self::Set => ConfigOption::values()
                .iter()
                .fold(cmd, |cmd, opt| cmd.arg(opt.arg())),
            _ => cmd,
        }
    }

    fn get_config(matches: &ArgMatches) -> SetConfig {
        SetConfig::new(|opt| matches.get_one(opt.name()).copied())
    }
}

impl CommandValues for ConfigOption {
    fn values() -> &'static [Self] {
        &[Self::Ast, Self::Timings]
    }

    fn name(self) -> &'static str {
        match self {
            Self::Ast => "ast",
            Self::Timings => "timinigs",
        }
    }
}

impl ConfigOption {
    const fn help(self) -> &'static str {
        match self {
            Self::Ast => "Print the AST of the query.",
            Self::Timings => "Print the timings of the query.",
        }
    }

    const fn long_help(self) -> &'static str {
        match self {
            Self::Ast => "Print the AST of the query in additiont to the result.",
            Self::Timings => "Print times for parsing and evaluating the query.",
        }
    }

    fn arg(self) -> Arg {
        Arg::new(self.name())
            .short(self.name().chars().next().unwrap())
            .long(self.name())
            .help(self.help())
            .long_help(self.long_help())
            .required(false)
            .num_args(1)
            .default_missing_value("true")
            .value_parser(clap::builder::BoolishValueParser::new())
    }

    fn config_field(self, config: &mut Config) -> &mut bool {
        match self {
            Self::Ast => &mut config.show_ast,
            Self::Timings => &mut config.show_timings,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct SetConfig([(ConfigOption, Option<bool>); 2]);

impl SetConfig {
    fn new(value: impl Fn(ConfigOption) -> Option<bool>) -> Self {
        Self(
            ConfigOption::values()
                .iter()
                .map(|&opt| (opt, value(opt)))
                .collect::<Vec<_>>()
                .try_into()
                .expect("Need to update the number of options in SetConfig"),
        )
    }
}

impl Default for SetConfig {
    fn default() -> Self {
        Self::new(|_| None)
    }
}

impl Index<ConfigOption> for SetConfig {
    type Output = Option<bool>;

    fn index(&self, index: ConfigOption) -> &Self::Output {
        &self.0[usize::from(index as u8)].1
    }
}

enum CommandMatchError<'a> {
    NoSubcommand,
    NoMatch(&'a str),
}

struct Completer {
    command: Command,
}

impl Completer {
    fn new(commands: &Command) -> Self {
        Self {
            command: commands.clone(),
        }
    }

    fn find_matching<'a, 'b: 'a>(
        &'a self,
        line: &'b str,
    ) -> impl Iterator<Item = (usize, &'a Command)> + 'a {
        fn addr(s: &str) -> usize {
            s.as_ptr() as usize
        }

        fn find_command<'a, 'b: 'a>(
            line: &'b str,
            (pos, word): (usize, &'b str),
            mut remaining: impl Iterator<Item = (usize, &'b str)>,
            command: &'a Command,
        ) -> impl Iterator<Item = (usize, &'a Command)> + 'a {
            match command.find_subcommand(word) {
                Some(cmd) => find_command(line, remaining.next().unwrap(), remaining, cmd),
                None => command
                    .get_subcommands()
                    .filter(move |c| c.get_name().starts_with(word))
                    .map(move |c| (pos + usize::from(word.is_empty() && !line.is_empty()), c)),
            }
        }

        let line = line.trim_end();

        let mut words = line
            .split_whitespace()
            .map(move |word| (addr(word) - addr(line), word))
            .chain(std::iter::repeat((line.len(), "")));

        let word = words.next().unwrap();

        find_command(line, word, words, &self.command)
    }

    fn build_suggestion(start: usize, pos: usize, command: &Command) -> Suggestion {
        let diff = start.saturating_sub(pos);
        let value = format!("{:>diff$}{}", "", command.get_name());

        Suggestion {
            value,
            description: command.get_about().map(ToString::to_string),
            extra: None,
            span: Span::new(start.min(pos), pos),
            append_whitespace: true,
        }
    }
}

impl reedline::Completer for Completer {
    fn complete(&mut self, line: &str, pos: usize) -> Vec<Suggestion> {
        self.find_matching(line)
            .map(|(start, c)| Self::build_suggestion(start, pos, c))
            .collect()
    }

    fn partial_complete(
        &mut self,
        line: &str,
        pos: usize,
        start: usize,
        offset: usize,
    ) -> Vec<Suggestion> {
        self.find_matching(line)
            .skip(start)
            .take(offset)
            .map(|(start, c)| Self::build_suggestion(start, pos, c))
            .collect()
    }

    fn total_completions(&mut self, line: &str, _pos: usize) -> usize {
        self.find_matching(line).count()
    }
}

struct Validator;

impl reedline::Validator for Validator {
    fn validate(&self, line: &str) -> ValidationResult {
        fn is_incomplete(error: &CroxError) -> bool {
            match &error.kind {
                CroxErrorKind::UnexpectedEndOfInput {
                    expected: Some(expected),
                } if expected.len() == 1 && expected.contains(TokenType::Semicolon) => false,
                CroxErrorKind::UnexpectedEndOfInput { .. }
                | CroxErrorKind::UnclosedStringLiteral
                | CroxErrorKind::UnclosedDelimiter { .. } => true,
                _ => false,
            }
        }

        let line = line.trim_start();
        if line.starts_with(':') || line.is_empty() {
            return ValidationResult::Complete;
        }

        match crox::parse(line) {
            Ok(_) => ValidationResult::Complete,
            Err(e) => match e.errors() {
                [e] if is_incomplete(e) => ValidationResult::Incomplete,
                _ => ValidationResult::Complete,
            },
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Changeable<T> {
    Value(T),
    Placeholder,
}

impl<T> Changeable<T> {
    const fn new(value: T) -> Self {
        Self::Value(value)
    }

    fn modify(&mut self, f: impl FnOnce(T) -> T) {
        self.try_modify(|v| Ok(f(v))).unwrap();
    }

    fn try_modify(&mut self, f: impl FnOnce(T) -> Result<T>) -> Result<()> {
        let this = std::mem::replace(self, Self::Placeholder);
        let this = this.try_map(f)?;
        let placeholder = std::mem::replace(self, this);
        debug_assert!(matches!(placeholder, Self::Placeholder));
        Ok(())
    }

    fn try_map<U>(self, f: impl FnOnce(T) -> Result<U>) -> Result<Changeable<U>> {
        Ok(match self {
            Self::Value(value) => Changeable::Value(f(value)?),
            Self::Placeholder => Changeable::Placeholder,
        })
    }
}

impl<T> Deref for Changeable<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        match self {
            Self::Value(value) => value,
            Self::Placeholder => panic!("using value while it's being changed"),
        }
    }
}

impl<T> DerefMut for Changeable<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            Self::Value(value) => value,
            Self::Placeholder => panic!("using value while it's being changed"),
        }
    }
}

struct Prompt;

impl reedline::Prompt for Prompt {
    fn render_prompt_left(&self) -> Cow<'_, str> {
        "".into()
    }

    fn render_prompt_right(&self) -> Cow<'_, str> {
        "".into()
    }

    fn render_prompt_indicator(&self, prompt_mode: PromptEditMode) -> Cow<'_, str> {
        match prompt_mode {
            PromptEditMode::Vi(PromptViMode::Insert) => ": ".into(),
            PromptEditMode::Custom(str) => format!("({str})").into(),
            _ => "> ".into(),
        }
    }

    fn render_prompt_multiline_indicator(&self) -> Cow<'_, str> {
        "..".into()
    }

    fn render_prompt_history_search_indicator(
        &self,
        history_search: PromptHistorySearch,
    ) -> Cow<'_, str> {
        match history_search.status {
            PromptHistorySearchStatus::Passing => "bck-i-search: ".into(),
            PromptHistorySearchStatus::Failing => {
                format!("failing bck-i-search: {}", history_search.term).into()
            }
        }
    }

    fn get_prompt_color(&self) -> Color {
        Color::Reset
    }

    fn get_indicator_color(&self) -> Color {
        Color::Reset
    }

    fn get_prompt_right_color(&self) -> Color {
        Color::Reset
    }
}
