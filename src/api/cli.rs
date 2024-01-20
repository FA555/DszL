/// `Arguments` holds the command line arguments provided to the `DszL` application.
/// It utilizes `clap` for parsing and managing these arguments, providing an easy
/// and efficient way to handle command line inputs. The struct fields represent the
/// different options and flags that can be passed to the program.
///
/// # Examples
///
/// ```
/// dszl --file script.dszl --run TUI
/// dszl -f script.dszl -r GUI
/// dszl --version
/// ```
use clap::Parser;

#[derive(Parser, Debug)]
#[command(name = "DszL", author)]
pub(crate) struct Arguments {
    /// The script file to execute.
    #[clap(short, long, value_name = "PATH")]
    pub(crate) file: Option<String>,

    /// The user interface to use.
    #[clap(short = 'r', long = "run", default_value = "gui")]
    pub(crate) ui: UI,

    /// Print the version information and exit.
    #[clap(short, long)]
    pub(crate) version: bool,
}

/// Represents the types of user interfaces that `DszL` can run in. This enum is used to specify
/// the UI mode via command line arguments.
///
/// # Variants
/// - `Tui`: Terminal User Interface.
/// - `Gui`: Graphical User Interface.
#[derive(Clone, clap::ValueEnum, Debug, PartialEq)]
pub(crate) enum UI {
    Tui,
    Gui,
}
