/// The `Interact` trait defines an interface for interaction, particularly for cases where input from a user is
/// required and output needs to be presented to the user. This trait can be implemented in various contexts such as
/// command-line applications, GUI applications, or web services.
///
/// This trait includes basic methods for input and output, along with an optional method to retrieve the output
/// history.
pub(crate) trait Interact {
    /// Requests and retrieves user input as a string.
    ///
    /// This method will block until user input is received.
    ///
    /// # Returns
    ///
    /// - `String`: The user's input.
    fn input(&self) -> String;

    /// Requests and retrieves user input, with a timeout for waiting.
    ///
    /// Returns `Some(String)` if the user provides input within the specified time, or `None` if it times out.
    ///
    /// # Arguments
    ///
    /// - `duration`: The maximum duration to wait for user input.
    ///
    /// # Returns
    ///
    /// - `Option<String>`: The user's input if available within the timeout, or `None` otherwise.
    fn input_timeout(&self, duration: std::time::Duration) -> Option<String>;

    /// Outputs the given string to the user.
    ///
    /// This method is used to display or send output to the user interface.
    ///
    /// # Arguments
    ///
    /// - `s`: The string to be outputted.
    fn output(&self, s: &str);

    /// Retrieves the history of outputs presented to the user.
    ///
    /// This optional method returns a string representing the historical outputs. It should be implemented if tracking
    /// of output history is required.
    ///
    /// # Returns
    ///
    /// - `String`: A string containing the history of outputs.
    fn output_history(&self) -> String {
        unimplemented!();
    }
}
