use crate::{
    api::interact::Interact,
    lang::{result::ExecError, statement::Statement, visitor::Visitor},
};
use egui::FontData;
use std::sync::{Arc, Condvar, Mutex, RwLock};

/// Constants representing labels used in the GUI for user messages.
static USER_LABEL: &str = "User                                                                                            ";
/// Constants representing labels used in the GUI for bot messages.
static BOT_LABEL: &str = "Bot                                                                                              ";

/// The `Message` enum defines types of messages that can be displayed in the GUI.
///
/// It includes user messages and interpreter-generated messages.
pub(crate) enum Message {
    User { content: String, valid: bool },
    Interpreter { content: String },
}

/// `SharedData` is a struct that holds data shared across threads, including the GUI and interpreter threads.
///
/// It contains the current input, acceptance state, and update flag.
struct SharedData {
    input: String,
    accept: bool,
    updated: bool,
}

impl SharedData {
    /// Constructs a new `SharedData` instance with default values.
    fn new() -> Self {
        Self {
            input: String::new(),
            accept: false,
            updated: false,
        }
    }
}

/// `GuiInteractor` is responsible for managing interactions in the GUI context.
///
/// It holds shared data for cross-thread communication and a list of messages for display.
struct GuiInteractor {
    shd: Arc<Mutex<SharedData>>,
    messages: Arc<RwLock<Vec<Message>>>,
    condvar: Condvar,
}

impl GuiInteractor {
    /// Creates a new `GuiInteractor` instance with the given shared data.
    ///
    /// # Arguments
    ///
    /// - `shd`: Shared data wrapped in an `Arc<Mutex<SharedData>>` for thread-safe access.
    ///
    /// # Returns
    ///
    /// A new instance of `GuiInteractor`.
    pub(crate) fn with_inner(shd: Arc<Mutex<SharedData>>) -> Self {
        Self {
            shd,
            messages: Arc::new(RwLock::new(Vec::new())),
            condvar: Condvar::new(),
        }
    }
}

impl Interact for GuiInteractor {
    /// Waits for and retrieves user input from the GUI.
    ///
    /// This method blocks until input is provided and `updated` is set to `true`.
    ///
    /// # Returns
    ///
    /// A `String` representing the user input.
    fn input(&self) -> String {
        let mut shd = self.shd.lock().unwrap();
        shd.accept = true;

        while !shd.updated {
            shd = self.condvar.wait(shd).unwrap();
        }

        shd.accept = false;
        shd.updated = false;
        shd.input.clone()
    }

    /// Waits for user input from the GUI with a specified timeout.
    ///
    /// This method blocks until input is provided or the timeout is reached.
    ///
    /// # Arguments
    ///
    /// - `duration`: The maximum time to wait for input.
    ///
    /// # Returns
    ///
    /// `Some(String)` if input is provided before the timeout, or `None` if the timeout is reached.
    fn input_timeout(&self, duration: std::time::Duration) -> Option<String> {
        let mut shd = self.shd.lock().unwrap();
        shd.accept = true;

        let (mut shd, ret) = self
            .condvar
            .wait_timeout_while(shd, duration, |shd| !shd.updated)
            .unwrap();

        shd.accept = false;
        if ret.timed_out() {
            None
        } else {
            shd.updated = false;
            Some(shd.input.clone())
        }
    }

    /// Outputs a given string to the GUI, typically for display as an interpreter message.
    ///
    /// # Arguments
    ///
    /// - `s`: The string to be outputted.
    fn output(&self, s: &str) {
        let mut messages = self.messages.write().unwrap();
        let mut s = s;
        if s.starts_with("[[LF]]") {
            s = &s[6..];
        }
        messages.push(Message::Interpreter {
            content: s.replace("[[LF]]", "\n").replace("[[TAB]]", "\t"),
        });
    }
}

/// `App` represents the main application state for the GUI.
///
/// It contains an interactor for handling user interactions, user input, and the name of the file being processed.
pub(crate) struct App {
    interactor: Arc<GuiInteractor>,
    input: String,
    file: String,
}

impl App {
    /// Constructs a new `App` instance with a given interactor and file name.
    ///
    /// # Arguments
    ///
    /// - `interactor`: An `Arc<GuiInteractor>` for managing interactions.
    /// - `file`: The name of the file being processed.
    ///
    /// # Returns
    ///
    /// A new instance of `App`.
    fn new(interactor: Arc<GuiInteractor>, file: String) -> Self {
        Self {
            interactor,
            input: String::new(),
            file,
        }
    }
}

impl eframe::App for App {
    /// Updates the GUI state. This method is called by the `eframe` runtime to render the GUI.
    ///
    /// # Arguments
    ///
    /// - `ctx`: The `egui::Context` used for GUI rendering.
    /// - `_frame`: Unused `eframe::Frame`.
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        // const MAX_FPS: f64 = 5.0;
        // std::thread::sleep(std::time::Duration::from_millis((1000.0 / MAX_FPS) as u64));
        // debug!("Update GUI.");

        use egui::FontId;
        egui::CentralPanel::default().show(ctx, |ui| {
            ui.heading("Domain Specific Zestful Bot");
            ui.label(format!("File: {}", self.file));
            ui.separator();
            egui::ScrollArea::vertical().show(ui, |ui| {
                use egui::Color32;

                let gen_text = |s| egui::RichText::new(s).font(FontId::proportional(20.0));
                let gen_text_color = |s, c| gen_text(s).color(c);

                let messages = self.interactor.messages.read().unwrap();
                for message in messages.iter() {
                    match message {
                        Message::User { content, valid } => {
                            ui.label(gen_text_color(USER_LABEL, Color32::DARK_GREEN));
                            let mut text = gen_text(content);
                            if *valid {
                                text = text.underline();
                            }
                            ui.label(text);
                        }
                        Message::Interpreter { content } => {
                            ui.label(gen_text_color(BOT_LABEL, Color32::DARK_BLUE));
                            ui.label(gen_text(content));
                        }
                    }
                }
                ui.label(gen_text_color("LAZY PADDING", Color32::TRANSPARENT));
                ui.label(gen_text_color("LAZY PADDING", Color32::TRANSPARENT));
            })
        });
        egui::TopBottomPanel::bottom("user-input").show(ctx, |ui| {
            let widget = egui::TextEdit::singleline(&mut self.input)
                .desired_width(f32::INFINITY)
                .hint_text("回车发送消息")
                .font(FontId::proportional(20.0))
                .margin(egui::vec2(8.0, 8.0));
            let response = ui.add(widget);
            if response.lost_focus() && ui.input(|i| i.key_pressed(egui::Key::Enter)) {
                let mut shd = self.interactor.shd.lock().unwrap();
                if shd.accept {
                    shd.input = self.input.clone();
                    shd.updated = true;
                    self.interactor.condvar.notify_one();
                    let mut messages = self.interactor.messages.write().unwrap();
                    messages.push(Message::User {
                        content: self.input.clone(),
                        valid: true,
                    });
                } else {
                    let mut messages = self.interactor.messages.write().unwrap();
                    messages.push(Message::User {
                        content: self.input.clone(),
                        valid: false,
                    });
                }

                self.input.clear();
                response.request_focus();
            }
        });

        ctx.request_repaint_after(std::time::Duration::from_millis(100));
    }
}

/// The entry point for the GUI application.
///
/// Initializes the GUI and interpreter, then runs the main event loop.
///
/// # Arguments
///
/// - `file`: The name of the file being processed.
/// - `statements`: A vector of `Statement` to be executed by the interpreter.
///
/// # Returns
///
/// `std::io::Result<()>`: Result indicating success or failure of the application initialization and execution.
pub(crate) fn main(file: String, statements: Vec<Statement>) -> std::io::Result<()> {
    let interactor = Arc::new(GuiInteractor::with_inner(Arc::new(Mutex::new(
        SharedData::new(),
    ))));
    let interactor_clone1 = interactor.clone();
    let interactor_clone2 = interactor.clone();
    std::thread::spawn(move || {
        match Visitor::with_interactor(interactor_clone1).executes(statements) {
            Ok(_) | Err(ExecError::Exit) => interactor.output("【客服机器人已离开会话。】"),
            Err(e) => interactor.output(&format!("运行错误：{}[[LF]]【客服机器人已退出。】", e)),
        }
    });

    match eframe::run_native(
        "DszL 客服机器人",
        Default::default(),
        Box::new(|eframe::CreationContext { egui_ctx, .. }| {
            let mut fonts = egui::FontDefinitions::default();
            fonts.font_data.insert(
                "HYZhengYuan".to_owned(),
                FontData::from_static(include_bytes!("../../assets/HYZhengYuan-55W.ttf")),
            );
            fonts
                .families
                .get_mut(&egui::FontFamily::Proportional)
                .unwrap()
                .insert(0, "HYZhengYuan".to_owned());
            egui_ctx.set_fonts(fonts);
            egui_ctx.set_visuals(egui::Visuals::light());
            Box::new(App::new(interactor_clone2, file))
        }),
    ) {
        Ok(_) => Ok(()),
        Err(e) => {
            error!("GUI exited with error: {}", e);
            Err(std::io::Error::new(
                std::io::ErrorKind::Other,
                "GUI exited with error.",
            ))
        }
    }
}
