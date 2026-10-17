"""
Developer Typing Bot

Exactness policy
----------------
* Source files are read-only input. They are hashed before and after a run.
* Each saved file must be BYTE-IDENTICAL to its original. Line endings
  (all-LF or all-CRLF) and a UTF-8 BOM are reproduced by configuring
  files.eol / files.encoding per language in the generated workspace.
* Files that cannot be reproduced exactly (mixed line endings, a lone CR,
  invalid UTF-8, control characters other than TAB/CR/LF) are refused at
  start-up instead of being altered.
* During the run every checkpoint compares decoded text; the final check
  compares the SHA-256 of the saved bytes with the SHA-256 of the original.
* Success is reported only after that final byte comparison passes.
"""

import ctypes
import hashlib
import json
import logging
import os
import queue
import random
import re
import shutil
import subprocess
import sys
import threading
import time
import traceback
import unicodedata
import tkinter as tk
from ctypes import wintypes
from datetime import datetime
from pathlib import Path
from tkinter import ttk, filedialog, messagebox

import pyautogui
import pygetwindow
from pynput import keyboard


# ==================================================================
# Low-level Windows keyboard input (SendInput)
# ==================================================================

IS_WINDOWS = sys.platform == "win32"

INPUT_KEYBOARD = 1
KEYEVENTF_EXTENDEDKEY = 0x0001
KEYEVENTF_KEYUP = 0x0002
KEYEVENTF_UNICODE = 0x0004
SW_RESTORE = 9

VK_BACK = 0x08
VK_TAB = 0x09
VK_RETURN = 0x0D
VK_SHIFT = 0x10
VK_CONTROL = 0x11
VK_MENU = 0x12
VK_END = 0x23
VK_HOME = 0x24
VK_F5 = 0x74
VK_LWIN = 0x5B
VK_RWIN = 0x5C
VK_1 = 0x31
VK_A = 0x41
VK_P = 0x50
VK_S = 0x53
EXTENDED_VKS = {VK_END, VK_HOME}

ULONG_PTR = ctypes.c_size_t


class KEYBDINPUT(ctypes.Structure):
    _fields_ = [
        ("wVk", wintypes.WORD),
        ("wScan", wintypes.WORD),
        ("dwFlags", wintypes.DWORD),
        ("time", wintypes.DWORD),
        ("dwExtraInfo", ULONG_PTR),
    ]


class MOUSEINPUT(ctypes.Structure):
    _fields_ = [
        ("dx", wintypes.LONG),
        ("dy", wintypes.LONG),
        ("mouseData", wintypes.DWORD),
        ("dwFlags", wintypes.DWORD),
        ("time", wintypes.DWORD),
        ("dwExtraInfo", ULONG_PTR),
    ]


class HARDWAREINPUT(ctypes.Structure):
    _fields_ = [
        ("uMsg", wintypes.DWORD),
        ("wParamL", wintypes.WORD),
        ("wParamH", wintypes.WORD),
    ]


class _INPUT_UNION(ctypes.Union):
    # MOUSEINPUT must be present so sizeof(INPUT) matches Windows.
    _fields_ = [("ki", KEYBDINPUT), ("mi", MOUSEINPUT), ("hi", HARDWAREINPUT)]


class INPUT(ctypes.Structure):
    _anonymous_ = ("u",)
    _fields_ = [("type", wintypes.DWORD), ("u", _INPUT_UNION)]


_user32 = None
_kernel32 = None

if IS_WINDOWS:
    _user32 = ctypes.WinDLL("user32", use_last_error=True)
    _kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)

    _user32.SendInput.argtypes = (
        wintypes.UINT, ctypes.POINTER(INPUT), ctypes.c_int
    )
    _user32.SendInput.restype = wintypes.UINT
    _user32.GetForegroundWindow.argtypes = ()
    _user32.GetForegroundWindow.restype = wintypes.HWND
    _user32.GetAsyncKeyState.argtypes = (ctypes.c_int,)
    _user32.GetAsyncKeyState.restype = ctypes.c_short
    _user32.MapVirtualKeyW.argtypes = (wintypes.UINT, wintypes.UINT)
    _user32.MapVirtualKeyW.restype = wintypes.UINT
    _user32.GetWindowTextLengthW.argtypes = (wintypes.HWND,)
    _user32.GetWindowTextLengthW.restype = ctypes.c_int
    _user32.GetWindowTextW.argtypes = (
        wintypes.HWND, wintypes.LPWSTR, ctypes.c_int
    )
    _user32.GetWindowTextW.restype = ctypes.c_int
    _user32.IsWindow.argtypes = (wintypes.HWND,)
    _user32.IsWindow.restype = wintypes.BOOL
    _user32.IsIconic.argtypes = (wintypes.HWND,)
    _user32.IsIconic.restype = wintypes.BOOL
    _user32.ShowWindow.argtypes = (wintypes.HWND, ctypes.c_int)
    _user32.ShowWindow.restype = wintypes.BOOL
    _user32.SetForegroundWindow.argtypes = (wintypes.HWND,)
    _user32.SetForegroundWindow.restype = wintypes.BOOL
    _user32.BringWindowToTop.argtypes = (wintypes.HWND,)
    _user32.BringWindowToTop.restype = wintypes.BOOL
    _user32.GetWindowThreadProcessId.argtypes = (
        wintypes.HWND, ctypes.POINTER(wintypes.DWORD)
    )
    _user32.GetWindowThreadProcessId.restype = wintypes.DWORD
    _user32.AttachThreadInput.argtypes = (
        wintypes.DWORD, wintypes.DWORD, wintypes.BOOL
    )
    _user32.AttachThreadInput.restype = wintypes.BOOL
    _kernel32.GetCurrentThreadId.argtypes = ()
    _kernel32.GetCurrentThreadId.restype = wintypes.DWORD


def _key_input(vk=0, scan=0, flags=0):
    item = INPUT()
    item.type = INPUT_KEYBOARD
    item.ki = KEYBDINPUT(vk, scan, flags, 0, 0)
    return item


def _send_events(events):
    """Send a batch of INPUT events atomically and check the result."""
    if _user32 is None:
        raise OSError("Keyboard injection is only supported on Windows.")
    count = len(events)
    if count == 0:
        return
    array = (INPUT * count)(*events)
    sent = _user32.SendInput(count, array, ctypes.sizeof(INPUT))
    if sent != count:
        raise OSError(
            f"SendInput delivered {sent}/{count} events "
            f"(Win32 error {ctypes.get_last_error()}). If VS Code runs "
            "as Administrator, run this bot as Administrator too."
        )


def utf16_units(char):
    """Return the UTF-16 code units of one character (2 for non-BMP)."""
    data = char.encode("utf-16-le")  # raises for lone surrogates
    return [
        int.from_bytes(data[i:i + 2], "little")
        for i in range(0, len(data), 2)
    ]


def send_unicode_char(char):
    """Send one literal character; non-BMP characters go as a surrogate
    pair inside a single SendInput call."""
    events = []
    for unit in utf16_units(char):
        events.append(_key_input(0, unit, KEYEVENTF_UNICODE))
        events.append(
            _key_input(0, unit, KEYEVENTF_UNICODE | KEYEVENTF_KEYUP)
        )
    _send_events(events)


def _vk_event(vk, key_up):
    flags = KEYEVENTF_KEYUP if key_up else 0
    if vk in EXTENDED_VKS:
        flags |= KEYEVENTF_EXTENDEDKEY
    scan = _user32.MapVirtualKeyW(vk, 0) if _user32 is not None else 0
    return _key_input(vk, scan, flags)


def send_vk(vk):
    """Press and release a virtual key (Enter, Tab, Backspace, F5...)."""
    _send_events([_vk_event(vk, False), _vk_event(vk, True)])


def send_chord(*vks):
    """Press keys in order, release in reverse (e.g. Ctrl+S)."""
    events = [_vk_event(vk, False) for vk in vks]
    events += [_vk_event(vk, True) for vk in reversed(vks)]
    _send_events(events)


def get_window_title(hwnd):
    if _user32 is None or not hwnd:
        return ""
    length = _user32.GetWindowTextLengthW(hwnd)
    buffer = ctypes.create_unicode_buffer(length + 1)
    _user32.GetWindowTextW(hwnd, buffer, length + 1)
    return buffer.value


# ==================================================================
# Pure helpers (no OS access)
# ==================================================================

# VS Code is told (via workspace settings) to use this window title so the
# bot can read the active editor's file name from the title bar.
TITLE_TEMPLATE = "TBOT::${activeEditorShort}::${rootName}::${dirty}::END"
_TITLE_RE = re.compile(
    r"^TBOT::(?P<file>.*?)::(?P<root>.*?)::(?P<dirty>.*?)::END", re.DOTALL
)
_DEFAULT_TITLE_RES = (
    re.compile(
        r"^(?P<dirty>[\u25cf*]\s*)?(?P<file>.+?) - (?P<root>.+?)"
        r" - Visual Studio Code(?: - Insiders)?\s*$"
    ),
    re.compile(
        r"^(?P<dirty>[\u25cf*]\s*)?(?P<root>.+?)"
        r" - Visual Studio Code(?: - Insiders)?\s*$"
    ),
)


def parse_title(title):
    """Return {'file','root','dirty'} for a VS Code title, else None."""
    title = title or ""
    match = _TITLE_RE.match(title)
    if match:
        return {
            "file": match.group("file").strip(),
            "root": match.group("root").strip(),
            "dirty": match.group("dirty").strip() != "",
        }
    for pattern in _DEFAULT_TITLE_RES:
        match = pattern.match(title)
        if match:
            groups = match.groupdict()
            return {
                "file": (groups.get("file") or "").strip(),
                "root": groups["root"].strip(),
                "dirty": bool(groups.get("dirty")),
            }
    return None


def classify(actual, expected):
    """'equal', 'behind' (actual is a proper prefix of expected) or
    'diverged' (anything else, including extra trailing content)."""
    if actual == expected:
        return "equal"
    if expected.startswith(actual):
        return "behind"
    return "diverged"


def first_difference(a, b):
    limit = min(len(a), len(b))
    for i in range(limit):
        if a[i] != b[i]:
            return i
    return limit


def sha256_text(text):
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def sha256_bytes(data):
    return hashlib.sha256(data).hexdigest()


class VerificationError(RuntimeError):
    """Saved content does not match the source."""


# ==================================================================
# Application
# ==================================================================

class DeveloperTypingBot:
    FILE_ORDER = ("index.html", "styles.css", "script.js")
    LANGUAGE_BLOCK = {
        "index.html": "[html]",
        "styles.css": "[css]",
        "script.js": "[javascript]",
    }

    CURSOR_MOVE_INTERVAL = 20
    CURSOR_MOVE_DURATION = 3
    BROWSER_REFRESH_INTERVAL = 30
    BROWSER_REFRESH_WAIT = 1

    # Checkpoint = save + read back from disk + exact comparison.
    SAVE_EVERY_CHARACTERS = 25
    SAVE_VERIFY_TIMEOUT = 4.0
    SAVE_VERIFY_ATTEMPTS = 3
    MAX_FOCUS_FAILURES = 5

    # Starts VS Code without third-party extensions (auto-close-tag,
    # Copilot...) that settings cannot switch off.
    DISABLE_EXTENSIONS = True

    # Typed and erased before every file to prove the right editor has
    # keyboard focus and that nothing auto-closes or auto-indents.
    CANARY = "<a href=\"x?a=1&b=2\">{[('`\u20ac\U0001F600\n\t;"

    # Typed and erased to prove the TEXT EDITOR (not the terminal, Quick
    # Open or another control) has keyboard focus after any interruption.
    FOCUS_PROBE = "~"

    def __init__(self, root):
        self.root = root
        self.root.title("Developer Typing Bot")
        self.root.geometry("760x700")
        self.root.minsize(680, 620)
        self.root.configure(bg="#101114")

        self.selected_files = []
        self.original_contents = {}   # typed text (BOM removed, EOLs kept)
        self.source_hashes = {}       # sha256 of original raw bytes
        self.source_had_bom = {}
        self.source_eol = {}

        self.workspace = None
        self.vscode = None
        self.vscode_hwnd = None
        self.current_filename = None
        self.current_index = 0

        self.duration = tk.IntVar(value=1)
        self.typing_speed = tk.IntVar(value=10)

        self.stop_event = threading.Event()
        self.pause_event = threading.Event()
        self.running = False
        self.keyboard_listener = None
        self.worker_thread = None

        self.next_mouse_move = None
        self.next_browser_refresh = None

        self.last_error = None
        self.preserve_evidence = False
        self.sources_changed = []

        # Worker/listener threads never touch Tk directly; they post here.
        self.ui_queue = queue.Queue()
        self.after_id = None

        pyautogui.PAUSE = 0.01
        pyautogui.FAILSAFE = True

        self.setup_logging()
        self.build_interface()
        self.after_id = self.root.after(100, self.poll_ui_queue)

        print("=" * 70)
        print("Developer Typing Bot")
        print(f"SendInput available: {_user32 is not None}")
        print("=" * 70)

    # ---------------------------------------------------------
    # Logging
    # ---------------------------------------------------------

    def setup_logging(self):
        try:
            log_dir = (
                Path(os.environ.get("LOCALAPPDATA", str(Path.home())))
                / "DeveloperTypingBot"
            )
            log_dir.mkdir(parents=True, exist_ok=True)
            log_path = log_dir / "debug.log"

            root_logger = logging.getLogger()
            root_logger.setLevel(logging.INFO)
            for handler in list(root_logger.handlers):
                root_logger.removeHandler(handler)

            fh = logging.FileHandler(str(log_path), encoding="utf-8")
            fh.setFormatter(logging.Formatter(
                "%(asctime)s | %(levelname)s | %(message)s"
            ))
            root_logger.addHandler(fh)

            ch = logging.StreamHandler(sys.stdout)
            ch.setFormatter(logging.Formatter("%(asctime)s | %(message)s"))
            root_logger.addHandler(ch)

            self.log(f"Log file: {log_path}")
            self.log("Application started.")
        except Exception as error:
            print(f"Could not initialize debug log: {error}")

    @staticmethod
    def log(message):
        try:
            logging.info("%s", message)
        except Exception:
            print(message)

    def log_exception(self, message):
        try:
            logging.error("%s\n%s", message, traceback.format_exc())
        except Exception:
            print(message)

    # ---------------------------------------------------------
    # Interface
    # ---------------------------------------------------------

    def build_interface(self):
        style = ttk.Style()
        style.theme_use("clam")
        style.configure(
            "TCombobox",
            fieldbackground="#202126",
            background="#202126",
            foreground="white"
        )

        header = tk.Frame(self.root, bg="#101114")
        header.pack(fill="x", padx=28, pady=(25, 12))

        tk.Label(
            header, text="DEVELOPER TYPING BOT",
            font=("Segoe UI", 20, "bold"),
            fg="white", bg="#101114"
        ).pack(anchor="w")

        tk.Label(
            header,
            text="Visible keyboard typing for website development",
            font=("Segoe UI", 10),
            fg="#A5A6AD", bg="#101114"
        ).pack(anchor="w", pady=(5, 0))

        content = tk.Frame(self.root, bg="#18191E")
        content.pack(fill="both", expand=True, padx=28, pady=12)

        tk.Label(
            content, text="1. Select your website files",
            font=("Segoe UI", 12, "bold"),
            fg="white", bg="#18191E"
        ).pack(anchor="w", padx=20, pady=(20, 10))

        tk.Button(
            content, text="Select Website Files",
            command=self.select_files,
            bg="#303139", fg="white",
            relief="flat", padx=14, pady=10, cursor="hand2"
        ).pack(anchor="w", padx=20, pady=10)

        self.file_label = tk.Label(
            content, text="No files selected",
            fg="#A5A6AD", bg="#18191E", justify="left",
            wraplength=620, font=("Consolas", 9)
        )
        self.file_label.pack(anchor="w", padx=20, pady=(0, 15))

        tk.Frame(content, bg="#303139", height=1).pack(
            fill="x", padx=20, pady=8
        )

        tk.Label(
            content, text="2. Configure the session",
            font=("Segoe UI", 12, "bold"),
            fg="white", bg="#18191E"
        ).pack(anchor="w", padx=20, pady=(10, 12))

        settings = tk.Frame(content, bg="#18191E")
        settings.pack(fill="x", padx=20)

        tk.Label(
            settings, text="Maximum session duration (hours)",
            fg="white", bg="#18191E"
        ).grid(row=0, column=0, sticky="w", pady=8)

        ttk.Combobox(
            settings, textvariable=self.duration,
            values=list(range(1, 13)), state="readonly", width=12
        ).grid(row=0, column=1, sticky="w", padx=20)

        tk.Label(
            settings, text="Typing speed (characters/second)",
            fg="white", bg="#18191E"
        ).grid(row=1, column=0, sticky="w", pady=8)

        ttk.Combobox(
            settings, textvariable=self.typing_speed,
            values=[1, 2, 3, 5, 8, 10, 15, 20, 30],
            state="readonly", width=12
        ).grid(row=1, column=1, sticky="w", padx=20)

        tk.Label(
            content,
            text=(
                "F8 pauses/resumes. Stop ends the run. Mouse movement: "
                "every 60 seconds for 10 seconds. Chrome refresh: every "
                "200 seconds. Original source files stay untouched. "
                "Saved files are read back and compared with the originals "
                "(byte-for-byte at the end); do not type or click while "
                "the bot runs."
            ),
            fg="#A5A6AD", bg="#18191E",
            wraplength=620, justify="left"
        ).pack(anchor="w", padx=20, pady=18)

        controls = tk.Frame(content, bg="#18191E")
        controls.pack(fill="x", padx=20, pady=(0, 12))

        self.start_button = tk.Button(
            controls, text="START BOT",
            command=self.start_bot,
            bg="#E5E5E7", fg="#101114",
            activebackground="#FFFFFF", relief="flat",
            font=("Segoe UI", 11, "bold"),
            padx=20, pady=12, cursor="hand2"
        )
        self.start_button.pack(
            side="left", fill="x", expand=True, padx=(0, 6)
        )

        self.stop_button = tk.Button(
            controls, text="STOP RUN",
            command=self.stop_bot,
            bg="#303139", fg="white",
            activebackground="#41424A", relief="flat",
            font=("Segoe UI", 10, "bold"),
            padx=16, pady=12, cursor="hand2", state="disabled"
        )
        self.stop_button.pack(side="left", padx=(6, 0))

        self.status = tk.Label(
            self.root, text="Status: Ready",
            fg="#A5A6AD", bg="#101114", anchor="w"
        )
        self.status.pack(fill="x", padx=30, pady=(0, 18))

    # ---------------------------------------------------------
    # Thread-safe UI bridge
    # ---------------------------------------------------------

    def set_status(self, text):
        self.ui_queue.put(("status", text))

    def poll_ui_queue(self):
        try:
            while True:
                item = self.ui_queue.get_nowait()
                if item[0] == "status":
                    self.status.config(text=f"Status: {item[1]}")
                elif item[0] == "finish":
                    self.finish_session(item[1], item[2])
        except queue.Empty:
            pass
        except tk.TclError:
            return
        try:
            self.after_id = self.root.after(100, self.poll_ui_queue)
        except tk.TclError:
            pass

    # ---------------------------------------------------------
    # Source file selection and loading
    # ---------------------------------------------------------

    def select_files(self):
        if self.running:
            messagebox.showinfo(
                "Session running",
                "Stop the current run before selecting files again."
            )
            return

        paths = filedialog.askopenfilenames(
            title="Select the three website files",
            filetypes=[
                ("Website files", "*.html *.css *.js"),
                ("All files", "*.*")
            ]
        )
        if not paths:
            return

        selected = [Path(path) for path in paths]
        names = {path.name.lower() for path in selected}

        if len(selected) != 3 or names != set(self.FILE_ORDER):
            messagebox.showerror(
                "Incorrect selection",
                "Select exactly these files:\n\n"
                "index.html\nstyles.css\nscript.js"
            )
            return

        parents = {str(path.parent.resolve()).lower() for path in selected}
        if len(parents) != 1:
            messagebox.showerror(
                "Different folders",
                "Select all three files from the same folder."
            )
            return

        by_name = {path.name.lower(): path for path in selected}
        self.selected_files = [by_name[name] for name in self.FILE_ORDER]

        self.file_label.config(
            text="\n".join(str(p) for p in self.selected_files),
            fg="#E5E5E7"
        )
        self.status.config(text="Status: Three files selected")
        self.log("Selected source files: " + repr(self.selected_files))

    def find_vscode(self):
        command = shutil.which("code")
        if command:
            self.log(f"Found VS Code via PATH: {command}")
            return command

        candidates = [
            Path(os.environ.get("LOCALAPPDATA", ""))
            / "Programs/Microsoft VS Code/Code.exe",
            Path("C:/Program Files/Microsoft VS Code/Code.exe"),
            Path("C:/Program Files (x86)/Microsoft VS Code/Code.exe"),
        ]
        for candidate in candidates:
            if candidate.is_file():
                self.log(f"Found VS Code at: {candidate}")
                return str(candidate)
        return None

    def load_sources(self):
        """
        Read each source as raw bytes and decode strict UTF-8. Record its
        BOM and line-ending style so the workspace can reproduce them, and
        refuse anything that cannot be typed and saved identically.
        Raises ValueError with a clear message.
        """
        contents, hashes, boms, eols = {}, {}, {}, {}
        problems = []

        for path in self.selected_files:
            name = path.name.lower()
            raw = path.read_bytes()
            hashes[name] = sha256_bytes(raw)
            try:
                text = raw.decode("utf-8")
            except UnicodeDecodeError as error:
                raise ValueError(
                    f"{path.name} is not valid UTF-8 ({error}). Convert it "
                    "to UTF-8 so it can be reproduced exactly."
                )

            boms[name] = text.startswith("\ufeff")
            if boms[name]:
                text = text[1:]

            crlf = text.count("\r\n")
            lone_lf = text.count("\n") - crlf
            lone_cr = text.count("\r") - crlf
            if lone_cr:
                problems.append(
                    f"{path.name}: contains a lone CR line ending."
                )
            if crlf and lone_lf:
                problems.append(
                    f"{path.name}: mixed LF and CRLF line endings "
                    "(VS Code cannot reproduce that exactly)."
                )
            eols[name] = "\r\n" if crlf else "\n"

            line, col = 1, 1
            for ch in text:
                if ch == "\n":
                    line, col = line + 1, 1
                    continue
                if ch == "\r":
                    continue
                if ch != "\t" and unicodedata.category(ch) in ("Cc", "Cs"):
                    problems.append(
                        f"{path.name}: control character U+{ord(ch):04X} "
                        f"at line {line}, column {col}"
                    )
                    if len(problems) >= 8:
                        break
                col += 1
            contents[name] = text

        if problems:
            raise ValueError(
                "These files cannot be reproduced exactly:\n\n"
                + "\n".join(problems[:8])
                + "\n\nFix the source files (UTF-8, consistent LF or CRLF, "
                "no control characters) and try again."
            )

        self.original_contents = contents
        self.source_hashes = hashes
        self.source_had_bom = boms
        self.source_eol = eols
        for name, text in contents.items():
            self.log(
                f"Loaded {name}: {len(text)} chars, "
                f"eol={'CRLF' if eols[name] == chr(13) + chr(10) else 'LF'}, "
                f"bom={boms[name]}, sha256(original bytes)={hashes[name]}"
            )

    def expected_text(self, filename, index=None):
        """Exact decoded text the saved file must contain once the first
        `index` characters of the source have been typed (whole file if
        index is None). Includes the BOM character for BOM files."""
        text = self.original_contents[filename]
        if index is not None:
            text = text[:index]
        bom = "\ufeff" if self.source_had_bom.get(filename) else ""
        return bom + text

    def check_sources_unmodified(self):
        changed = []
        for path in self.selected_files:
            try:
                now = sha256_bytes(path.read_bytes())
            except OSError:
                now = None
            if now != self.source_hashes.get(path.name.lower()):
                changed.append(path.name)
        return changed

    # ---------------------------------------------------------
    # Workspace settings (workspace only; global settings untouched)
    # ---------------------------------------------------------

    def configure_workspace(self, workspace):
        settings_dir = workspace / ".vscode"
        settings_dir.mkdir(parents=True, exist_ok=True)

        settings = {
            "editor.autoClosingBrackets": "never",
            "editor.autoClosingQuotes": "never",
            "editor.autoClosingComments": "never",
            "editor.autoClosingDelete": "never",
            "editor.autoClosingOvertype": "never",
            "editor.autoSurround": "never",
            "editor.autoIndent": "none",
            "editor.formatOnType": False,
            "editor.formatOnPaste": False,
            "editor.formatOnSave": False,
            "editor.acceptSuggestionOnCommitCharacter": False,
            "editor.acceptSuggestionOnEnter": "off",
            "editor.tabCompletion": "off",
            "editor.quickSuggestions": {
                "other": "off", "comments": "off", "strings": "off"
            },
            "editor.suggestOnTriggerCharacters": False,
            "editor.inlineSuggest.enabled": False,
            "editor.wordBasedSuggestions": "off",
            "editor.parameterHints.enabled": False,
            "editor.snippetSuggestions": "none",
            "editor.linkedEditing": False,
            "editor.unusualLineTerminators": "off",
            "editor.insertSpaces": False,
            "editor.detectIndentation": False,
            "editor.tabSize": 4,
            "editor.useTabStops": False,
            "editor.trimAutoWhitespace": False,
            "emmet.triggerExpansionOnTab": False,
            "emmet.showExpandedAbbreviation": "never",
            "html.autoClosingTags": False,
            "html.autoCreateQuotes": False,
            "javascript.autoClosingTags": False,
            "typescript.autoClosingTags": False,
            "files.autoSave": "off",
            "files.eol": "\n",
            "files.encoding": "utf8",
            "files.autoGuessEncoding": False,
            "files.insertFinalNewline": False,
            "files.trimFinalNewlines": False,
            "files.trimTrailingWhitespace": False,
            "workbench.startupEditor": "none",
            "workbench.editor.enablePreview": False,
            "workbench.editor.enablePreviewFromQuickOpen": False,
            "window.title": TITLE_TEMPLATE,
        }

        # Language-specific blocks: a user-level "[html]" override cannot
        # win over these, and each file gets ITS OWN line ending / BOM.
        language_block = {
            key: value for key, value in settings.items()
            if key.startswith("editor.")
        }
        for name, language in self.LANGUAGE_BLOCK.items():
            block = dict(language_block)
            block["files.eol"] = self.source_eol[name]
            block["files.encoding"] = (
                "utf8bom" if self.source_had_bom[name] else "utf8"
            )
            settings[language] = block

        (settings_dir / "settings.json").write_text(
            json.dumps(settings, indent=2), encoding="utf-8"
        )
        self.log(f"Configured workspace settings: {workspace}")

    # ---------------------------------------------------------
    # Start / stop
    # ---------------------------------------------------------

    def start_bot(self):
        if self.running:
            return
        if not IS_WINDOWS:
            messagebox.showerror(
                "Windows only",
                "This bot uses Windows SendInput and can only run on Windows."
            )
            return
        if len(self.selected_files) != 3:
            messagebox.showwarning(
                "Files required",
                "Select index.html, styles.css and script.js first."
            )
            return

        vscode = self.find_vscode()
        if not vscode:
            messagebox.showerror(
                "VS Code not found", "Could not locate VS Code."
            )
            return

        try:
            self.load_sources()
        except (ValueError, OSError) as error:
            self.log(f"Source validation failed: {error}")
            messagebox.showerror("Cannot use source files", str(error))
            return

        try:
            self.last_error = None
            self.preserve_evidence = False
            self.sources_changed = []
            self.vscode_hwnd = None
            self.current_filename = None
            self.current_index = 0

            source_folder = self.selected_files[0].parent
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            self.workspace = (
                source_folder / f"BusinessWebsite_{timestamp}"
            )
            self.workspace.mkdir(exist_ok=False)

            for name in self.FILE_ORDER:
                (self.workspace / name).touch(exist_ok=False)

            self.configure_workspace(self.workspace)
            time.sleep(0.3)

            self.vscode = vscode
            self.stop_event.clear()
            self.pause_event.clear()
            self.running = True

            self.start_button.config(state="disabled")
            self.stop_button.config(state="normal")
            self.status.config(text="Status: Opening workspace...")
            self.log(f"Workspace: {self.workspace}")

            command = [self.vscode, "-n", "--disable-workspace-trust"]
            if self.DISABLE_EXTENSIONS:
                command.append("--disable-extensions")
            command.append(str(self.workspace))

            try:
                creationflags = 0x00000008 if sys.platform == "win32" else 0
                subprocess.Popen(
                    command,
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                    creationflags=creationflags,
                )
                self.log(f"VS Code launch command sent: {command}")
            except Exception as launch_error:
                self.log_exception("Failed to launch VS Code.")
                raise RuntimeError(
                    f"Failed to launch VS Code: {launch_error}"
                )

            self.keyboard_listener = keyboard.Listener(
                on_press=self.on_key_press
            )
            self.keyboard_listener.start()

            self.worker_thread = threading.Thread(
                target=self.typing_worker, daemon=True
            )
            self.worker_thread.start()

        except Exception as error:
            self.log_exception("Could not start bot.")
            self.running = False
            self.start_button.config(state="normal")
            self.stop_button.config(state="disabled")
            messagebox.showerror("Could not start bot", str(error))

    def on_key_press(self, key):
        if key == keyboard.Key.f8 and self.running:
            if self.pause_event.is_set():
                self.pause_event.clear()
                self.set_status("Resuming typing (re-verifying editor)...")
                self.log("Typing resumed with F8.")
            else:
                self.pause_event.set()
                self.set_status("Paused - press F8 to resume")
                self.log("Typing paused with F8.")
        return None

    def stop_bot(self):
        if not self.running:
            return
        self.stop_event.set()
        self.pause_event.clear()
        self.log("Stop requested.")
        self.set_status("Stopping...")
        self.stop_button.config(state="disabled")

    def wait_if_paused(self, deadline):
        pause_started = None
        while self.pause_event.is_set() and not self.stop_event.is_set():
            if pause_started is None:
                pause_started = time.monotonic()
            if time.monotonic() >= deadline:
                self.stop_event.set()
                break
            time.sleep(0.1)
        return (
            time.monotonic() - pause_started
            if pause_started is not None else 0.0
        )

    # ---------------------------------------------------------
    # Window helpers (identity by HWND + title, never by title alone)
    # ---------------------------------------------------------

    def _list_all_windows(self):
        try:
            return pygetwindow.getAllWindows()
        except Exception as error:
            self.log(f"Could not enumerate windows: {error}")
            return []

    def find_workspace_window(self):
        """Strict match on OUR workspace folder name. No guessing."""
        if not self.workspace:
            return None
        wanted = self.workspace.name.lower()
        for window in self._list_all_windows():
            info = parse_title(window.title)
            if info and info["root"].lower() == wanted:
                return window
        return None

    def foreground_hwnd(self):
        return _user32.GetForegroundWindow() if _user32 else None

    def fast_focus_ok(self, filename):
        """
        Cheap per-character guard: our VS Code window is the foreground
        window and its title shows `filename` as the active editor.
        This does NOT prove the text editor has keyboard focus; that is
        proven by prove_editor_focus() and by the checkpoints.
        """
        hwnd = self.vscode_hwnd
        if not hwnd or _user32 is None:
            return False
        if self.foreground_hwnd() != hwnd:
            return False
        info = parse_title(get_window_title(hwnd))
        if info is None or self.workspace is None:
            return False
        return (
            info["root"].lower() == self.workspace.name.lower()
            and info["file"].lower() == filename.lower()
        )

    def force_foreground(self, hwnd):
        """Bring a window forward WITHOUT tapping Alt (an Alt tap focuses
        VS Code's menu bar, so typed letters would trigger menu keys)."""
        try:
            if _user32.IsIconic(hwnd):
                _user32.ShowWindow(hwnd, SW_RESTORE)
                time.sleep(0.2)
            if self.foreground_hwnd() == hwnd:
                return True

            current = _kernel32.GetCurrentThreadId()
            fg = self.foreground_hwnd()
            fg_thread = (
                _user32.GetWindowThreadProcessId(fg, None) if fg else 0
            )
            attached = False
            if fg_thread and fg_thread != current:
                attached = bool(
                    _user32.AttachThreadInput(current, fg_thread, True)
                )
            try:
                _user32.BringWindowToTop(hwnd)
                _user32.SetForegroundWindow(hwnd)
            finally:
                if attached:
                    _user32.AttachThreadInput(current, fg_thread, False)

            time.sleep(0.3)
            return self.foreground_hwnd() == hwnd
        except Exception as error:
            self.log(f"force_foreground failed: {error}")
            return False

    def activate_vscode(self):
        hwnd = self.vscode_hwnd
        if not hwnd or not _user32.IsWindow(hwnd):
            window = self.find_workspace_window()
            if window is None:
                return False
            hwnd = getattr(window, "_hWnd", None)
            if not hwnd:
                return False
            self.vscode_hwnd = hwnd

        for attempt in range(3):
            if self.force_foreground(hwnd):
                return True
            self.log(
                f"Activation attempt {attempt + 1}/3 failed; foreground "
                f"title={get_window_title(self.foreground_hwnd())!r}"
            )
            time.sleep(0.15)
        return False

    def ensure_editor_ready(self, filename, max_attempts=3):
        for _ in range(max_attempts):
            if self.fast_focus_ok(filename):
                return True
            if self.stop_event.is_set():
                return False
            if self.activate_vscode() and self.fast_focus_ok(filename):
                return True
            time.sleep(0.15)
        return False

    def modifiers_down(self):
        if _user32 is None:
            return False
        for vk in (VK_SHIFT, VK_CONTROL, VK_MENU, VK_LWIN, VK_RWIN):
            if _user32.GetAsyncKeyState(vk) & 0x8000:
                return True
        return False

    def wait_modifiers_released(self):
        """Literal characters must never be sent while Ctrl/Alt/Win is held
        (that would turn them into shortcuts)."""
        warned = False
        while self.modifiers_down() and not self.stop_event.is_set():
            if not warned:
                self.set_status("Waiting for modifier keys to be released")
                warned = True
            time.sleep(0.05)

    # ---------------------------------------------------------
    # Disk verification
    # ---------------------------------------------------------

    def read_disk(self, filename):
        """Raw read, strict UTF-8, no newline normalisation, BOM kept."""
        try:
            data = (self.workspace / filename).read_bytes()
            return data.decode("utf-8")
        except (OSError, UnicodeDecodeError) as error:
            self.log(f"read_disk({filename}) failed: {error}")
            return None

    def wait_for_disk(self, filename, expected, timeout):
        """
        Poll the file until it equals `expected`. Returns (state, actual):
        'equal', 'behind' (still a prefix after the timeout), 'diverged',
        or 'unreadable'. 'diverged' must persist across two reads so a
        half-written file is not misreported.
        """
        # A BOM-only expectation also accepts a truly empty file, because
        # an empty file may be written with or without the BOM.
        accept_empty = expected == "\ufeff"
        end = time.monotonic() + timeout
        diverged_reads = 0
        state, actual = "unreadable", None
        while True:
            actual = self.read_disk(filename)
            if actual is None:
                state = "unreadable"
                diverged_reads = 0
            elif accept_empty and actual == "":
                return "equal", actual
            else:
                state = classify(actual, expected)
                if state == "equal":
                    return state, actual
                if state == "diverged":
                    diverged_reads += 1
                    if diverged_reads >= 2:
                        return state, actual
                else:
                    diverged_reads = 0
            if time.monotonic() >= end:
                return state, actual
            time.sleep(0.05)

    def report_mismatch(self, filename, expected, actual, state):
        if actual is None:
            message = (
                f"{filename}: verification FAILED - file could not be read "
                "back as UTF-8."
            )
            self.log(message)
        else:
            index = first_difference(expected, actual)
            lo = max(0, index - 30)
            message = (
                f"{filename}: verification FAILED ({state}) at character "
                f"index {index}. expected_len={len(expected)}, "
                f"actual_len={len(actual)}."
            )
            self.log(message)
            self.log(f"  expected[{lo}:{index + 40}] = "
                     f"{expected[lo:index + 40]!r}")
            self.log(f"  actual  [{lo}:{index + 40}] = "
                     f"{actual[lo:index + 40]!r}")
            self.log(f"  sha256 expected={sha256_text(expected)}")
            self.log(f"  sha256 actual  ={sha256_text(actual)}")
            message += (
                f" Expected {expected[lo:index + 40]!r} but found "
                f"{actual[lo:index + 40]!r}."
            )
        self.preserve_evidence = True
        self.last_error = message
        return message

    def save_active_file(self, filename):
        if not self.ensure_editor_ready(filename):
            self.log(f"Save aborted: {filename} not verified as active.")
            return False
        send_chord(VK_CONTROL, VK_S)
        time.sleep(0.15)
        return True

    def save_and_verify(self, filename, expected, timeout=None):
        """
        Save and require the disk to equal `expected`. A save that is merely
        slow ('behind'/'unreadable') is retried; content that differs
        ('diverged') fails immediately without further typing.
        """
        timeout = timeout or self.SAVE_VERIFY_TIMEOUT
        state, actual = "unreadable", None
        for attempt in range(1, self.SAVE_VERIFY_ATTEMPTS + 1):
            if not self.save_active_file(filename):
                raise RuntimeError(
                    f"Could not save {filename}: the editor for this file "
                    "is not the verified, focused window."
                )
            state, actual = self.wait_for_disk(filename, expected, timeout)
            if state == "equal":
                return
            if state == "diverged":
                break
            self.log(
                f"{filename}: save not yet reflected on disk ({state}); "
                f"retry {attempt}/{self.SAVE_VERIFY_ATTEMPTS}."
            )
        raise VerificationError(
            self.report_mismatch(filename, expected, actual, state)
        )

    # ---------------------------------------------------------
    # Opening a file and proving the editor is ready
    # ---------------------------------------------------------

    def place_cursor_at_end(self, filename):
        if not self.ensure_editor_ready(filename):
            return False
        send_chord(VK_CONTROL, VK_1)       # focus first editor group
        time.sleep(0.2)
        send_chord(VK_CONTROL, VK_END)     # caret to end of document
        time.sleep(0.2)
        return self.fast_focus_ok(filename)

    def _wait_for_editor(self, filename, seconds):
        end = time.monotonic() + seconds
        while time.monotonic() < end:
            if self.stop_event.is_set():
                return False
            if self.fast_focus_ok(filename):
                return True
            time.sleep(0.2)
        return False

    def _quick_open(self, filename):
        info = parse_title(get_window_title(self.vscode_hwnd))
        if info and info["dirty"]:
            time.sleep(1.0)
            info = parse_title(get_window_title(self.vscode_hwnd))
            if info and info["dirty"]:
                raise RuntimeError(
                    "The active editor has unsaved changes; refusing to "
                    "use Quick Open because it could type into that file."
                )

        send_chord(VK_CONTROL, VK_P)
        time.sleep(0.6)
        for ch in filename:
            send_unicode_char(ch)
            time.sleep(0.03)
        time.sleep(0.9)
        send_vk(VK_RETURN)

        if self._wait_for_editor(filename, 5.0):
            return True

        info = parse_title(get_window_title(self.vscode_hwnd))
        if info and info["dirty"]:
            raise RuntimeError(
                f"Quick Open did not open {filename} and the active editor "
                f"({info['file']!r}) now has unsaved text. Stopping to "
                "protect your content; check the workspace."
            )
        return False

    def _cli_open(self, filename):
        try:
            subprocess.Popen(
                [self.vscode, "--reuse-window",
                 str(self.workspace / filename)],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                creationflags=0x00000008 if sys.platform == "win32" else 0,
            )
        except Exception as error:
            self.log(f"CLI open failed: {error}")
            return False
        return self._wait_for_editor(filename, 8.0)

    def open_target(self, filename):
        for attempt in range(1, 4):
            if self.stop_event.is_set():
                return
            if not self.activate_vscode():
                self.log(f"open_target: cannot activate window "
                         f"(attempt {attempt}/3)")
                time.sleep(0.5)
                continue

            if self.fast_focus_ok(filename):
                opened = True
            elif attempt == 2:
                self.log(f"Opening {filename} via CLI (attempt 2/3).")
                opened = self._cli_open(filename)
            else:
                self.log(f"Opening {filename} via Quick Open "
                         f"(attempt {attempt}/3).")
                opened = self._quick_open(filename)

            if not opened:
                self.log(f"{filename} did not become the active editor.")
                continue

            if self.place_cursor_at_end(filename):
                self.log(f"Opened and focused by title: {filename}")
                return
            self.log("Editor focus could not be confirmed after opening.")

        raise RuntimeError(
            f"Could not open {filename} in the correct VS Code workspace "
            "window after 3 attempts."
        )

    def type_char(self, character):
        if character == "\n":
            send_vk(VK_RETURN)
        elif character == "\t":
            send_vk(VK_TAB)
        else:
            send_unicode_char(character)

    def canary_test(self, filename):
        """
        Before the first real character: type a punctuation/Unicode canary,
        save, read it back and require an EXACT match (using this file's
        own line ending and BOM), then erase it and require an empty file.
        """
        bom = "\ufeff" if self.source_had_bom[filename] else ""
        canary_on_disk = bom + self.CANARY.replace(
            "\n", self.source_eol[filename]
        )
        empty = self.expected_text(filename, 0)

        state, actual = self.wait_for_disk(filename, empty, 1.0)
        if state != "equal":
            raise VerificationError(self.report_mismatch(
                filename, empty, actual, state
            ))

        if not self.place_cursor_at_end(filename):
            raise RuntimeError(f"Editor for {filename} is not ready.")

        self.set_status(f"Pre-flight check for {filename}...")
        self.log(f"Canary test start: {filename}")
        for ch in self.CANARY:
            if self.stop_event.is_set():
                return
            if not self.fast_focus_ok(filename):
                raise RuntimeError("Lost editor focus during pre-flight.")
            self.wait_modifiers_released()
            self.type_char(ch)
            time.sleep(0.05)

        self.save_and_verify(filename, canary_on_disk, timeout=8.0)
        self.log("Canary typed and verified exactly on disk.")

        for _ in range(len(self.CANARY)):
            if not self.fast_focus_ok(filename):
                raise RuntimeError("Lost editor focus during pre-flight.")
            send_vk(VK_BACK)
            time.sleep(0.05)

        self.save_active_file(filename)
        state, actual = self.wait_for_disk(filename, empty, 3.0)
        if state != "equal":
            # The file held ONLY the canary, so select-all + delete is safe.
            self.log("Canary erase left residue; trying Ctrl+A, Backspace.")
            send_chord(VK_CONTROL, VK_A)
            time.sleep(0.1)
            send_vk(VK_BACK)
            time.sleep(0.2)
            self.save_active_file(filename)
            state, actual = self.wait_for_disk(filename, empty, 3.0)
            if state != "equal":
                raise VerificationError(self.report_mismatch(
                    filename, empty, actual, state
                ))
        self.log("Canary erased; file is empty and verified.")

        if not self.place_cursor_at_end(filename):
            raise RuntimeError(f"Editor for {filename} lost focus.")

    def prove_editor_focus(self, filename, index):
        """
        Proves the TEXT EDITOR itself has keyboard focus (a matching window
        title is not enough: the terminal, Quick Open or a sidebar could
        hold focus). Types one probe character, requires it to appear on
        disk after a save, erases it and requires the original content
        back. If the probe went anywhere else, disk never changes and the
        run stops before any real character is typed.
        """
        self.wait_modifiers_released()
        base = self.expected_text(filename, index)
        self.type_char(self.FOCUS_PROBE)
        time.sleep(0.05)
        self.save_and_verify(filename, base + self.FOCUS_PROBE)
        send_vk(VK_BACK)
        time.sleep(0.05)
        self.save_and_verify(filename, base)

    def resync(self, filename, index):
        """
        Re-establish and PROVE editor state after any interruption (pause,
        Chrome refresh, mouse movement, focus loss): window + title ok,
        editor focused, saved content == source[:index], caret at the end,
        and the text editor demonstrably receives keystrokes.
        """
        if not self.ensure_editor_ready(filename):
            raise RuntimeError(
                f"Cannot confirm {filename} is the active editor in the "
                "workspace window."
            )
        send_chord(VK_CONTROL, VK_1)
        time.sleep(0.2)
        self.save_and_verify(filename, self.expected_text(filename, index))
        send_chord(VK_CONTROL, VK_END)
        time.sleep(0.2)
        if not self.fast_focus_ok(filename):
            raise RuntimeError("Editor focus not confirmed after resync.")
        self.prove_editor_focus(filename, index)
        self.log(f"Resynced {filename} at verified index {index}.")

    # ---------------------------------------------------------
    # Mouse movement
    # ---------------------------------------------------------

    def move_mouse_for_ten_seconds(self):
        original_x, original_y = pyautogui.position()
        end = time.monotonic() + self.CURSOR_MOVE_DURATION

        self.set_status("Mouse movement break (10 seconds)...")

        window = self.find_workspace_window()
        if window is not None:
            left = max(5, int(window.left) + 20)
            top = max(5, int(window.top) + 70)
            right = max(left + 1, int(window.left + window.width) - 20)
            bottom = max(top + 1, int(window.top + window.height) - 20)
        else:
            sw, sh = pyautogui.size()
            left, top = 35, 35
            right = max(left + 1, sw - 35)
            bottom = max(top + 1, sh - 35)

        try:
            while (
                time.monotonic() < end
                and not self.stop_event.is_set()
            ):
                if self.pause_event.is_set():
                    paused_for = self.wait_if_paused(
                        time.monotonic() + 3600
                    )
                    end += paused_for
                    if self.stop_event.is_set():
                        break

                remaining = end - time.monotonic()
                if remaining <= 0:
                    break

                pyautogui.moveTo(
                    random.randint(left, right),
                    random.randint(top, bottom),
                    duration=min(random.uniform(0.35, 0.8), remaining),
                    tween=pyautogui.easeInOutQuad
                )

            if not self.stop_event.is_set():
                pyautogui.moveTo(original_x, original_y, duration=0.3)
        except pyautogui.FailSafeException:
            self.log("Mouse failsafe triggered.")
            self.stop_event.set()

    # ---------------------------------------------------------
    # Chrome refresh
    # ---------------------------------------------------------

    def refresh_existing_chrome(self, filename, index):
        if self.stop_event.is_set():
            return False

        # Save and PROVE the saved content before leaving VS Code.
        self.save_and_verify(filename, self.expected_text(filename, index))
        self.set_status("Saved and verified; switching to Chrome...")

        try:
            chrome = None
            for window in self._list_all_windows():
                title = (window.title or "")
                if "google chrome" in title.lower() and "TBOT::" not in title:
                    chrome = window
                    break

            if chrome is None:
                self.set_status(
                    "Chrome window not found; typing will continue."
                )
                self.log("Chrome window not found; refresh skipped.")
                return True

            chrome_hwnd = getattr(chrome, "_hWnd", None)
            if not chrome_hwnd or not self.force_foreground(chrome_hwnd):
                self.log("Chrome did not come to foreground; skipped.")
                return True

            if self.stop_event.is_set():
                return False
            if self.foreground_hwnd() != chrome_hwnd:
                self.log("Chrome lost foreground before F5; skipped.")
                return True

            send_vk(VK_F5)
            self.set_status("Chrome refreshed; waiting 10 seconds...")

            wait_until = time.monotonic() + self.BROWSER_REFRESH_WAIT
            while time.monotonic() < wait_until:
                if self.stop_event.wait(0.1):
                    return False
                if self.pause_event.is_set():
                    paused_for = self.wait_if_paused(
                        time.monotonic() + 3600
                    )
                    wait_until += paused_for
                    if self.stop_event.is_set():
                        return False

            if not self.activate_vscode():
                self.last_error = (
                    "Could not return to VS Code after the Chrome refresh."
                )
                self.stop_event.set()
                return False

            self.move_mouse_for_ten_seconds()
            if self.stop_event.is_set():
                return False

            self.resync(filename, index)
            self.set_status("Back in VS Code; typing resumed.")
            self.log("Chrome refresh cycle completed.")
            return True

        except (VerificationError, RuntimeError):
            raise
        except Exception as error:
            self.log_exception("Browser refresh failed.")
            self.set_status(f"Browser refresh failed: {error}")
            self.last_error = f"Browser refresh failed: {error}"
            self.stop_event.set()
            return False

    # ---------------------------------------------------------
    # Periodic tasks
    # ---------------------------------------------------------

    def handle_periodic_tasks(self, filename, index):
        now = time.monotonic()

        if (
            self.next_browser_refresh is not None
            and now >= self.next_browser_refresh
        ):
            if not self.refresh_existing_chrome(filename, index):
                return False
            current = time.monotonic()
            self.next_browser_refresh = (
                current + self.BROWSER_REFRESH_INTERVAL
            )
            self.next_mouse_move = current + self.CURSOR_MOVE_INTERVAL
            return True

        if (
            self.next_mouse_move is not None
            and now >= self.next_mouse_move
        ):
            self.save_and_verify(
                filename, self.expected_text(filename, index)
            )
            self.move_mouse_for_ten_seconds()
            if self.stop_event.is_set():
                return False

            self.resync(filename, index)
            self.next_mouse_move = (
                time.monotonic() + self.CURSOR_MOVE_INTERVAL
            )
            self.set_status(f"Typing {filename}...")

        return True

    # ---------------------------------------------------------
    # Character-by-character typing
    # ---------------------------------------------------------

    def type_source(self, filename, deadline):
        source = self.original_contents[filename]
        speed = max(1, int(self.typing_speed.get()))
        interval = 1.0 / speed
        index = self.current_index
        last_checkpoint = index
        next_log = index + 500

        self.log(
            f"type_source START: file={filename}, index={index}, "
            f"source_length={len(source)}, speed={speed} char/s"
        )

        focus_failures = 0

        while index < len(source):
            if self.stop_event.is_set():
                break

            if time.monotonic() >= deadline:
                self.set_status("Duration limit reached")
                self.stop_event.set()
                break

            paused_for = self.wait_if_paused(deadline)
            if paused_for > 0:
                if self.next_mouse_move is not None:
                    self.next_mouse_move += paused_for
                if self.next_browser_refresh is not None:
                    self.next_browser_refresh += paused_for
                if self.stop_event.is_set():
                    break
                self.set_status("Re-verifying editor after pause...")
                self.resync(filename, index)
                last_checkpoint = index
                self.set_status(f"Typing {filename}...")

            if self.stop_event.is_set():
                break

            if not self.handle_periodic_tasks(filename, index):
                break

            pyautogui.failSafeCheck()
            self.wait_modifiers_released()
            if self.stop_event.is_set():
                break

            # Checked before EVERY character: foreground HWND + title.
            if not self.fast_focus_ok(filename):
                self.log(
                    f"Focus check failed at index {index}; foreground="
                    f"{get_window_title(self.foreground_hwnd())!r}"
                )
                if self.ensure_editor_ready(filename):
                    self.resync(filename, index)
                    last_checkpoint = index
                    focus_failures = 0
                    continue
                focus_failures += 1
                self.log(
                    f"Focus could not be restored "
                    f"({focus_failures}/{self.MAX_FOCUS_FAILURES})."
                )
                if focus_failures >= self.MAX_FOCUS_FAILURES:
                    raise RuntimeError(
                        "Lost focus to the workspace VS Code editor and "
                        "could not restore it. Nothing further was typed."
                    )
                time.sleep(0.3)
                continue
            focus_failures = 0

            char = source[index]

            # Never send Enter unless everything typed so far has been
            # proven (by disk read-back) to be in the editor. This keeps an
            # Enter from ever landing in a terminal or other control.
            if char in "\r\n" and index > last_checkpoint:
                self.save_and_verify(
                    filename, self.expected_text(filename, index)
                )
                last_checkpoint = index
                continue

            # CRLF sources: one Enter produces the CRLF (files.eol is CRLF
            # for that language), so the pair is consumed as one key.
            step = 2 if char == "\r" else 1
            self.type_char("\n" if char == "\r" else char)

            index += step
            self.current_index = index

            if (
                index - last_checkpoint >= self.SAVE_EVERY_CHARACTERS
                and index < len(source)
            ):
                self.save_and_verify(
                    filename, self.expected_text(filename, index)
                )
                last_checkpoint = index

            if index >= next_log:
                self.log(f"  progress: {filename} -> {index}/{len(source)}")
                next_log = index + 500

            if self.stop_event.wait(interval):
                break

        self.log(
            f"type_source END: file={filename}, index={index}, "
            f"stop_event={self.stop_event.is_set()}"
        )
        return index == len(source) and not self.stop_event.is_set()

    def finalize_file(self, filename):
        self.save_and_verify(
            filename, self.expected_text(filename), timeout=10.0
        )
        self.log(
            f"Text verified for {filename} "
            f"({len(self.original_contents[filename])} chars)."
        )

    def verify_all_files(self):
        """Final gate: each saved file must be byte-identical to its
        original (SHA-256 of the saved bytes == SHA-256 of the original)."""
        failures = []
        for name in self.FILE_ORDER:
            expected = self.expected_text(name)
            state, actual = self.wait_for_disk(name, expected, 3.0)
            if state != "equal":
                failures.append(
                    self.report_mismatch(name, expected, actual, state)
                )
                continue

            saved_hash = sha256_bytes((self.workspace / name).read_bytes())
            if saved_hash != self.source_hashes[name]:
                message = (
                    f"{name}: decoded text matches but the saved BYTES "
                    f"differ from the original (saved sha256={saved_hash}, "
                    f"original sha256={self.source_hashes[name]})."
                )
                self.log(message)
                self.preserve_evidence = True
                self.last_error = message
                failures.append(message)
            else:
                self.log(
                    f"BYTE-IDENTICAL: {name} sha256={saved_hash}"
                )
        if failures:
            raise VerificationError(" | ".join(failures))

    def checkpoint_on_stop(self):
        """After a user stop / time limit: save if (and only if) the
        verified editor is in front, and record what is verifiably on disk."""
        name = self.current_filename
        if not name or self.preserve_evidence:
            return
        try:
            if not self.fast_focus_ok(name):
                self.log("Stop checkpoint skipped: editor not in front. "
                         "Disk content for the current file is unverified.")
                return
            send_chord(VK_CONTROL, VK_S)
            time.sleep(0.4)
            actual = self.read_disk(name)
            expected = self.expected_text(name, self.current_index)
            if actual is None:
                self.log("Stop checkpoint: file unreadable.")
            elif actual == expected:
                self.log(f"Stop checkpoint: {name} verified up to index "
                         f"{self.current_index}.")
            else:
                self.report_mismatch(name, expected, actual,
                                     classify(actual, expected))
        except Exception as error:
            self.log(f"Stop checkpoint failed: {error}")

    # ---------------------------------------------------------
    # Main worker
    # ---------------------------------------------------------

    def typing_worker(self):
        deadline = time.monotonic() + self.duration.get() * 3600

        self.next_mouse_move = time.monotonic() + self.CURSOR_MOVE_INTERVAL
        self.next_browser_refresh = (
            time.monotonic() + self.BROWSER_REFRESH_INTERVAL
        )

        completed = False
        error_to_show = None

        try:
            self.log("Worker started. Waiting for VS Code to appear...")

            found = False
            for attempt in range(60):
                if self.stop_event.is_set():
                    break
                if self.activate_vscode():
                    found = True
                    self.log(
                        f"Workspace window found after {attempt * 0.5:.1f}s"
                    )
                    break
                time.sleep(0.5)

            if not found and not self.stop_event.is_set():
                raise RuntimeError(
                    "Could not find the workspace VS Code window "
                    "after 30 seconds."
                )

            time.sleep(1.5)

            for name in self.FILE_ORDER:
                if self.stop_event.is_set():
                    break

                self.current_filename = name
                self.current_index = 0

                self.set_status(f"Opening {name}...")
                self.open_target(name)
                if self.stop_event.is_set():
                    break

                self.canary_test(name)
                if self.stop_event.is_set():
                    break

                self.current_index = 0
                self.set_status(f"Typing {name}...")
                self.log(
                    f"Typing started: {name}, "
                    f"source_length={len(self.original_contents[name])}"
                )

                if not self.type_source(name, deadline):
                    break

                self.finalize_file(name)
                self.set_status(f"{name} finished and verified.")
                time.sleep(0.4)

            if not self.stop_event.is_set():
                self.set_status("Final byte-for-byte verification...")
                self.verify_all_files()
                completed = True
                self.log("All three files typed and verified byte-identical.")

        except pyautogui.FailSafeException:
            self.stop_event.set()
            self.set_status("Stopped by mouse failsafe.")
            self.log("Mouse failsafe stopped the session.")

        except VerificationError as error:
            self.stop_event.set()
            error_to_show = (
                "VERIFICATION FAILED - the saved file does not match the "
                "source. The workspace was preserved for investigation.\n\n"
                f"{error}"
            )
            self.last_error = error_to_show
            self.log_exception("Verification failed; typing stopped.")
            self.set_status("Stopped: verification failed")

        except Exception as error:
            self.stop_event.set()
            error_to_show = str(error)
            self.last_error = error_to_show
            self.log_exception("Typing worker stopped.")
            self.set_status(f"Stopped safely: {error}")

        finally:
            if error_to_show is None and self.last_error:
                error_to_show = self.last_error

            if not completed:
                self.checkpoint_on_stop()

            try:
                self.sources_changed = self.check_sources_unmodified()
                if self.sources_changed:
                    self.log(
                        "WARNING: source files changed during the run: "
                        f"{self.sources_changed}"
                    )
                else:
                    self.log("Original source files unmodified (hash match).")
            except Exception as error:
                self.log(f"Source hash check failed: {error}")

            self.running = False
            self.ui_queue.put(("finish", completed, error_to_show))

    # ---------------------------------------------------------
    # Finish / close  (runs on the Tk main thread via the queue)
    # ---------------------------------------------------------

    def finish_session(self, completed, error_to_show=None):
        self.start_button.config(state="normal")
        self.stop_button.config(state="disabled")

        if (
            self.keyboard_listener
            and self.keyboard_listener.is_alive()
        ):
            self.keyboard_listener.stop()

        if error_to_show:
            self.status.config(
                text="Status: Stopped - check the error message"
            )
            messagebox.showerror("Typing stopped", error_to_show)
        elif completed:
            note = ""
            if self.sources_changed:
                note = (
                    "\n\nWARNING: these source files changed while the bot "
                    "ran: " + ", ".join(self.sources_changed)
                )
            self.status.config(
                text="Status: All three files typed and verified"
            )
            messagebox.showinfo(
                "Typing finished",
                "All three saved files are byte-for-byte identical to the "
                "originals (SHA-256 compared, including line endings and "
                "BOM).\n\n"
                f"Workspace:\n{self.workspace}\n\n"
                "Hash values are in the log file." + note
            )
        elif self.stop_event.is_set():
            self.status.config(text="Status: Stopped (not complete)")
        else:
            self.status.config(text="Status: Session ended")

    def close(self):
        self.stop_event.set()
        self.pause_event.clear()
        if (
            self.keyboard_listener
            and self.keyboard_listener.is_alive()
        ):
            self.keyboard_listener.stop()
        if self.after_id is not None:
            try:
                self.root.after_cancel(self.after_id)
            except tk.TclError:
                pass
        self.root.destroy()


if __name__ == "__main__":
    root = tk.Tk()
    app = DeveloperTypingBot(root)
    root.protocol("WM_DELETE_WINDOW", app.close)
    root.mainloop()