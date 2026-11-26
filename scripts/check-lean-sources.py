#!/usr/bin/env python3
"""Check Palomar Lean source requirements (module headers, UTF-8, 10,000-line cap)."""
import os
import re
from pathlib import Path

COMMENT_MARKER = re.compile(r"/-|-/")
ID_LETTER_LIKE = (
    r"\u03b1-\u03ba\u03bc-\u03c9\u0391-\u039f\u03a1-\u03a2\u03a4-\u03a9"
    r"\u03ca-\u03fb\u1f00-\u1ffe\u2100-\u214f\U0001d49c-\U0001d59f"
    r"\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u017f"
)
ID_FIRST = rf"A-Za-z_{ID_LETTER_LIKE}"
ID_REST = rf"{ID_FIRST}0-9'!?\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a\u2c7c"
IDENTIFIER_CONTINUATION = re.compile(rf"[{ID_REST}]|\.[{ID_FIRST}«]")


def has_module_header(text: str) -> bool:
    index = 0
    while index < len(text):
        if text[index] in " \r\n":
            index += 1
        elif text.startswith("--", index):
            end = text.find("\n", index + 2)
            index = len(text) if end < 0 else end + 1
        elif text.startswith("/-", index) and not text.startswith(("/--", "/-!"), index):
            index += 3
            depth = 1
            while depth:
                marker = COMMENT_MARKER.search(text, index)
                if marker is None:
                    break
                depth += 1 if marker.group() == "/-" else -1
                index = marker.end()
            if depth:
                return False
        else:
            return text.startswith("module", index) and (
                IDENTIFIER_CONTINUATION.match(text, index + 6) is None
            )
    return False


def physical_lines(text: str) -> int:
    return text.count("\n") + int(bool(text) and not text.endswith("\n"))


def lean_source_files(root: Path) -> list[Path]:
    files = []
    for directory, subdirectories, names in os.walk(root, followlinks=False):
        subdirectories[:] = sorted(
            name for name in subdirectories
            if name not in {".git", ".lake"} and not (Path(directory) / name).is_symlink()
        )
        for name in sorted(names):
            path = Path(directory) / name
            if name.endswith(".lean") and (path.is_symlink() or path.is_file()):
                files.append(path)
    return files


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    failed = False
    for path in lean_source_files(root):
        relative = path.relative_to(root)
        if path.is_symlink():
            print(f"{relative}: must be a regular Lean file, not a symbolic link")
            failed = True
            continue
        try:
            text = path.read_bytes().decode("utf-8")
        except UnicodeDecodeError:
            print(f"{relative}: source is not valid UTF-8")
            failed = True
            continue
        if path.name != "lakefile.lean" and not has_module_header(text):
            print(f"{relative}: must use the module header keyword")
            failed = True
        if physical_lines(text) > 10_000:
            print(f"{relative}: exceeds 10,000 lines; split into smaller modules")
            failed = True
    if not failed:
        print("check-lean-sources: OK")
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
