#!/usr/bin/env python3
"""Check the source rule for the Lean files of the repository.

Every `.lean` file tracked by git must be a regular file (not a symbolic link), valid UTF-8,
begin with the `module` header (after blank lines and ordinary `--` or `/- … -/` comments; a
`lakefile.lean` is exempt from this), and have at most 10,000 physical lines (LF or CRLF
terminated; an unterminated final line counts, a final newline adds none).

Usage: check-lean-sources.py [REPOSITORY_ROOT]   (default: the parent of this script's directory)
"""
import re
import subprocess
import sys
from pathlib import Path

MAX_LINES = 10_000
# A character that may continue an identifier after `module` (so `moduleFoo` is no header).
IDENT_CONTINUATION = re.compile(r"[\w'!?.₀-₉ₐ-ₜᵢ-ᵪⱼ]")


def starts_with_module(text: str) -> bool:
    i = 0
    while i < len(text):
        if text[i] in " \r\n":
            i += 1
        elif text.startswith("--", i):
            newline = text.find("\n", i)
            i = len(text) if newline < 0 else newline + 1
        elif text.startswith("/-", i) and not text.startswith(("/--", "/-!"), i):
            depth, i = 1, i + 2
            while depth:
                opening, closing = text.find("/-", i), text.find("-/", i)
                if closing < 0:
                    return False
                if 0 <= opening < closing:
                    depth, i = depth + 1, opening + 2
                else:
                    depth, i = depth - 1, closing + 2
        else:
            return text.startswith("module", i) and not IDENT_CONTINUATION.match(text, i + 6)
    return False


def physical_lines(text: str) -> int:
    return text.count("\n") + (1 if text and not text.endswith("\n") else 0)


def main(argv) -> int:
    root = Path(argv[1]) if len(argv) > 1 else Path(__file__).resolve().parents[1]
    listing = subprocess.run(["git", "-C", str(root), "ls-files", "-z", "--", "*.lean"],
                             check=True, capture_output=True).stdout.decode("utf-8")
    paths = [p for p in listing.split("\0") if p]
    failures = 0
    for relative in paths:
        path = root / relative
        problems = []
        if path.is_symlink():
            problems.append("is a symbolic link")
        elif not path.is_file():
            problems.append("is not a regular file")
        else:
            try:
                text = path.read_bytes().decode("utf-8")
            except UnicodeDecodeError:
                problems.append("is not valid UTF-8")
            else:
                if path.name != "lakefile.lean" and not starts_with_module(text):
                    problems.append("does not start with the `module` header")
                lines = physical_lines(text)
                if lines > MAX_LINES:
                    problems.append(f"has {lines} lines (at most {MAX_LINES})")
        for problem in problems:
            print(f"{relative}: {problem}", file=sys.stderr)
        failures += bool(problems)
    if failures:
        print(f"{failures} of {len(paths)} Lean files violate the source rule", file=sys.stderr)
        return 1
    print(f"{len(paths)} Lean files: module headers, at most {MAX_LINES} lines, no symbolic links")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
