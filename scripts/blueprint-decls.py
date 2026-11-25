#!/usr/bin/env python3
"""Collect the Lean declaration names referenced by the blueprint.

Reads every ``\\lean{...}`` annotation under ``blueprint/src`` and prints the
sorted, duplicate-free list of names, one per line.  ``blueprint/lean_decls``
is the committed copy of this list; the release gate regenerates it and fails
if it differs, then checks every name against the built library with
``lake exe checkdecls blueprint/lean_decls``.
"""
import pathlib
import re
import sys

root = pathlib.Path(__file__).resolve().parent.parent / "blueprint" / "src"
names = set()
for tex in sorted(root.rglob("*.tex")):
    text = tex.read_text(encoding="utf-8")
    # drop LaTeX comments
    text = re.sub(r"(?<!\\)%.*", "", text)
    for m in re.finditer(r"\\lean\{([^}]*)\}", text):
        for n in m.group(1).split(","):
            n = n.strip()
            if n:
                names.add(n)
sys.stdout.write("".join(n + "\n" for n in sorted(names)))
