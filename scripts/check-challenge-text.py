#!/usr/bin/env python3
"""Check the textual identities between the Challenge statement and the library.

Usage: check-challenge-text.py CHALLENGE STATEMENT SOLUTION

* Every declaration block of CHALLENGE (`Challenge.lean`) other than the theorems — its
  docstring and declaration, from `/--` to the next docstring — is identical, character for
  character, to the block of the same name in STATEMENT (`LionsC12/Paper/Statement.lean`), the
  two files declare the same definitions and instances, and the `import`, section and `open`
  lines of the two files agree.
* The theorem blocks of CHALLENGE (docstring and statement up to `:=`) are identical to those in
  SOLUTION (`Solution.lean`), which declares the same theorems in the same namespace with the
  same `open` lines.

Exit status 0 when every check passes, 1 otherwise.
"""
import re
import sys

NAMESPACE = "LionsC12Challenge"
THEOREMS = ("lions_counterexample_interval", "lions_counterexample_domain")
DECL = re.compile(r"(?m)^(?:abbrev|def|structure|theorem|instance)\s+(\S+)")


def namespace_body(text, path):
    start = text.find(f"namespace {NAMESPACE}\n")
    end = text.find(f"end {NAMESPACE}", start)
    if start < 0 or end < 0:
        raise SystemExit(f"{path}: no `namespace {NAMESPACE}` … `end {NAMESPACE}` block")
    return text[start:end]


def blocks(text, path):
    """The preamble of the namespace, and its docstring-delimited declaration blocks by name."""
    parts = re.split(r"(?m)^(?=/-- )", namespace_body(text, path))
    named = {}
    for part in parts[1:]:
        match = DECL.search(part)
        if match is None:
            raise SystemExit(f"{path}: a docstring is not followed by a declaration")
        if match.group(1) in named:
            raise SystemExit(f"{path}: {match.group(1)} is declared twice")
        named[match.group(1)] = part.rstrip("\n")
    return parts[0], named


def header_lines(text):
    prefixes = ("module", "public import", "import", "@[expose]", "public section",
                "noncomputable section", "open ")
    return [line for line in text.splitlines() if line.startswith(prefixes)]


def theorem_statement(block):
    """The docstring and statement of the theorem, up to (excluding) its `:=`."""
    head = re.search(r"(?m)^theorem\s+\S+", block)
    index = block.find(":=", head.end())
    if index < 0:
        raise SystemExit("a theorem has no `:=`")
    return block[:index]


def main(argv):
    if len(argv) != 4:
        print(__doc__, file=sys.stderr)
        return 2
    challenge_path, statement_path, solution_path = argv[1:]
    challenge = open(challenge_path, encoding="utf-8").read()
    statement = open(statement_path, encoding="utf-8").read()
    solution = open(solution_path, encoding="utf-8").read()
    ok = True

    def check(condition, message):
        nonlocal ok
        if not condition:
            print(message, file=sys.stderr)
            ok = False

    c_pre, c_blocks = blocks(challenge, challenge_path)
    s_pre, s_blocks = blocks(statement, statement_path)
    o_pre, o_blocks = blocks(solution, solution_path)

    definitions = [name for name in c_blocks if name not in THEOREMS]
    for name in THEOREMS:
        check(name in c_blocks, f"{challenge_path}: theorem {name} not found")
    check(set(s_blocks) == set(definitions),
          f"{statement_path} declares {sorted(s_blocks)}, {challenge_path} defines "
          f"{sorted(definitions)}")
    check(c_pre == s_pre, f"{statement_path}: the namespace preamble differs from the Challenge's")
    check(header_lines(challenge) == header_lines(statement),
          f"{statement_path}: the import, section or open lines differ from the Challenge's")
    for name in definitions:
        check(s_blocks.get(name) == c_blocks[name],
              f"{statement_path}: the block of {name} differs from the Challenge's")

    check(set(o_blocks) == set(THEOREMS),
          f"{solution_path} must declare exactly {sorted(THEOREMS)} in {NAMESPACE}, found "
          f"{sorted(o_blocks)}")
    check(o_pre == c_pre, f"{solution_path}: the namespace preamble differs from the Challenge's")
    for name in THEOREMS:
        if name in c_blocks and name in o_blocks:
            check(theorem_statement(o_blocks[name]) == theorem_statement(c_blocks[name]),
                  f"{solution_path}: the docstring or statement of {name} differs from the "
                  "Challenge's")

    if ok:
        print(f"{len(definitions)} definitions of {challenge_path} match {statement_path}; "
              f"the statements of {', '.join(THEOREMS)} match {solution_path}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
