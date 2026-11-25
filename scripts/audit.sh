#!/usr/bin/env bash
set -euo pipefail

project_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)
cd "$project_root"
lake_cmd="$project_root/scripts/lake"
lean_cmd="$project_root/scripts/lean"

shopt -s globstar nullglob
lean_sources=(LionsC12/**/*.lean LionsC12.lean Check.lean CheckDecls.lean Solution.lean)
audited_list="scripts/audited-declarations.txt"

# The source rule for every tracked Lean file: a `module` file of at most 10,000
# lines, and no symbolic links.
python3 -I scripts/check-lean-sources.py "$project_root"

# `Challenge.lean` states Theorem 1.1 and Corollary 1.2 with mathlib notions and the definitions of the statement layer;
# `LionsC12/Paper/Statement.lean` must repeat those definitions character for
# character, and `Solution.lean` must state the theorem with the Challenge's text.
python3 -I scripts/check-challenge-text.py \
  Challenge.lean LionsC12/Paper/Statement.lean Solution.lean

# Strip Lean line comments, nested block comments, and strings before matching
# placeholders and declaration-level trust/escape hatches.  Token boundaries
# are identifier boundaries rather than whitespace boundaries, so forms such
# as `(by sorry)` cannot evade the scan.  This also keeps prose in module
# comments (for example a line beginning with "constant") from tripping it.
# The scanned tokens are the placeholders `sorry`/`sorryAx`/`admit`; the
# declaration keywords `axiom`/`opaque`/`constant`/`unsafe`/`extern` and
# `partial def`, both at the start of a line and after `... in`; and the
# trust attributes/axioms `implemented_by`, `extern`, `native_decide`,
# `lcProof`, `unsafeCast` and the kernel-reduction axioms `ofReduceBool`,
# `ofReduceNat`, `trustCompiler` that `native_decide` is built on.
if awk '
  FNR == 1 { blockDepth = 0; inString = 0 }
  {
    source = $0
    code = ""
    i = 1
    while (i <= length(source)) {
      c = substr(source, i, 1)
      pair = substr(source, i, 2)
      if (blockDepth > 0) {
        if (pair == "/-") {
          blockDepth++
          i += 2
        } else if (pair == "-/") {
          blockDepth--
          i += 2
        } else {
          i++
        }
      } else if (inString) {
        if (c == "\\") {
          i += 2
        } else if (c == "\"") {
          inString = 0
          i++
        } else {
          i++
        }
      } else if (pair == "--") {
        break
      } else if (pair == "/-") {
        blockDepth++
        i += 2
      } else if (c == "\"") {
        inString = 1
        code = code " "
        i++
      } else {
        code = code c
        i++
      }
    }
    placeholder = code ~ /(^|[^[:alnum:]_])(sorryAx|sorry|admit)([^[:alnum:]_]|$)/
    declaration = code ~ /^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|noncomputable)[[:space:]]+)*((axiom|axioms|opaque|constant|constants|unsafe|extern)[[:space:]]|partial[[:space:]]+def[[:space:]])/
    trustAttribute = code ~ /(^|[^[:alnum:]_])(implemented_by|extern|native_decide|lcProof|unsafeCast|ofReduceBool|ofReduceNat|trustCompiler)([^[:alnum:]_]|$)/
    # Declaration keywords after `... in` (for example `open X in axiom ...`) do
    # not start the line; catch the keyword tokens anywhere in code as well.
    inlineDeclaration = code ~ /(^|[^[:alnum:]_])(axiom|opaque|unsafe|partial)[[:space:]]/
    if (placeholder || declaration || trustAttribute || inlineDeclaration) {
      print FILENAME ":" FNR ":" $0
      found = 1
    }
  }
  END { exit found ? 0 : 1 }
' "${lean_sources[@]}"; then
  echo "release Lean source contains a placeholder, trust declaration, or escape hatch" >&2
  exit 1
fi

# Lake builds only the root module's transitive import closure, so a module that
# is not imported from LionsC12.lean would be silently uncompiled.  Require every
# source module (except the audit driver itself) to be reachable from the root.
if ! awk '
  function modname(path) {
    sub(/\.lean$/, "", path); gsub(/\//, ".", path); return path
  }
  FNR == 1 { current = modname(FILENAME); known[current] = 1 }
  /^(public[[:space:]]+)?import[[:space:]]+LionsC12/ {
    target = $NF; edges[current] = edges[current] " " target
  }
  END {
    queue[1] = "LionsC12"; head = 1; tail = 1; seen["LionsC12"] = 1
    while (head <= tail) {
      node = queue[head++]
      n = split(edges[node], targets, " ")
      for (i = 1; i <= n; i++) {
        if (targets[i] != "" && !(targets[i] in seen)) {
          seen[targets[i]] = 1; queue[++tail] = targets[i]
        }
      }
    }
    for (m in known) {
      if (m != "LionsC12.AxiomAudit" && !(m in seen)) {
        print "module not reachable from the root: " m > "/dev/stderr"; missing = 1
      }
    }
    if (missing) exit 1
  }
' LionsC12/**/*.lean LionsC12.lean; then
  echo "every release module must be imported from LionsC12.lean" >&2
  exit 1
fi

# The axiom report is compared against short names, so the audit module must not
# shorten any name: it may contain no `namespace`, `open`, or `section` command,
# and every audited declaration is written fully qualified.
if grep -nE '^[[:space:]]*(namespace|open|section|export|set_option)[[:space:]]' LionsC12/AxiomAudit.lean; then
  echo "LionsC12/AxiomAudit.lean must not open or enter namespaces" >&2
  exit 1
fi
# One grep for the negation of the intended shape: the target must be a fully
# qualified `LionsC12.…` name (which may contain non-ASCII letters such as `σ`)
# and nothing may follow it on the line, so a target such as `Foo.bar` is rejected.
if grep -nE '^[[:space:]]*#print[[:space:]]+axioms[[:space:]]+' LionsC12/AxiomAudit.lean \
   | grep -vE '#print[[:space:]]+axioms[[:space:]]+LionsC12\.[^[:space:]]+[[:space:]]*$'; then
  echo "every #print axioms target must be a fully qualified LionsC12 declaration" >&2
  exit 1
fi

# The axiom audit is gated against a checked-in *set* of declaration names
# (`scripts/audited-declarations.txt`), not just a count, so the list and the
# audit module have to change together.  Verify here that the list is sorted,
# duplicate-free, and exactly the set of `#print axioms` targets, and that every
# public smoke-test name in `Check.lean` is on it.  `LC_ALL=C` keeps AWK's string
# comparison in byte order, matching `scripts/regenerate-audited-declarations.sh`.
if ! LC_ALL=C awk '
  NR == FNR {
    name = $0
    sub(/[[:space:]]+$/, "", name)
    if (name == "") next
    listed[name] = 1
    entries++
    if (previous != "" && previous >= name) {
      print "audited-declaration list is not sorted/unique at: " name > "/dev/stderr"
      bad = 1
    }
    previous = name
    next
  }
  FILENAME ~ /AxiomAudit\.lean$/ {
    if ($1 == "#print" && $2 == "axioms") {
      audited[$3] = 1
      if (!($3 in listed)) {
        print "#print axioms target is not listed in the audited declarations: " $3 > "/dev/stderr"
        bad = 1
      }
    }
    next
  }
  $1 == "#check" {
    checks++
    if (!($2 in listed)) {
      print "Check.lean name is not listed in the audited declarations: " $2 > "/dev/stderr"
      bad = 1
    }
  }
  END {
    if (entries == 0) {
      print "the audited-declaration list is empty" > "/dev/stderr"
      exit 1
    }
    if (checks == 0) {
      print "Check.lean contains no #check commands" > "/dev/stderr"
      exit 1
    }
    for (name in listed) {
      if (!(name in audited)) {
        print "listed declaration has no #print axioms command: " name > "/dev/stderr"
        bad = 1
      }
    }
    if (bad) exit 1
  }
' "$audited_list" LionsC12/AxiomAudit.lean Check.lean; then
  echo "the audited-declaration list, LionsC12/AxiomAudit.lean and Check.lean disagree" >&2
  echo "regenerate the list with scripts/regenerate-audited-declarations.sh" >&2
  exit 1
fi

# Every public smoke-test declaration must also be inspected by the transitive
# axiom whitelist.  The comparison is one AWK process, so that it does not depend
# on the `/dev/fd` paths used by process substitution.
if ! awk '
  FNR == NR {
    if ($1 == "#print" && $2 == "axioms") covered[$3] = 1
    next
  }
  $1 == "#check" {
    total++
    if (!($2 in covered)) {
      print "missing axiom audit for " $2 > "/dev/stderr"
      missing++
    }
  }
  END {
    if (total == 0) {
      print "Check.lean contains no #check commands" > "/dev/stderr"
      exit 1
    }
    if (missing) exit 1
  }
' LionsC12/AxiomAudit.lean Check.lean; then
  echo "public-check axiom coverage failed" >&2
  exit 1
fi

# The library build must be warning-free as well as error-free.  The default
# targets are the library and `Solution`, the proof of the Challenge statement.
"$lake_cmd" build --wfail
"$lake_cmd" build --wfail Solution
# `Challenge.lean` ends its two theorems in the deliberate `sorry`s that `Solution.lean`
# replaces, so it is built without `--wfail`; the build must succeed with exactly those two
# warnings.
challenge_log=$("$lake_cmd" build Challenge 2>&1) || { printf '%s\n' "$challenge_log" >&2; exit 1; }
printf '%s\n' "$challenge_log"
if [[ $(printf '%s\n' "$challenge_log" | grep -c '^warning:') -ne 2 ]] \
    || [[ $(printf '%s\n' "$challenge_log" | grep -c "^warning: Challenge.lean:.*declaration uses \`sorry\`") -ne 2 ]]; then
  echo "Challenge.lean must build with exactly two warnings, its deliberate sorries" >&2
  exit 1
fi
# `Check.lean` belongs to none of the Lake libraries of `lakefile.toml`
# (`LionsC12`, `Challenge`, `Solution`), so neither `lake build --wfail` above nor
# `lake exe runLinter` below sees it.  Elaborate it here with every warning
# promoted to an error: `-D warningAsError=true` sets the `warningAsError`
# option, which covers `declaration uses 'sorry'` and every linter warning.
# (`-E` would not do: it takes a message *kind*, not a severity.)
"$lean_cmd" -D warningAsError=true Check.lean
"$lake_cmd" exe runLinter LionsC12

# The audited-declaration list is checked below against `LionsC12/AxiomAudit.lean`, but both
# are checked-in files and could agree while omitting a theorem.  Compare the audit module with
# a fresh enumeration of the theorems of the built library (`--check` writes nothing).
python3 -I scripts/generate-axiom-audit.py --check

# The two compared theorems themselves: `Solution.lean` must prove the Challenge statements
# from the three standard axioms only (the library audit covers `LionsC12.*`, not the
# `LionsC12Challenge.*` theorems of `Solution.lean`).
solution_axioms=$(mktemp -d "${TMPDIR:-/tmp}/lions-c12-solution-axioms.XXXXXX")
trap 'rm -rf "$solution_axioms"' EXIT
cat > "$solution_axioms/SolutionAxioms.lean" <<'LEAN'
import Solution
#print axioms LionsC12Challenge.lions_counterexample_interval
#print axioms LionsC12Challenge.lions_counterexample_domain
LEAN
printf '%s\n' LionsC12Challenge.lions_counterexample_domain \
  LionsC12Challenge.lions_counterexample_interval > "$solution_axioms/expected.txt"
if ! "$lean_cmd" "$solution_axioms/SolutionAxioms.lean" 2>&1 \
    | LC_ALL=C awk -v listfile="$solution_axioms/expected.txt" -f scripts/check-axiom-audit.awk; then
  echo "the axiom check of the two Solution theorems failed" >&2
  exit 1
fi

# Every declaration the blueprint cites (`\lean{...}` in blueprint/src) must
# exist in the built library, and the committed list `blueprint/lean_decls`
# must be the one generated from those annotations.
if [ -d blueprint/src ]; then
  # `leanblueprint web` rewrites the list in document order with repetitions,
  # so compare the two as sets.
  if ! diff -u <(LC_ALL=C sort -u blueprint/lean_decls) \
      <(python3 scripts/blueprint-decls.py | LC_ALL=C sort -u); then
    echo "blueprint/lean_decls is out of date: run scripts/blueprint-decls.py > blueprint/lean_decls" >&2
    exit 1
  fi
  "$lake_cmd" exe checkdecls blueprint/lean_decls
fi

# `#print axioms` is informational by itself: Lean exits successfully even if
# a theorem acquires an unexpected axiom.  Forward the complete report, but make
# the release gate fail unless every dependency is one of the three standard
# logical axioms accepted by this project *and* the set of reported declarations
# is exactly `scripts/audited-declarations.txt`.
if ! "$lean_cmd" LionsC12/AxiomAudit.lean 2>&1 \
    | LC_ALL=C awk -v listfile="$audited_list" \
        -f scripts/check-axiom-audit.awk; then
  echo "axiom audit failed" >&2
  exit 1
fi
