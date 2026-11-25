#!/usr/bin/env bash
# Regenerate `scripts/audited-declarations.txt` from `LionsC12/AxiomAudit.lean`.
#
# The list is the release gate's record of *which* declarations are covered by
# the axiom audit: `scripts/check-axiom-audit.awk` fails unless the set of
# `#print axioms` reports Lean emits is exactly this set, so a rename or a
# quietly dropped target cannot slip through.  Run this after editing the audit
# module and commit both files together.
set -euo pipefail

project_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)
audit_module="$project_root/LionsC12/AxiomAudit.lean"
list_file="$project_root/scripts/audited-declarations.txt"

if [[ ! -f "$audit_module" ]]; then
  echo "missing $audit_module" >&2
  exit 1
fi

targets=$(awk '
  $1 == "#print" && $2 == "axioms" {
    if (NF != 3) {
      print "malformed #print axioms command on line " FNR > "/dev/stderr"
      bad = 1
      next
    }
    print $3
  }
  END { if (bad) exit 1 }
' "$audit_module" | LC_ALL=C sort)

if [[ -z "$targets" ]]; then
  echo "no #print axioms commands found in $audit_module" >&2
  exit 1
fi

duplicates=$(printf '%s\n' "$targets" | LC_ALL=C uniq -d)
if [[ -n "$duplicates" ]]; then
  echo "duplicate #print axioms targets:" >&2
  printf '%s\n' "$duplicates" >&2
  exit 1
fi

printf '%s\n' "$targets" > "$list_file"
echo "wrote $(wc -l < "$list_file" | tr -d ' ') declarations to ${list_file#"$project_root"/}"
