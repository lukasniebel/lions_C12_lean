# Validate Lean's `#print axioms` report while forwarding it unchanged.
#
# The checked-in list of audited declarations is supplied with
# `-v listfile=scripts/audited-declarations.txt`.  Two things are enforced:
#
#   * every axiom a report mentions is one of the three standard logical
#     axioms this project accepts, and
#   * the *set* of declarations reported is exactly the set in `listfile` —
#     not merely its cardinality, so a rename that preserves the count, a
#     silently dropped target, or an unlisted addition all fail the gate.
#
# Lean may wrap an axiom list across several lines, so keep parsing until its
# closing bracket rather than checking each output line independently.  The
# declaration name is quoted on the line that carries the marker, before it.

function trim(value) {
  sub(/^[[:space:]]+/, "", value)
  sub(/[[:space:]]+$/, "", value)
  return value
}

function allowed(axiomName) {
  return axiomName == "propext" || \
    axiomName == "Classical.choice" || \
    axiomName == "Quot.sound"
}

function checkAxioms(fragment, count, entries, i, axiomName) {
  count = split(fragment, entries, ",")
  for (i = 1; i <= count; i++) {
    axiomName = trim(entries[i])
    if (axiomName != "" && !allowed(axiomName)) {
      print "unexpected axiom dependency: " axiomName > "/dev/stderr"
      invalid = 1
    }
  }
}

# Lean quotes the declaration name, and a Lean name may itself contain `'`
# (as in `foo'`), so take everything between the first and the last quote.
function reportedName(prefixText, text, first, last, i) {
  text = trim(prefixText)
  first = index(text, "'")
  if (first == 0) return ""
  last = 0
  for (i = length(text); i > first; i--) {
    if (substr(text, i, 1) == "'") { last = i; break }
  }
  if (last == 0) return ""
  return substr(text, first + 1, last - first - 1)
}

function record(name) {
  if (name == "") {
    print "could not read the declaration name from: " $0 > "/dev/stderr"
    invalid = 1
    return
  }
  reports++
  if (name in seen) {
    print "declaration audited twice: " name > "/dev/stderr"
    invalid = 1
  }
  seen[name] = 1
  if (!(name in expected)) {
    print "audited declaration is not in " listfile ": " name > "/dev/stderr"
    invalid = 1
  }
}

BEGIN {
  if (listfile == "") {
    print "check-axiom-audit.awk needs -v listfile=<audited declaration list>" > "/dev/stderr"
    invalid = 1
    exit 1
  }
  while ((getline line < listfile) > 0) {
    sub(/[[:space:]]+$/, "", line)
    if (line == "") continue
    expected[line] = 1
    expectedCount++
  }
  close(listfile)
  if (expectedCount == 0) {
    print "no declarations listed in " listfile > "/dev/stderr"
    invalid = 1
    exit 1
  }
}

{
  print

  if (inAxiomList) {
    closingBracket = index($0, "]")
    if (closingBracket == 0) {
      checkAxioms($0)
    } else {
      checkAxioms(substr($0, 1, closingBracket - 1))
      inAxiomList = 0
    }
    next
  }

  marker = "does not depend on any axioms"
  markerStart = index($0, marker)
  if (markerStart != 0) {
    record(reportedName(substr($0, 1, markerStart - 1)))
    next
  }

  marker = "depends on axioms:"
  markerStart = index($0, marker)
  if (markerStart != 0) {
    record(reportedName(substr($0, 1, markerStart - 1)))
    remainder = substr($0, markerStart + length(marker))
    openingBracket = index(remainder, "[")
    if (openingBracket == 0) {
      print "could not parse axiom dependency report: " $0 > "/dev/stderr"
      invalid = 1
      next
    }

    remainder = substr(remainder, openingBracket + 1)
    closingBracket = index(remainder, "]")
    if (closingBracket == 0) {
      checkAxioms(remainder)
      inAxiomList = 1
    } else {
      checkAxioms(substr(remainder, 1, closingBracket - 1))
    }
  }
}

END {
  if (inAxiomList) {
    print "unterminated axiom dependency list" > "/dev/stderr"
    invalid = 1
  }
  for (name in expected) {
    if (!(name in seen)) {
      print "listed declaration has no axiom report: " name > "/dev/stderr"
      invalid = 1
    }
  }
  if (reports != expectedCount) {
    print "expected " expectedCount " axiom reports, parsed " reports > "/dev/stderr"
    invalid = 1
  }
  if (invalid) {
    exit 1
  }
}
