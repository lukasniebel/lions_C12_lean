module

public import Lean

/-!
# Declaration check for the blueprint

`lake exe checkdecls blueprint/lean_decls` reads a list of fully qualified
declaration names (one per line, as produced by `leanblueprint web` from the
`\lean{...}` annotations of the blueprint) and fails unless every name is a
declaration of the built `LionsC12` library.  It takes the place of the external
`checkdecls` package of the standard blueprint setup, so that the check runs
on this project's own toolchain.
-/

@[expose] public section

open Lean

def main (args : List String) : IO UInt32 := do
  let [file] := args
    | IO.println "usage: checkdecls <file with one declaration name per line>"; return 1
  unless ← System.FilePath.pathExists file do
    IO.println s!"Could not find declaration list {file}."; return 1
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `LionsC12 }] {} (loadExts := false)
  let mut ok := true
  let mut checked := 0
  for line in ← IO.FS.lines file do
    let name := line.trimAscii.copy
    if name.isEmpty then continue
    checked := checked + 1
    unless env.contains name.toName do
      IO.println s!"{name} is missing."
      ok := false
  IO.println s!"checkdecls: {checked} declarations checked, {if ok then "all present" else "some missing"}."
  return if ok then 0 else 1
