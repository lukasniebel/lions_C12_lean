#!/usr/bin/env bash
set -euo pipefail

# Judge `Solution.lean` against `Challenge.lean` with the `lake comparator` of the
# pinned toolchain (`lean-toolchain`), replaying the exported proof through Lean's
# kernel and through the independent kernels bundled with the toolchain (NanoDa and
# con-ron), as the configuration in `comparator.json` prescribes.
#
# Lean and Lake are those of the self-contained installation of
# `scripts/bootstrap-lean.sh`, run through the wrappers `scripts/lake` and
# `scripts/lean`.  `lake comparator` builds and exports the project inside a
# `bwrap` sandbox, so `bwrap` (bubblewrap) must be installed and able to create
# user namespaces.  Extra arguments are passed to `lake comparator`.
project_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)
cd "$project_root"
lake_cmd="$project_root/scripts/lake"
lean_cmd="$project_root/scripts/lean"

for required_command in bwrap python3; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required to run lake comparator" >&2
    exit 1
  fi
done

toolchain=$(tr -d '[:space:]' < lean-toolchain)
prefix=$("$lean_cmd" --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  if [ ! -x "$prefix/bin/$tool" ]; then
    echo "error: toolchain $toolchain does not bundle $tool" >&2
    exit 1
  fi
done

# The checked-in configuration names no external kernel; this generated copy
# registers the bundled ones, as the registry's own protected configuration does.
config=$(mktemp "${TMPDIR:-/tmp}/lions-c12-comparator.XXXXXX")
trap 'rm -f "$config"' EXIT
python3 -I - comparator.json "$config" "$prefix" <<'PY'
import json
import pathlib
import sys

source, destination, prefix = sys.argv[1:]
try:
    config = json.loads(pathlib.Path(source).read_text(encoding="utf-8"))
except (OSError, UnicodeError, json.JSONDecodeError) as error:
    print(f"error: cannot read valid Comparator config {source}: {error}", file=sys.stderr)
    raise SystemExit(1)
if not isinstance(config, dict):
    print(f"error: {source} must contain one JSON object", file=sys.stderr)
    raise SystemExit(1)
if "external_kernels" in config:
    print(f"error: {source}: external_kernels belongs in the generated copy only", file=sys.stderr)
    raise SystemExit(1)
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron"],
}
pathlib.Path(destination).write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
PY

"$lake_cmd" comparator --config "$config" "$@"
