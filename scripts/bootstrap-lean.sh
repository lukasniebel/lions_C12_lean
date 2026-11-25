#!/usr/bin/env bash
set -euo pipefail

project_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)
tool_dir="$project_root/.toolchains"
download_dir="$tool_dir/downloads"
lean_version=4.35.0
lean_archive="lean-$lean_version-linux.tar.zst"
lean_root="$tool_dir/lean-$lean_version-linux"
archive_path="$download_dir/$lean_archive"
archive_url="https://github.com/leanprover/lean4/releases/download/v$lean_version/$lean_archive"
archive_sha256=7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d
mathlib_rev=56a005855ea17e0b0958f73ec801ae140b0a1679

expected_toolchain="leanprover/lean4:v$lean_version"
actual_toolchain=$(tr -d '[:space:]' < "$project_root/lean-toolchain")
if [[ "$actual_toolchain" != "$expected_toolchain" ]]; then
  echo "expected lean-toolchain '$expected_toolchain', found '$actual_toolchain'" >&2
  exit 1
fi

for command_name in curl sha256sum tar unzstd cc git flock; do
  if ! command -v "$command_name" >/dev/null 2>&1; then
    echo "required command is missing: $command_name" >&2
    exit 1
  fi
done

mkdir -p "$tool_dir"
exec 9>"$tool_dir/bootstrap.lock"
if ! flock --nonblock 9; then
  echo "another Lean bootstrap is already using '$tool_dir'" >&2
  exit 1
fi
ready_marker="$tool_dir/.lions-c12-ready"
rm -f "$ready_marker"

mkdir -p "$download_dir" "$tool_dir/curl-home" "$tool_dir/mathlib-cache"
cp "$project_root/scripts/cache.curlrc" "$tool_dir/curl-home/.curlrc"

archive_ok=false
if [[ -f "$archive_path" ]]; then
  current_sha=$(sha256sum "$archive_path")
  current_sha=${current_sha%% *}
  [[ "$current_sha" == "$archive_sha256" ]] && archive_ok=true
fi

if [[ "$archive_ok" != true ]]; then
  partial_path="$archive_path.part"
  echo "Downloading Lean $lean_version..."
  curl --fail --location --retry 3 --retry-all-errors \
    --continue-at - --output "$partial_path" "$archive_url"
  current_sha=$(sha256sum "$partial_path")
  current_sha=${current_sha%% *}
  if [[ "$current_sha" != "$archive_sha256" ]]; then
    echo "Lean archive checksum mismatch: expected $archive_sha256, got $current_sha" >&2
    exit 1
  fi
  mv "$partial_path" "$archive_path"
fi

extract_marker="$lean_root/.lions-c12-extracted"
if [[ ! -f "$extract_marker" ]]; then
  echo "Extracting Lean $lean_version..."
  tar --no-same-owner --no-same-permissions --use-compress-program=unzstd \
    -xf "$archive_path" -C "$tool_dir"
  touch "$extract_marker"
fi

cc -shared -fPIC -O2 -Wall -Wextra \
  -o "$tool_dir/libproc_exe_shim.so" "$project_root/scripts/proc_exe_shim.c" -ldl

export PATH="$project_root/scripts:$PATH"
export LIONS_C12_BOOTSTRAPPING=1
lean --version
lake --version

echo "Fetching dependencies pinned by lake-manifest.json..."
update_ok=false
for update_attempt in 1 2 3; do
  if (
    cd "$project_root"
    MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
  ); then
    update_ok=true
    break
  fi
  if (( update_attempt < 3 )); then
    echo "Dependency update attempt $update_attempt failed; retrying..." >&2
  fi
done
if [[ "$update_ok" != true ]]; then
  echo "dependency update failed after 3 attempts" >&2
  exit 1
fi

actual_mathlib_rev=$(git -C "$project_root/.lake/packages/mathlib" rev-parse HEAD)
if [[ "$actual_mathlib_rev" != "$mathlib_rev" ]]; then
  echo "expected mathlib revision $mathlib_rev, found $actual_mathlib_rev" >&2
  exit 1
fi

mathlib_imports_text=$(
  {
    find "$project_root/LionsC12" -type f -name '*.lean' -print0 \
      | xargs -0 grep -hE '^(public[[:space:]]+)?import[[:space:]]+Mathlib\.' || true
    grep -hE '^(public[[:space:]]+)?import[[:space:]]+Mathlib\.' "$project_root/LionsC12.lean" || true
  } | awk '{print $NF}' | sort -u
)

if [[ -z "$mathlib_imports_text" ]]; then
  echo "no direct Mathlib imports found" >&2
  exit 1
fi
mapfile -t mathlib_imports <<< "$mathlib_imports_text"

echo "Fetching the Mathlib cache closure for ${#mathlib_imports[@]} direct imports..."
cache_ok=false
for cache_attempt in 1 2 3 4 5; do
  if (
    cd "$project_root"
    lake exe cache get "${mathlib_imports[@]}"
  ); then
    cache_ok=true
    break
  fi
  if (( cache_attempt < 5 )); then
    echo "Mathlib cache attempt $cache_attempt failed; retrying missing objects..." >&2
  fi
done
if [[ "$cache_ok" != true ]]; then
  echo "Mathlib cache download failed after 5 attempts" >&2
  exit 1
fi

touch "$ready_marker"

echo
echo "Lean environment ready. Run:"
echo "  cd '$project_root'"
echo '  PATH="$PWD/scripts:$PATH" lake build'
