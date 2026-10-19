#!/usr/bin/env bash
# Install the checksum-pinned Linux x86_64 Lean release into a local tools directory.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
if [[ $(uname -s) != Linux || $(uname -m) != x86_64 ]]; then
  printf 'This installer supports Linux x86_64. Install the lean-toolchain version for your platform.\n' >&2
  exit 2
fi
for program in python3 curl tar sha256sum; do
  command -v "$program" >/dev/null || { printf 'Missing prerequisite: %s\n' "$program" >&2; exit 2; }
done
tools_dir=${1:-.tools}
mkdir -p "$tools_dir"
tools_dir=$(cd "$tools_dir" && pwd)
mapfile -t pin < <(python3 - <<'PY'
import json
p=json.load(open('TOOLCHAIN.json'))
a=p['linux_x86_64']
for value in (a['url'],a['sha256'],a['directory'],p['lean_version'],p['lean_commit']):
    print(value)
PY
)
if [[ ${#pin[@]} != 5 ]]; then printf 'Invalid TOOLCHAIN.json\n' >&2; exit 2; fi
lean_dir="$tools_dir/${pin[2]}"
if [[ ! -x "$lean_dir/bin/lean" ]]; then
  archive="$tools_dir/lean-${pin[3]}.tar.zst"
  curl --fail --location --silent --show-error --retry 3 "${pin[0]}" -o "$archive"
  printf '%s  %s\n' "${pin[1]}" "$archive" | sha256sum --check -
  if command -v zstd >/dev/null; then
    tar --zstd -xf "$archive" -C "$tools_dir"
  else  # Python 3.14+ ships a zstd decoder
    python3 -c 'import sys, tarfile, compression.zstd as z
with z.open(sys.argv[1], "rb") as f, tarfile.open(fileobj=f, mode="r|") as t: t.extractall(sys.argv[2], filter="tar")' \
      "$archive" "$tools_dir"
  fi
fi
[[ $("$lean_dir/bin/lean" --short-version) == "${pin[3]}" ]]
[[ $("$lean_dir/bin/lean" --githash) == "${pin[4]}" ]]
printf 'Pinned Lean binary directory: %s/bin\n' "$lean_dir"
