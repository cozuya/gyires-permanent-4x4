#!/usr/bin/env bash
# Materialize the locked dependencies and download mathlib's prebuilt files.
# The lockfile must not change.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
if [[ -n ${LEAN_BIN_DIR:-} ]]; then export PATH="$LEAN_BIN_DIR:$PATH"; fi
command -v lake >/dev/null || { printf 'Put the pinned Lean bin directory on PATH.\n' >&2; exit 2; }
before=$(sha256sum lake-manifest.json)
lake exe cache get
[[ $(sha256sum lake-manifest.json) == "$before" ]]
python3 scripts/audit.py pins
