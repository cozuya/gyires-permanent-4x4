#!/usr/bin/env bash
# Rebuild the whole Lean project from source and audit the exact statements and axioms.
# Requires the pinned Lean on PATH (or LEAN_BIN_DIR) and fetched dependencies; see REPRODUCE.md.
set -uo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
if [[ -n ${LEAN_BIN_DIR:-} ]]; then export PATH="$LEAN_BIN_DIR:$PATH"; fi
for program in lean lake python3 sha256sum git; do
  command -v "$program" >/dev/null || { printf 'Missing prerequisite: %s\n' "$program" >&2; exit 2; }
done
mkdir -p .build
log=.build/verification.log
started=$(date -u '+%Y-%m-%dT%H:%M:%SZ')
run() {
  printf '\n$'
  printf ' %q' "$@"
  printf '\n'
  local start=$SECONDS
  "$@"
  local code=$?
  printf 'EXIT_CODE=%s WALL_SECONDS=%s\n' "$code" "$((SECONDS - start))"
  return "$code"
}
run_capture() {
  local capture=$1
  shift
  printf '\n$'
  printf ' %q' "$@"
  printf '  # output also saved to %s\n' "$capture"
  local start=$SECONDS
  "$@" 2>&1 | tee "$capture"
  local codes=("${PIPESTATUS[@]}")
  local code=${codes[0]}
  if (( codes[1] != 0 )); then code=${codes[1]}; fi
  printf 'EXIT_CODE=%s WALL_SECONDS=%s\n' "$code" "$((SECONDS - start))"
  return "$code"
}
verify_main() {
  run date -u '+%Y-%m-%dT%H:%M:%SZ' || return $?
  run lean --version || return $?
  run lean --githash || return $?
  run lake --version || return $?
  run cat lean-toolchain || return $?
  run git -C .lake/packages/mathlib rev-parse HEAD || return $?
  run python3 scripts/audit.py pins || return $?
  run python3 scripts/audit.py sources || return $?
  run python3 scripts/check-package.py --sources-only || return $?
  run sha256sum --check SOURCE_SHA256SUMS || return $?
  run python3 scripts/audit.py hashes || return $?
  # Remove this project's build outputs only; dependency caches stay in .lake/packages.
  run rm -rf .lake/build || return $?
  run lake build RequestProject GyiresCompute GyiresStrictCompute GyiresEquality || return $?
  run_capture .build/kernel-check.log lake env lean --trust=0 Verification.lean || return $?
  run python3 scripts/audit.py axioms .build/kernel-check.log || return $?
  run date -u '+%Y-%m-%dT%H:%M:%SZ' || return $?
  printf '\nFULL_REBUILD=PASS\nINEQUALITY=PASS\nEQUALITY_CASE=PASS\nRATIO_FORM=PASS\n'
  printf 'STRONGER_INEQUALITY=PASS\nGRAM_COMPARISON=PASS\nAXIOM_AUDIT=PASS\n'
  printf 'TRUST_MODEL=kernel+native_decide (Lean.ofReduceBool, Lean.trustCompiler)\n'
}
verify_main 2>&1 | tee "$log"
codes=("${PIPESTATUS[@]}")
code=${codes[0]}
if (( codes[1] != 0 )); then code=${codes[1]}; fi
finished=$(date -u '+%Y-%m-%dT%H:%M:%SZ')
run python3 scripts/audit.py record "$code" "$started" "$finished" 2>&1 | tee -a "$log"
record_codes=("${PIPESTATUS[@]}")
if (( record_codes[0] != 0 )); then code=${record_codes[0]}; fi
if (( record_codes[1] != 0 )); then code=${record_codes[1]}; fi
printf '\nVERIFY_EXIT_CODE=%s\n' "$code" | tee -a "$log"
exit "$code"
