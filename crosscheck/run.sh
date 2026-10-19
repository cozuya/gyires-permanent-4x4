#!/usr/bin/env bash
# Independent cross-check of the finite certificate outside Lean (about a minute).
# Requires python3 and a C++ compiler with OpenMP and __int128 (g++ or clang++).
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
work=../.build/crosscheck
mkdir -p "$work"
python3 tree.py "$work"
"${CXX:-g++}" -O2 -fopenmp -o "$work/leafcheck" leafcheck.cpp
"$work/leafcheck" "$work" 32
printf '\nNegative control (31 in place of 32; every leaf must fail):\n'
if "$work/leafcheck" "$work" 31; then
  printf 'NEGATIVE_CONTROL=FAIL (the checker accepted a false statement)\n'
  exit 1
fi
printf 'NEGATIVE_CONTROL=PASS\n'
