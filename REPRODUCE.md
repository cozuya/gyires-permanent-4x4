# Reproducing the verification

Everything needed is in this repository. No files from any other repository are used.

## Requirements

- Linux x86_64, with Bash, Git, Python 3, curl, tar, zstd and coreutils. Without zstd,
  Python 3.14 or later can unpack the Lean archive instead.
- About 10 GB of free disk: 2.6 GB for Lean and about 7 GB for the dependencies and
  prebuilt Mathlib.
- About 8 GB of RAM. The recorded runs stayed within a 7 GiB memory limit, with one
  process peaking at about 6.7 GB of resident memory, most of it shared, read-only
  Mathlib files.
- For the optional cross-check: a C++ compiler with OpenMP and `__int128` support
  (g++ or clang).

Other platforms can install Lean 4.28.0 from [lean-toolchain](lean-toolchain), put it on
`PATH`, and run the same fetch and verification commands in Bash.

## Commands

```sh
git clone https://github.com/cozuya/gyires-permanent-4x4.git
cd gyires-permanent-4x4
bash scripts/install-lean.sh                  # checksum-pinned Lean 4.28.0 into .tools/
export PATH="$PWD/.tools/lean-4.28.0-linux/bin:$PATH"
bash scripts/fetch-deps.sh                    # locked dependencies + prebuilt Mathlib
./verify.sh                                   # full rebuild and statement/axiom audit
python3 scripts/check-package.py              # inventory, hashes, links, evidence
bash crosscheck/run.sh                        # optional independent re-check
```

If Lean 4.28.0 is already installed elsewhere, skip the installer. Put its `bin`
directory on `PATH`, or set `LEAN_BIN_DIR` for `fetch-deps.sh` and `verify.sh`.

`fetch-deps.sh` runs `lake exe cache get` and then checks that `lake-manifest.json` is
unchanged and that every dependency is checked out at its pinned revision. No
`lake update` is needed. Only Mathlib and its dependencies come from the prebuilt cache.
Every module of this project is compiled from source by `verify.sh`.

## What `verify.sh` does

1. It prints the Lean, Lake and Mathlib versions and checks them against
   [TOOLCHAIN.json](TOOLCHAIN.json) and the lockfile.
2. It scans all 43 Lean files with [scripts/audit.py](scripts/audit.py) `sources`. The scan
   rejects `sorry`, `admit`, axiom declarations, `unsafe`, `implemented_by`, `extern`,
   `csimp`, `opaque`, kernel-check options, attributes, instances, notation and macros.
   It also requires `native_decide` to appear exactly 36 times, in the expected
   certificate files only.
3. It checks [SOURCE_SHA256SUMS](SOURCE_SHA256SUMS).
4. It deletes `.lake/build` and runs `lake build` on all four project libraries (41
   modules, including all 26 certificate pieces).
5. It runs `lake env lean --trust=0 Verification.lean`, which prints the type and the
   axioms of 15 declarations.
6. It checks with `audit.py axioms` that each declaration has exactly its expected axiom
   set. Three must use only `propext`, `Classical.choice` and `Quot.sound`; the other
   twelve must use exactly those plus `Lean.ofReduceBool` and `Lean.trustCompiler`. Any
   warning, error, `sorryAx` or other axiom fails the run.
7. It writes `.build/verification.log`, `.build/kernel-check.log` and
   `.build/verification.json`, with the commit, source hashes, exit codes and timings.

The final lines of a successful transcript include `AXIOM_AUDIT=PASS` and
`VERIFY_EXIT_CODE=0`.

## Checking only Aristotle's original project

To rebuild exactly what Aristotle delivered, without this package's additions:

```sh
mkdir /tmp/aristotle && tar xzf provenance/aristotle/gyires-lean-complete.tar.gz -C /tmp/aristotle
cd /tmp/aristotle/gyires-lean-complete
lake exe cache get
lake build RequestProject GyiresCompute
lake env lean scripts/PrintAxioms.lean
```

The output of this sequence on October 19, 2026 is in
[evidence/aristotle-asreceived-build.log](evidence/aristotle-asreceived-build.log).
