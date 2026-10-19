# Original computer-assisted proof

These files are the original proof of the 4×4 result, as written before any Lean work,
preserved byte-for-byte except for the display copy noted below:

- [RESULTS.md](RESULTS.md) is the mathematical write-up: reduction, cone covering,
  certificate and equality case. This is a display copy. Its exact original bytes are in
  [RESULTS.original.txt](RESULTS.original.txt), and the copy changes only math markup
  that GitHub's renderer rejects, such as `\operatorname`.
- [RESULTS_certificate/generate.py](RESULTS_certificate/generate.py) enumerates faces and
  flag-orbit representatives and writes the cones.
- [RESULTS_certificate/verify.cpp](RESULTS_certificate/verify.cpp) checks every coefficient
  with signed 64-bit integers, which RESULTS.md shows to be exact.
- [RESULTS_certificate/verification.txt](RESULTS_certificate/verification.txt) is the
  recorded output: 65,376 flags and 1,589,290,560 coefficients, all nonnegative, with
  strictly positive pure powers. The file carries no input identity or timing.

The local file times are 2026-10-15 03:39–03:47 UTC. They are not authenticated
timestamps.

On October 16, 2026 a separate audit reran the full coefficient check twice: once with
this verifier, and once with an independent implementation using Ryser's formula and
128-bit arithmetic. It also reconstructed all 7,443 faces and the flag counts
independently. Those records stay in the private development repository; see
[PROVENANCE.md](../PROVENANCE.md).

None of this is needed to rebuild the Lean theorems: the Lean checker regenerates its
certificate itself. To rerun the original computation, which takes a few minutes on a
workstation:

```sh
python3 original/RESULTS_certificate/generate.py > /tmp/perm4-cones.txt
g++ -std=c++17 -O3 original/RESULTS_certificate/verify.cpp -o /tmp/perm4-verify
/tmp/perm4-verify < /tmp/perm4-cones.txt
```

RESULTS.md section 5 gives the same commands with paths relative to the original
workspace.
