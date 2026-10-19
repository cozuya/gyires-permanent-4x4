# Verification and statement correspondence

The reproducible entry point is `./verify.sh`. Its complete output is retained in
[evidence/verification.log](evidence/verification.log), with machine-readable metadata in
[evidence/verification.json](evidence/verification.json) and the exact theorem types and
axiom reports in [evidence/kernel-check.log](evidence/kernel-check.log).

## What the theorems say

The main theorem, in [RequestProject/Gyires.lean](RequestProject/Gyires.lean), as printed by
Lean:

```text
Gyires.gyires_4x4 : ∀ A ∈ doublyStochastic ℝ (Fin 4),
  3 * ((A * A.transpose).permanent + (A.transpose * A).permanent + 2 * (A * A).permanent) ≤ 128 * A.permanent ^ 2
```

Every name is Mathlib's own:

- `Matrix.permanent` is $\sum_{\sigma}\prod_i M_{\sigma(i),i}$.
- `*` is the ordinary matrix product and `transpose` the transpose.
- `doublyStochastic ℝ (Fin 4)` is the set of real 4×4 matrices with nonnegative entries
  whose row sums and column sums are all 1.

The project defines no replacement for any of these, and the source audit rejects
notation, macros, instances and attribute changes that could alter them.

[Verification.lean](Verification.lean) imports the proof and restates the results without
`doublyStochastic`. It assumes `∀ i j, 0 ≤ A i j`, `∀ i, ∑ j, A i j = 1` and
`∀ j, ∑ i, A i j = 1`, and proves:

| Declaration | Statement |
| --- | --- |
| `GyiresVerification.inequality` | $3(\mathrm{per}AA^T+\mathrm{per}A^TA+2\mathrm{per}A^2)\le128\mathrm{per}(A)^2$ |
| `GyiresVerification.equality_iff` | equality holds iff `∀ i j, A i j = 1/4` |
| `GyiresVerification.ratio` | $4!/4^4\le 4\mathrm{per}(A)^2/(\mathrm{per}AA^T+\mathrm{per}A^TA+2\mathrm{per}A^2)$ |
| `GyiresVerification.denominator_pos` | that denominator is positive, so the division above is genuine |
| `GyiresVerification.ratio_equality_iff` | equality in the ratio form iff `∀ i j, A i j = 1/4` |
| `GyiresVerification.stronger` | $3\mathrm{per}(AA^T)\le32\mathrm{per}(A)^2$ |
| `GyiresVerification.gram_comparison` | for every `n` and real `M N : Matrix (Fin n) (Fin n) ℝ`, $2\mathrm{per}(MN^T)\le\mathrm{per}(MM^T)+\mathrm{per}(NN^T)$ |

There are no other hypotheses. Zero entries, boundary matrices and singular matrices are
included. The ratio form is the statement of Cheon–Wanless Conjecture 20 for $n=4$, with
$A^{*}=A^T$ for real matrices.

## Trust model

`./verify.sh` audits the printed axioms of 15 declarations: the 8 project theorems and the
7 restatements above.

| Axioms | Declarations |
| --- | --- |
| `propext`, `Classical.choice`, `Quot.sound` only | `Gyires.permanent_gram_add_ge`, `GyiresVerification.gram_comparison`, `GyiresVerification.denominator_pos` |
| the same, plus `Lean.ofReduceBool` and `Lean.trustCompiler` | all others, including every 4×4 inequality and equality statement |

The two extra axioms come from `native_decide`. Each use proves a closed Boolean fact by
running compiled code, so these theorems trust the Lean compiler, interpreter and runtime
(here Lean 4.28.0, precompiled through its bundled C compiler) in addition to the kernel.
They are **not** compiler-independent, kernel-only certificates. The audit allows exactly
36 `native_decide` uses:

| File | Uses | Boolean fact |
| --- | --- | --- |
| [RequestProject/HEval.lean](RequestProject/HEval.lean) | 4 | the monomial multiplication tables are correct (`tableOK`, `e1OK`) |
| [RequestProject/Cert/Assemble.lean](RequestProject/Cert/Assemble.lean) | 5 | the four top-level face splits, and that every symmetry fixes $J$ |
| [RequestProject/Cert/C_*.lean](RequestProject/Cert) | 13 | `checkNode` succeeds on each certificate piece |
| [GyiresEquality/StrictSound.lean](GyiresEquality/StrictSound.lean) | 1 | positions of the pure powers $t_k^8$ in the exponent table |
| [GyiresEquality/Cert/S_*.lean](GyiresEquality/Cert) | 13 | the strict checker `checkNodeS` succeeds on each piece |

Every other step is checked by the kernel in the usual way:

- the meaning of each Boolean fact, via `checkNode_sound`, `checkNodeS_sound`,
  `splitCheck_sound` and `polyCheck_sound`;
- the Birkhoff support lemma;
- symmetry invariance;
- evaluation of the dense polynomial arithmetic and the Laplace expansion of the
  permanent;
- the reduction from doubly stochastic matrices to cones;
- the permanent Gram inequality;
- the equality and ratio arguments.

The source scan rejects `sorry`, `admit`, `axiom` declarations, `unsafe`,
`implemented_by`, `extern`, `csimp`, `opaque`, kernel-checking options, attributes,
instances, notation and macros in all 43 Lean files.

Independently of Lean, [crosscheck/](crosscheck/README.md) recomputes the same finite claim
in Python and C++, including the strict pure powers, and rejects a deliberately false
variant. That is ordinary software evidence, not a proof. Its value is that it does not
share the Lean compiler with the main proof.

## Measured results

The clean local run took place on 2026-10-19, from 14:58:33 to 15:07:35 UTC. The machine
was a WSL2 Linux host with 24 hardware threads, shared with another long-running job, and the run was capped
at 7 GiB of memory with no swap. Earlier clean runs on the same day took 5 min 37 s and
5 min 46 s, with a peak of 6.7 GB.

| Step | Result |
| --- | --- |
| Pins, source scan, inventory, 66 source hashes | PASS |
| `rm -rf .lake/build`, then `lake build` of the four project libraries | 8,074 jobs (41 project modules plus prebuilt Mathlib), exit 0, 503 s wall time |
| Slowest certificate pieces | `C_65502_64478` and `S_65502_64478`, 293 s each; the others 40–151 s |
| `lake env lean --trust=0 Verification.lean` | exit 0, no warnings or errors, 39 s |
| Axiom audit | all 15 declarations exactly as expected |
| Whole script | exit 0; 9 min 2 s wall time; 3,080 s user CPU; largest single-process resident size 5.2 GB |

The unmodified Aristotle project was rebuilt separately from its own archive with the same
pins. It completed 8,052 jobs with exit 0 in 302.6 s, and its axiom output matched
Aristotle's report. The record is
[evidence/aristotle-asreceived-build.log](evidence/aristotle-asreceived-build.log).

The cross-check, [evidence/crosscheck.log](evidence/crosscheck.log), found:

- 65,376 leaf cones, none with a negative coefficient;
- exactly 10 tight coefficients per cone, all pure powers $t_k^8$ ($k\ge1$) strict, a
  smallest margin of 190/189, and a largest coefficient of $7.45\times10^{11}$;
- with 31 in place of 32, all cones rejected (negative control passed).

GitHub Actions repeats the full verification and the cross-check on each push. This
report does not record a workflow result; see the
[Actions page](https://github.com/cozuya/gyires-permanent-4x4/actions/workflows/verify.yml).
A hosted runner has fewer cores than the machine above, so expect a longer build.

## Commands

After installing the pinned compiler and fetching the locked dependencies, as described in
[REPRODUCE.md](REPRODUCE.md):

```sh
./verify.sh
python3 scripts/check-package.py
bash crosscheck/run.sh
```

## Limits of what is verified

- The results depend on the trust model above. A fault in the Lean compiler or runtime
  that made one of the 36 Boolean checks wrongly return `true` would not be detected by
  the kernel. The cross-check and the original computation address this risk only
  empirically.
- Lean versions after 4.28 record `native_decide` differently: from 4.29 one auxiliary
  axiom per use, and from 4.35 `Lean.ofReduceBool` and `Lean.trustCompiler` no longer
  exist. The toolchain is pinned to Aristotle's 4.28.0, and the audit's expected axiom
  sets are specific to it.
- Only $n=4$ is proved. The method enumerates the faces of the 4×4 Birkhoff polytope and
  gives no proof for larger $n$.
- Verification establishes the stated theorems. It does not establish historical priority;
  see [PRIOR_ART.md](PRIOR_ART.md).
