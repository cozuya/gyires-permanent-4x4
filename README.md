# Gyires' Permanent Inequality for 4×4 Doubly Stochastic Matrices

**By Chris Ozols, with AI-assisted proof development and formalization.**

> **Proof available for n = 4; no novelty claim.** A bounded search found no
> earlier proof of the complete 4×4 case in the sources reviewed. I do not
> claim novelty, first discovery, or that any problem listing has been closed.
> This repository makes the 4×4 argument and its Lean checks available to
> anyone investigating it. The general-n conjecture is not resolved here.
> The proof's `native_decide` compiler/runtime trust is disclosed below.
> See the [prior-art review](PRIOR_ART.md).

This repository proves the **n = 4 case** of a permanent inequality conjectured by
**Béla Gyires** (published 1978). It is recorded as Conjecture 20 in Cheon and
Wanless's update of Minc's list of open problems on permanents. For every real
doubly stochastic 4×4 matrix $A$,

```math
128\,\mathrm{per}(A)^2 \;\ge\; 3\bigl[\mathrm{per}(AA^{T})+\mathrm{per}(A^{T}A)+2\mathrm{per}(A^{2})\bigr],
```

with equality **if and only if every entry of $A$ is $1/4$**. Both the inequality and the
equality case are formalized in **Lean 4.28.0 with Mathlib v4.28.0**.

Only the 4×4 case is proved here. The conjecture for general $n$ is not resolved here. It was
previously known for $n \le 3$.

> **Trust model.** The proof contains a finite certificate that is checked by compiled code
> through Lean's `native_decide`. The main theorems therefore depend on the axioms
> `Lean.ofReduceBool` and `Lean.trustCompiler` in addition to Lean's standard
> `propext`, `Classical.choice` and `Quot.sound`. In other words, they trust the Lean
> compiler and runtime as well as the Lean kernel; this is not a kernel-only proof. The
> same finite fact has also been checked outside Lean by an
> [independent C++ program](crosscheck/README.md). See [Trust model](#trust-model) below.

[Problem and verification overview](https://cozuya.github.io/gyires-permanent-4x4/) ·
[Readable proof](PROOF.md) · [Main Lean theorem](RequestProject/Gyires.lean) ·
[Equality case](GyiresEquality/Equality.lean) · [Ratio form](GyiresEquality/Ratio.lean) ·
[Exact-statement check](Verification.lean) ·
[Verification runs](https://github.com/cozuya/gyires-permanent-4x4/actions/workflows/verify.yml) ·
[Verification report](VERIFICATION_REPORT.md) · [Provenance](PROVENANCE.md) ·
[Prior art](PRIOR_ART.md) · [Citation](CITATION.cff)

## The conjecture and what is proved

A real matrix is *doubly stochastic* if its entries are nonnegative and every row and
column sums to 1. Write $\Omega_n$ for the set of such $n\times n$ matrices and $J_n$ for
the matrix with every entry $1/n$. Gyires' conjecture, as stated by Cheon and Wanless
(2005, Conjecture 20), is

```math
\frac{4\mathrm{per}(A)^2}{\mathrm{per}(AA^{*})+\mathrm{per}(A^{*}A)+2\mathrm{per}(A^{2})}
\;\ge\; \frac{n!}{n^{n}} \qquad (A\in\Omega_n),
```

with equality only at $A=J_n$. For real $A$, $A^{*}=A^{T}$. For $n=4$ the right-hand side is
$24/256 = 3/32$, and since the denominator is positive this is the polynomial inequality
displayed above.

| Statement | Status | Lean declaration |
| --- | --- | --- |
| Gyires' inequality, $n=4$ (polynomial form) | Formalized | `Gyires.gyires_4x4` |
| Equality exactly at $J_4$ | Formalized | `Gyires.gyires_4x4_eq_iff` |
| Strict inequality away from $J_4$ | Formalized | `Gyires.gyires_4x4_strict` |
| Cheon–Wanless ratio form, $n=4$, and its equality case | Formalized | `Gyires.gyires_4x4_ratio`, `Gyires.gyires_4x4_ratio_eq_iff` |
| Stronger inequality $3\mathrm{per}(AA^T)\le 32\mathrm{per}(A)^2$ on $\Omega_4$ | Formalized | `Gyires.permanent_gram_le`, strict form `Gyires.permanent_gram_lt` |
| $2\mathrm{per}(MN^T)\le\mathrm{per}(MM^T)+\mathrm{per}(NN^T)$ for real square $M,N$ of every size | Formalized, standard axioms only | `Gyires.permanent_gram_add_ge` |
| Gyires' conjecture for $n \ge 5$ | **Not addressed here** | — |

All statements use Mathlib's own `Matrix.permanent`, ordinary matrix products and
transposes, and Mathlib's `doublyStochastic ℝ (Fin 4)`. [Verification.lean](Verification.lean)
restates the 4×4 results with the doubly stochastic conditions written out entrywise
(nonnegative entries, all row sums 1, all column sums 1) and proves them from the
theorems above.

## Proof overview

1. **A stronger inequality suffices.** Let $H(M)=32\mathrm{per}(M)^2-3\mathrm{per}(MM^T)$.
   A sum-of-squares identity for permanents gives
   $\mathrm{per}(AA^T)+\mathrm{per}(A^TA)\ge 2\mathrm{per}(A^2)$ for every real
   square $A$, and
   $128p^2-3(g+h+2z)=2H(A)+2H(A^T)+3(g+h-2z)$, where $p,g,h,z$ are the four permanents.
   So it is enough to show $H\ge 0$ on $\Omega_4$, with equality only at $J_4$.
2. **Reduction to cones.** Subtract the smallest entry: $A=m\,J+x$, where $J$ is the
   all-ones matrix and $x\ge 0$ has equal line sums and a zero entry. Repeatedly
   pulling out the center of the smallest face containing $x$ (Birkhoff's theorem
   controls the supports) writes $A$ as a nonnegative combination $\sum_{k=0}^{9}t_kV_k$
   of $J$ and the centers of a chain of faces of the Birkhoff polytope, ending at a
   permutation matrix.
3. **A finite certificate.** For each such chain, $H(\sum t_kV_k)$ is a degree-8 polynomial in
   $t$. If all of its coefficients are nonnegative, then $H\ge 0$ on that cone. Using the
   576 row and column permutations, 65,376 chains suffice. For every one of them, every
   coefficient is nonnegative, and the pure powers $t_k^8$ with $k\ge1$ have strictly
   positive coefficients, which gives the equality case.
4. **Checked inside Lean.** The checker regenerates the chains, symmetry reduction and
   polynomials itself, from scratch. It is proved sound in Lean: a successful run implies
   the real-matrix statement. Running it is the only step not checked by the kernel.

[PROOF.md](PROOF.md) gives the full argument.

## Trust model

`native_decide` proves a statement of the form `f x = true` by compiling `f` to native
code and running it. The kernel then accepts the result through the axiom
`Lean.ofReduceBool`; `Lean.trustCompiler` records that the compiler, interpreter and
runtime are trusted. Mathlib does not accept `native_decide`, and external Lean
proof checkers cannot replay such proofs. Here it is used for 36 Boolean checks: the
certificate pieces, the multiplication tables, the top-level face splits and two small
index facts. [scripts/audit.py](scripts/audit.py) enforces that inventory.

Everything else is ordinary kernel-checked Lean. That covers the reduction to cones, the
Birkhoff support lemma, the symmetry argument, the polynomial arithmetic and its
evaluation, the checker's soundness, the permanent Gram inequality, and the equality and
ratio forms.

As an independent check of the finite part, [crosscheck/](crosscheck/README.md) re-implements
the certificate tree in Python and the coefficient test in C++ with 128-bit integers.
It confirms all 65,376 cones, the 10 tight coefficients per cone, and the strict pure
powers. As a negative control, it rejects all 65,376 cones when 32 is replaced by 31.
The largest integer arising anywhere is below $2^{40}$. The earlier, separate computational
proof ([original/](original/README.md)) checked the same 65,376 cone classes with
another implementation.

## Reproduce the verification

On Linux x86_64 with Bash, Git, Python 3, curl, tar, zstd and coreutils:

```sh
git clone https://github.com/cozuya/gyires-permanent-4x4.git
cd gyires-permanent-4x4
bash scripts/install-lean.sh
export PATH="$PWD/.tools/lean-4.28.0-linux/bin:$PATH"
bash scripts/fetch-deps.sh        # locked dependencies + prebuilt mathlib (about 7 GB)
./verify.sh                       # full rebuild of this project + statement/axiom audit
python3 scripts/check-package.py
bash crosscheck/run.sh            # optional: independent C++ re-check (needs g++)
```

`./verify.sh` deletes this project's build outputs, rebuilds all 41 project modules (all
certificate pieces included), then runs `lake env lean --trust=0 Verification.lean`. It
audits the printed theorem types and the exact axiom set of each of the 15 audited
declarations. On a 24-thread workstation the rebuild took 6–9 minutes (about 50–55
CPU-minutes); on a GitHub-hosted runner it takes about 50 minutes. See
[REPRODUCE.md](REPRODUCE.md) for details and resource needs.

| Component | Pinned version or revision |
| --- | --- |
| Lean | 4.28.0, `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b` |
| Lake | `5.0.0-src+7e01a1b` |
| Mathlib | v4.28.0, `8f9d9cff6bd728b17a24e163c9402775d9e6a365` |

GitHub Actions repeats the full rebuild and the cross-check on pushes, pull requests,
manual runs, and a change to public visibility. The committed [local evidence](evidence/verification.json)
identifies its sources by hash.

## Provenance

Chris Ozols directed the work. The original computer-assisted proof and its audits were
developed with AI assistants. The Lean formalization of the inequality
([RequestProject/](RequestProject), [GyiresCompute/](GyiresCompute)) was produced by
Harmonic's Aristotle. Anthropic's Claude independently rebuilt it and added the
formalized equality case and ratio form ([GyiresEquality/](GyiresEquality),
[GyiresStrictCompute/](GyiresStrictCompute)), the cross-check, and this package.
[PROVENANCE.md](PROVENANCE.md) gives dates, sources and what each record does and does
not establish.

Formal verification establishes the stated results relative to Lean and the trust model
above. It does not establish historical priority. [PRIOR_ART.md](PRIOR_ART.md) records
the literature review and its access limitations. No earlier unrestricted proof of the
4×4 case was located in the sources examined.

## Discovery and novelty-checking summary

**Search identifiers:** Gyires' permanent inequality; Béla Gyires; Cheon and
Wanless Conjecture 20; Minc's list of permanent conjectures; permanent of
doubly stochastic 4×4 matrices; Gyires n=4 proof; Lean Gyires 4x4.

**Exact scope:** The inequality and equality case for **real 4×4 doubly
stochastic matrices** are supplied here; no proof for general n is claimed.
The [Lean statements](Verification.lean), [verification report](VERIFICATION_REPORT.md),
[finite-certificate cross-check](crosscheck/README.md), and
[prior-art review](PRIOR_ART.md) enable a direct novelty check. The main
theorems rely on `native_decide` and its documented compiler trust, not
only the Lean kernel.

## License

Copyright 2026 Chris Ozols. The Lean proofs, scripts, and documentation in this
repository are licensed under the [Apache License, Version 2.0](LICENSE).
Third-party dependencies retain their respective licenses.
