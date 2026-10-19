# Independent cross-check of the finite certificate

The Lean proof evaluates its certificate with `native_decide`, so a bug in the Lean
compiler or runtime could in principle make a false certificate pass. This folder checks
the same finite claim with separately written code that shares no implementation with
the Lean checker.

- [tree.py](tree.py) re-implements the certificate tree of
  [GyiresCompute/Basic.lean](../GyiresCompute/Basic.lean) in Python: face closures,
  centers, facet candidates, stabilizers, and the split used in
  [Cert/Assemble.lean](../RequestProject/Cert/Assemble.lean). It checks the structural
  conditions the Lean checker checks, counts the leaf cones, and writes each leaf's ten
  generator matrices.
- [leafcheck.cpp](leafcheck.cpp) computes, for every leaf and with exact unsigned
  128-bit integers, all 24,310 degree-8 coefficients of $32\mathrm{per}(M)^2$ and
  $3\mathrm{per}(MM^T)$, where $M=\sum_k t_kV_k$. It reports:
  - any negative coefficient of $H$;
  - the set of tight coefficients;
  - strictness of the pure powers $t_k^8$, $k\ge1$;
  - the smallest ratio and the largest coefficient.

  On a sample of leaves, a self-test compares the polynomials with directly computed
  permanents.
- [run.sh](run.sh) runs both with the constant 32, then again with 31 as a negative
  control, which must fail.

Run it with `bash crosscheck/run.sh`. It takes about two minutes on 8 threads and
needs Python 3 and a C++ compiler with OpenMP. Output from October 19, 2026:
[evidence/crosscheck.log](../evidence/crosscheck.log).

## Result

| Quantity | Value |
| --- | --- |
| Leaf cones | 65,376, each with ten generators ending at a permutation matrix |
| Leaves with a negative coefficient | 0 |
| Tight coefficients per leaf | exactly 10: $t_0^8$ and $t_0^7t_k$, $k=1,\dots,9$ |
| Leaves with a non-strict pure power $t_k^8$, $k\ge1$ | 0 |
| Smallest ratio $32[\mathrm{per}^2]_\alpha / 3[\mathrm{per}(MM^T)]_\alpha$ over non-tight coefficients | $190/189\approx1.00529$ |
| Largest coefficient | $7.45\times10^{11}$ (40 bits) |
| Negative control (31 in place of 32) | all 65,376 leaves rejected |

The largest value is far below $2^{63}$. The Lean checker's natural-number arithmetic on
this certificate therefore stays in machine-word range and never needs big-integer (GMP)
arithmetic.

This is ordinary software evidence: it reduces the risk that a compiler fault produced
the Lean result, but it is not itself a proof. The [original computational
proof](../original/README.md) checked the same 65,376 orbit classes with a third,
independent implementation, using differently scaled generators.
