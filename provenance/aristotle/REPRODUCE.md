# Reproducing the Lean proof of Gyires' inequality for 4×4 matrices

## Contents

| File | Role |
| --- | --- |
| `lean-toolchain` | Lean version (`leanprover/lean4:v4.28.0`) |
| `lakefile.toml` | Lake configuration (libraries `RequestProject` and `GyiresCompute`) |
| `lake-manifest.json` | Pinned dependencies (Mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365` and its transitive git dependencies; there are no local/path dependencies) |
| `GyiresCompute/Basic.lean` | Executable certificate checker (`checkNode`, `splitCheck`, polynomial arithmetic, symmetry group) |
| `RequestProject/PolySound.lean` | Soundness of the polynomial evaluation |
| `RequestProject/HEval.lean` | Evaluation of the polynomial `H` on cone combinations |
| `RequestProject/Faces.lean` | Face covering of the doubly stochastic polytope |
| `RequestProject/TreeSound.lean` | Soundness of the certificate-tree checker (`checkNode_sound`, `splitCheck_sound`) |
| `RequestProject/Cert/Defs.lean` | Data for splitting the certificate into pieces |
| `RequestProject/Cert/C_*.lean` (13 files) | The certificate pieces, each one `native_decide` call |
| `RequestProject/Cert/Assemble.lean` | Assembles the pieces into `face_root` |
| `RequestProject/Reduction.lean` | `per(M Mᵀ) + per(N Nᵀ) ≥ 2 per(M Nᵀ)` |
| `RequestProject/Gyires.lean` | The final theorems `permanent_gram_le` and `gyires_4x4` |
| `RequestProject/Main.lean` | Template file (options only, not imported by the proof) |
| `scripts/PrintAxioms.lean` | Prints the axioms of the final theorems |

The certificate data is not stored as a separate file: each `C_*.lean` piece asks the
checker to regenerate and check its subtree, so no external generator or data file is needed.

## Build commands

Requires [elan](https://github.com/leanprover/elan) and git.

```sh
tar xzf gyires-lean-complete.tar.gz
cd gyires-lean-complete
lake exe cache get          # optional: downloads prebuilt Mathlib oleans
lake build RequestProject GyiresCompute
lake env lean scripts/PrintAxioms.lean
```

On the machine used for the export (several cores) the full project build took about
7 minutes of wall-clock time once Mathlib was available; the slowest certificate piece
took about 6 minutes on its own.

## The final theorem

```lean
theorem gyires_4x4 (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A ∈ doublyStochastic ℝ (Fin 4)) :
    3 * ((A * A.transpose).permanent + (A.transpose * A).permanent + 2 * (A * A).permanent) ≤
      128 * A.permanent ^ 2
```

## Actual `#print axioms` output

Output of `lake env lean scripts/PrintAxioms.lean`, from the export build:

```
'Gyires.gyires_4x4' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]
'Gyires.permanent_gram_le' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Lean.trustCompiler,
 Quot.sound]
```

Trust model: `Lean.ofReduceBool` and `Lean.trustCompiler` come from `native_decide`, which
is used for the certificate pieces and the splitting checks. The result therefore also
trusts the Lean compiler and runtime that evaluate the checker, not only the kernel. The
project contains no `sorry`, no user-declared `axiom` and no `@[implemented_by]`.

## Equality case: inequality only

Only the **inequality** is formalized. The equality characterization (equality exactly
when every entry of `A` is `1/4`) is **not** formalized in Lean. It is argued only in
prose in `RESULTS.md`, section 4.
