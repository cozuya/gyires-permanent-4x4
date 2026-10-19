import RequestProject.Gyires
import GyiresEquality.Ratio

/-!
# Independent restatement of the verified results

Each statement below is written with Mathlib's `Matrix.permanent`, ordinary matrix products
and transposes, and the doubly stochastic conditions spelled out entrywise (nonnegative
entries, every row sum and every column sum equal to `1`). Each is proved directly from
the project's theorems, with no further hypotheses. `verify.sh` checks the printed types
and transitive axioms below.
-/

open Finset

set_option autoImplicit false

namespace GyiresVerification

/-- Gyires' inequality for every real doubly stochastic `4 × 4` matrix. -/
theorem inequality (A : Matrix (Fin 4) (Fin 4) ℝ)
    (nonneg : ∀ i j, 0 ≤ A i j) (rows : ∀ i, ∑ j, A i j = 1) (cols : ∀ j, ∑ i, A i j = 1) :
    3 * ((A * A.transpose).permanent + (A.transpose * A).permanent + 2 * (A * A).permanent) ≤
      128 * A.permanent ^ 2 :=
  Gyires.gyires_4x4 A (mem_doublyStochastic_iff_sum.mpr ⟨nonneg, rows, cols⟩)

/-- Equality holds exactly when every entry is `1/4`. -/
theorem equality_iff (A : Matrix (Fin 4) (Fin 4) ℝ)
    (nonneg : ∀ i j, 0 ≤ A i j) (rows : ∀ i, ∑ j, A i j = 1) (cols : ∀ j, ∑ i, A i j = 1) :
    3 * ((A * A.transpose).permanent + (A.transpose * A).permanent + 2 * (A * A).permanent) =
      128 * A.permanent ^ 2 ↔ ∀ i j, A i j = 1 / 4 := by
  rw [Gyires.gyires_4x4_eq_iff A (mem_doublyStochastic_iff_sum.mpr ⟨nonneg, rows, cols⟩)]
  constructor
  · rintro rfl i j
    rfl
  · intro h
    ext i j
    exact h i j

/-- The ratio form of Cheon–Wanless Conjecture 20 for `n = 4`: `4 per(A)² / D ≥ 4!/4⁴`. -/
theorem ratio (A : Matrix (Fin 4) (Fin 4) ℝ)
    (nonneg : ∀ i j, 0 ≤ A i j) (rows : ∀ i, ∑ j, A i j = 1) (cols : ∀ j, ∑ i, A i j = 1) :
    ((Nat.factorial 4 : ℕ) : ℝ) / (4 : ℝ) ^ 4 ≤
      4 * A.permanent ^ 2 /
        ((A * A.transpose).permanent + (A.transpose * A).permanent + 2 * (A * A).permanent) :=
  Gyires.gyires_4x4_ratio A (mem_doublyStochastic_iff_sum.mpr ⟨nonneg, rows, cols⟩)

/-- The denominator of the ratio form is positive. -/
theorem denominator_pos (A : Matrix (Fin 4) (Fin 4) ℝ)
    (nonneg : ∀ i j, 0 ≤ A i j) (rows : ∀ i, ∑ j, A i j = 1) (cols : ∀ j, ∑ i, A i j = 1) :
    0 < (A * A.transpose).permanent + (A.transpose * A).permanent + 2 * (A * A).permanent :=
  Gyires.gyires_denominator_pos A (mem_doublyStochastic_iff_sum.mpr ⟨nonneg, rows, cols⟩)

/-- Equality in the ratio form holds exactly when every entry is `1/4`. -/
theorem ratio_equality_iff (A : Matrix (Fin 4) (Fin 4) ℝ)
    (nonneg : ∀ i j, 0 ≤ A i j) (rows : ∀ i, ∑ j, A i j = 1) (cols : ∀ j, ∑ i, A i j = 1) :
    4 * A.permanent ^ 2 /
        ((A * A.transpose).permanent + (A.transpose * A).permanent + 2 * (A * A).permanent) =
      ((Nat.factorial 4 : ℕ) : ℝ) / (4 : ℝ) ^ 4 ↔ ∀ i j, A i j = 1 / 4 := by
  rw [Gyires.gyires_4x4_ratio_eq_iff A (mem_doublyStochastic_iff_sum.mpr ⟨nonneg, rows, cols⟩)]
  constructor
  · rintro rfl i j
    rfl
  · intro h
    ext i j
    exact h i j

/-- The stronger inequality `3 per(A Aᵀ) ≤ 32 per(A)²`. -/
theorem stronger (A : Matrix (Fin 4) (Fin 4) ℝ)
    (nonneg : ∀ i j, 0 ≤ A i j) (rows : ∀ i, ∑ j, A i j = 1) (cols : ∀ j, ∑ i, A i j = 1) :
    3 * (A * A.transpose).permanent ≤ 32 * A.permanent ^ 2 :=
  Gyires.permanent_gram_le A (mem_doublyStochastic_iff_sum.mpr ⟨nonneg, rows, cols⟩)

/-- The permanent Gram comparison, for real square matrices of every size. -/
theorem gram_comparison (n : ℕ) (M N : Matrix (Fin n) (Fin n) ℝ) :
    2 * (M * N.transpose).permanent ≤
      (M * M.transpose).permanent + (N * N.transpose).permanent :=
  Gyires.permanent_gram_add_ge M N

end GyiresVerification

set_option format.width 120
#check @Gyires.gyires_4x4
#print axioms Gyires.gyires_4x4
#check @Gyires.permanent_gram_le
#print axioms Gyires.permanent_gram_le
#check @Gyires.permanent_gram_add_ge
#print axioms Gyires.permanent_gram_add_ge
#check @Gyires.permanent_gram_lt
#print axioms Gyires.permanent_gram_lt
#check @Gyires.gyires_4x4_strict
#print axioms Gyires.gyires_4x4_strict
#check @Gyires.gyires_4x4_eq_iff
#print axioms Gyires.gyires_4x4_eq_iff
#check @Gyires.gyires_4x4_ratio
#print axioms Gyires.gyires_4x4_ratio
#check @Gyires.gyires_4x4_ratio_eq_iff
#print axioms Gyires.gyires_4x4_ratio_eq_iff
#check @GyiresVerification.inequality
#print axioms GyiresVerification.inequality
#check @GyiresVerification.equality_iff
#print axioms GyiresVerification.equality_iff
#check @GyiresVerification.ratio
#print axioms GyiresVerification.ratio
#check @GyiresVerification.denominator_pos
#print axioms GyiresVerification.denominator_pos
#check @GyiresVerification.ratio_equality_iff
#print axioms GyiresVerification.ratio_equality_iff
#check @GyiresVerification.stronger
#print axioms GyiresVerification.stronger
#check @GyiresVerification.gram_comparison
#print axioms GyiresVerification.gram_comparison
