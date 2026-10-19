import RequestProject.Gyires
import GyiresEquality.Assemble

/-!
# The equality case of Gyires' inequality for `4 × 4` matrices

For a real doubly stochastic `4 × 4` matrix `A`, the stronger inequality
`3 per(A Aᵀ) ≤ 32 per(A)²` is strict unless every entry of `A` is `1/4`. Consequently
equality holds in Gyires' inequality exactly at the uniform matrix `J₄`.
-/

open Finset

namespace Gyires

/-- The stronger inequality is strict away from the uniform matrix. -/
theorem permanent_gram_lt (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A ∈ doublyStochastic ℝ (Fin 4))
    (hJ : A ≠ Matrix.of fun _ _ => (1 / 4 : ℝ)) :
    3 * (A * A.transpose).permanent < 32 * A.permanent ^ 2 := by
  suffices 0 < Hf A by unfold Hf at this; linarith
  obtain ⟨hnn, hr, hc⟩ := mem_doublyStochastic_iff_sum.mp hA
  obtain ⟨⟨i0, j0⟩, -, hmin⟩ :=
    exists_min_image (univ : Finset (Fin 4 × Fin 4)) (fun p => A p.1 p.2) univ_nonempty
  set ρ := Equiv.swap (0 : Fin 4) i0
  set γ := Equiv.swap (0 : Fin 4) j0
  set B := A.submatrix ρ γ with hB
  rw [← Hf_submatrix A ρ γ]
  set m := A i0 j0 with hm
  set x : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun i j => B i j - m with hx
  have hxK : InK maskF x := by
    refine ⟨fun i j => ?_, ⟨1 - 4 * m, fun i => ?_, fun j => ?_⟩, fun i j hb => ?_⟩
    · simp only [hx, hB, Matrix.of_apply, Matrix.submatrix_apply, sub_nonneg]
      exact hmin (ρ i, γ j) (mem_univ _)
    · simp only [hx, hB, Matrix.of_apply, Matrix.submatrix_apply]
      rw [sum_sub_distrib, Equiv.sum_comp γ (fun j => A (ρ i) j), hr]
      simp
    · simp only [hx, hB, Matrix.of_apply, Matrix.submatrix_apply]
      rw [sum_sub_distrib, Equiv.sum_comp ρ (fun i => A i (γ j)), hc]
      simp
    · rw [maskF_testBit] at hb
      simp only [Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      simp [hx, hB, ρ, γ, hm]
  have hm0 : 0 ≤ m := hnn _ _
  -- `x = 0` would force `A` to be constant, hence uniform
  have hx0 : x ≠ 0 := by
    intro h0
    apply hJ
    have hAm : ∀ i j, A i j = m := by
      intro i j
      have := congrFun (congrFun h0 (ρ i)) (γ j)
      simp only [hx, hB, Matrix.of_apply, Matrix.submatrix_apply, Matrix.zero_apply,
        sub_eq_zero] at this
      simpa [ρ, γ, Equiv.swap_apply_self] using this
    have h4 : 4 * m = 1 := by
      have := hr 0
      simp only [Fin.sum_univ_four, hAm] at this
      linarith
    ext i j
    simp only [Matrix.of_apply, hAm]
    linarith
  have h := face_rootS (fun k => if k.val = 0 then m else 0)
    (fun k => by dsimp only; split_ifs <;> simp [hm0]) x hxK (Or.inl hx0)
  have heq : combR [allOnes] (fun k => if k.val = 0 then m else 0) + x = B := by
    ext i j
    simp [combR_allOnes, hx]
  rwa [heq] at h

/-- **Gyires' inequality is strict away from `J₄`.** -/
theorem gyires_4x4_strict (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A ∈ doublyStochastic ℝ (Fin 4))
    (hJ : A ≠ Matrix.of fun _ _ => (1 / 4 : ℝ)) :
    3 * ((A * A.transpose).permanent + (A.transpose * A).permanent + 2 * (A * A).permanent) <
      128 * A.permanent ^ 2 := by
  have h1 := permanent_gram_lt A hA hJ
  have h2 := permanent_gram_le A.transpose (transpose_mem_doublyStochastic' hA)
  have h3 := permanent_gram_add_ge A A.transpose
  simp only [Matrix.transpose_transpose, Matrix.permanent_transpose] at h2 h3
  linarith

/-- **Equality case of Gyires' inequality for `4 × 4` matrices.** For a real doubly
stochastic `4 × 4` matrix `A`, equality holds exactly when every entry of `A` is `1/4`. -/
theorem gyires_4x4_eq_iff (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A ∈ doublyStochastic ℝ (Fin 4)) :
    3 * ((A * A.transpose).permanent + (A.transpose * A).permanent + 2 * (A * A).permanent) =
      128 * A.permanent ^ 2 ↔ A = Matrix.of fun _ _ => (1 / 4 : ℝ) := by
  constructor
  · intro heq
    by_contra hJ
    have := gyires_4x4_strict A hA hJ
    linarith
  · rintro rfl
    set U : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun _ _ => (1 / 4 : ℝ) with hU
    have hT : U.transpose = U := by
      ext i j
      simp [hU]
    have hUU : U * U = U := by
      ext i j
      simp [hU, Matrix.mul_apply]
    have hp : U.permanent = 3 / 32 := by
      rw [permanent_eq_laplaceN]
      simp [hU, laplaceN]
      norm_num
    rw [hT, hUU, hp]
    norm_num

end Gyires
