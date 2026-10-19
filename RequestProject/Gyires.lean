import RequestProject.Cert.Assemble
import RequestProject.Reduction

/-!
# Gyires' permanent inequality for `4 × 4` doubly stochastic matrices

For every real doubly stochastic `4 × 4` matrix `A`,
`128 per(A)² ≥ 3 [per(A Aᵀ) + per(Aᵀ A) + 2 per(A²)]`.

The proof goes through the stronger inequality `32 per(A)² ≥ 3 per(A Aᵀ)`, which is
established by a computer-checked cone-covering certificate, together with the inequality
`per(M Mᵀ) + per(N Nᵀ) ≥ 2 per(M Nᵀ)` valid for all real square matrices.
-/

open Finset

namespace Gyires

lemma maskF_testBit : ∀ i j : Fin 4,
    maskF.testBit (4 * i.val + j.val) = !(decide (i = 0) && decide (j = 0)) := by
  decide

lemma toR_allOnes (i j : Fin 4) : toR allOnes i j = 1 := by
  simp only [toR, allOnes]
  rw [getElem!_pos _ _ (by simp; omega)]
  simp

lemma combR_allOnes (t : Fin NV → ℝ) (i j : Fin 4) :
    combR [allOnes] t i j = t ⟨0, by decide⟩ := by
  simp only [combR]
  rw [sum_eq_single ⟨0, by decide⟩]
  · simp [toR_allOnes]
  · intro k _ hk
    have hk' : 1 ≤ k.val := by
      rcases Nat.eq_zero_or_pos k.val with h | h
      · exact absurd (Fin.ext h) hk
      · exact h
    rw [List.getD_eq_default _ _ (by simpa using hk'), toR_zeroMat]
    simp
  · simp

/-- The stronger inequality `(1)`: `3 per(A Aᵀ) ≤ 32 per(A)²` for doubly stochastic `A`. -/
theorem permanent_gram_le (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A ∈ doublyStochastic ℝ (Fin 4)) :
    3 * (A * A.transpose).permanent ≤ 32 * A.permanent ^ 2 := by
  suffices 0 ≤ Hf A by unfold Hf at this; linarith
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
  have h := face_root (fun k => if k.val = 0 then m else 0)
    (fun k => by dsimp only; split_ifs <;> simp [hm0]) x hxK
  have heq : combR [allOnes] (fun k => if k.val = 0 then m else 0) + x = B := by
    ext i j
    simp [combR_allOnes, hx]
  rwa [heq] at h

lemma transpose_mem_doublyStochastic' {A : Matrix (Fin 4) (Fin 4) ℝ}
    (hA : A ∈ doublyStochastic ℝ (Fin 4)) : A.transpose ∈ doublyStochastic ℝ (Fin 4) := by
  obtain ⟨hnn, hr, hc⟩ := mem_doublyStochastic_iff_sum.mp hA
  exact mem_doublyStochastic_iff_sum.mpr ⟨fun i j => hnn j i, hc, hr⟩

/-- **Gyires' inequality for `4 × 4` matrices.** For every real doubly stochastic `4 × 4`
matrix `A`, `128 per(A)² ≥ 3 [per(A Aᵀ) + per(Aᵀ A) + 2 per(A²)]`. -/
theorem gyires_4x4 (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A ∈ doublyStochastic ℝ (Fin 4)) :
    3 * ((A * A.transpose).permanent + (A.transpose * A).permanent + 2 * (A * A).permanent) ≤
      128 * A.permanent ^ 2 := by
  have h1 := permanent_gram_le A hA
  have h2 := permanent_gram_le A.transpose (transpose_mem_doublyStochastic' hA)
  have h3 := permanent_gram_add_ge A A.transpose
  simp only [Matrix.transpose_transpose, Matrix.permanent_transpose] at h2 h3
  linarith

end Gyires
