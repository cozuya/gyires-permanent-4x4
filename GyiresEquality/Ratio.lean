import GyiresEquality.Equality

/-!
# Gyires' inequality in ratio form

Cheon and Wanless (2005, Conjecture 20) state Gyires' conjecture as
`4 per(A)² / (per(A A*) + per(A* A) + 2 per(A²)) ≥ n! / nⁿ` for doubly stochastic `A`,
with equality only at `Jₙ`. For real matrices `A* = Aᵀ`. The denominator is positive
because every doubly stochastic matrix has positive permanent, so this ratio form is
equivalent to the polynomial form proved in `RequestProject.Gyires` and
`GyiresEquality.Equality`.
-/

open Finset

namespace Gyires

/-- A doubly stochastic matrix has positive permanent (a consequence of Birkhoff's theorem). -/
theorem permanent_pos_of_doublyStochastic {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℝ} (hM : M ∈ doublyStochastic ℝ n) : 0 < M.permanent := by
  obtain ⟨w, hw0, hw1, hwM⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hM
  have hMe : ∀ a b, M a b = ∑ σ : Equiv.Perm n, w σ * (if σ a = b then 1 else 0) := by
    intro a b
    rw [← hwM]
    simp [Matrix.sum_apply, Equiv.toPEquiv_apply]
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm n, 0 < w σ := by
    by_contra hcon
    push_neg at hcon
    have : ∑ σ, w σ ≤ 0 := sum_nonpos fun σ _ => hcon σ
    linarith
  have hnn : ∀ a b, 0 ≤ M a b := (mem_doublyStochastic_iff_sum.mp hM).1
  have hdiag : ∀ a, 0 < M a (σ a) := by
    intro a
    have : w σ ≤ M a (σ a) := by
      rw [hMe]
      have := single_le_sum (f := fun τ : Equiv.Perm n => w τ * (if τ a = σ a then 1 else 0))
        (fun τ _ => mul_nonneg (hw0 τ) (by split_ifs <;> norm_num)) (mem_univ σ)
      simpa using this
    linarith
  unfold Matrix.permanent
  apply sum_pos'
  · intro τ _
    exact prod_nonneg fun i _ => hnn _ _
  · refine ⟨σ.symm, mem_univ _, prod_pos fun i _ => ?_⟩
    have := hdiag (σ.symm i)
    simpa using this

lemma gyires_denominator_pos (A : Matrix (Fin 4) (Fin 4) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin 4)) :
    0 < (A * A.transpose).permanent + (A.transpose * A).permanent + 2 * (A * A).permanent := by
  have hT := transpose_mem_doublyStochastic' hA
  have h1 := permanent_pos_of_doublyStochastic (Submonoid.mul_mem _ hA hT)
  have h2 := permanent_pos_of_doublyStochastic (Submonoid.mul_mem _ hT hA)
  have h3 := permanent_pos_of_doublyStochastic (Submonoid.mul_mem _ hA hA)
  linarith

/-- **Gyires' inequality (Conjecture 20 of Cheon–Wanless) for `n = 4`, ratio form.** -/
theorem gyires_4x4_ratio (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A ∈ doublyStochastic ℝ (Fin 4)) :
    ((Nat.factorial 4 : ℕ) : ℝ) / (4 : ℝ) ^ 4 ≤
      4 * A.permanent ^ 2 /
        ((A * A.transpose).permanent + (A.transpose * A).permanent + 2 * (A * A).permanent) := by
  have hD := gyires_denominator_pos A hA
  have h := gyires_4x4 A hA
  rw [le_div_iff₀ hD]
  norm_num [Nat.factorial]
  linarith

/-- **Equality in the ratio form holds exactly at `J₄`.** -/
theorem gyires_4x4_ratio_eq_iff (A : Matrix (Fin 4) (Fin 4) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin 4)) :
    4 * A.permanent ^ 2 /
        ((A * A.transpose).permanent + (A.transpose * A).permanent + 2 * (A * A).permanent) =
      ((Nat.factorial 4 : ℕ) : ℝ) / (4 : ℝ) ^ 4 ↔ A = Matrix.of fun _ _ => (1 / 4 : ℝ) := by
  have hD := gyires_denominator_pos A hA
  rw [← gyires_4x4_eq_iff A hA, div_eq_iff hD.ne']
  norm_num [Nat.factorial]
  constructor <;> intro h <;> linarith

end Gyires
