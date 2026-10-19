import RequestProject.HEval

/-!
# Faces of the Birkhoff polytope, symmetries, and the support lemma

`InK S x` says that `x` is a nonnegative 4×4 matrix with all line sums equal and support
inside the 16-bit mask `S` (bit `4i+j` stands for the entry `(i,j)`).
-/

open Finset

namespace Gyires

/-- Nonnegative matrices with equal row and column sums, supported in the mask `S`. -/
def InK (S : ℕ) (x : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  (∀ i j, 0 ≤ x i j) ∧ (∃ c : ℝ, (∀ i, ∑ j, x i j = c) ∧ (∀ j, ∑ i, x i j = c)) ∧
    (∀ i j, S.testBit (4 * i.val + j.val) = false → x i j = 0)

lemma subMask_testBit {a b : ℕ} (h : subMask a b = true) {e : ℕ} (he : a.testBit e = true) :
    b.testBit e = true := by
  simp only [subMask, beq_iff_eq] at h
  rw [← h, Nat.testBit_and] at he
  simp only [Bool.and_eq_true] at he
  exact he.2

lemma InK.mono {S T : ℕ} {x : Matrix (Fin 4) (Fin 4) ℝ} (hx : InK S x) (h : subMask S T = true) :
    InK T x := by
  refine ⟨hx.1, hx.2.1, fun i j hT => hx.2.2 i j ?_⟩
  by_contra hS
  simp only [Bool.not_eq_false] at hS
  rw [subMask_testBit h hS] at hT
  exact Bool.noConfusion hT

/-! ## Permutations as lists -/

/-- A list read as a function `Fin 4 → Fin 4`. -/
def fpl (p : List ℕ) : Fin 4 → Fin 4 := fun i => ⟨p.getD i.val 0 % 4, Nat.mod_lt _ (by norm_num)⟩

lemma permList_lt : ∀ p ∈ permList, ∀ i : Fin 4, p.getD i.val 0 < 4 := by decide

lemma fpl_val {p : List ℕ} (hp : p ∈ permList) (i : Fin 4) : (fpl p i).val = p.getD i.val 0 :=
  Nat.mod_eq_of_lt (permList_lt p hp i)

lemma fpl_injective : ∀ p ∈ permList, Function.Injective (fpl p) := by decide

lemma fpl_bijective {p : List ℕ} (hp : p ∈ permList) : Function.Bijective (fpl p) :=
  (Finite.injective_iff_bijective).mp (fpl_injective p hp)

/-- The permutation encoded by `p ∈ permList`. -/
noncomputable def toPerm {p : List ℕ} (hp : p ∈ permList) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (fpl p) (fpl_bijective hp)

lemma toPerm_apply {p : List ℕ} (hp : p ∈ permList) (i : Fin 4) :
    ((toPerm hp i : Fin 4) : ℕ) = p.getD i.val 0 := by
  simp [toPerm, fpl_val hp]

lemma mem_permList_of_distinct :
    ∀ a b c d : Fin 4, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      [a.val, b.val, c.val, d.val] ∈ permList := by decide

lemma permMask_testBit : ∀ p ∈ permList, ∀ i j : Fin 4,
    (permMask p).testBit (4 * i.val + j.val) = decide (p.getD i.val 0 = j.val) := by decide

lemma permMask_lt : ∀ p ∈ permList, permMask p < 2 ^ 16 := by decide

/-- Bits above `16` are irrelevant: a mask below `2^16` is determined by bits `4i+j`. -/
lemma testBit_of_lt {a : ℕ} (ha : a < 2 ^ 16) {e : ℕ} (he : 16 ≤ e) : a.testBit e = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) he))

lemma subMask_of_bits {a b : ℕ} (ha : a < 2 ^ 16)
    (h : ∀ i j : Fin 4, a.testBit (4 * i.val + j.val) = true →
      b.testBit (4 * i.val + j.val) = true) : subMask a b = true := by
  simp only [subMask, beq_iff_eq]
  apply Nat.eq_of_testBit_eq
  intro e
  rw [Nat.testBit_and]
  by_cases he : e < 16
  · have : e = 4 * (⟨e / 4, by omega⟩ : Fin 4).val + (⟨e % 4, by omega⟩ : Fin 4).val := by
      simp; omega
    rw [this]
    cases hb : a.testBit (4 * (⟨e / 4, by omega⟩ : Fin 4).val + (⟨e % 4, by omega⟩ : Fin 4).val)
    · simp
    · simp [h _ _ hb]
  · have h16 := testBit_of_lt ha (show 16 ≤ e by omega)
    simp [h16]

lemma closureOf_testBit_of_mem {ps : List (List ℕ)} {p : List ℕ} (hp : p ∈ ps) {e : ℕ}
    (he : (permMask p).testBit e = true) : (closureOf ps).testBit e = true := by
  unfold closureOf
  suffices ∀ (acc : ℕ) (l : List (List ℕ)), (acc.testBit e = true ∨ ∃ q ∈ l,
      (permMask q).testBit e = true) →
      (l.foldl (fun acc p => acc ||| permMask p) acc).testBit e = true from
    this 0 ps (Or.inr ⟨p, hp, he⟩)
  intro acc l
  induction l generalizing acc with
  | nil => simp
  | cons q l ih =>
    intro h
    simp only [List.foldl_cons]
    apply ih
    rcases h with h | ⟨q', hq', h'⟩
    · left; simp [Nat.testBit_or, h]
    · simp only [List.mem_cons] at hq'
      rcases hq' with rfl | hq'
      · left; simp [Nat.testBit_or, h']
      · right; exact ⟨q', hq', h'⟩

lemma mem_of_closureOf_testBit {ps : List (List ℕ)} {e : ℕ}
    (he : (closureOf ps).testBit e = true) : ∃ p ∈ ps, (permMask p).testBit e = true := by
  unfold closureOf at he
  suffices ∀ (acc : ℕ) (l : List (List ℕ)),
      (l.foldl (fun acc p => acc ||| permMask p) acc).testBit e = true →
      acc.testBit e = true ∨ ∃ q ∈ l, (permMask q).testBit e = true by
    rcases this 0 ps he with h | h
    · simp at h
    · exact h
  intro acc l
  induction l generalizing acc with
  | nil => simp
  | cons q l ih =>
    intro h
    simp only [List.foldl_cons] at h
    rcases ih _ h with h | ⟨q', hq', h'⟩
    · rw [Nat.testBit_or] at h
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨q, by simp, h⟩
    · exact Or.inr ⟨q', by simp [hq'], h'⟩

lemma mem_permsIn {S : ℕ} {p : List ℕ} : p ∈ permsIn S ↔ p ∈ permList ∧ subMask (permMask p) S :=
  by simp [permsIn]

/-! ## The support lemma (via Birkhoff's theorem) -/

lemma InK.exists_perm {S : ℕ} {x : Matrix (Fin 4) (Fin 4) ℝ} (hx : InK S x) {i j : Fin 4}
    (hij : x i j ≠ 0) : ∃ p ∈ permsIn S, (permMask p).testBit (4 * i.val + j.val) = true := by
  obtain ⟨hnn, ⟨c, hr, hc⟩, hs⟩ := hx
  have hpos : 0 < x i j := lt_of_le_of_ne (hnn i j) (Ne.symm hij)
  have hcpos : 0 < c := by
    rw [← hr i]
    exact lt_of_lt_of_le hpos (single_le_sum (fun j _ => hnn i j) (mem_univ j))
  set M : Matrix (Fin 4) (Fin 4) ℝ := c⁻¹ • x with hM
  have hMds : M ∈ doublyStochastic ℝ (Fin 4) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun a b => ?_, fun a => ?_, fun b => ?_⟩
    · simp only [hM, Matrix.smul_apply, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.mpr hcpos.le) (hnn a b)
    · simp only [hM, Matrix.smul_apply, smul_eq_mul, ← mul_sum, hr a]
      field_simp
    · simp only [hM, Matrix.smul_apply, smul_eq_mul, ← mul_sum, hc b]
      field_simp
  obtain ⟨w, hw0, -, hwM⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hMds
  have hMe : ∀ a b, M a b = ∑ σ : Equiv.Perm (Fin 4), w σ * (if σ a = b then 1 else 0) := by
    intro a b
    rw [← hwM]
    simp [Matrix.sum_apply, Equiv.toPEquiv_apply]
  have hMij : 0 < M i j := by
    simp only [hM, Matrix.smul_apply, smul_eq_mul]
    exact mul_pos (inv_pos.mpr hcpos) hpos
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin 4), 0 < w σ * (if σ i = j then 1 else 0) := by
    by_contra hcon
    push_neg at hcon
    have : M i j ≤ 0 := by rw [hMe]; exact sum_nonpos fun σ _ => hcon σ
    linarith
  have hσij : σ i = j := by
    by_contra hne
    simp [hne] at hσ
  have hwσ : 0 < w σ := by simpa [hσij] using hσ
  -- every entry of σ is in the support
  have hsupp : ∀ a : Fin 4, S.testBit (4 * a.val + (σ a).val) = true := by
    intro a
    by_contra hb
    simp only [Bool.not_eq_true] at hb
    have hx0 := hs a (σ a) hb
    have : w σ ≤ M a (σ a) := by
      rw [hMe]
      have := single_le_sum (f := fun τ : Equiv.Perm (Fin 4) => w τ * (if τ a = σ a then 1 else 0))
        (fun τ _ => mul_nonneg (hw0 τ) (by split_ifs <;> norm_num)) (mem_univ σ)
      simpa using this
    have : M a (σ a) = 0 := by simp [hM, hx0]
    linarith
  refine ⟨[(σ 0).val, (σ 1).val, (σ 2).val, (σ 3).val], ?_, ?_⟩
  · have hmem := mem_permList_of_distinct (σ 0) (σ 1) (σ 2) (σ 3)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    rw [mem_permsIn]
    refine ⟨hmem, subMask_of_bits (permMask_lt _ hmem) fun a b hab => ?_⟩
    rw [permMask_testBit _ hmem] at hab
    simp only [decide_eq_true_eq] at hab
    have : (σ a).val = b.val := by
      fin_cases a <;> simpa using hab
    rw [← Fin.ext this]
    exact hsupp a
  · have hmem := mem_permList_of_distinct (σ 0) (σ 1) (σ 2) (σ 3)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    rw [permMask_testBit _ hmem]
    simp only [decide_eq_true_eq]
    subst hσij
    fin_cases i <;> simp

/-- Support lemma: a matrix in `InK S` is supported in the closure of `S`. -/
lemma InK.closure {S : ℕ} {x : Matrix (Fin 4) (Fin 4) ℝ} (hx : InK S x) :
    InK (closureOf (permsIn S)) x := by
  refine ⟨hx.1, hx.2.1, fun i j hb => ?_⟩
  by_contra hne
  obtain ⟨p, hp, hpb⟩ := hx.exists_perm hne
  rw [closureOf_testBit_of_mem hp hpb] at hb
  exact Bool.noConfusion hb

/-! ## Symmetries -/

/-- `Hf` is invariant under independent row and column permutations. -/
lemma Hf_submatrix (M : Matrix (Fin 4) (Fin 4) ℝ) (σ τ : Equiv.Perm (Fin 4)) :
    Hf (M.submatrix σ τ) = Hf M := by
  unfold Hf
  have h1 : (M.submatrix σ τ).permanent = M.permanent := by
    have : M.submatrix σ τ = (M.submatrix σ id).submatrix id τ := rfl
    rw [this, Matrix.permanent_permute_rows, Matrix.permanent_permute_cols]
  have h2 : M.submatrix σ τ * (M.submatrix σ τ).transpose = (M * M.transpose).submatrix σ σ := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply]
    exact Equiv.sum_comp τ (fun k => M (σ a) k * M (σ b) k)
  have h3 : ((M * M.transpose).submatrix σ σ).permanent = (M * M.transpose).permanent := by
    have : (M * M.transpose).submatrix σ σ = ((M * M.transpose).submatrix σ id).submatrix id σ :=
      rfl
    rw [this, Matrix.permanent_permute_rows, Matrix.permanent_permute_cols]
  rw [h1, h2, h3]

end Gyires
