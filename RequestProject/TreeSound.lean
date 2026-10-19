import RequestProject.Faces

/-!
# Soundness of the recursive cone-covering certificate

`FaceState pre S` asserts that `Hf (∑ tₖ preₖ + x) ≥ 0` for all nonnegative weights `t`
and all `x ∈ InK S`. The checker `checkNode` establishes such statements by pulling
from face centers (stellar subdivision), using symmetries, and the polynomial leaf test.
-/

open Finset

namespace Gyires

/-- Face-state semantics of a node of the certificate tree. -/
def FaceState (pre : List Mat) (S : ℕ) : Prop :=
  ∀ t : Fin NV → ℝ, (∀ k, 0 ≤ t k) → ∀ x, InK S x → 0 ≤ Hf (combR pre t + x)

lemma toR_zeroMat : toR zeroMat = 0 := by
  ext i j
  simp only [toR, zeroMat, Matrix.zero_apply, Nat.cast_eq_zero]
  by_cases h : 4 * i.val + j.val < 16
  · simp [getElem!_pos, h]
  · simp [getElem!_neg, h]

lemma getD_append_singleton (pre : List Mat) (V : Mat) (k : ℕ) :
    (pre ++ [V]).getD k zeroMat =
      if k < pre.length then pre.getD k zeroMat else if k = pre.length then V else zeroMat := by
  split_ifs with h1 h2
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  · subst h2; simp [List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_default _ _ (by simp; omega)]

lemma combR_append (pre : List Mat) (V : Mat) (hℓ : pre.length < NV) (t : Fin NV → ℝ) (τ : ℝ) :
    combR (pre ++ [V]) (Function.update t ⟨pre.length, hℓ⟩ τ) = combR pre t + τ • toR V := by
  ext i j
  simp only [combR, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have key : ∀ k : Fin NV, Function.update t ⟨pre.length, hℓ⟩ τ k *
      toR ((pre ++ [V]).getD k.val zeroMat) i j =
      t k * toR (pre.getD k.val zeroMat) i j +
        if k = ⟨pre.length, hℓ⟩ then τ * toR V i j else 0 := by
    intro k
    rw [getD_append_singleton]
    by_cases h1 : k.val < pre.length
    · have hne : k ≠ ⟨pre.length, hℓ⟩ := fun h => by rw [h] at h1; exact lt_irrefl _ h1
      simp [h1, hne]
    · have hpre : pre.getD k.val zeroMat = zeroMat := List.getD_eq_default _ _ (by omega)
      by_cases h2 : k = ⟨pre.length, hℓ⟩
      · subst h2; simp [toR_zeroMat]
      · have h2' : k.val ≠ pre.length := fun h => h2 (Fin.ext h)
        simp [h1, h2, h2', toR_zeroMat]
  rw [sum_congr rfl fun k _ => key k, sum_add_distrib, sum_ite_eq']
  simp

/-! ## Symmetries -/

lemma mem_symList {g : Sym} (hg : g ∈ symList) : g.1 ∈ permList ∧ g.2 ∈ permList := by
  simp only [symList, List.mem_flatMap, List.mem_map] at hg
  obtain ⟨r, hr, c, hc, rfl⟩ := hg
  exact ⟨hr, hc⟩

lemma symIdx_eq {g : Sym} (hg : g ∈ symList) (i j : Fin 4) :
    symIdx g (4 * i.val + j.val) =
      4 * (toPerm (mem_symList hg).1 i).val + (toPerm (mem_symList hg).2 j).val := by
  rw [toPerm_apply, toPerm_apply, symIdx]
  congr 2
  · congr 1; omega
  · omega

lemma toR_fixed {g : Sym} (hg : g ∈ symList) {V : Mat} (hV : fixesMat g V = true) (i j : Fin 4) :
    toR V (toPerm (mem_symList hg).1 i) (toPerm (mem_symList hg).2 j) = toR V i j := by
  simp only [fixesMat, List.all_eq_true, List.mem_range, beq_iff_eq] at hV
  have := hV (4 * i.val + j.val) (by omega)
  rw [symIdx_eq hg] at this
  simp only [toR]
  rw [this]

lemma combR_fixed {g : Sym} (hg : g ∈ symList) {pre : List Mat}
    (hpre : ∀ v ∈ pre, fixesMat g v = true) (t : Fin NV → ℝ) (i j : Fin 4) :
    combR pre t (toPerm (mem_symList hg).1 i) (toPerm (mem_symList hg).2 j) = combR pre t i j := by
  simp only [combR]
  refine sum_congr rfl fun k _ => ?_
  by_cases hk : k.val < pre.length
  · have hmem : pre.getD k.val zeroMat ∈ pre := by
      rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
    rw [toR_fixed hg (hpre _ hmem)]
  · rw [List.getD_eq_default _ _ (by omega), toR_zeroMat]
    simp

lemma actMask_testBit {g : Sym} {f e : ℕ} (hf : f.testBit e = true) (he : e < 16) :
    (actMask g f).testBit (symIdx g e) = true := by
  unfold actMask
  suffices ∀ (acc : ℕ) (l : List ℕ), (acc.testBit (symIdx g e) = true ∨ e ∈ l) →
      (l.foldl (fun acc e => if f.testBit e then acc ||| (1 <<< symIdx g e) else acc)
        acc).testBit (symIdx g e) = true from this 0 _ (Or.inr (List.mem_range.mpr he))
  intro acc l
  induction l generalizing acc with
  | nil => intro h; simpa using h
  | cons a l ih =>
    intro h
    simp only [List.foldl_cons]
    apply ih
    rcases h with h | h
    · left; split_ifs <;> simp [Nat.testBit_or, h]
    · simp only [List.mem_cons] at h
      rcases h with rfl | h
      · left; simp [hf, Nat.testBit_or, Nat.one_shiftLeft]
      · right; exact h

lemma FaceState.of_sym {g : Sym} (hg : g ∈ symList) {pre : List Mat}
    (hpre : ∀ v ∈ pre, fixesMat g v = true) {f : ℕ} (h : FaceState pre (actMask g f)) :
    FaceState pre f := by
  intro t ht x hx
  set ρ := toPerm (mem_symList hg).1
  set γ := toPerm (mem_symList hg).2
  set y := x.submatrix ρ.symm γ.symm with hy
  have hyK : InK (actMask g f) y := by
    obtain ⟨hnn, ⟨c, hr, hc⟩, hs⟩ := hx
    refine ⟨fun a b => hnn _ _, ⟨c, fun a => ?_, fun b => ?_⟩, fun a b hab => ?_⟩
    · simp only [hy, Matrix.submatrix_apply]
      rw [Equiv.sum_comp γ.symm (fun j => x (ρ.symm a) j)]; exact hr _
    · simp only [hy, Matrix.submatrix_apply]
      rw [Equiv.sum_comp ρ.symm (fun i => x i (γ.symm b))]; exact hc _
    · simp only [hy, Matrix.submatrix_apply]
      by_contra hne
      have hbit : f.testBit (4 * (ρ.symm a).val + (γ.symm b).val) = true := by
        by_contra hb
        exact hne (hs _ _ (by simpa using hb))
      have := actMask_testBit (g := g) hbit (by omega)
      rw [symIdx_eq hg] at this
      simp only [ρ, γ, Equiv.apply_symm_apply] at this
      rw [this] at hab
      exact Bool.noConfusion hab
  have h0 := h t ht y hyK
  have heq : combR pre t + y = (combR pre t + x).submatrix ρ.symm γ.symm := by
    ext a b
    simp only [Matrix.add_apply, Matrix.submatrix_apply, hy]
    congr 1
    have := combR_fixed hg hpre t (ρ.symm a) (γ.symm b)
    simp only [ρ, γ, Equiv.apply_symm_apply] at this
    exact this
  rw [heq, Hf_submatrix] at h0
  exact h0

/-! ## Masks -/

lemma testBit_remove {S e b : ℕ} (he : e < 16) (hb : b < 16) :
    (S &&& ((2 ^ 16 - 1) ^^^ (1 <<< e))).testBit b = (S.testBit b && decide (b ≠ e)) := by
  rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.one_shiftLeft,
    Nat.testBit_two_pow]
  by_cases h : b = e
  · subst h; simp [hb]
  · simp [hb, h, Ne.symm h]

lemma fin4_idx_inj {i j i' j' : Fin 4} (h : 4 * i.val + j.val = 4 * i'.val + j'.val) :
    i = i' ∧ j = j' := by
  constructor <;> apply Fin.ext <;> omega

/-! ## Leaves -/

lemma toR_permMat (p : List ℕ) (i j : Fin 4) :
    toR (permMat p) i j = if p.getD i.val 0 = j.val then 1 else 0 := by
  simp only [toR, permMat]
  have h1 : (4 * i.val + j.val) / 4 = i.val := by omega
  have h2 : (4 * i.val + j.val) % 4 = j.val := by omega
  rw [getElem!_pos _ _ (by simp; omega)]
  simp only [Array.getElem_ofFn, h1, h2]
  split_ifs <;> simp_all

lemma FaceState.of_leaf {pre : List Mat} {S : ℕ} (hps : (permsIn S).length ≤ 1)
    (h : polyCheck (pre ++ (permsIn S).map permMat) = true) : FaceState pre S := by
  intro t ht x hx
  have hlen := h
  simp only [polyCheck, Bool.and_eq_true, decide_eq_true_eq] at hlen
  match hp : permsIn S, hps with
  | [], _ =>
    have hx0 : x = 0 := by
      ext i j
      by_contra hne
      obtain ⟨p, hp', -⟩ := hx.exists_perm hne
      rw [hp] at hp'
      simp at hp'
    rw [hp] at h
    have := polyCheck_sound _ h t ht
    simpa [hx0] using this
  | [p], _ =>
    rw [hp] at h hlen
    have hpl : p ∈ permList := (mem_permsIn.mp (hp ▸ List.mem_singleton_self p)).1
    set σ := toPerm hpl
    have hx2 := hx
    obtain ⟨hnn, ⟨c, hr, -⟩, -⟩ := hx2
    have hzero : ∀ i j, j ≠ σ i → x i j = 0 := by
      intro i j hj
      by_contra hne
      obtain ⟨q, hq, hbit⟩ := hx.exists_perm hne
      rw [hp, List.mem_singleton] at hq
      subst hq
      rw [permMask_testBit _ hpl] at hbit
      simp only [decide_eq_true_eq] at hbit
      apply hj
      apply Fin.ext
      rw [toPerm_apply]; exact hbit.symm
    have hxc : ∀ i, x i (σ i) = c := by
      intro i
      rw [← hr i, sum_eq_single (σ i) (fun j _ hj => hzero i j hj) (by simp)]
    have hc0 : 0 ≤ c := by rw [← hxc 0]; exact hnn _ _
    have hxeq : x = c • toR (permMat p) := by
      ext i j
      simp only [Matrix.smul_apply, smul_eq_mul, toR_permMat]
      by_cases hj : j = σ i
      · subst hj; rw [hxc, ← toPerm_apply hpl]; simp [σ]
      · rw [hzero i j hj]
        have : p.getD i.val 0 ≠ j.val := by
          rw [← toPerm_apply hpl]; exact fun h' => hj (Fin.ext h').symm
        rw [if_neg this, mul_zero]
    have hℓ : pre.length < NV := by simp at hlen; omega
    have := polyCheck_sound _ h (Function.update t ⟨pre.length, hℓ⟩ c) (by
      intro k
      by_cases hk : k = ⟨pre.length, hℓ⟩
      · subst hk; simpa using hc0
      · rw [Function.update_of_ne hk]; exact ht k)
    simp only [List.map_cons, List.map_nil] at this
    rw [combR_append pre _ hℓ] at this
    rw [hxeq]
    exact this

/-! ## Pulling from the center of a face -/

lemma FaceState.of_pull {pre : List Mat} {S : ℕ} (F : List ℕ)
    (hne : (permsIn S) ≠ [])
    (hℓ : pre.length < NV)
    (hsupp : suppOK (centerOf (permsIn S)) (closureOf (permsIn S)) = true)
    (hline : lineSumsEq (centerOf (permsIn S)) = true)
    (hcov : ∀ c ∈ candidates (closureOf (permsIn S)), ∃ f ∈ F, subMask c f = true)
    (hchild : ∀ f ∈ F, FaceState (pre ++ [centerOf (permsIn S)]) f) :
    FaceState pre S := by
  intro t ht x hx
  set S' := closureOf (permsIn S) with hS'
  set V := centerOf (permsIn S) with hV
  have hx' : InK S' x := hx.closure
  obtain ⟨hnn, ⟨c, hr, hc⟩, hs⟩ := hx'
  -- facts about V
  have hVpos : ∀ i j : Fin 4, (0 < toR V i j ↔ S'.testBit (4 * i.val + j.val) = true) := by
    intro i j
    simp only [suppOK, List.all_eq_true, List.mem_range, beq_iff_eq] at hsupp
    have := hsupp (4 * i.val + j.val) (by omega)
    simp only [toR, Nat.cast_pos]
    rw [← this]
    simp
  have hVnn : ∀ i j, 0 ≤ toR V i j := fun i j => Nat.cast_nonneg _
  obtain ⟨r0, hVr, hVc⟩ : ∃ r0 : ℝ, (∀ i, ∑ j, toR V i j = r0) ∧ (∀ j, ∑ i, toR V i j = r0) := by
    simp only [lineSumsEq, Bool.and_eq_true, beq_iff_eq] at hline
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hline
    refine ⟨((V[0]! + V[1]! + V[2]! + V[3]! : ℕ) : ℝ), fun i => ?_, fun j => ?_⟩
    · simp only [Fin.sum_univ_four, toR]
      fin_cases i <;> simp <;> norm_cast
    · simp only [Fin.sum_univ_four, toR]
      fin_cases j <;> simp <;> norm_cast
  -- the set of support entries is nonempty
  set A := (univ : Finset (Fin 4 × Fin 4)).filter
    (fun ij => S'.testBit (4 * ij.1.val + ij.2.val) = true) with hA
  have hAne : A.Nonempty := by
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hne
    have hpl := (mem_permsIn.mp hp).1
    refine ⟨(0, toPerm hpl 0), ?_⟩
    simp only [hA, mem_filter, mem_univ, true_and]
    apply closureOf_testBit_of_mem hp
    rw [permMask_testBit _ hpl, toPerm_apply]
    simp
  obtain ⟨⟨i0, j0⟩, hmem0, hmin⟩ := exists_min_image A (fun ij => x ij.1 ij.2 / toR V ij.1 ij.2) hAne
  simp only [hA, mem_filter, mem_univ, true_and] at hmem0
  set τ := x i0 j0 / toR V i0 j0 with hτ
  have hV0 : 0 < toR V i0 j0 := (hVpos i0 j0).mpr hmem0
  have hτ0 : 0 ≤ τ := div_nonneg (hnn _ _) hV0.le
  set x' := x - τ • toR V with hx'def
  -- x' lies in a child face
  set e0 := 4 * i0.val + j0.val with he0
  have he0lt : e0 < 16 := by omega
  have hx'K : InK (S' &&& ((2 ^ 16 - 1) ^^^ (1 <<< e0))) x' := by
    refine ⟨fun i j => ?_, ⟨c - τ * r0, fun i => ?_, fun j => ?_⟩, fun i j hb => ?_⟩
    · simp only [hx'def, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, sub_nonneg]
      by_cases hij : S'.testBit (4 * i.val + j.val) = true
      · have hVij : 0 < toR V i j := (hVpos i j).mpr hij
        have := hmin (i, j) (by simp [hA, hij])
        simp only at this
        calc τ * toR V i j ≤ x i j / toR V i j * toR V i j := by
              exact mul_le_mul_of_nonneg_right this hVij.le
          _ = x i j := div_mul_cancel₀ _ hVij.ne'
      · have hVij : toR V i j = 0 := by
          have := (hVpos i j).not.mpr hij
          linarith [hVnn i j, not_lt.mp this]
        rw [hVij, mul_zero]; exact hnn i j
    · simp only [hx'def, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      rw [sum_sub_distrib, ← mul_sum, hr, hVr]
    · simp only [hx'def, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      rw [sum_sub_distrib, ← mul_sum, hc, hVc]
    · simp only [hx'def, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      rw [testBit_remove he0lt (by omega)] at hb
      by_cases hij : S'.testBit (4 * i.val + j.val) = true
      · rw [hij] at hb
        simp only [Bool.true_and, decide_eq_false_iff_not, not_not] at hb
        obtain ⟨rfl, rfl⟩ := fin4_idx_inj hb
        rw [hτ, div_mul_cancel₀ _ hV0.ne', sub_self]
      · simp only [Bool.not_eq_true] at hij
        have hVij : toR V i j = 0 := by
          have := (hVpos i j).not.mpr (by simp [hij])
          linarith [hVnn i j, not_lt.mp this]
        rw [hs i j hij, hVij, mul_zero, sub_zero]
  have hx'cl := hx'K.closure
  have hcand : closureOf (permsIn (S' &&& ((2 ^ 16 - 1) ^^^ (1 <<< e0)))) ∈ candidates S' := by
    simp only [candidates, List.mem_map, List.mem_filter, List.mem_range]
    exact ⟨e0, ⟨he0lt, hmem0⟩, rfl⟩
  obtain ⟨f, hf, hsub⟩ := hcov _ hcand
  have hx'f := hx'cl.mono hsub
  have := hchild f hf (Function.update t ⟨pre.length, hℓ⟩ τ) (by
    intro k
    by_cases hk : k = ⟨pre.length, hℓ⟩
    · subst hk; simpa using hτ0
    · rw [Function.update_of_ne hk]; exact ht k) x' hx'f
  rw [combR_append pre V hℓ] at this
  have heq : combR pre t + τ • toR V + x' = combR pre t + x := by
    simp only [hx'def]; abel
  rw [heq] at this
  exact this

/-! ## The fold over facets -/

/-- The step function of the fold in `checkNode`. -/
def foldStep (chk : ℕ → Bool) (G' : List Sym) (acc : Option (List ℕ)) (f : ℕ) :
    Option (List ℕ) :=
  match acc with
  | none => none
  | some reps =>
    if reps.any (fun r => G'.any fun g => actMask g f == r) then some reps
    else if chk f then some (f :: reps) else none

lemma foldl_foldStep_none (chk : ℕ → Bool) (G' : List Sym) (L : List ℕ) :
    L.foldl (foldStep chk G') none = none := by
  induction L with
  | nil => rfl
  | cons a L ih => simpa [foldStep] using ih

lemma foldl_foldStep_cover (chk : ℕ → Bool) (G' : List Sym) :
    ∀ (L reps0 : List ℕ), (∀ r ∈ reps0, chk r = true) →
      (L.foldl (foldStep chk G') (some reps0)).isSome = true →
      ∀ f ∈ L, ∃ r, chk r = true ∧ (r = f ∨ ∃ g ∈ G', actMask g f = r) := by
  intro L
  induction L with
  | nil => intro _ _ _ f hf; simp at hf
  | cons a L ih =>
    intro reps0 hreps h f hf
    simp only [List.foldl_cons] at h
    simp only [foldStep] at h
    split_ifs at h with h1 h2
    · -- skipped: a is covered by an existing representative
      simp only [List.mem_cons] at hf
      rcases hf with rfl | hf
      · simp only [List.any_eq_true, beq_iff_eq] at h1
        obtain ⟨r, hr, g, hg, hgr⟩ := h1
        exact ⟨r, hreps r hr, Or.inr ⟨g, hg, hgr⟩⟩
      · exact ih reps0 hreps h f hf
    · have hreps' : ∀ r ∈ a :: reps0, chk r = true := by
        intro r hr
        simp only [List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact h2
        · exact hreps r hr
      simp only [List.mem_cons] at hf
      rcases hf with rfl | hf
      · exact ⟨f, h2, Or.inl rfl⟩
      · exact ih (a :: reps0) hreps' h f hf
    · rw [foldl_foldStep_none] at h
      exact absurd h (by simp)

/-! ## Main soundness theorem -/

theorem checkNode_sound : ∀ (fuel : ℕ) (pre : List Mat) (S : ℕ) (G : List Sym),
    (∀ g ∈ G, g ∈ symList ∧ ∀ v ∈ pre, fixesMat g v = true) →
    checkNode fuel pre S G = true → FaceState pre S := by
  intro fuel
  induction fuel with
  | zero =>
    intro pre S G _ h
    unfold checkNode at h
    simp only at h
    split_ifs at h with hps
    · exact FaceState.of_leaf hps h
  | succ n ih =>
    intro pre S G hG h
    unfold checkNode at h
    simp only at h
    split_ifs at h with hps
    · exact FaceState.of_leaf hps h
    · simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨hℓ, hsupp⟩, hline⟩, hcov⟩, hfold⟩ := h
      simp only [decide_eq_true_eq] at hℓ
      simp only [List.all_eq_true, List.any_eq_true] at hcov
      have hne : permsIn S ≠ [] := by
        intro h0; rw [h0] at hps; simp at hps
      set V := centerOf (permsIn S)
      set G' := G.filter fun g => fixesMat g V
      have hG' : ∀ g ∈ G', g ∈ symList ∧ ∀ v ∈ pre ++ [V], fixesMat g v = true := by
        intro g hg
        simp only [G', List.mem_filter] at hg
        refine ⟨(hG g hg.1).1, fun v hv => ?_⟩
        simp only [List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | rfl
        · exact (hG g hg.1).2 v hv
        · exact hg.2
      have hcover := foldl_foldStep_cover (fun f => checkNode n (pre ++ [V]) f G') G'
        (maximals (candidates (closureOf (permsIn S)))) [] (by simp) hfold
      refine FaceState.of_pull (maximals (candidates (closureOf (permsIn S)))) hne hℓ hsupp hline
        (fun c hc => hcov c hc) (fun f hf => ?_)
      obtain ⟨r, hr, hrf⟩ := hcover f hf
      have hFr := ih (pre ++ [V]) r G' hG' hr
      rcases hrf with rfl | ⟨g, hg, rfl⟩
      · exact hFr
      · exact FaceState.of_sym (hG' g hg).1 (hG' g hg).2 hFr

end Gyires

namespace Gyires

lemma symInv_filter {G : List Sym} {pre : List Mat} (V : Mat)
    (hG : ∀ g ∈ G, g ∈ symList ∧ ∀ v ∈ pre, fixesMat g v = true) :
    ∀ g ∈ G.filter (fun g => fixesMat g V), g ∈ symList ∧ ∀ v ∈ pre ++ [V], fixesMat g v = true := by
  intro g hg
  simp only [List.mem_filter] at hg
  refine ⟨(hG g hg.1).1, fun v hv => ?_⟩
  simp only [List.mem_append, List.mem_singleton] at hv
  rcases hv with hv | rfl
  · exact (hG g hg.1).2 v hv
  · exact hg.2

theorem splitCheck_sound {pre : List Mat} {S : ℕ} {G : List Sym} {reps : List ℕ}
    (hG : ∀ g ∈ G, g ∈ symList ∧ ∀ v ∈ pre, fixesMat g v = true)
    (h : splitCheck pre S G reps = true)
    (hreps : ∀ r ∈ reps, FaceState (pre ++ [centerOf (permsIn S)]) r) :
    FaceState pre S := by
  unfold splitCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hps, hℓ⟩, hsupp⟩, hline⟩, hcov⟩, hfac⟩ := h
  simp only [decide_eq_true_eq] at hps hℓ
  simp only [List.all_eq_true, List.any_eq_true] at hcov hfac
  have hne : permsIn S ≠ [] := by
    intro h0; rw [h0] at hps; simp at hps
  have hG' := symInv_filter (centerOf (permsIn S)) hG
  refine FaceState.of_pull _ hne hℓ hsupp hline (fun c hc => hcov c hc) (fun f hf => ?_)
  obtain ⟨r, hr, hrf⟩ := hfac f hf
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hrf
  rcases hrf with rfl | ⟨g, hg, hgr⟩
  · exact hreps r hr
  · subst hgr
    exact FaceState.of_sym (hG' g hg).1 (hG' g hg).2 (hreps _ hr)

end Gyires
