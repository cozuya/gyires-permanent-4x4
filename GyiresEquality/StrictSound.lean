import RequestProject.TreeSound
import GyiresStrictCompute.Basic

/-!
# Soundness of the strict certificate

`FaceStateS pre S` strengthens `FaceState pre S` to strict positivity whenever the matrix
`x` is nonzero or some generator after the first has positive weight. The proofs follow
`RequestProject.TreeSound`, tracking that extra hypothesis through each step.
-/

open Finset

namespace Gyires

/-! ## The strict leaf test -/

theorem pureOK_true : pureOK = true := by native_decide

lemma pureIdx_spec (k : Fin NV) :
    pureIdxs[k.val]! < E8.size ∧
      ∀ j : Fin NV, (E8[pureIdxs[k.val]!]!)[j.val]! = if j = k then 8 else 0 := by
  have h := pureOK_true
  simp only [pureOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨-, h⟩ := h
  obtain ⟨h1, h2⟩ := h k.val k.isLt
  refine ⟨h1, fun j => ?_⟩
  rw [h2 j.val j.isLt]
  by_cases hjk : j = k
  · subst hjk; simp
  · have : j.val ≠ k.val := fun h => hjk (Fin.ext h)
    simp [hjk, this]

lemma monoR_pure (k : Fin NV) (t : Fin NV → ℝ) : monoR E8 (pureIdxs[k.val]!) t = t k ^ 8 := by
  unfold monoR
  rw [Finset.prod_eq_single k]
  · rw [(pureIdx_spec k).2 k]; simp
  · intro j _ hj
    rw [(pureIdx_spec k).2 j, if_neg hj, pow_zero]
  · simp

lemma polyCheckS_polyCheck {gs : List Mat} (h : polyCheckS gs = true) : polyCheck gs = true := by
  simp only [polyCheckS, polyCheck, Bool.and_eq_true] at h ⊢
  exact h.1

/-- **Soundness of the strict leaf test.** -/
theorem polyCheckS_sound (gs : List Mat) (h : polyCheckS gs = true) (t : Fin NV → ℝ)
    (ht : ∀ k, 0 ≤ t k) (k : Fin NV) (hk0 : 0 < k.val) (hk : 0 < t k) :
    0 < Hf (combR gs t) := by
  simp only [polyCheckS, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨-, hdom⟩, hstrict⟩ := h
  have hsk := (hstrict k.val k.isLt).resolve_left (by omega)
  simp only [dominates, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at hdom
  obtain ⟨hsize, hle⟩ := hdom
  have hsa : (posPart gs).size = E8.size := (posPart_spec gs t).1
  unfold Hf
  rw [← (posPart_spec gs t).2, ← (negPart_spec gs t).2]
  unfold ev
  rw [← hsize, ← sum_sub_distrib]
  apply sum_pos'
  · intro i hi
    rw [← sub_mul]
    exact mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hle i (mem_range.mp hi)))
      (monoR_nonneg E8 i ht)
  · refine ⟨pureIdxs[k.val]!, mem_range.mpr (hsa ▸ (pureIdx_spec k).1), ?_⟩
    rw [← sub_mul, monoR_pure]
    exact mul_pos (sub_pos.mpr (by exact_mod_cast hsk)) (pow_pos hk 8)

/-! ## Strict face states -/

/-- Strict face-state semantics: positivity when `x ≠ 0` or a later generator is used. -/
def FaceStateS (pre : List Mat) (S : ℕ) : Prop :=
  ∀ t : Fin NV → ℝ, (∀ k, 0 ≤ t k) → ∀ x, InK S x →
    (x ≠ 0 ∨ ∃ k : Fin NV, 0 < k.val ∧ k.val < pre.length ∧ 0 < t k) →
    0 < Hf (combR pre t + x)

lemma update_old {pre : List Mat} (hℓ : pre.length < NV) (t : Fin NV → ℝ) (τ : ℝ)
    {k : Fin NV} (hk : k.val < pre.length) :
    Function.update t ⟨pre.length, hℓ⟩ τ k = t k := by
  rw [Function.update_of_ne]
  intro h
  rw [h] at hk
  exact lt_irrefl _ hk

lemma update_nonneg {pre : List Mat} (hℓ : pre.length < NV) {t : Fin NV → ℝ}
    (ht : ∀ k, 0 ≤ t k) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∀ k, 0 ≤ Function.update t ⟨pre.length, hℓ⟩ τ k := by
  intro k
  by_cases hk : k = ⟨pre.length, hℓ⟩
  · subst hk; simpa using hτ
  · rw [Function.update_of_ne hk]; exact ht k

lemma FaceStateS.of_sym {g : Sym} (hg : g ∈ symList) {pre : List Mat}
    (hpre : ∀ v ∈ pre, fixesMat g v = true) {f : ℕ} (h : FaceStateS pre (actMask g f)) :
    FaceStateS pre f := by
  intro t ht x hx hpos
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
  have hpos' : y ≠ 0 ∨ ∃ k : Fin NV, 0 < k.val ∧ k.val < pre.length ∧ 0 < t k := by
    rcases hpos with hne | hk
    · left
      intro hy0
      apply hne
      ext i j
      have := congrFun (congrFun hy0 (ρ i)) (γ j)
      simpa [hy, Matrix.submatrix_apply] using this
    · right; exact hk
  have h0 := h t ht y hyK hpos'
  have heq : combR pre t + y = (combR pre t + x).submatrix ρ.symm γ.symm := by
    ext a b
    simp only [Matrix.add_apply, Matrix.submatrix_apply, hy]
    congr 1
    have := combR_fixed hg hpre t (ρ.symm a) (γ.symm b)
    simp only [ρ, γ, Equiv.apply_symm_apply] at this
    exact this
  rw [heq, Hf_submatrix] at h0
  exact h0

lemma FaceStateS.of_leaf {pre : List Mat} {S : ℕ} (hpre : 0 < pre.length)
    (hps : (permsIn S).length ≤ 1)
    (h : polyCheckS (pre ++ (permsIn S).map permMat) = true) : FaceStateS pre S := by
  intro t ht x hx hpos
  have hlen := polyCheckS_polyCheck h
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
    rcases hpos with hne | ⟨k, hk0, -, hk⟩
    · exact absurd hx0 hne
    · have := polyCheckS_sound _ h t ht k hk0 hk
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
    have hpos' : ∃ k : Fin NV, 0 < k.val ∧ 0 < Function.update t ⟨pre.length, hℓ⟩ c k := by
      rcases hpos with hne | ⟨k, hk0, hkl, hk⟩
      · have hc : c ≠ 0 := by
          rintro rfl
          apply hne
          rw [hxeq, zero_smul]
        exact ⟨⟨pre.length, hℓ⟩, hpre, by simpa using lt_of_le_of_ne hc0 (Ne.symm hc)⟩
      · exact ⟨k, hk0, by rw [update_old hℓ t c hkl]; exact hk⟩
    obtain ⟨k, hk0, hk⟩ := hpos'
    have := polyCheckS_sound _ h (Function.update t ⟨pre.length, hℓ⟩ c)
      (update_nonneg hℓ ht hc0) k hk0 hk
    simp only [List.map_cons, List.map_nil] at this
    rw [combR_append pre _ hℓ] at this
    rw [hxeq]
    exact this

lemma FaceStateS.of_pull {pre : List Mat} {S : ℕ} (F : List ℕ)
    (hpre : 0 < pre.length)
    (hne : (permsIn S) ≠ [])
    (hℓ : pre.length < NV)
    (hsupp : suppOK (centerOf (permsIn S)) (closureOf (permsIn S)) = true)
    (hline : lineSumsEq (centerOf (permsIn S)) = true)
    (hcov : ∀ c ∈ candidates (closureOf (permsIn S)), ∃ f ∈ F, subMask c f = true)
    (hchild : ∀ f ∈ F, FaceStateS (pre ++ [centerOf (permsIn S)]) f) :
    FaceStateS pre S := by
  intro t ht x hx hpos
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
  -- the strictness hypothesis passes to the child
  have hpos' : x' ≠ 0 ∨ ∃ k : Fin NV, 0 < k.val ∧ k.val < (pre ++ [V]).length ∧
      0 < Function.update t ⟨pre.length, hℓ⟩ τ k := by
    rcases hpos with hx0 | ⟨k, hk0, hkl, hk⟩
    · by_cases hτz : τ = 0
      · left
        rw [hx'def, hτz, zero_smul, sub_zero]
        exact hx0
      · right
        refine ⟨⟨pre.length, hℓ⟩, hpre, by simp, ?_⟩
        simpa using lt_of_le_of_ne hτ0 (Ne.symm hτz)
    · right
      refine ⟨k, hk0, by simp; omega, ?_⟩
      rw [update_old hℓ t τ hkl]
      exact hk
  have := hchild f hf (Function.update t ⟨pre.length, hℓ⟩ τ) (update_nonneg hℓ ht hτ0) x' hx'f
    hpos'
  rw [combR_append pre V hℓ] at this
  have heq : combR pre t + τ • toR V + x' = combR pre t + x := by
    simp only [hx'def]; abel
  rw [heq] at this
  exact this

/-! ## Main strict soundness theorems -/

theorem checkNodeS_sound : ∀ (fuel : ℕ) (pre : List Mat) (S : ℕ) (G : List Sym),
    0 < pre.length →
    (∀ g ∈ G, g ∈ symList ∧ ∀ v ∈ pre, fixesMat g v = true) →
    checkNodeS fuel pre S G = true → FaceStateS pre S := by
  intro fuel
  induction fuel with
  | zero =>
    intro pre S G hpre _ h
    unfold checkNodeS at h
    simp only at h
    split_ifs at h with hps
    · exact FaceStateS.of_leaf hpre hps h
  | succ n ih =>
    intro pre S G hpre hG h
    unfold checkNodeS at h
    simp only at h
    split_ifs at h with hps
    · exact FaceStateS.of_leaf hpre hps h
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
      have hcover := foldl_foldStep_cover (fun f => checkNodeS n (pre ++ [V]) f G') G'
        (maximals (candidates (closureOf (permsIn S)))) [] (by simp) hfold
      have hpre' : 0 < (pre ++ [V]).length := by simp
      refine FaceStateS.of_pull (maximals (candidates (closureOf (permsIn S)))) hpre hne hℓ hsupp
        hline (fun c hc => hcov c hc) (fun f hf => ?_)
      obtain ⟨r, hr, hrf⟩ := hcover f hf
      have hFr := ih (pre ++ [V]) r G' hpre' hG' hr
      rcases hrf with rfl | ⟨g, hg, rfl⟩
      · exact hFr
      · exact FaceStateS.of_sym (hG' g hg).1 (hG' g hg).2 hFr

theorem splitCheckS_sound {pre : List Mat} {S : ℕ} {G : List Sym} {reps : List ℕ}
    (hpre : 0 < pre.length)
    (hG : ∀ g ∈ G, g ∈ symList ∧ ∀ v ∈ pre, fixesMat g v = true)
    (h : splitCheck pre S G reps = true)
    (hreps : ∀ r ∈ reps, FaceStateS (pre ++ [centerOf (permsIn S)]) r) :
    FaceStateS pre S := by
  unfold splitCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hps, hℓ⟩, hsupp⟩, hline⟩, hcov⟩, hfac⟩ := h
  simp only [decide_eq_true_eq] at hps hℓ
  simp only [List.all_eq_true, List.any_eq_true] at hcov hfac
  have hne : permsIn S ≠ [] := by
    intro h0; rw [h0] at hps; simp at hps
  have hG' := symInv_filter (centerOf (permsIn S)) hG
  refine FaceStateS.of_pull _ hpre hne hℓ hsupp hline (fun c hc => hcov c hc) (fun f hf => ?_)
  obtain ⟨r, hr, hrf⟩ := hfac f hf
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hrf
  rcases hrf with rfl | ⟨g, hg, hgr⟩
  · exact hreps r hr
  · subst hgr
    exact FaceStateS.of_sym (hG' g hg).1 (hG' g hg).2 (hreps _ hr)

end Gyires
