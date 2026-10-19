import RequestProject.PolySound

/-!
# The leaf test is sound

`polyCheck gs = true` implies `32 per(M)^2 - 3 per(M Mᵀ) ≥ 0` for every nonnegative
combination `M = ∑ t_k g_k` of the generators `gs`.
-/

open Finset

namespace Gyires

/-- The degree-8 form whose nonnegativity on doubly stochastic matrices is the core claim. -/
noncomputable def Hf (M : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  32 * M.permanent ^ 2 - 3 * (M * M.transpose).permanent

/-- The real matrix encoded by a 16-entry array (row-major). -/
noncomputable def toR (g : Mat) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => ((g[4 * i.val + j.val]! : ℕ) : ℝ)

/-- The combination `∑ₖ tₖ gₖ` of (at most `NV`) generators, padded with zeros. -/
noncomputable def combR (gs : List Mat) (t : Fin NV → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => ∑ k : Fin NV, t k * toR (gs.getD k.val zeroMat) i j

/-- Laplace expansion of a 4×4 permanent along rows `{0,1}` (natural-number indices). -/
def laplaceN {R : Type*} [CommRing R] (Y : ℕ → ℕ → R) : R :=
  let p2 (r1 r2 c1 c2 : ℕ) := Y r1 c1 * Y r2 c2 + Y r1 c2 * Y r2 c1
  let t (a b c d : ℕ) := p2 0 1 a b * p2 2 3 c d
  t 0 1 2 3 + t 0 2 1 3 + t 0 3 1 2 + t 1 2 0 3 + t 1 3 0 2 + t 2 3 0 1

theorem permanent_eq_laplaceN (M : Matrix (Fin 4) (Fin 4) ℝ) :
    M.permanent = laplaceN (fun i j => M (Fin.ofNat 4 i) (Fin.ofNat 4 j)) := by
  simp only [Matrix.permanent]
  simp only [← (Equiv.Perm.decomposeFin.symm).sum_comp, Fintype.sum_prod_type, Fin.sum_univ_succ,
    Fin.prod_univ_succ, Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ, Fintype.sum_unique, Fintype.prod_unique]
  simp only [laplaceN, show Fin.ofNat 4 0 = 0 from rfl, show Fin.ofNat 4 1 = 1 from rfl,
    show Fin.ofNat 4 2 = 2 from rfl, show Fin.ofNat 4 3 = 3 from rfl]
  simp [Equiv.swap_apply_def, Fin.ext_iff]
  ring

/-! ## Facts about the tables (checked by evaluation) -/

theorem e1OK_true : e1OK = true := by native_decide
theorem T11_ok : tableOK E1 E1 E2 T11 = true := by native_decide
theorem T22_ok : tableOK E2 E2 E4 T22 = true := by native_decide
theorem T44_ok : tableOK E4 E4 E8 T44 = true := by native_decide

lemma E1_size : E1.size = NV := by
  have h := e1OK_true
  simp only [e1OK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

lemma monoR_E1 (k : Fin NV) (t : Fin NV → ℝ) : monoR E1 k.val t = t k := by
  have h := e1OK_true
  simp only [e1OK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  unfold monoR
  rw [Finset.prod_eq_single k]
  · rw [h.2 k.val k.isLt k.val k.isLt]; simp
  · intro b _ hb
    rw [h.2 k.val k.isLt b.val b.isLt]
    have : ¬ (k.val = b.val) := fun h' => hb (Fin.ext h').symm
    simp [this]
  · simp

/-! ## Multiplication lemmas -/

lemma mul11_spec (p q : Array Nat) (hp : p.size = E1.size) (hq : q.size = E1.size)
    (t : Fin NV → ℝ) :
    (mul11 p q).size = E2.size ∧ ev E2 (mul11 p q) t = ev E1 p t * ev E1 q t :=
  ⟨size_pmul _ _ _ _ _ _, ev_pmul (tableProp_of_tableOK T11_ok) p q hp hq t⟩

lemma mul22_spec (p q : Array Nat) (hp : p.size = E2.size) (hq : q.size = E2.size)
    (t : Fin NV → ℝ) :
    (mul22 p q).size = E4.size ∧ ev E4 (mul22 p q) t = ev E2 p t * ev E2 q t :=
  ⟨size_pmul _ _ _ _ _ _, ev_pmul (tableProp_of_tableOK T22_ok) p q hp hq t⟩

lemma mul44_spec (p q : Array Nat) (hp : p.size = E4.size) (hq : q.size = E4.size)
    (t : Fin NV → ℝ) :
    (mul44 p q).size = E8.size ∧ ev E8 (mul44 p q) t = ev E4 p t * ev E4 q t :=
  ⟨size_pmul _ _ _ _ _ _, ev_pmul (tableProp_of_tableOK T44_ok) p q hp hq t⟩

/-! ## Linear forms, Gram entries and Laplace expansion -/

lemma linForm_size (gs : List Mat) (i j : Nat) : (linForm gs i j).size = E1.size := by
  simp [linForm, E1_size]

lemma ev_linForm (gs : List Mat) (i j : Fin 4) (t : Fin NV → ℝ) :
    ev E1 (linForm gs i.val j.val) t = combR gs t i j := by
  unfold ev combR
  have hs : (linForm gs i.val j.val).size = NV := by simp [linForm]
  rw [hs, ← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun k _ => ?_
  rw [monoR_E1]
  simp [linForm, toR, getElem!_pos, mul_comm]

lemma laplace_spec {Ea Eb Ec : Array (Array Nat)} (X : Nat → Nat → Array Nat)
    (m1 m2 : Array Nat → Array Nat → Array Nat) (t : Fin NV → ℝ)
    (hX : ∀ i j, (X i j).size = Ea.size)
    (h1 : ∀ p q, p.size = Ea.size → q.size = Ea.size →
      (m1 p q).size = Eb.size ∧ ev Eb (m1 p q) t = ev Ea p t * ev Ea q t)
    (h2 : ∀ p q, p.size = Eb.size → q.size = Eb.size →
      (m2 p q).size = Ec.size ∧ ev Ec (m2 p q) t = ev Eb p t * ev Eb q t) :
    (laplace X m1 m2).size = Ec.size ∧
      ev Ec (laplace X m1 m2) t = laplaceN (fun i j => ev Ea (X i j) t) := by
  have hp2 : ∀ r1 r2 c1 c2 : ℕ,
      (padd (m1 (X r1 c1) (X r2 c2)) (m1 (X r1 c2) (X r2 c1))).size = Eb.size ∧
      ev Eb (padd (m1 (X r1 c1) (X r2 c2)) (m1 (X r1 c2) (X r2 c1))) t =
        ev Ea (X r1 c1) t * ev Ea (X r2 c2) t + ev Ea (X r1 c2) t * ev Ea (X r2 c1) t := by
    intro r1 r2 c1 c2
    obtain ⟨a1, a2⟩ := h1 _ _ (hX r1 c1) (hX r2 c2)
    obtain ⟨b1, b2⟩ := h1 _ _ (hX r1 c2) (hX r2 c1)
    exact ⟨by rw [size_padd, a1, b1, min_self], by rw [ev_padd _ _ _ (a1.trans b1.symm), a2, b2]⟩
  have ht : ∀ a b c d : ℕ,
      (m2 (padd (m1 (X 0 a) (X 1 b)) (m1 (X 0 b) (X 1 a)))
        (padd (m1 (X 2 c) (X 3 d)) (m1 (X 2 d) (X 3 c)))).size = Ec.size ∧
      ev Ec (m2 (padd (m1 (X 0 a) (X 1 b)) (m1 (X 0 b) (X 1 a)))
        (padd (m1 (X 2 c) (X 3 d)) (m1 (X 2 d) (X 3 c)))) t =
        (ev Ea (X 0 a) t * ev Ea (X 1 b) t + ev Ea (X 0 b) t * ev Ea (X 1 a) t) *
        (ev Ea (X 2 c) t * ev Ea (X 3 d) t + ev Ea (X 2 d) t * ev Ea (X 3 c) t) := by
    intro a b c d
    obtain ⟨s1, e1⟩ := hp2 0 1 a b
    obtain ⟨s2, e2⟩ := hp2 2 3 c d
    obtain ⟨s3, e3⟩ := h2 _ _ s1 s2
    exact ⟨s3, by rw [e3, e1, e2]⟩
  obtain ⟨s1, e1⟩ := ht 0 1 2 3
  obtain ⟨s2, e2⟩ := ht 0 2 1 3
  obtain ⟨s3, e3⟩ := ht 0 3 1 2
  obtain ⟨s4, e4⟩ := ht 1 2 0 3
  obtain ⟨s5, e5⟩ := ht 1 3 0 2
  obtain ⟨s6, e6⟩ := ht 2 3 0 1
  unfold laplace laplaceN
  simp only
  refine ⟨by simp only [size_padd, s1, s2, s3, s4, s5, s6, min_self], ?_⟩
  repeat rw [ev_padd _ _ _ (by simp [size_padd, s1, s2, s3, s4, s5, s6])]
  rw [e1, e2, e3, e4, e5, e6]
  ring

lemma gramForm_spec (gs : List Mat) (i j : Fin 4) (t : Fin NV → ℝ) :
    (gramForm gs i.val j.val).size = E2.size ∧
      ev E2 (gramForm gs i.val j.val) t = (combR gs t * (combR gs t).transpose) i j := by
  have hm : ∀ l : Fin 4, (mul11 (linForm gs i.val l.val) (linForm gs j.val l.val)).size = E2.size ∧
      ev E2 (mul11 (linForm gs i.val l.val) (linForm gs j.val l.val)) t =
        combR gs t i l * combR gs t j l := by
    intro l
    obtain ⟨a, b⟩ := mul11_spec _ _ (linForm_size gs _ _) (linForm_size gs _ _) t
    exact ⟨a, by rw [b, ev_linForm, ev_linForm]⟩
  obtain ⟨s0, e0⟩ := hm 0
  obtain ⟨s1, e1⟩ := hm 1
  obtain ⟨s2, e2⟩ := hm 2
  obtain ⟨s3, e3⟩ := hm 3
  have v3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, v3] at s0 s1 s2 s3 e0 e1 e2 e3
  unfold gramForm
  refine ⟨by simp only [size_padd, s0, s1, s2, s3, min_self], ?_⟩
  rw [ev_padd _ _ _ (by simp only [size_padd, s0, s1, s2, s3, min_self]),
    ev_padd _ _ _ (by simp only [s0, s1]), ev_padd _ _ _ (by simp only [s2, s3]), e0, e1, e2, e3]
  simp [Matrix.mul_apply, Fin.sum_univ_four]
  ring

lemma gramForm_size (gs : List Mat) (i j : ℕ) : (gramForm gs i j).size = E2.size := by
  unfold gramForm
  simp only [size_padd, (mul11_spec _ _ (linForm_size gs _ _) (linForm_size gs _ _) (fun _ => 0)).1,
    min_self]

lemma perPoly_spec (gs : List Mat) (t : Fin NV → ℝ) :
    (perPoly gs).size = E4.size ∧ ev E4 (perPoly gs) t = (combR gs t).permanent := by
  obtain ⟨s, e⟩ := laplace_spec (Ea := E1) (Eb := E2) (Ec := E4) (linForm gs)
    mul11 mul22 t (fun i j => linForm_size gs _ _)
    (fun p q hp hq => mul11_spec p q hp hq t) (fun p q hp hq => mul22_spec p q hp hq t)
  refine ⟨s, ?_⟩
  rw [perPoly, e, permanent_eq_laplaceN]
  have h : ∀ i j : Fin 4, ev E1 (linForm gs i.val j.val) t = combR gs t i j := fun i j => ev_linForm gs i j t
  simp only [laplaceN]
  simp only [show Fin.ofNat 4 0 = 0 from rfl, show Fin.ofNat 4 1 = 1 from rfl,
    show Fin.ofNat 4 2 = 2 from rfl, show Fin.ofNat 4 3 = 3 from rfl, ← h]
  rfl

lemma perGramPoly_spec (gs : List Mat) (t : Fin NV → ℝ) :
    (perGramPoly gs).size = E8.size ∧
      ev E8 (perGramPoly gs) t = (combR gs t * (combR gs t).transpose).permanent := by
  obtain ⟨s, e⟩ := laplace_spec (Ea := E2) (Eb := E4) (Ec := E8) (gramForm gs)
    mul22 mul44 t (fun i j => gramForm_size gs _ _)
    (fun p q hp hq => mul22_spec p q hp hq t) (fun p q hp hq => mul44_spec p q hp hq t)
  refine ⟨s, ?_⟩
  rw [perGramPoly, e, permanent_eq_laplaceN]
  have h : ∀ i j : Fin 4, ev E2 (gramForm gs i.val j.val) t =
      (combR gs t * (combR gs t).transpose) i j := fun i j => (gramForm_spec gs i j t).2
  simp only [laplaceN]
  simp only [show Fin.ofNat 4 0 = 0 from rfl, show Fin.ofNat 4 1 = 1 from rfl,
    show Fin.ofNat 4 2 = 2 from rfl, show Fin.ofNat 4 3 = 3 from rfl, ← h]
  rfl

lemma posPart_spec (gs : List Mat) (t : Fin NV → ℝ) :
    (posPart gs).size = E8.size ∧ ev E8 (posPart gs) t = 32 * (combR gs t).permanent ^ 2 := by
  obtain ⟨s, e⟩ := perPoly_spec gs t
  obtain ⟨s', e'⟩ := mul44_spec _ _ s s t
  refine ⟨by rw [posPart, size_psmul, s'], ?_⟩
  rw [posPart, ev_psmul, e', e]
  push_cast; ring

lemma negPart_spec (gs : List Mat) (t : Fin NV → ℝ) :
    (negPart gs).size = E8.size ∧
      ev E8 (negPart gs) t = 3 * (combR gs t * (combR gs t).transpose).permanent := by
  obtain ⟨s, e⟩ := perGramPoly_spec gs t
  refine ⟨by rw [negPart, size_psmul, s], ?_⟩
  rw [negPart, ev_psmul, e]
  push_cast; ring

lemma ev_sub_nonneg_of_dominates (E : Array (Array Nat)) (a b : Array Nat)
    (h : dominates a b = true) (t : Fin NV → ℝ) (ht : ∀ k, 0 ≤ t k) :
    ev E b t ≤ ev E a t := by
  simp only [dominates, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨hs, h⟩ := h
  unfold ev
  rw [← hs]
  refine sum_le_sum fun i hi => ?_
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast h i (mem_range.mp hi))
    (monoR_nonneg E i ht)

/-- **Soundness of the leaf test.** -/
theorem polyCheck_sound (gs : List Mat) (h : polyCheck gs = true) (t : Fin NV → ℝ)
    (ht : ∀ k, 0 ≤ t k) : 0 ≤ Hf (combR gs t) := by
  simp only [polyCheck, Bool.and_eq_true] at h
  have := ev_sub_nonneg_of_dominates E8 _ _ h.2 t ht
  rw [(posPart_spec gs t).2, (negPart_spec gs t).2] at this
  unfold Hf
  linarith

end Gyires
