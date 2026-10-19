import Mathlib
import GyiresCompute.Basic

/-!
# Soundness of the dense polynomial arithmetic

We interpret coefficient arrays as real polynomials in `NV = 10` variables and show
that the executable operations of `GyiresCompute.Basic` compute products, sums and
the permanent expressions correctly.
-/

open Finset

namespace Gyires

/-- Value of the `i`-th monomial (exponents from `E`) at `t`. -/
noncomputable def monoR (E : Array (Array Nat)) (i : Nat) (t : Fin NV → ℝ) : ℝ :=
  ∏ k : Fin NV, t k ^ (E[i]!)[k.val]!

/-- Evaluation of a coefficient array (with exponent table `E`) at `t`. -/
noncomputable def ev (E : Array (Array Nat)) (p : Array Nat) (t : Fin NV → ℝ) : ℝ :=
  ∑ i ∈ range p.size, (p[i]! : ℝ) * monoR E i t

lemma monoR_nonneg (E : Array (Array Nat)) (i : Nat) {t : Fin NV → ℝ} (ht : ∀ k, 0 ≤ t k) :
    0 ≤ monoR E i t :=
  prod_nonneg fun k _ => pow_nonneg (ht k) _

/-! ## Sizes -/

lemma size_innerLoop (T : Array Nat) (base px : Nat) (q : Array Nat) :
    ∀ (y : Nat) (r : Array Nat), (innerLoop T base px q y r).size = r.size
  | 0, r => rfl
  | y + 1, r => by
    simp only [innerLoop]
    rw [size_innerLoop]
    split <;> simp

lemma size_outerLoop (T : Array Nat) (nb : Nat) (p q : Array Nat) :
    ∀ (x : Nat) (r : Array Nat), (outerLoop T nb p q x r).size = r.size
  | 0, r => rfl
  | x + 1, r => by
    simp only [outerLoop]
    rw [size_outerLoop]
    split
    · rfl
    · exact size_innerLoop _ _ _ _ _ _

lemma size_pmul (T : Array Nat) (na nb nc : Nat) (p q : Array Nat) :
    (pmul T na nb nc p q).size = nc := by
  simp [pmul, size_outerLoop]

lemma size_padd (p q : Array Nat) : (padd p q).size = min p.size q.size := by
  simp [padd]

lemma size_psmul (c : Nat) (p : Array Nat) : (psmul c p).size = p.size := by
  simp [psmul]

/-! ## Evaluation lemmas -/

lemma getElem!_set!_eq (r : Array Nat) (i j v : Nat) (hi : i < r.size) :
    (r.set! i v)[j]! = if j = i then v else r[j]! := by
  by_cases hj : j < r.size
  · by_cases hji : j = i
    · subst hji
      simp [Array.set!, hi]
    · simp [Array.set!, hji, getElem!_pos, hj, Ne.symm hji]
  · have : j ≠ i := fun h => hj (h ▸ hi)
    simp [this, getElem!_neg, hj]

lemma ev_set_add (E : Array (Array Nat)) (r : Array Nat) (i c : Nat) (hi : i < r.size)
    (t : Fin NV → ℝ) :
    ev E (r.set! i (r[i]! + c)) t = ev E r t + (c : ℝ) * monoR E i t := by
  unfold ev
  have hs : (r.set! i (r[i]! + c)).size = r.size := by simp
  rw [hs]
  have : ∀ j ∈ range r.size, (((r.set! i (r[i]! + c))[j]! : ℕ) : ℝ) * monoR E j t =
      (r[j]! : ℝ) * monoR E j t + if j = i then (c : ℝ) * monoR E j t else 0 := by
    intro j _
    rw [getElem!_set!_eq r i j _ hi]
    split_ifs with h
    · subst h; push_cast; ring
    · simp
  rw [sum_congr rfl this, sum_add_distrib, sum_ite_eq']
  simp [mem_range.mpr hi]

lemma ev_innerLoop (E : Array (Array Nat)) (T : Array Nat) (base px : Nat) (q : Array Nat)
    (t : Fin NV → ℝ) :
    ∀ (y : Nat) (r : Array Nat), (∀ y' < y, T[base + y']! < r.size) →
      ev E (innerLoop T base px q y r) t =
        ev E r t + ∑ y' ∈ range y, (px : ℝ) * (q[y']! : ℝ) * monoR E (T[base + y']!) t
  | 0, r, _ => by simp [innerLoop]
  | y + 1, r, h => by
    simp only [innerLoop]
    split_ifs with hq
    · rw [ev_innerLoop E T base px q t y r (fun y' hy' => h y' (by omega))]
      rw [sum_range_succ]
      have : q[y]! = 0 := by simpa using hq
      simp [this]
    · have hsz : (r.set! T[base + y]! (r[T[base + y]!]! + px * q[y]!)).size = r.size := by simp
      rw [ev_innerLoop E T base px q t y _ (fun y' hy' => hsz ▸ h y' (by omega))]
      rw [ev_set_add E r _ _ (h y (by omega)), sum_range_succ]
      push_cast; ring

lemma ev_outerLoop (E : Array (Array Nat)) (T : Array Nat) (nb : Nat) (p q : Array Nat)
    (t : Fin NV → ℝ) :
    ∀ (x : Nat) (r : Array Nat), (∀ x' < x, ∀ y' < nb, T[x' * nb + y']! < r.size) →
      ev E (outerLoop T nb p q x r) t =
        ev E r t + ∑ x' ∈ range x, ∑ y' ∈ range nb,
          (p[x']! : ℝ) * (q[y']! : ℝ) * monoR E (T[x' * nb + y']!) t
  | 0, r, _ => by simp [outerLoop]
  | x + 1, r, h => by
    simp only [outerLoop]
    split_ifs with hp
    · rw [ev_outerLoop E T nb p q t x r (fun x' hx' => h x' (by omega))]
      rw [sum_range_succ]
      have : p[x]! = 0 := by simpa using hp
      simp [this]
    · have hsz : (innerLoop T (x * nb) p[x]! q nb r).size = r.size := size_innerLoop _ _ _ _ _ _
      rw [ev_outerLoop E T nb p q t x _ (fun x' hx' y' hy' => hsz ▸ h x' (by omega) y' hy')]
      rw [ev_innerLoop E T (x * nb) p[x]! q t nb r (fun y' hy' => h x (by omega) y' hy'),
        sum_range_succ]
      ring

lemma ev_replicate_zero (E : Array (Array Nat)) (n : Nat) (t : Fin NV → ℝ) :
    ev E (Array.replicate n 0) t = 0 := by
  unfold ev
  apply sum_eq_zero
  intro i hi
  simp only [Array.size_replicate, mem_range] at hi
  simp [getElem!_pos, hi]

/-- Table property: the table `T` realises the product of monomials. -/
def TableProp (Ea Eb Ec : Array (Array Nat)) (T : Array Nat) : Prop :=
  ∀ x < Ea.size, ∀ y < Eb.size, T[x * Eb.size + y]! < Ec.size ∧
    ∀ k < NV, (Ec[T[x * Eb.size + y]!]!)[k]! = (Ea[x]!)[k]! + (Eb[y]!)[k]!

lemma tableProp_of_tableOK {Ea Eb Ec : Array (Array Nat)} {T : Array Nat}
    (h : tableOK Ea Eb Ec T = true) : TableProp Ea Eb Ec T := by
  intro x hx y hy
  simp only [tableOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨_, h⟩ := h
  obtain ⟨h1, h2⟩ := h x hx y hy
  exact ⟨h1, fun k hk => h2 k hk⟩

lemma monoR_table {Ea Eb Ec : Array (Array Nat)} {T : Array Nat} (hT : TableProp Ea Eb Ec T)
    {x y : Nat} (hx : x < Ea.size) (hy : y < Eb.size) (t : Fin NV → ℝ) :
    monoR Ec (T[x * Eb.size + y]!) t = monoR Ea x t * monoR Eb y t := by
  unfold monoR
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun k _ => ?_
  rw [(hT x hx y hy).2 k k.isLt, pow_add]

lemma ev_pmul {Ea Eb Ec : Array (Array Nat)} {T : Array Nat} (hT : TableProp Ea Eb Ec T)
    (p q : Array Nat) (hp : p.size = Ea.size) (hq : q.size = Eb.size) (t : Fin NV → ℝ) :
    ev Ec (pmul T Ea.size Eb.size Ec.size p q) t = ev Ea p t * ev Eb q t := by
  unfold pmul
  rw [ev_outerLoop Ec T Eb.size p q t Ea.size _ (fun x hx y hy => by
    simpa using (hT x hx y hy).1), ev_replicate_zero, zero_add]
  unfold ev
  rw [hp, hq, sum_mul_sum]
  refine sum_congr rfl fun x hx => sum_congr rfl fun y hy => ?_
  rw [monoR_table hT (mem_range.mp hx) (mem_range.mp hy)]
  ring

lemma ev_padd (E : Array (Array Nat)) (p q : Array Nat) (h : p.size = q.size)
    (t : Fin NV → ℝ) : ev E (padd p q) t = ev E p t + ev E q t := by
  unfold ev
  rw [size_padd, h, min_self, ← sum_add_distrib]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i < q.size := mem_range.mp hi
  have hp : i < p.size := h ▸ hi'
  simp [padd, getElem!_pos, hi', hp, Array.getElem_zipWith]
  ring

lemma ev_psmul (E : Array (Array Nat)) (c : Nat) (p : Array Nat) (t : Fin NV → ℝ) :
    ev E (psmul c p) t = c * ev E p t := by
  unfold ev
  rw [size_psmul, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i < p.size := mem_range.mp hi
  simp [psmul, getElem!_pos, hi']
  ring

end Gyires
