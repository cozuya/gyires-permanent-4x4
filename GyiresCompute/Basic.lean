import Std.Data.HashMap
/-!
# Computational core for the 4×4 permanent inequality certificate

Everything in this file is executable code over `Nat`/`Array`, without Mathlib.
Its correctness is established in the `RequestProject` files.
-/

namespace Gyires

/-- Number of cone generators (polynomial variables). -/
def NV : Nat := 10

/-- All exponent vectors of length `n` with entry sum `d`. -/
def monos : Nat → Nat → List (List Nat)
  | 0, 0 => [[]]
  | 0, _ + 1 => []
  | n + 1, d => (List.range (d + 1)).reverse.flatMap (fun e => (monos n (d - e)).map (e :: ·))

/-- Exponent table for degree `d` monomials in `NV` variables. -/
def expo (d : Nat) : Array (Array Nat) := ((monos NV d).map List.toArray).toArray

/-- Base-9 key of an exponent vector (injective for entries `< 9`). -/
def key (v : Array Nat) : Nat := v.foldr (fun e acc => acc * 9 + e) 0

def rankMap (E : Array (Array Nat)) : Std.HashMap Nat Nat :=
  E.foldl (init := ((∅ : Std.HashMap Nat Nat), 0)) (fun (acc : Std.HashMap Nat Nat × Nat) v =>
    (acc.1.insert (key v) acc.2, acc.2 + 1)) |>.1

def vadd (a b : Array Nat) : Array Nat := Array.zipWith (· + ·) a b

/-- Multiplication table: entry `x * Eb.size + y` is the index (in `Ec`) of the
sum of exponent vectors `Ea[x] + Eb[y]`. -/
def mulTable (Ea Eb Ec : Array (Array Nat)) : Array Nat :=
  let m := rankMap Ec
  Array.ofFn (n := Ea.size * Eb.size) fun idx =>
    m.getD (key (vadd Ea[idx.val / Eb.size]! Eb[idx.val % Eb.size]!)) 0

def E1 : Array (Array Nat) := expo 1
def E2 : Array (Array Nat) := expo 2
def E4 : Array (Array Nat) := expo 4
def E8 : Array (Array Nat) := expo 8

def T11 : Array Nat := mulTable E1 E1 E2
def T22 : Array Nat := mulTable E2 E2 E4
def T44 : Array Nat := mulTable E4 E4 E8

/-- Checks the defining property of a multiplication table. -/
def tableOK (Ea Eb Ec : Array (Array Nat)) (T : Array Nat) : Bool :=
  T.size == Ea.size * Eb.size &&
  (List.range Ea.size).all fun x =>
    (List.range Eb.size).all fun y =>
      let i := T[x * Eb.size + y]!
      i < Ec.size && (List.range NV).all fun k =>
        Ec[i]![k]! == Ea[x]![k]! + Eb[y]![k]!

/-- The degree-one exponent table is the standard basis. -/
def e1OK : Bool :=
  E1.size == NV && (List.range NV).all fun x => (List.range NV).all fun k =>
    E1[x]![k]! == if x == k then 1 else 0

/-! ## Dense polynomial arithmetic -/

/-- Inner loop of multiplication: adds `px * q[y']` at `T[base + y']` for `y' < y`. -/
def innerLoop (T : Array Nat) (base px : Nat) (q : Array Nat) : Nat → Array Nat → Array Nat
  | 0, r => r
  | y + 1, r =>
    let qy := q[y]!
    let r := if qy == 0 then r else
      let i := T[base + y]!
      r.set! i (r[i]! + px * qy)
    innerLoop T base px q y r

/-- Outer loop of multiplication over `x' < x`. -/
def outerLoop (T : Array Nat) (nb : Nat) (p q : Array Nat) : Nat → Array Nat → Array Nat
  | 0, r => r
  | x + 1, r =>
    let px := p[x]!
    let r := if px == 0 then r else innerLoop T (x * nb) px q nb r
    outerLoop T nb p q x r

def pmul (T : Array Nat) (na nb nc : Nat) (p q : Array Nat) : Array Nat :=
  outerLoop T nb p q na (Array.replicate nc 0)

def padd (p q : Array Nat) : Array Nat := Array.zipWith (· + ·) p q

def psmul (c : Nat) (p : Array Nat) : Array Nat := p.map (c * ·)

def mul11 (p q : Array Nat) : Array Nat := pmul T11 E1.size E1.size E2.size p q
def mul22 (p q : Array Nat) : Array Nat := pmul T22 E2.size E2.size E4.size p q
def mul44 (p q : Array Nat) : Array Nat := pmul T44 E4.size E4.size E8.size p q

/-! ## Matrices as arrays of 16 natural numbers (row-major) -/

abbrev Mat := Array Nat

def zeroMat : Mat := Array.replicate 16 0

/-- Linear form of entry `(i,j)`: coefficient of variable `k` is `gs[k][4i+j]`. -/
def linForm (gs : List Mat) (i j : Nat) : Array Nat :=
  Array.ofFn (n := NV) fun k => (gs.getD k.val zeroMat)[4 * i + j]!

/-- Laplace expansion (rows `{0,1}` versus `{2,3}`) of a 4×4 permanent, given
the entries `X i j`, a multiplication `m1` for 2×2 products and `m2` for the
final products. -/
def laplace (X : Nat → Nat → Array Nat) (m1 m2 : Array Nat → Array Nat → Array Nat) :
    Array Nat :=
  let p2 (r1 r2 c1 c2 : Nat) := padd (m1 (X r1 c1) (X r2 c2)) (m1 (X r1 c2) (X r2 c1))
  let t (a b c d : Nat) := m2 (p2 0 1 a b) (p2 2 3 c d)
  padd (padd (padd (t 0 1 2 3) (t 0 2 1 3)) (padd (t 0 3 1 2) (t 1 2 0 3)))
    (padd (t 1 3 0 2) (t 2 3 0 1))

/-- Entries of `M Mᵀ` as degree-2 polynomials. -/
def gramForm (gs : List Mat) (i j : Nat) : Array Nat :=
  padd (padd (mul11 (linForm gs i 0) (linForm gs j 0)) (mul11 (linForm gs i 1) (linForm gs j 1)))
    (padd (mul11 (linForm gs i 2) (linForm gs j 2)) (mul11 (linForm gs i 3) (linForm gs j 3)))

/-- `per(M)` as a degree-4 polynomial. -/
def perPoly (gs : List Mat) : Array Nat := laplace (linForm gs) mul11 mul22

/-- `per(M Mᵀ)` as a degree-8 polynomial. -/
def perGramPoly (gs : List Mat) : Array Nat := laplace (gramForm gs) mul22 mul44

/-- The positive part `32 per(M)^2`. -/
def posPart (gs : List Mat) : Array Nat := psmul 32 (mul44 (perPoly gs) (perPoly gs))

/-- The negative part `3 per(M Mᵀ)`. -/
def negPart (gs : List Mat) : Array Nat := psmul 3 (perGramPoly gs)

/-- Coefficientwise comparison. -/
def dominates (a b : Array Nat) : Bool :=
  a.size == b.size && (List.range a.size).all fun i => b[i]! ≤ a[i]!

/-- Leaf test: all coefficients of `32 per(M)^2 - 3 per(M Mᵀ)`, `M = ∑ t_k g_k`,
are nonnegative. -/
def polyCheck (gs : List Mat) : Bool :=
  gs.length ≤ NV && dominates (posPart gs) (negPart gs)

/-! ## Faces of the Birkhoff polytope -/

/-- The 24 permutations of `{0,1,2,3}` as image lists. -/
def permList : List (List Nat) :=
  [0, 1, 2, 3].flatMap fun a => [0, 1, 2, 3].flatMap fun b => [0, 1, 2, 3].flatMap fun c =>
    [0, 1, 2, 3].filterMap fun d =>
      if a != b && a != c && a != d && b != c && b != d && c != d then some [a, b, c, d]
      else none

def permMask (p : List Nat) : Nat :=
  (List.range 4).foldl (fun acc i => acc ||| (1 <<< (4 * i + p.getD i 0))) 0

def permMat (p : List Nat) : Mat :=
  Array.ofFn (n := 16) fun e => if p.getD (e.val / 4) 0 == e.val % 4 then 1 else 0

def subMask (a b : Nat) : Bool := a &&& b == a

def permsIn (S : Nat) : List (List Nat) := permList.filter fun p => subMask (permMask p) S

def closureOf (ps : List (List Nat)) : Nat := ps.foldl (fun acc p => acc ||| permMask p) 0

def matAdd (a b : Mat) : Mat := Array.zipWith (· + ·) a b

def centerOf (ps : List (List Nat)) : Mat :=
  ps.foldl (fun acc p => matAdd acc (permMat p)) zeroMat

def allOnes : Mat := Array.replicate 16 1

/-- A symmetry: a pair (row permutation, column permutation). -/
abbrev Sym := List Nat × List Nat

def symList : List Sym := permList.flatMap fun r => permList.map fun c => (r, c)

/-- Image of entry index `e = 4i+j` under a symmetry. -/
def symIdx (g : Sym) (e : Nat) : Nat := 4 * g.1.getD (e / 4) 0 + g.2.getD (e % 4) 0

def actMask (g : Sym) (S : Nat) : Nat :=
  (List.range 16).foldl (fun acc e => if S.testBit e then acc ||| (1 <<< symIdx g e) else acc) 0

def fixesMat (g : Sym) (M : Mat) : Bool :=
  (List.range 16).all fun e => M[symIdx g e]! == M[e]!

/-- Line sums of `V` are all equal. -/
def lineSumsEq (V : Mat) : Bool :=
  let r (i : Nat) := V[4*i]! + V[4*i+1]! + V[4*i+2]! + V[4*i+3]!
  let c (j : Nat) := V[j]! + V[4+j]! + V[8+j]! + V[12+j]!
  r 1 == r 0 && r 2 == r 0 && r 3 == r 0 && c 0 == r 0 && c 1 == r 0 && c 2 == r 0 &&
    c 3 == r 0

/-- `V` is positive exactly on the mask `S`. -/
def suppOK (V : Mat) (S : Nat) : Bool :=
  (List.range 16).all fun e => (decide (0 < V[e]!)) == S.testBit e

/-- Candidate children: closures of `S` with one entry removed. -/
def candidates (S : Nat) : List Nat :=
  ((List.range 16).filter fun e => S.testBit e).map fun e =>
    closureOf (permsIn (S &&& ((2^16 - 1) ^^^ (1 <<< e))))

/-- Maximal elements (under inclusion), deduplicated. -/
def maximals (l : List Nat) : List Nat :=
  (l.filter fun a => !(l.any fun b => subMask a b && a != b)).eraseDups

/-- Recursive certificate check of the face-state `(pre, S)`. -/
def checkNode : Nat → List Mat → Nat → List Sym → Bool
  | fuel, pre, S, G =>
    let ps := permsIn S
    if ps.length ≤ 1 then polyCheck (pre ++ ps.map permMat)
    else match fuel with
    | 0 => false
    | fuel + 1 =>
      let S' := closureOf ps
      let V := centerOf ps
      let cands := candidates S'
      let facets := maximals cands
      let G' := G.filter fun g => fixesMat g V
      decide (pre.length < NV) && suppOK V S' && lineSumsEq V &&
      (cands.all fun c => facets.any fun f => subMask c f) &&
      (facets.foldl (fun (acc : Option (List Nat)) f =>
          match acc with
          | none => none
          | some reps =>
            if reps.any (fun r => G'.any fun g => actMask g f == r) then some reps
            else if checkNode fuel (pre ++ [V]) f G' then some (f :: reps) else none)
        (some [])).isSome

/-- One step of `checkNode` with the recursive calls replaced by an explicit list `reps`
of facet representatives (used to split the certificate into independent pieces). -/
def splitCheck (pre : List Mat) (S : Nat) (G : List Sym) (reps : List Nat) : Bool :=
  let ps := permsIn S
  let S' := closureOf ps
  let V := centerOf ps
  let cands := candidates S'
  let facets := maximals cands
  let G' := G.filter fun g => fixesMat g V
  decide (1 < ps.length) && decide (pre.length < NV) && suppOK V S' && lineSumsEq V &&
    (cands.all fun c => facets.any fun f => subMask c f) &&
    (facets.all fun f => reps.any fun r => r == f || G'.any fun g => actMask g f == r)

/-- The facet `x₀₀ = 0` of the Birkhoff polytope. -/
def maskF : Nat := (2^16 - 1) ^^^ 1


end Gyires
