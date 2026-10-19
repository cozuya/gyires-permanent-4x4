import GyiresCompute.Basic
/-!
# Strict leaf test for the equality case

Executable code over `Nat`/`Array`, without Mathlib, extending `GyiresCompute.Basic`.
The strict leaf test additionally requires that, for every generator other than the
first (the all-ones matrix), the coefficient of the pure power `t_k^8` in
`32 per(M)^2 - 3 per(M Mᵀ)` is strictly positive. Its correctness is established in
`GyiresEquality.StrictSound`.
-/

namespace Gyires

/-- Exponent vector of the pure power `t_k^8`. -/
def pureExp (k : Nat) : Array Nat := Array.ofFn (n := NV) fun j => if j.val = k then 8 else 0

/-- Positions of the pure powers `t_k^8` in the degree-8 exponent table `E8`. -/
def pureIdxs : Array Nat :=
  Array.ofFn (n := NV) fun k =>
    ((List.range E8.size).find? fun i => E8[i]! == pureExp k.val).getD 0

/-- `pureIdxs` locates the pure powers. -/
def pureOK : Bool :=
  pureIdxs.size == NV && (List.range NV).all fun k =>
    decide (pureIdxs[k]! < E8.size) && (List.range NV).all fun j =>
      E8[pureIdxs[k]!]![j]! == if j = k then 8 else 0

/-- Strict leaf test: coefficientwise dominance, and strict dominance at every pure power
`t_k^8` with `k ≥ 1`. -/
def polyCheckS (gs : List Mat) : Bool :=
  let a := posPart gs
  let b := negPart gs
  decide (gs.length ≤ NV) && dominates a b &&
    (List.range NV).all fun k => k == 0 || decide (b[pureIdxs[k]!]! < a[pureIdxs[k]!]!)

/-- `checkNode` with the strict leaf test. -/
def checkNodeS : Nat → List Mat → Nat → List Sym → Bool
  | fuel, pre, S, G =>
    let ps := permsIn S
    if ps.length ≤ 1 then polyCheckS (pre ++ ps.map permMat)
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
            else if checkNodeS fuel (pre ++ [V]) f G' then some (f :: reps) else none)
        (some [])).isSome

end Gyires
