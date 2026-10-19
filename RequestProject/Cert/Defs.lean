import GyiresCompute.Basic

/-!
# Data for splitting the certificate into independent pieces

The certificate tree is split at its first two levels; the vertex lists `pre` and the
symmetry groups at those levels are given by the definitions below.
-/

namespace Gyires

/-- Center of the root facet `x₀₀ = 0`. -/
def V0 : Mat := centerOf (permsIn maskF)
/-- Symmetries fixing the first two cone generators. -/
def G1 : List Sym := symList.filter fun g => fixesMat g V0
/-- Generators at the second level, below child facet `f`. -/
def pre2 (f : Nat) : List Mat := [allOnes, V0, centerOf (permsIn f)]
/-- Symmetries at the second level, below child facet `f`. -/
def G2 (f : Nat) : List Sym := G1.filter fun g => fixesMat g (centerOf (permsIn f))

end Gyires
