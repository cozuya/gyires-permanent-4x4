import RequestProject.Cert.Defs
import GyiresStrictCompute.Basic

/-! One piece of the strict certificate: the subtree below facets `65502` and `64478`. -/

namespace Gyires

theorem certS_65502_64478 : checkNodeS 14 (pre2 65502) 64478 (G2 65502) = true := by
  native_decide

end Gyires
