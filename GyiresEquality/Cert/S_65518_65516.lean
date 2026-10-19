import RequestProject.Cert.Defs
import GyiresStrictCompute.Basic

/-! One piece of the strict certificate: the subtree below facets `65518` and `65516`. -/

namespace Gyires

theorem certS_65518_65516 : checkNodeS 14 (pre2 65518) 65516 (G2 65518) = true := by
  native_decide

end Gyires
