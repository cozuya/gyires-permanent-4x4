import RequestProject.Cert.Defs
import GyiresStrictCompute.Basic

/-! One piece of the strict certificate: the subtree below facets `65532` and `65500`. -/

namespace Gyires

theorem certS_65532_65500 : checkNodeS 14 (pre2 65532) 65500 (G2 65532) = true := by
  native_decide

end Gyires
