import RequestProject.Cert.Defs

/-! One piece of the certificate: the subtree below facets `65518` and `65486`. -/

namespace Gyires

theorem cert_65518_65486 : checkNode 14 (pre2 65518) 65486 (G2 65518) = true := by
  native_decide

end Gyires
