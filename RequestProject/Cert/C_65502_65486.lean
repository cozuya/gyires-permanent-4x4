import RequestProject.Cert.Defs

/-! One piece of the certificate: the subtree below facets `65502` and `65486`. -/

namespace Gyires

theorem cert_65502_65486 : checkNode 14 (pre2 65502) 65486 (G2 65502) = true := by
  native_decide

end Gyires
