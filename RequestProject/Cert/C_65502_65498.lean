import RequestProject.Cert.Defs

/-! One piece of the certificate: the subtree below facets `65502` and `65498`. -/

namespace Gyires

theorem cert_65502_65498 : checkNode 14 (pre2 65502) 65498 (G2 65502) = true := by
  native_decide

end Gyires
