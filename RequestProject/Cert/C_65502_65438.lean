import RequestProject.Cert.Defs

/-! One piece of the certificate: the subtree below facets `65502` and `65438`. -/

namespace Gyires

theorem cert_65502_65438 : checkNode 14 (pre2 65502) 65438 (G2 65502) = true := by
  native_decide

end Gyires
