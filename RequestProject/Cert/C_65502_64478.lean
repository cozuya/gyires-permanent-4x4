import RequestProject.Cert.Defs

/-! One piece of the certificate: the subtree below facets `65502` and `64478`. -/

namespace Gyires

theorem cert_65502_64478 : checkNode 14 (pre2 65502) 64478 (G2 65502) = true := by
  native_decide

end Gyires
