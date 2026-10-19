import RequestProject.Cert.Defs

/-! One piece of the certificate: the subtree below facets `65532` and `65500`. -/

namespace Gyires

theorem cert_65532_65500 : checkNode 14 (pre2 65532) 65500 (G2 65532) = true := by
  native_decide

end Gyires
