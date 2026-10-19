import RequestProject.TreeSound
import RequestProject.Cert.C_65532_65516
import RequestProject.Cert.C_65532_65500
import RequestProject.Cert.C_65532_65468
import RequestProject.Cert.C_65518_65516
import RequestProject.Cert.C_65518_65486
import RequestProject.Cert.C_65518_65006
import RequestProject.Cert.C_65502_65500
import RequestProject.Cert.C_65502_65498
import RequestProject.Cert.C_65502_65486
import RequestProject.Cert.C_65502_65438
import RequestProject.Cert.C_65502_65246
import RequestProject.Cert.C_65502_64990
import RequestProject.Cert.C_65502_64478

/-!
# Assembling the certificate pieces

The result: `Hf (t • J + x) ≥ 0` for every `t ≥ 0` and every nonnegative matrix `x` with
equal line sums vanishing at entry `(0,0)`, where `J` is the all-ones matrix.
-/

namespace Gyires

lemma symList_fixes_allOnes : symList.all (fun g => fixesMat g allOnes) = true := by
  native_decide

lemma hG0 : ∀ g ∈ symList, g ∈ symList ∧ ∀ v ∈ [allOnes], fixesMat g v = true := by
  intro g hg
  refine ⟨hg, fun v hv => ?_⟩
  rw [List.mem_singleton] at hv
  subst hv
  exact List.all_eq_true.mp symList_fixes_allOnes g hg

lemma hG1 : ∀ g ∈ G1, g ∈ symList ∧ ∀ v ∈ [allOnes, V0], fixesMat g v = true :=
  symInv_filter V0 hG0

lemma hG2 (f : ℕ) : ∀ g ∈ G2 f, g ∈ symList ∧ ∀ v ∈ pre2 f, fixesMat g v = true :=
  symInv_filter (centerOf (permsIn f)) hG1

lemma split_root : splitCheck [allOnes] maskF symList [65532, 65518, 65502] = true := by
  native_decide

lemma split_65532 : splitCheck [allOnes, V0] 65532 G1 [65516, 65500, 65468] = true := by
  native_decide

lemma split_65518 : splitCheck [allOnes, V0] 65518 G1 [65516, 65486, 65006] = true := by
  native_decide

lemma split_65502 : splitCheck [allOnes, V0] 65502 G1
    [65500, 65498, 65486, 65438, 65246, 64990, 64478] = true := by
  native_decide

lemma leaf (f1 f2 : ℕ) (h : checkNode 14 (pre2 f1) f2 (G2 f1) = true) :
    FaceState ([allOnes, V0] ++ [centerOf (permsIn f1)]) f2 :=
  checkNode_sound 14 (pre2 f1) f2 (G2 f1) (hG2 f1) h

lemma face_65532 : FaceState [allOnes, V0] 65532 := by
  refine splitCheck_sound hG1 split_65532 ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact leaf _ _ cert_65532_65516
  · exact leaf _ _ cert_65532_65500
  · exact leaf _ _ cert_65532_65468

lemma face_65518 : FaceState [allOnes, V0] 65518 := by
  refine splitCheck_sound hG1 split_65518 ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact leaf _ _ cert_65518_65516
  · exact leaf _ _ cert_65518_65486
  · exact leaf _ _ cert_65518_65006

lemma face_65502 : FaceState [allOnes, V0] 65502 := by
  refine splitCheck_sound hG1 split_65502 ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact leaf _ _ cert_65502_65500
  · exact leaf _ _ cert_65502_65498
  · exact leaf _ _ cert_65502_65486
  · exact leaf _ _ cert_65502_65438
  · exact leaf _ _ cert_65502_65246
  · exact leaf _ _ cert_65502_64990
  · exact leaf _ _ cert_65502_64478

theorem face_root : FaceState [allOnes] maskF := by
  refine splitCheck_sound hG0 split_root ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact face_65532
  · exact face_65518
  · exact face_65502

end Gyires
