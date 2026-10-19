import RequestProject.Cert.Assemble
import GyiresEquality.StrictSound
import GyiresEquality.Cert.S_65502_64478
import GyiresEquality.Cert.S_65502_64990
import GyiresEquality.Cert.S_65502_65246
import GyiresEquality.Cert.S_65502_65438
import GyiresEquality.Cert.S_65502_65486
import GyiresEquality.Cert.S_65502_65498
import GyiresEquality.Cert.S_65502_65500
import GyiresEquality.Cert.S_65518_65006
import GyiresEquality.Cert.S_65518_65486
import GyiresEquality.Cert.S_65518_65516
import GyiresEquality.Cert.S_65532_65468
import GyiresEquality.Cert.S_65532_65500
import GyiresEquality.Cert.S_65532_65516

/-!
# Assembling the strict certificate

The split lemmas `split_root`, `split_65532`, `split_65518`, `split_65502` and the symmetry
facts `hG0`, `hG1`, `hG2` are reused from `RequestProject.Cert.Assemble`; they do not
involve the leaf test.
-/

namespace Gyires

lemma leafS (f1 f2 : ℕ) (h : checkNodeS 14 (pre2 f1) f2 (G2 f1) = true) :
    FaceStateS ([allOnes, V0] ++ [centerOf (permsIn f1)]) f2 :=
  checkNodeS_sound 14 (pre2 f1) f2 (G2 f1) (by simp [pre2]) (hG2 f1) h

lemma faceS_65532 : FaceStateS [allOnes, V0] 65532 := by
  refine splitCheckS_sound (by simp) hG1 split_65532 ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact leafS _ _ certS_65532_65516
  · exact leafS _ _ certS_65532_65500
  · exact leafS _ _ certS_65532_65468

lemma faceS_65518 : FaceStateS [allOnes, V0] 65518 := by
  refine splitCheckS_sound (by simp) hG1 split_65518 ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact leafS _ _ certS_65518_65516
  · exact leafS _ _ certS_65518_65486
  · exact leafS _ _ certS_65518_65006

lemma faceS_65502 : FaceStateS [allOnes, V0] 65502 := by
  refine splitCheckS_sound (by simp) hG1 split_65502 ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact leafS _ _ certS_65502_65500
  · exact leafS _ _ certS_65502_65498
  · exact leafS _ _ certS_65502_65486
  · exact leafS _ _ certS_65502_65438
  · exact leafS _ _ certS_65502_65246
  · exact leafS _ _ certS_65502_64990
  · exact leafS _ _ certS_65502_64478

theorem face_rootS : FaceStateS [allOnes] maskF := by
  refine splitCheckS_sound (by simp) hG0 split_root ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact faceS_65532
  · exact faceS_65518
  · exact faceS_65502

end Gyires
