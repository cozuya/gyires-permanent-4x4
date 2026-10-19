# Summary of changes for run eb710500-b937-42c7-9500-0b756fcc6362
I found the Lean files from the earlier run. They were in the project the whole time, but they had never been published, which is why your download only contained the three Markdown files. I did not change the proof or how it is checked.

**Files that were there:** `lean-toolchain` (Lean v4.28.0), `lakefile.toml`, `lake-manifest.json`, `GyiresCompute/Basic.lean` (the certificate checker), `RequestProject/PolySound.lean` and `RequestProject/HEval.lean` (polynomial evaluation and its soundness), `RequestProject/Faces.lean` and `RequestProject/TreeSound.lean` (face covering and checker soundness), `RequestProject/Reduction.lean`, `RequestProject/Gyires.lean`, `RequestProject/Main.lean` (settings only, not used by the proof), `RequestProject/Cert/Defs.lean`, all 13 `RequestProject/Cert/C_*.lean` pieces and `RequestProject/Cert/Assemble.lean`. There are no separate certificate data files or generator scripts: each certificate piece has the checker rebuild and check its part of the certificate inside Lean. All external dependencies are git repositories pinned in `lake-manifest.json` (Mathlib commit `8f9d9cff…`); there are no local dependencies.

**What I added:** `REPRODUCE.md` and a short `scripts/PrintAxioms.lean` that prints the axioms of the final theorems.

**The archive:** `gyires-lean-complete.tar.gz` (SHA-256 `7c191f7d…ed76c`) holds all of the above under one folder, with the folder layout preserved, plus `README.md`, `RESULTS.md` and `ARISTOTLE_SUMMARY.md`. I listed the archive's own contents and confirmed it has the sources, toolchain file, Lake configuration, manifest and all 13 certificate pieces.

**Build checks:**
- I unpacked the archive into a fresh directory and confirmed its sources match the project byte for byte.
- I built it there with no earlier project build output; only the already-downloaded dependency checkouts were reused. All 8052 build jobs succeeded.
- The project itself also rebuilt cleanly, in about 7 minutes once Mathlib was available.
- There is no `sorry`, no added `axiom` and no `@[implemented_by]` anywhere.

**Actual `#print axioms Gyires.gyires_4x4` output:**
`[propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]`
`Lean.ofReduceBool` and `Lean.trustCompiler` come from `native_decide`, so the result also relies on the Lean compiler being correct, not only on the Lean kernel.

**Equality case:** only the inequality \(3[\mathrm{per}(AA^T)+\mathrm{per}(A^TA)+2\,\mathrm{per}(A^2)] \le 128\,\mathrm{per}(A)^2\) is proved in Lean. The claim that equality holds exactly when every entry is \(1/4\) is argued only in prose in `RESULTS.md` (section 4) and is not checked by Lean.

**Downloads:** the archive, `REPRODUCE.md` and every individual Lean, configuration and manifest file are now published, so the normal project download should include the Lean sources as well. `REPRODUCE.md` has the exact build commands:
```
tar xzf gyires-lean-complete.tar.gz
cd gyires-lean-complete
lake exe cache get
lake build RequestProject GyiresCompute
lake env lean scripts/PrintAxioms.lean
```