# Summary of changes for run c0b83b52-1589-49c2-8e0b-1c2ce7b64682
Not quite. What has been proved is the 4×4 case. That is a real, machine-checked result, but it is not a proof of a general conjecture.

**What I re-checked this session:** I rebuilt the whole project from scratch and it completed without errors. There is no `sorry`, no added `axiom` and no `@[implemented_by]` anywhere in the project. `#print axioms Gyires.gyires_4x4` lists only `propext`, `Classical.choice`, `Quot.sound`, `Lean.ofReduceBool` and `Lean.trustCompiler`. The last two come from `native_decide`, so the result also depends on the Lean compiler being correct, not only on the kernel.

**What the theorem says** (`RequestProject/Gyires.lean`): for every real doubly stochastic 4×4 matrix \(A\),
\[ 3\,[\mathrm{per}(AA^T)+\mathrm{per}(A^TA)+2\,\mathrm{per}(A^2)] \le 128\,\mathrm{per}(A)^2. \]
Equality holds at the matrix with every entry \(1/4\). The proof is computer-assisted: an exhaustive certificate covering 71,376 cones, checked inside Lean by a checker that is itself proved sound.

**Why that doesn't settle "the conjecture":**
- **Only \(n=4\).** If the conjecture you mean is for all sizes \(n\), the natural general form is \(\mathrm{per}(AA^T)+\mathrm{per}(A^TA)+2\,\mathrm{per}(A^2) \le \frac{4n^n}{n!}\,\mathrm{per}(A)^2\). At \(n=4\) the constant is \(128/3\), which matches. This project proves only that case. Nothing here covers \(n \ge 5\), and the method (splitting the 4×4 doubly stochastic matrices into cones and checking each one) does not extend to all \(n\) as it stands.
- **History not checked.** I can't confirm from the project the conjecture's exact original wording, its date (so not the "48 years" either), or whether the 4×4 case was already known. I didn't check the literature. If Gyires' original statement was specifically about 4×4 matrices, the answer becomes "yes, that case". If it was for all \(n\), the answer is "one case of it".

So the accurate description is a formally verified proof of Gyires' inequality for 4×4 doubly stochastic matrices, which relies on trusting the compiler. I made no changes to the project this session.