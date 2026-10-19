# Provenance

**Chris Ozols, with AI-assisted proof development and formalization.** Chris directed the
work and its verification.

- **Original proof, audits and literature review:** AI assistants contributed these. No
  exact model identity is asserted for that work.
- **Lean formalization of the inequality:** produced by Harmonic's
  [Aristotle](https://aristotle.harmonic.fun) ([RequestProject/](RequestProject),
  [GyiresCompute/](GyiresCompute)).
- **Rebuild, extension, cross-check and packaging:** Anthropic's Claude (Claude Opus 5.5,
  in Claude Code) independently rebuilt that formalization. It wrote the formalized
  equality case and ratio form ([GyiresEquality/](GyiresEquality),
  [GyiresStrictCompute/](GyiresStrictCompute)), [Verification.lean](Verification.lean),
  the [cross-check](crosscheck/README.md), and this package.

Nobody wrote the Lean proofs by hand. Chris Ozols is listed as author in
[CITATION.cff](CITATION.cff) as the person responsible for the work and the repository.

## Timeline

| Date (UTC) | Event | Record and its limits |
| --- | --- | --- |
| 2026-10-15, 03:39–03:47 | Original computer-assisted proof written: [write-up](original/RESULTS.md), generator, verifier and recorded output | Modification times in the private working directory; not authenticated timestamps |
| 2026-10-16 | Pre-formalization audit: two fresh complete coefficient runs, independent structural reconstruction, literature review | Private development repository, initial commit 2026-10-16 19:14 UTC |
| 2026-10-16 to 10-17 | Kernel-only Lean prototypes; restricted cones succeeded, full cones exceeded memory limits | Private development repository |
| No later than 2026-10-19 04:49 | Aristotle's Lean formalization of the inequality (runs `c0b83b52-1589-49c2-8e0b-1c2ce7b64682` and `eb710500-b937-42c7-9500-0b756fcc6362`) | Timestamps inside the exported archive; the runs' own logs were not retained |
| 2026-10-19 | Independent rebuild of the unmodified Aristotle sources; equality and ratio extension; cross-check; this package | [evidence/](evidence/verification.json) in this repository |
| 2026-10-19 | Private GitHub repository created | Git metadata |
| Not yet | First public availability | — |

Git commit dates are editable metadata, and hashes identify bytes. Neither proves
mathematical truth, an authenticated creation date, or discovery priority.

## Aristotle's formalization as received

Aristotle's export is preserved in [provenance/aristotle/](provenance/aristotle):

- the project archive `gyires-lean-complete.tar.gz`, SHA-256
  `7c191f7dd261848e384eccf42c56c98b3982a192ce3496e64662bd69af1ed76c`, the value Aristotle reported;
- its `README.md` and `REPRODUCE.md`;
- the summaries of both runs.

The `RESULTS.md` inside the export is byte-identical to the original write-up,
[original/RESULTS.original.txt](original/RESULTS.original.txt).

All Lean files in [RequestProject/](RequestProject), [GyiresCompute/](GyiresCompute) and
[scripts/PrintAxioms.lean](scripts/PrintAxioms.lean), together with `lean-toolchain` and
`lake-manifest.json`, are **byte-identical** to the archive. The only differences:

- `lakefile.toml` adds the two new libraries `GyiresStrictCompute` and `GyiresEquality`
  and lists `GyiresEquality` as a default target. Nothing else in it changed.
- The archive's empty `RequestProject/.gitkeep` and its `.gitignore` are not included.

Aristotle's run summaries are kept verbatim and contain claims this package does not
adopt:

- The run `c0b83b52` summary says "71,376 cones". The checker actually produces
  **65,376** leaf cones, as both the [cross-check](crosscheck/README.md) and the original
  computation count.
- That summary also says the method "does not extend to all n as it stands". That is an
  accurate caution about scope.

On October 19, 2026 the unmodified archive was rebuilt from source with the pinned Lean
and Mathlib. All 8,052 build jobs succeeded and the axiom report matched Aristotle's.
The record is [evidence/aristotle-asreceived-build.log](evidence/aristotle-asreceived-build.log).

Harmonic's [Aristotle terms](https://aristotle.harmonic.fun/terms) (last modified October
13, 2026) assign ownership of generated output to the user and permit its use in
open-source projects (§5.4). They require no attribution. Aristotle is credited here as a
factual description of how the formalization was produced.

## Other material

[original/](original/README.md) preserves the original proof write-up and its generator,
verifier and recorded output byte-for-byte. The write-up's exact bytes are in
`RESULTS.original.txt`; `RESULTS.md` is a display copy that changes only math markup
GitHub cannot render. They are historical computational evidence,
and are not needed to rebuild the Lean theorems. `verification.txt` is the original run's
output and carries no input identity or timing.

The private development repository `cozuya/gyires-permanent-4x4-dev` retains, unchanged:

- the full pre-formalization audit (exhaustive checks, structural reconstruction,
  benchmarks, logs);
- the literature review;
- the unsuccessful kernel-only Lean experiments.

That repository is not needed for anything here.

## Verification evidence

The package uses Lean **4.28.0** at `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b` and Mathlib
**v4.28.0** at `8f9d9cff6bd728b17a24e163c9402775d9e6a365`; [TOOLCHAIN.json](TOOLCHAIN.json)
and [lake-manifest.json](lake-manifest.json) record every pin. These versions are
Aristotle's choice and were kept unchanged. [SOURCE_SHA256SUMS](SOURCE_SHA256SUMS)
identifies every file that can affect verification, plus the preserved material.

Evidence files:

- [verification report](evidence/verification.json)
- [transcript](evidence/verification.log)
- [theorem types and axioms](evidence/kernel-check.log)
- [cross-check output](evidence/crosscheck.log)

These are fresh checks of the sources in this package. They can be repeated with
`./verify.sh` and `bash crosscheck/run.sh`.
