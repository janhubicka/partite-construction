# Survey EPPA definition bridge: independent build

This directory is a **standalone** Lean 4.34.1 project, separate from the
`partite-construction` root project's Lean toolchain and Mathlib version.

Its `SurveyEPPA.lean` is a validation mirror of the same file in draft survey
PR [#69](https://github.com/janhubicka/Ne-et-il-s-classification-programme-of-Ramsey-classes/pull/69).
The project uses the verified external `AllThoseEPPA` library at the pinned
commit `8bc10cdde68e997eb0a456e1a7c1a4a152fbf309`.

Run:

```sh
cd SurveyEPPAValidation
lake update
lake exe cache get
lake build SurveyEPPA
lake env lean AxiomAudit.lean
```

The GitHub workflow `survey-eppa-bridge.yml` performs this on public CI so
that a private-repository runner problem cannot be mistaken for a Lean result.
Changes to survey-source proofs should be kept in sync in both repositories;
a green public run validates only the exact mirrored source commit.
