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
lake build SurveyEPPA SurveyEPPACompletion SurveyEPPANullary
lake env lean AxiomAudit.lean
```

The GitHub workflow `survey-eppa-bridge.yml` performs this on public CI so
that a private-repository runner problem cannot be mistaken for a Lean result.
Changes to survey-source proofs should be kept in sync in both repositories;
a green public run validates only the exact mirrored source commit.

## Independently validated results

At revision `e16dc97beefb4e2b20a335f78d80f1b91f033d8a`, public
[GitHub Actions run 38270183111](https://github.com/janhubicka/partite-construction/actions/runs/38270183111)
successfully built all three modules and audited their named theorems for
`sorryAx` dependencies. The same three Lean files in survey draft PR #69
have identical Git blob SHAs.

The bridge establishes the exact unary-function homomorphism-embedding
equivalence, unrestricted and restricted faithful/coherent EPPA, the survey
locally finite EPPA class transfer, EPPA+JEP⇒AP, Proposition 11.3 with
survey exact-fibre completions, and a fixed-nullary-relation encoding.
It deliberately does **not** assert the unconditional forbidden-homomorphism
statement incorrectly printed in the survey.
