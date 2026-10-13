# Survey EPPA definition bridge — independent Lean library

This directory is a **standalone Lean 4.34.1 project**; it does not alter
the `partite-construction` root project's Lean/Mathlib dependencies.

Source theorem library: [shulda/lean_all_those_eppa_classes](https://github.com/shulda/lean_all_those_eppa_classes),
pinned to `8bc10cdde68e997eb0a456e1a7c1a4a152fbf309`.
The survey-facing proof modules are mirrored byte-for-byte in
[draft survey PR #69](https://github.com/janhubicka/Ne-et-il-s-classification-programme-of-Ramsey-classes/pull/69).

## Build and axiom audit

```sh
cd SurveyEPPAValidation
lake update
lake exe cache get
lake build
lake env lean AxiomAudit.lean
```

The independent GitHub workflow builds all ten modules and audits named
theorems for `sorryAx`. The exact compilation status is attached to each
run; do not infer that one green revision verifies subsequent edits.

**Green at the ten-module code revision**
`cf97666437e82fabaf77533cb8c291cb6fc71501`:
[Lean build + axiom audit run 38424354094](https://github.com/janhubicka/partite-construction/actions/runs/38424354094).

## Reusable survey theorem interfaces

- **`SurveyEPPA.lean`**: exact equality of unary function fibres for
  homomorphism-embeddings, unrestricted/restricted EPPA, direct survey
  locally finite transfer, and the conditional generalized Herwig–Lascar
  theorem with its necessary ambient-extension hypothesis.
- **`SurveyEPPAAmalgamation.lean`**: EPPA + joint embedding yields an
  amalgam in which both composites are **literally equal Γ-embeddings**.
- **`SurveyEPPACompletion.lean`**: ordinary-versus-strong completion
  equivalence with the survey's exact function-fibre convention.
- **`SurveyEPPANullary.lean`**: faithful coherent unrestricted and
  restricted EPPA with arbitrary fixed nullary relations.
- **`SurveyEPPAClassNullary.lean`**: ordinary/coherent locally finite
  transfer separately for every nullary truth-value profile.
- **`SurveyEPPAClassNullaryDirect.lean`**: the full class-level
  transfer where membership depends on all nullary truth values.
- **`SurveyEPPAForbidden.lean`**: faithful coherent EPPA for a finite
  family of forbidden irreducible embedded substructures; equivalence
  with forbidden homomorphism-embeddings for irreducible patterns.
- **`SurveyEPPAForbiddenNullary.lean`**: finite forbidden families
  indexed by arbitrary fixed-nullary profiles.
- **`SurveyEPPATree.lean`**: the paper's recursive full-source-copy
  tree amalgams satisfy the survey's less restrictive tree-amalgam
  definition for irreducible sources; restricted EPPA in this convention.
- **`SurveyEPPAForbiddenArbitrary.lean`**: arbitrary indexed families
  of forbidden irreducibles, without finiteness of the family, including
  fixed-nullary profile dependence.

There are **ten** source modules listed above, including the new arbitrary
family theorem. The workflow build target list is authoritative.

## Cautions about manuscript scope

The survey's homomorphism definition uses **equality** of function
images, while the EPPA paper uses **inclusion**; they agree for
homomorphism-embeddings in unary-function languages. The two local
finiteness conditions also differ: the survey demands an irreducible
substructure extend to a full internal copy, while the paper asks only
for embeddability into the source.

The survey's **unconditional forbidden-homomorphism** statement is false
as printed (see the directed-path counterexample in the survey's
`EPPA_VALIDATION_AUDIT.md`). Neither this project nor the source EPPA
library proves that claim. Likewise the present metric results cover
bounded **integer** distances, not arbitrary real-valued metrics or
diversities in their full generality.
