# Track D — all non-full EHN defects cross irreducible source charts

**12 November 2026.** Development note, NOT a change to the frozen
numbered Nešetřil programme survey Appendix A or to collaborator TODOs.

## Source-matched four-theorem refinement

The already kernel-checked three-way EHN defect theorem (merged #589)
gives an actual source vertex collision, an actual source relation input
whose target incidence is newly positive, or an original source function
input that is undefined even though its target input is defined.
Under the original-2019 source-defined partial-function convention
there is NO fourth extra-output alternative for defined source inputs.

This patch proves for each case that its vertices/tuple are **not
contained together** in ANY full function-closed irreducible SOURCE test:

1. distinct colliding vertices x,y are never together inside one such
   chart, because the EHN restriction is represented by a full embedding;
2. the input vertices of a target-only positive relation tuple are
   never all contained in a full irreducible source chart, including
   when the source relation is negative;
3. the input vertices of a target-defined/source-undefined function
   tuple are never all contained in a full irreducible source chart.

The fourth named theorem packages an exhaustive cross-chart
trichotomy **without a finite-carrier hypothesis**. It strengthens the
global sufficient tuple-cover result merged as #598 by identifying a
specific uncovered ORIGINAL tuple in each non-collision failure case.

## No false target-completion or rank claim

This is an obstruction localization, NOT a history-compatible
relative strict B-tree construction. It does not assert the
source charts form disconnected components, have an acyclic
intersection graph, possess disjoint target images, or can be glued
with a common prescribed strict tree. A graph two-edge path with
an EHN map identifying endpoints already shows why local full-chart
agreement cannot imply global injectivity.

Nor does a decomposed original input hull replace the literal weak
Hales–Jewett test or imply that its decomposition sides have lower
generator rank. Generator ranks of the actual whole mixed test and
historical target-root compatibility remain separate obligations.

**Validation gate:** full exact-head Lean build and all four named
`#print axioms` checks; no new axioms/admissions. No green
validation marker for unrestricted strict functional n-pass proof.
