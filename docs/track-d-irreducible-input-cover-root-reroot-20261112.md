# Track D — EHN full reflection from irreducible input-test coverage

**12 November 2026.** This note belongs only to the proof-development
repository; the frozen numbered Appendix A manuscript is unchanged.

## New source-only criterion

For a genuine original-function-language structure C, define two explicit
source properties:

* Every OLD relation input tuple `xs`, **whether or not the source
  relation holds**, is contained in the carrier of a FULL induced
  irreducible, function-closed source test `C|S`.
* Every OLD function input tuple `xs`, **including source-undefined
  inputs**, is covered by such a FULL irreducible source test.

For an EHN projection `p:C→D`, the full embedding supplied on each
irreducible test then reflects (1) target-positive relations and (2)
target-defined function-domain status back to C, for the SAME ACTUAL
original source tuples. No global injectivity is needed for either
reflection statement. If `p` is additionally vertex-injective,
the previously verified three-defect equivalence upgrades `p` to a
FULL structure embedding on exactly its original vertex map.
Full fibre equality on source-defined tuples was already established
by EHN; no extra total-fibre hypothesis was inserted.

## Positive strict-relative target application

Suppose an absolute strict original-partial B-tree completion
`p:Side→T` has an injective restriction `p∘s` to a chosen full
separator `s:Root↪Side`. If Root satisfies both input-cover properties
and `p(s(Root))` lies inside one specified irreducible B-copy of T,
then the previous positive reroot theorem yields a relative strict
completion over any prescribed FULL `Root↪Base`. Root itself need
not be irreducible, and the SIDE map p may be noninjective away from Root.

## Sharp limitations

This is a SUFFICIENT source-cover condition, not an assertion that
an arbitrary mixed Hales–Jewett separator has those covers. The
requirements deliberately include source-negative relations and
source-undefined function inputs; covering only positive source
incidences would NOT imply relation/domain reflection.

The remaining maximal-mixed history problem may have a NONINJECTIVE
canonical root projection and need a larger common strict Start tree
instead of a full Root↪Base embedding. No old-copy historical relative
target has been constructed by this patch. None of the source-test
covering hypotheses follows merely from the input-generator crossing
certificates of merged PR #589.

**DRAFT until exact-head full Lean build and four named axiom checks
pass.** No author TODO or validation marker in the survey is restored.
