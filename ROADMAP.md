# Roadmap

The target remains all of Appendix A, with reusable endpoints and survey
markers pinned to successful immutable Lean commits.  The current coverage map
is [docs/appendix-a.md](docs/appendix-a.md); older chronological notes are
historical only.

## Completed routes

The relational non-induced and induced constructions, the local closure
calculus, and the positive-arity recursive theorem for set-valued functions
are checked.

The **functional EHN theorem is now complete for arbitrary arities**, including
nullary set-valued functions/constants.  The proof contains:

- the canonical nullary root and full rooted encode/decode construction;
- transport of full embeddings, free amalgams, and free-amalgamation classes;
- reconstruction of the global order from root cuts and the moving order;
- `Rooted.Structure.FreeAmalgamationClass.orderedRamsey_allArity`;
- an all-arity EHN initial picture gluing B-copies over their canonical root;
- `FunctionalPartite.EHN.inducedConstruction_allArity`;
- the exact ordered forbidden-pattern theorem
  `Structure.orderedRamsey_forbidden_expansions_allArity`.

The global EHN projection remains weak and becomes a full embedding on each
full irreducible; all embeddings in the Ramsey arrow are full embeddings.
This distinction is intentional.

Strict relational sparsening with B irreducible and arbitrary A is checked
through the complete binary-relation expansion and does not depend on the
stronger synchronized tree invariant.

### Completed direct functional iteration

The positive-arity native EHN iteration with weak-substructure size control
is fully verified as
`Structure.inducedRamsey_directFunctionalWeakGraph` (merged #104, successful
build and axiom audit on proof head
`9bd2c03388a3c778b84a6f344b7464c32b8c9088`).

Every stage carries genuine set-valued functions. The weak EHN projection
makes the selected A-support function-closed, so the Hales--Jewett power and
full free attachments proceed directly in the function language.
The controlled local tree invariant is tested on arbitrary **weak**
substructures, of at most n vertices, without enlarging tests to their
function-closed hulls. One whole induced Ramsey pass raises the rank by one.
The result preserves class membership, the full functional Ramsey arrow, and
a weak EHN projection back to the original witness D.

The older U-closed n-pass graph theorem remains a correct auxiliary route
but is unnecessary for this iteration. U-closed relational stages belong to
the separately checked recursive construction, which temporarily lacks the
intended function-structure constraints.

### Published two-case native proof, combined invariants (15 October 2026)

The author-uploaded published Appendix A proof uses initial pictures, a
two-case induction on the exact projected vertex test, n complete passes,
and final B-attachments. In merged PR #273, the initial Picture, Hales–Jewett
Picture step, and one entire pass now retain weak function-GRAPH tree control
and projected B-copy coverage on the **same** genuine functional stage.
See `EHNCombinedInitialWeakTreeCover`, `EHNCombinedPictureWeakTreeCover`
and `EHNCombinedConstructionWeakTreeCover`. The unrestricted corrected
endpoint `sparseningRamsey_nativeFunctional_graphStrict_withBCover_unrestricted`
is also exported. Full build and axioms passed in Actions run 38648195271.
The strong strict full-FUNCTION local tree gluing of reducible mixed roots
remains unproved; do not conflate it with the function-GRAPH conclusion.

### Stronger native functional final sparsening (14 October 2026)

The actual published-style final B-copy attachment is now combined with
the native n-pass graph-tree result, without running any new recursive
partite construction:
`Structure.sparseningRamsey_nativeFunctional_graphStrict_withBCover`.
The theorem gives the Ramsey arrow, a global original-2019 partial-function
homomorphism-embedding (equivalently EHN), exact n-vertex controlled strict
**function-graph** B-tree tests, class membership, and genuine full B-copy
extension of every irreducible source substructure. It also returns a loose
full-functional B-tree of which the final C is an instance. All assertions
were built and axiom-audited in GitHub Actions for PR #271, then merged;
the combined main build passed in run 38642478038.

The native Hales--Jewett power core itself has a strict full-functional
one-copy completion in the original partial-map convention. This extends
to its genuinely closed tests, **not** arbitrary weak tests. The actual
closed mixed separator also has a strict one-copy completion, even if
reducible, by
`FunctionalPartite.Attachment.native_closed_separator_originalPartial_oneCopy`
(merged PR #267). The stronger original-2019 strict functional theorem now has a verified
relative B-tree **gluing** step: two strict relative extensions over the
SAME possibly reducible completed root can be combined without a root
isolation assumption for bare local completion. Producing both side
extensions remains an open mathematical obligation at maximal projected
generator rank n≥2. Extra source/projected history control may require
stronger compatibility. Independent completions cannot simply be glued.
Do not confuse the fully verified strict function-GRAPH theorem, the
unconditional strict original-partial n=1 theorem, and the conditional
strict full-FUNCTION n-pass conclusion.

A strict **function-language target-tree** statement is a different open
strengthening: graph tree witnesses may have non-closed gluing roots and local
maps need not preserve the entire target function fibre.
The necessity of a separate target-side argument is now formally witnessed
by `FunctionalClosedTestGraphObstruction.closedSource_graphCompletion_not_fullCompletion`
(merged Lean #109): even an entire closed function source can have a
strict graph-tree B-completion but no full function-tree B-completion.
This does not disprove a native-EHN-specific strengthening.

### Strict full-FUNCTION original-2019 refinement (15 October 2026)

Lean now fully verifies the small-projected-GENERATOR case by closing the
exact image of a generating set and charging its **generator rank**, never
the cardinality of its potentially much larger function-closed hull.
The original-2019 partial-function projection preserves defined fibres
and does not reflect undefined input domains.

Full functional Hales–Jewett cores, initial pictures, pure mixed-attachment
sides, original-partial root gluing, the rank-zero base, and the final
B-coverage transfer are all checked. An arbitrary full functional free
amalgam generated by at most one vertex is contained in one side, so the
first genuinely mixed attachment case is vacuous. This yields
`FunctionalPartite.EHN.sparsening_originalPartial_strict_one`, a
kernel/audit-verified **unconditional n=1 theorem**, under its stated
A↪B and B-irreducibility assumptions.

The theorem
`FunctionalPartite.EHN.StrictRanked.sparsening_of_maximal_mixed_schema`
checks the **entire n-pass construction**, original-partial composite
projection, strict closed vertex-n full-function B-tree completion and
final genuine B-copy cover, **conditional** on
`StrictRanked.MaximalMixedSchema`. CI verified this conditional
implication, not the schema. The schema is exactly the existence of
two compatible relative strict B-tree completions of an actual maximal
genuinely mixed rank-n test over its same completed reducible root.
The problem remains open for n≥2. No recursive or U-closed Ramsey proof
was replayed.

### Sharpened genuine-function hard-root frontier (15 October 2026)

The rank-zero and rank-one strict original-2019 functional construction
is now unconditional, including the vacuous case without A ↪ B.
At arbitrary rank, the complete genuine EHN n-pass and final B-copy
extension are kernel-verified **conditional** on the remaining relative
completion of genuinely mixed maximal tests whose exact closed separator
requires **two or more generators**. All cases with a one-generated
separator are now discharged, even when the separator has many vertices.

More generally, the quantitative generator-budget theorem shows
that exterior source generators can pay for the generators of the
common full-functional root. With an irreducible root and sufficiently
large exterior reserves on both sides, this budget combines with
strict original-partial irreducible-root synchronization to produce
both compatible relative B-tree witnesses on one prescribed copy
of B. The full n-pass conditional theorem no longer needs a
prescribed A ↪ B embedding either: the no-copy case uses C=B.

**Still open:** the hard-root relative extension for those actual
maximal mixed native tests requiring at least two separator generators
for which exterior reserves and the checked irreducible-root
synchronization hypotheses do not suffice. None of the conditional
theorems proves this premise. This is a separate original-2019
partial-map refinement, not the printed survey's refuted total-fibre
functional formulation. Do not re-run the verified recursive Ramsey
construction while developing this remaining local step.
## Remaining proof obligations

The relational Appendix statements are checked. The requested iterated
construction with genuine functional target trees remains open; its status
must not be inferred from the narrower relational statements currently
printed in the survey.

The 20 October source calculus now also handles the requested whole-fibre
weak restriction: omit an application if any output leaves the exact test,
while retaining an originally defined-empty value. Full embeddings and
free-amalgam diagrams restrict to the exact weak sides and root, and
source-defined projections restrict to exact weak images. Complete-value
relation tuples commute with this restriction. The existing per-output
singleton closure/rank dictionary instead uses the restriction that retains
individual surviving outputs. A canonical whole-value closure description
and the actual mixed-step compatible target completions remain to be proved.

The arbitrary-alpha Picture issue was resolved by correcting the manuscript:
the ordinary Picture-with-closures lemma assumes a closed projection and is
covered by `Closed.Picture.pictureLemma`; the recursive arbitrary-projection
step is the separately checked semi-closed
`Partite.SemiClosed.Picture.pictureLemma`.

Strict sparsening is a completed relational theorem.  A direct
set-valued-function version with the survey's full fibre-surjective
homomorphism is false, as checked by
`FullFunctionalSparseningObstruction.direct_functional_sparsening_false`,
and is therefore not a pending task.

The stronger synchronized ambient-A invariant and other diagnostic variants
are optional research directions, not prerequisites for any current survey
statement.

## Editorial follow-through

Use the all-arity EHN endpoints in the survey and mark `thm:HN` fully
verified.  Keep the direct globally fibre-surjective functional partite
formulation separate from the checked weak global projection formulation.
Do not silently replace irreducibility by hereditary irreducibility.

