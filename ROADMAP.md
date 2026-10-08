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

A strict **function-language target-tree** statement is a different open
strengthening: graph tree witnesses may have non-closed gluing roots and local
maps need not preserve the entire target function fibre.
The necessity of a separate target-side argument is now formally witnessed
by `FunctionalClosedTestGraphObstruction.closedSource_graphCompletion_not_fullCompletion`
(merged Lean #109): even an entire closed function source can have a
strict graph-tree B-completion but no full function-tree B-completion.
This does not disprove a native-EHN-specific strengthening.

## Remaining proof obligations

There are no remaining proof obligations for the statements currently printed
in Appendix A.

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
