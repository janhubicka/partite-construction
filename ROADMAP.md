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

### Optional direct functional iteration

Implement the iterated weak-substructure size bound directly on genuine
`FunctionalPartite.EHN` systems. The selected part support is closed under
actual function values by `System.weak_support_closed`, and
`System.weakRestrict` is a genuine full substructure. Use
`Structure.weakInduce` for arbitrary small weak tests, without taking
a closure hull or importing the recursive U-closed graph construction.
The already-verified U-closed n-pass theorem is a separate auxiliary
graph-level route. The remaining target-side issue for a strict functional
tree statement is closure of gluing roots and local completion maps.

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
