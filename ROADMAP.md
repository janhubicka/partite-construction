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

## Remaining proof obligations

1. Complete the separate **functional iterated sparsening** theorem.  Weak
   substructures are already exactly induced graph restrictions, and the
   failure of naive relational tree transfer is isolated by the checked
   `FunctionalTreeTransferObstruction`.  The required positive target
   interface is now formalized as `FunctionClosedTreeAmalgam`: closed gluing
   roots force closed side embeddings and full decoded constituent copies.
   The remaining work is propagation of this invariant through the
   Picture/trace iteration and the final support-group sparsening phase.
2. Resolve the editorial status of the stronger arbitrary-alpha
   `lem:indpicutreU`: replace its printed argument by the checked domain-aware
   semi-closed version or prove the stronger assertion independently.

The former synchronized ambient-A invariant has been replaced in the survey by
the exact checked local-tree-completability statement.  It is optional stronger
work, not a prerequisite for the sparsening theorem.

Constants are **not** a remaining EHN or survey-`thm:HN` obligation.

## Editorial follow-through

Use the all-arity EHN endpoints in the survey and mark `thm:HN` fully
verified.  Keep the direct globally fibre-surjective functional partite
formulation separate from the checked weak global projection formulation.
Do not silently replace irreducibility by hereditary irreducibility.
