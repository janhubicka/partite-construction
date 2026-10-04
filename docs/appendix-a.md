# Appendix A: current coverage and exact scope

The previous chronological inventory is preserved in
[the historical coverage log](archive/appendix-a-before-closure-audit.md).
Historical TODOs in that log are not current proof obligations.

## Construction routes

| Survey component | Lean endpoint (under `StructuralRamsey`) | Exact scope |
| --- | --- | --- |
| Non-induced construction / ordered relational theorem | `Partite.orderedRamsey` | Finite relational structures; all pictures constructed |
| Induced construction | `Partite.Induced.inducedConstruction` | Relational projection invariant and finite trace |
| Functions as graph relations | `Structure.embeddingEquivClosedGraph` | Full functional embeddings correspond to closed graph embeddings, not arbitrary homomorphisms |
| Closed Partite Lemma | `Partite.Closed.Induced.partiteLemma` | U-transversal input |
| Closed-alpha Picture Lemma | `Partite.Closed.Picture.pictureLemma` | The prescribed alpha is closed |
| Domain-aware semi-closed Picture | `Partite.SemiClosed.Picture.pictureLemma` | The intermediate little picture need not be U-transversal |
| Half-closed construction, `lem:rpartite` | `Partite.HalfClosed.ramseyPartiteWitness` | Positive arity; no input-D transversality assumption |
| Recursive theorem, `thm:models2` | `Structure.orderedClosedGraphRamsey` | Positive-arity set-valued functions |
| Closure observations | `RelStructure.IsFreeAmalgam.sides_closed_iff` / `common_image_closed_iff` | Both directions; arbitrary full diagram; local statements allow constants |
| Closed hull of a weak image | `Structure.Irreducible.functionClosure_weakImage` | Full irreducible source; target is the closed hull, not the raw coordinate range; constants allowed |
| Functional Partite Lemma | `FunctionalPartite.Induced.weak_partiteLemma_withInvariant` | Weak projection globally; full embeddings on closed irreducibles; full Ramsey embeddings |
| All-arity initial EHN picture | `FunctionalPartite.EHN.initial_allArity` | Initial B-copies are amalgamated over the canonical nullary root |
| Functional class-preserving refinement | `FunctionalPartite.EHN.inducedConstruction_allArity` | One pass; arbitrary function arities; arbitrary full Ramsey witness D; A,B in K |
| Rooted unrestricted functional EHN | `Rooted.Structure.FreeAmalgamationClass.orderedRamsey_allArity` | Hereditary full free-amalgamation class; arbitrary set-valued function arities; constants included |
| Exact ordered forbidden-pattern theorem, `thm:HN` | `Structure.orderedRamsey_forbidden_expansions_allArity` | Arbitrary function arities; forbidden structures may specify orders; only their reducts must be irreducible |
| Strict relational sparsening | `Partite.IteratedSparsening.sparseningRamsey_strict_baseIrreducible_all` | B irreducible; A arbitrary; independent of the unresolved stronger synchronized invariant |
| Function-closed tree amalgam interface | `RelStructure.FunctionClosedTreeAmalgam.irreducible_contained_in_full_copy` | Strict relational tree geometry plus closed gluing roots; side embeddings stay closed and constituent copies decode to full function embeddings |

The all-arity endpoints are in
`Ramsey/FreeAmalgamationFunctionsAllArity.lean` and
`Ramsey/ForbiddenFunctionsAllArity.lean`; the class-preserving pass is in
`Functional/EHNConstruction.lean`.  The umbrella import exposes them all.

## Constants and the fixed-root reduction

For a finite structure A, the canonical root
`A.nullaryRoot = A.functionClosure ∅` is contained in every closed
substructure and is carried **onto** the target root by every full embedding.

The rooted formalization then:
1. separates each tuple into fixed-root and moving coordinates;
2. encodes all root incidences in a positive-arity moving language;
3. proves encode/decode correctness and full embedding transport;
4. transports concrete free amalgams and hereditary free-amalgamation classes;
5. reconstructs the full linear order from root cuts and the moving order.

This proves the unrestricted all-arity Ramsey theorem.  Independently, the EHN
initial picture now handles constants directly by gluing placements of B over
their common canonical root.  Therefore constants are no longer either a
mathematical or a formalization restriction on `thm:HN`.

## Simplifications and precise distinctions

The two local closure observations follow from one statement: a subset is
closed in a free amalgam iff its inverse images in both sides are closed.  This
does not require positive arity.

The Hales--Jewett line-map exactness proof uses one parameter coordinate and
output transversality of the whole power.  The EHN projection is weak globally
and full on full irreducibles; this is
`Structure.IsEHNHomomorphismEmbedding`.  The existing graph-encoding
`Structure.IsWeakHomomorphismEmbedding` remains a different notion.

For the exact survey theorem, particular ordered forbidden structures are not
replaced by all orderings of their reducts.  `OrderTotalOnIrreducibles`
ensures that final order completion creates no new forbidden embedding.

## Remaining manuscript obligations

1. **Functional iterated sparsening.** Weak restriction itself is already
   exact under graph encoding (`weakInduce_graph_rel_iff`).  The naive
   relational transfer fails by
   `Structure.FunctionalTreeTransferObstruction.target_not_singletonValued`:
   a non-closed gluing root can create extra function outputs.  The positive
   target interface is now checked as `FunctionClosedTreeAmalgam`.  Its
   gluing roots are closed; `glue_sides_closed` proves every side embedding
   remains closed, and `irreducible_contained_in_full_copy` shows constituent
   copies decode to full function embeddings.  What remains is to propagate
   this closed-tree invariant through the Picture/trace iteration and final
   sparsening construction.
2. **Arbitrary-alpha Picture statement.** Replace the printed argument by the
   checked domain-aware version or prove the stronger assertion separately.

The former synchronized ambient-A tree condition is no longer an Appendix
proof obligation: the manuscript now states the exact local-tree-completability
invariant used by the sparsening proof.  It may still be studied as an optional
stronger theorem.

The original globally fibre-surjective functional induced formulation is not
silently proved by the EHN weak-projection theorem; keep the interfaces
explicitly distinct.

## Validation discipline

CI builds the umbrella and all audit imports, then checks every declaration in
`CheckAxioms.lean`, `CheckClosureAxioms.lean`, and
`CheckEHNFunctions.lean`. Only `propext`, `Classical.choice`, and
`Quot.sound` are accepted. Missing audit results, `sorryAx`, and custom
unproved axioms fail. Survey markers must be pinned to a successful immutable
proof commit.
