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

## Appendix A manuscript status

There are no remaining proof obligations for the current Appendix A
statements.

The ordinary induced construction and strict sparsening theorem are explicitly
relational, matching the checked Lean development and the source construction.
The direct set-valued-function reading of sparsening with fibre-surjective
homomorphisms is false; the checked
`FullFunctionalSparseningObstruction.direct_functional_sparsening_false`
records this scope boundary.

The formerly problematic arbitrary-projection Picture claim has also been
removed.  The manuscript now states the exact checked closed-alpha Picture
Lemma (`Closed.Picture.pictureLemma`).  Arbitrary projections in the
recursive theorem use
`Partite.SemiClosed.Picture.pictureLemma`, whose intermediate little picture
is D-partite but is not required to be U-transversal.

The former synchronized ambient-A tree condition is not a claim of the
current Appendix; the checked local-tree-completability statement is the
invariant actually used by sparsening.

Optional stronger variants and diagnostic modules remain useful research
infrastructure, but they are not manuscript validation obligations.


### Actual U-closed weak-vertex iteration (8 October 2026)

The full positive-arity functional Ramsey construction has now been
formally iterated with **weak** vertex-set graph completions.
`Partite.Closed.Picture.locallyTreeLike_weakStep` transfers the
controlled relational locally-tree-like invariant through the exact
U-closed Picture stage, including its restricted family of closed attaching
maps.  The finite closed Ramsey trace and n-pass iteration are the theorems
`Partite.Closed.Construction.inducedConstruction_withStrongTree` and
`Structure.inducedRamsey_iteratedWeakGraph`.  CI checks the latter
under graph-hereditary irreducibility of A and positive function arities.

The final output retains the **full function-language Ramsey arrow** and a
graph homomorphism-embedding to the original control.  Every weak vertex
test of size at most n has a controlled relational graph-tree completion,
hence every *genuine function-closed* test of this size inherits that
graph-level conclusion without adding closure vertices.

**Distinct target-side obligation.**  A relational tree amalgam of
function graphs may have non-closed roots, and a graph homomorphism-embedding
of a closed test need not be fibre-surjective.  The verified bridge
`RelStructure.FunctionClosedLocallyTreeCompletable.toFunctional`
does yield genuine strict functional tree completions **once** the graph
tree's gluing roots and local test map are function-closed.  The n-pass
weak-vertex theorem alone does not supply these additional certificates.

The direct functional version should use `FunctionalPartite.EHN.pictureLemma`
and `FunctionalPartite.EHN.inducedConstruction_preserving` on genuine
functions. Its selected supports are already function-closed by
`System.weak_support_closed`, so it requires no U-closed relational graph
expansion. The verified n-pass **U-closed** route above is an optional
representation theorem; it should not be confused with the native
function-language induction still to be established. U-closed graph
embeddings serve the separately checked recursive construction, whose
intermediate graph stages need repair to restore intended functions.
This is the precise remaining issue for an optional stronger functional
sparsening theorem; it is not a gap in the relational Appendix theorem.


## Validation discipline

CI builds the umbrella and all audit imports, then checks every declaration in
`CheckAxioms.lean`, `CheckClosureAxioms.lean`, and
`CheckEHNFunctions.lean`. Only `propext`, `Classical.choice`, and
`Quot.sound` are accepted. Missing audit results, `sorryAx`, and custom
unproved axioms fail. Survey markers must be pinned to a successful immutable
proof commit.
