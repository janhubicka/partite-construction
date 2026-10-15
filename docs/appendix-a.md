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
| Native initial/Picture/full pass, *both invariants on same witness* | `FunctionalPartite.EHN.initial_weakTree_and_projectedCover`; `pictureLemma_weakTree_and_projectedCover`; `inducedConstruction_weakTree_and_projectedCover` | Native Hales–Jewett power; positive-arity weak vertex tests; projected irreducible B-cover; one actual full Ramsey pass; verified together, no recursive replay |
| Native class-free corrected graph-tree sparsening | `Structure.sparseningRamsey_nativeFunctional_graphStrict_withBCover_unrestricted` | No specified free-amalgamation subclass; weak/original-partial projection, n-vertex relational function-graph trees, and full B-extension; not the printed total-fibre theorem |
| Native functional n-pass iteration | `Structure.inducedRamsey_nativeFunctionalIteration_originalPartial_all` | Positive function arity, free amalgamation K, graph-hereditarily irreducible A, finite nonempty colours; exact weak vertex tests and original 2019 partial projection |
| Native functional graph-tree sparsening **with final B-coverage** | `Structure.sparseningRamsey_nativeFunctional_graphStrict_withBCover` | Preserves the same Ramsey arrow, original-partial projection, strict *relational function-graph* local trees, and extension of every irreducible to a genuine B-copy; NOT a strict functional local-tree theorem |
| Native closed mixed separator | `FunctionalPartite.Attachment.native_closed_separator_originalPartial_oneCopy` | One-copy strict original-partial completion for the actual common closed separator, even if reducible; compatible relative side completions remain open for maximal mixed rank ≥2; root isolation is not necessary for bare original-partial gluing |
| Original-partial strict full-functional gluing | `Structure.IsFreeAmalgam.originalPartialTreeCompletion_glue_relative` | Fully checked relative gluing over one strict completed, possibly reducible root; **does not construct compatible side extensions** |
| Exact projected generator drop | `Structure.HasOriginalPartialTreeCompletion.of_EHN_generator_image_drop` | Strict full-functional B-tree target in original-2019 partial-function sense; the closed image hull is charged by its generators, not its vertex count |
| One genuine strict functional induced pass (conditional) | `FunctionalPartite.EHN.inducedConstruction_originalPartial_generatorRank_of_maximal_mixed` | Full function-language Ramsey arrow and generator-rank n invariant conditional on the maximal mixed-root relative extension request |
| Complete strict original-partial n-pass and final B-cover (conditional) | `FunctionalPartite.EHN.StrictRanked.sparsening_of_maximal_mixed_schema` | **CI verified conditional theorem**; uniform `MaximalMixedSchema` not established for n≥2; original global projection is partial, not total-fibre |
| Rank-zero and rank-one native strict functional sparsening | `Structure.closed_rank_zero_originalPartial_completion_of_arrow`; `FunctionalPartite.EHN.sparsening_originalPartial_strict_one` | **Unconditional** (for n=1, with A↪B and B irreducible); mixed full free-amalgam tests are impossible with ≤1 generator, hence strict full-functional B-trees for closed one-vertex tests |
| Rank-one no-A-copy strict functional sparsening | `FunctionalPartite.EHN.sparsening_originalPartial_strict_one_all` | **Unconditional** n=1 original-2019 strict functional B-trees on genuine closed vertex tests; B irreducible, positive function arity; no prescribed A↪B |
| Irreducible-root strict synchronization | `Structure.IsFreeAmalgam.originalPartialTreeCompletion_of_irreducible_root` | Turns independent absolute strict original-partial completions of two sides into compatible relative completions over one prescribed B-copy; side completion hypotheses explicit |
| One-generated actual native separator | `FunctionalPartite.Attachment.native_closedTest_oneGeneratedRoot_compatibleRelativeCompletions` | **Verified** both shared strict relative B-tree witnesses even for multi-vertex common root generated by one element, if full mixed closed test is n-generated and both side rank-n invariants hold |
| Quantitative root generator budget | `Structure.IsFreeAmalgam.left_generatedByAtMost_of_exterior_root_seeds` | A finite set of outside source generators pays for the same number of root generators; arbitrary full set-valued function arities, no root-size bound |
| Irreducible root + exterior reserves | `Structure.IsFreeAmalgam.compatibleOriginalPartialRelativeCompletions_of_exterior_root_budget` | **Verified** shared relative witnesses when each side has enough exterior source generators to pay for the common irreducible root's generators |
| Sharp n-pass strict functional conditional theorem | `FunctionalPartite.EHN.StrictRanked.sparsening_of_hard_root_schema_from_two_all` | **Verified implication**, not the hypothesis: strict functional closed vertex-n B-trees, full Ramsey, original-partial projection, final B-copy cover, conditional only on maximal genuinely mixed separator requiring ≥2 generators; no A↪B hypothesis |
| Function-closed tree amalgam interface | `RelStructure.FunctionClosedTreeAmalgam.irreducible_contained_in_full_copy` | Strict relational tree geometry plus closed gluing roots; side embeddings stay closed and constituent copies decode to full function embeddings |

The all-arity endpoints are in
`Ramsey/FreeAmalgamationFunctionsAllArity.lean` and
`Ramsey/ForbiddenFunctionsAllArity.lean`; the class-preserving pass is in
`Functional/EHNConstruction.lean`.  The umbrella import exposes them all.

## Strict original-partial functional sparsening: certified proof boundary (15 October 2026)

The direct native weak-function-GRAPH theorem remains fully verified, including
arbitrary exact weak vertex tests, full function Ramsey embeddings and final
B-copy coverage. It is a different result from strict full-FUNCTION local trees.

For strict full-functional local targets under the ORIGINAL 2019 partial map,
these distinct results are now formally certified:

- the generator-rank small-image alternative for genuine **closed** source
  tests, including arbitrary weak EHN projections whose image is not closed;
- the pure power and pure attached-copy cases; simultaneous relative gluing
  over a single completed (possibly reducible) root;
- the actual rank-zero base using an embedded B-copy, plus the structural
  theorem that a closed full-functional free amalgam generated by at most
  one vertex is contained entirely in one side;
- a **fully unconditional** genuine native rank-one Ramsey and final
  B-coverage construction (as stated in the rank-one theorem, including
  the A↪B hypothesis);
- the complete n-pass Ramsey and final B-extension construction as a
  **conditional theorem**, with exactly the uniformly quantified
  `StrictRanked.MaximalMixedSchema` left as an explicit hypothesis.

Passing the axiom audit for an implication whose premise is this schema
does not establish the schema itself. The remaining *mathematical* lemma
is to construct compatible strict original-partial B-tree relative
extensions on both sides of a genuinely mixed closed native attachment
with **n≥2 distinct projected generators**, preserving the actual closed
overlap and (if the stronger printed invariant is needed) projected
A-copy histories. Do not claim either that independent completions glue
or that both pieces automatically lose a generator.

The later survey's **total-fibre** homomorphism notion differs from the
original 2019 partial-function notion. The unrestricted functional
sparsening statement with that stronger map is refuted independently;
the corrected strict targets asserted here must be read with the
original partial global projection.

## Current strict functional mixed-root frontier (15 October 2026)

The original-2019 partial-function strict-target programme is now
kernel/axiom verified through its genuine n-pass construction and
final B-coverage, **conditional** on one multi-generated-root extension
assertion. The 2019 partial map preserves full fibres at defined
source inputs but does not reflect undefined domains; the later survey's
global total-fibre map is different and its unrestricted functional
reading is refuted.

New verified geometry reduces the genuinely hard mixed cases:
an empty root is automatic; a one-generated full-functional root is
always irreducible and costs at most one generator **regardless of its
vertex cardinality**, so every genuine mixed n-generated test with
such a root admits compatible relative strict B-tree side witnesses.
More generally, a finite root generating set can be paid for by
exclusive generators outside both sides, and for irreducible roots
the independently chosen side completions are synchronized over the
same prescribed B-copy.

The remaining mathematical obligation is to construct compatible
relative strict B-tree side extensions for **maximal genuinely mixed
closed native attachment tests whose common separator requires at
least two generators**, when these exterior reserve conditions do
not suffice. The conditional Lean n-pass theorem does **not** certify
the existence of these still missing side witnesses. The separate
stronger ambient-A/projected-history-controlled property is also
not obtained merely from the bare original-partial target-tree glue.
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

## The false uniform fixed-root strengthening (15 October 2026)

The strict original-2019 partial-function route cannot use a
*globally fixed* Hales--Jewett A-to-Base root map on every small
closed test. An independent hand audit gives two explicit graph
counterexamples, documented in
[fixed-core-root-invariant-counterexample.md](fixed-core-root-invariant-counterexample.md):

* a 3-edge path with its endpoints forced to the same K₂ vertex,
  an impossible odd closed walk (projected-size drop);
* a 2-edge path with its endpoints forced to opposite K₂ vertices,
  impossible by bipartiteness **even with maximal projected
  cardinality**.

The finite-star fixed-root wrapper proposed in PR #311 was therefore
closed unmerged. The sound geometric reductions in #308–#310 are
conditional or initial-core results; they do not imply that the
uniform incoming-copy relative extensions exist.

For the actual strict functional theorem, use the verified
`EHNNativeOriginalPartialMaximalMixedReduction` and
`EHNMaximalMixedHardRootReduction`. The projected image of a
finite set of **generators**, not the cardinality of its full
function-closed hull, determines the rank drop. At maximal rank
the projection is injective on the chosen generators alone.
Any remaining hard-root completion must choose a **shared target
root tree and map per test**, as the current `MaximalMixedHardRootSchemaFromTwo`
already permits. The root must not be forced to the original
A-label map. A full proof of that hard-root schema and the
ambient A-copy histories is still open.

The small graph counterexamples above are **hand proofs, not
Lean-certified refutations**. The named Lean declarations and
axiom audits apply only to their explicitly stated conditional
lemmas and to the corrected generator-rank dichotomy.

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

### Direct genuine-function weak-vertex iteration: completed

The intended native iteration is now Lean-verified in the original function
language (merged PR #104, green CI workflow 37738639824).
`RelStructure.Attachment.locallyTreeLike_of_projected_support` handles
the generic mixed/pure projected free-attachment step;
`FunctionalPartite.EHN.Stage.attach_weakGraphLocallyTreeLike` transports
that invariant through a **full** functional attachment;
`FunctionalPartite.EHN.pictureLemma_weakGraphLocallyTreeLike` handles
the genuine Hales--Jewett core and its canonical support;
`FunctionalPartite.EHN.initial_weakGraphLocallyTreeLike` handles the full
initial B-copy picture; and
`FunctionalPartite.EHN.inducedConstruction_weakGraphLocallyTreeLike`
carries the invariant through one complete Ramsey pass.

After n passes, `Structure.inducedRamsey_directFunctionalWeakGraph` gives
a full functional Ramsey witness in the same free-amalgamation class,
with the controlled graph-tree completion bound for **all weak vertex tests**
of size at most n, and a weak EHN projection to the original witness.
This proves the graph-level conclusion for every genuinely function-closed
substructure of that size. A generic strengthening to strict
**total-fibre** functional B-tree targets is **false**: the actual tagged
native power has a verified function-closed test of exactly twelve
vertices that has no such completion, even with a hereditarily
irreducible base graph. Its completion *does* exist under the
original 2019 partial-function homomorphism convention. The two
completion notions must not be conflated; the positive weak graph-tree
induction remains unchanged.

This argument does not use U-closed relational graph expansions: those
are needed only in the recursive partite construction, whose intermediate
graph stages may lack the full function-structure constraints. The older
U-closed n-pass proof is a valid auxiliary result, not the construction used
here.


### Verified closed-source versus full-target obstruction

The exact source/target distinction is not merely a deficiency of notation.
`Structure.FunctionalClosedTestGraphObstruction.closedSource_graphCompletion_not_fullCompletion`
(Lean PR #109, successful CI on commit
`a175a045df4088c2597966e32251420d5e19f2a1`) proves that an
**entire closed function structure** may have a strict tree completion
of its function graph without having any full function-language tree
completion over the same base.

For the unary partial function with F(0)={1} and F(1)=empty, glue
two B-graphs along the output of one and input of the next, producing
a directed two-step path. This is a strict relational tree of B-graphs;
its full decoded source is closed. Every genuine full-function B-tree
still satisfies F∘F=empty, so the path cannot even map into one by a
full function homomorphism. The obstacle is the *nonclosed target gluing
root*, not a function-closure enlargement of the source test.

This rules out an automatic graph-to-full-target conversion for
arbitrary closed sources. It does **not** refute a potential stronger
theorem for the special native EHN outputs, provided extra closure
certificates are constructed. The validated n-pass theorem remains
graph-level, and the printed relational Appendix remains unchanged.
## Validation discipline

CI builds the umbrella and all audit imports, then checks every declaration in
`CheckAxioms.lean`, `CheckClosureAxioms.lean`, and
`CheckEHNFunctions.lean`. Only `propext`, `Classical.choice`, and
`Quot.sound` are accepted. Missing audit results, `sorryAx`, and custom
unproved axioms fail. Survey markers must be pinned to a successful immutable
proof commit.
