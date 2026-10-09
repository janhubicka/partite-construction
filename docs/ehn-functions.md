# EHN with set-valued functions: proof architecture and survey interface

## Public conclusions

The fully general endpoints are:

- `Rooted.Structure.FreeAmalgamationClass.orderedRamsey_allArity` in
  `Ramsey/FreeAmalgamationFunctionsAllArity.lean`;
- `Structure.orderedRamsey_forbidden_expansions_allArity` in
  `Ramsey/ForbiddenFunctionsAllArity.lean`, the exact survey `thm:HN`.

Both allow genuinely set-valued functions of **arbitrary input arity,
including nullary functions/constants**.  Colour types are finite nonempty
types, and all embeddings in Ramsey arrows preserve complete function fibres.
No irreducibility assumption on A or B is needed for the general class
theorem.

The older positive-arity endpoints remain useful implementation layers:
`Structure.FreeAmalgamationClass.orderedRamsey` and
`Structure.orderedRamsey_forbidden_expansions`.

## Weak projections versus full embeddings

A full homomorphism has equality
`f[F_A(x)] = F_B(f(x))`.  An EHN weak projection only preserves incidences
forward globally, but its restriction to every full irreducible is a full
embedding.  This is `Structure.IsEHNHomomorphismEmbedding`.

This is deliberately different from the graph-encoding
`Structure.IsWeakHomomorphismEmbedding` used in weak-substructure iteration.
Ramsey arrows themselves always use full embeddings.

## Closed hulls and the power invariant

`Irreducible.of_generated_weakHomomorphism` proves that the target generated
by a weak image of an irreducible source is irreducible.  Hence the closed
hull of every coordinate image in the Hales--Jewett power is irreducible even
when the raw coordinate range is not closed.

This supplies the coordinate embeddings required to prove that the power
retains the EHN projection invariant.  Function exactness then follows by
lifting an output coordinatewise and using output transversality.

The line-map proof is correspondingly short: one parameter coordinate supplies
a preimage; output transversality of the whole power gives uniqueness.

## Constants: two formalized mechanisms

### 1. Rooted unrestricted Ramsey reduction

`Structure/NullaryRoot.lean` defines the canonical root
`A.nullaryRoot = <empty>`.  Every closed substructure contains it and every
full embedding maps it onto the target root.

The modules
`RootedReduction`, `RootedFunctor`, `RootedSplit`,
`RootedCorrectness`, `RootedFreeAmalgam`, `RootedClass`,
`RootedEmbedding`, `RootedOrder`, and `RootedCanonical`
formalize the whole fixed-root translation:

- encode/decode on the moving complement;
- full embedding equivalence on rooted structures;
- transport of concrete free amalgams and free-amalgamation classes;
- rigidity of the finite ordered canonical root;
- reconstruction of the global order from cut predicates and the witness order.

This yields
`Rooted.Structure.FreeAmalgamationClass.orderedRamsey_allArity`.

### 2. Root-shared EHN initial picture

The class-preserving induced pass does not need to translate the class to the
rooted language.  Its only positive-arity dependency was the initial disjoint
picture.  `FunctionalPartite.EHN.initial_allArity` instead takes one B-copy
as the core and attaches every other placement over B's canonical nullary
root.  Two full placements of B in D map that root onto the same target root,
so a full root transport identifies the overlap.

The rest of the Picture/Hales--Jewett construction is unchanged, giving
`FunctionalPartite.EHN.inducedConstruction_allArity`.

## Exact forbidden ordered patterns

For particular forbidden orderings, the auxiliary class keeps both
F-freeness and `OrderTotalOnIrreducibles`.  This class is hereditary and
closed under full free amalgamation.  Final order completion cannot create a
new forbidden copy because every comparison on an embedded irreducible reduct
was already present before completion.

Using the unrestricted all-arity witness followed by
`inducedConstruction_allArity` gives
`Structure.orderedRamsey_forbidden_expansions_allArity` directly in the
original language.  There is no remaining constants reduction outside Lean.


## Direct functional iteration versus recursive graph encoding

For an iterated functional partite construction the intermediate systems
already interpret **genuine set-valued functions**. The correct route is
`FunctionalPartite.Induced.weak_partiteLemma` and
`FunctionalPartite.EHN.pictureLemma`, directly in the function language,
with the weak global projection `System.WeaklyPartiteOver`.
`System.weak_support_closed` says that the inverse image of a genuinely
embedded A-copy under this weak projection is function-closed. The actual
`System.weakRestrict` is therefore a **full induced substructure** and
all Hales--Jewett letter embeddings and attaching maps are full.

The induction on the sparsening test size must still use **weak**
substructures on arbitrary vertex sets, retaining only function outputs
inside the test; `Structure.weakInduce_graph_rel_iff` supplies their exact
graph representation. This representation is a way to inspect arbitrary
weak tests, **not a reason to replace the functional Picture by U-closed
relational pictures**. The direct n-pass weak-size tree invariant
is now proved as `Structure.inducedRamsey_directFunctionalWeakGraph`.
It uses the EHN power and genuine binary functional attachments, with
the existing `EHN.pictureLemma_preservingSupport` and
`EHN.inducedConstruction_preserving` providing the finite
colour/attachment and Ramsey-pass bookkeeping.

U-closed relational graph embeddings are required instead in the
**recursive partite construction**: its intermediate relational stages
need not preserve all the intended functional constraints or closure
certificates, and therefore require an explicit repair/decoding step.
The already-checked U-closed n-pass graph theorem is a valid **auxiliary
route**, but not the intended proof of the direct functional iteration.

Do not identify weak graph-tree completion with the strict full-function
target conclusion. With **total-fibre** homomorphism maps as defined in
the 2026 survey, generic strict-functional tree invariance through the
native Hales--Jewett power is now **refuted**, even for a base whose
graph is hereditarily irreducible and a closed test of exactly twelve
vertices. The target-root and output-closure observations remain
conditionally correct, but they cannot prove this false generic
strengthening. Under the **original 2019 partial-function** maps the
same test has a strict one-copy completion; that different general
induction still requires its own proof.

The gap persists even for **function-closed source tests**, as the
checked two-edge unary-function path in
`FunctionalClosedTestGraphObstruction.closedSource_graphCompletion_not_fullCompletion`
shows. The path is a relational B-graph tree; no full functional B-tree
can contain a two-step function chain. This only rules out automatic
conversion, not special additional invariants of the native EHN stages.

## What remains separate

This work does **not** prove a globally fibre-surjective partite projection.
The checked EHN projection is weak globally/full on irreducibles.

The native weak-vertex-size functional iteration is complete at the
**graph-tree** level, including its full function-language Ramsey arrow.
It does not assert a strict function-language tree target: this requires
function-closed graph-tree gluing roots and complete local function output
preservation. The stronger synchronized ambient-A tree invariant remains
separate and is not a gap in the printed relational Appendix.
