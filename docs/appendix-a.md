# Appendix A: current coverage and exact scope

The previous chronological inventory is preserved in
[the historical coverage log](archive/appendix-a-before-closure-audit.md).
Historical TODOs in that log are not current obligations.

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
| Functional class-preserving refinement | `FunctionalPartite.EHN.inducedConstruction` | One pass; finite A,B in K; arbitrary full Ramsey witness D; positive input arity |
| Functional EHN | `Structure.FreeAmalgamationClass.orderedRamsey` | Hereditary full free-amalgamation class; arbitrary positive-arity set-valued functions; A,B need not be irreducible |
| Exact ordered forbidden-pattern theorem, `thm:HN` | `Structure.orderedRamsey_forbidden_expansions` | Forbidden structures may specify orders; only their reducts must be irreducible; positive input arity |
| Strict relational sparsening | `Partite.IteratedSparsening.sparseningRamsey_strict_baseIrreducible_all` | B irreducible; A arbitrary; independent of the unresolved stronger synchronized invariant |

The functional endpoints are in `Ramsey/FreeAmalgamationFunctions.lean` and
`Ramsey/ForbiddenFunctions.lean`. The full derivation is explained in
[the functional EHN guide](ehn-functions.md). The umbrella import exposes
all endpoints; compiler and axiom validation remain the gate for any claim
about a particular immutable commit.

## Simplifications and precise distinctions

The two local closure observations follow from one statement: a subset is
closed in a free amalgam iff its inverse images in both sides are closed.
This is not a transversality theorem and does not require positive arity.

The Hales–Jewett line-map exactness proof now uses one parameter coordinate
and output transversality of the whole power, rather than repeating the
coordinate analysis to prove uniqueness. The simplification is also applied
to the existing full-projection proof without changing its interface.

The essential functional invariant uses the **closed hull** of each coordinate
image. A generating weak homomorphic image of an irreducible structure is
irreducible. Pulling back a proper free decomposition needs only forward
preservation, not fibre surjectivity. This repairs the functional power
invariant without pretending a noninjective quotient is a full homomorphism.

`Structure.IsEHNHomomorphismEmbedding` is the new invariant: weak globally,
full on full irreducibles. The existing `Structure.IsWeakHomomorphismEmbedding`
means a homomorphism-embedding of graph encodings and remains separate.

For the exact survey theorem, forbidding particular ordered structures is not
replaced by forbidding every ordering of their reducts. The auxiliary class
also keeps `OrderTotalOnIrreducibles`, which prevents order completion from
creating a new forbidden embedding. The same one-pass construction proves the
general free-amalgamation class theorem with no need for this extra invariant.

The unrestricted recursive route still uses domain-aware semi-closed pictures.
The old arbitrary-alpha free-attachment argument is not a dependency of it.
A counterexample to that argument is not a counterexample to the entire
existential Picture statement.

## Remaining manuscript obligations

1. **Strong synchronized tree invariant.** Full-copy localization does not
   settle simultaneous control of every ambient-A intersection with a partial
   boundary. The hereditary-irreducibility/projected-history variants are not
   the literal `thm:tree_invariant` under mere irreducibility of A.
2. **Functional iterated sparsening.** The new functional EHN theorem supplies
   the one-pass class transfer, but not the local tree-amalgam bounds of the
   iterated theorem. Arbitrary weak substructures still belong in that proof.
3. **Constants globally.** The global Ramsey endpoints and initial disjoint
   attachment use positive input arity. Local closure and weak-image lemmas
   allow constants; do not transfer the global restriction to those lemmas.
4. **Arbitrary-alpha Picture statement.** Replace the printed argument by the
   domain-aware version or prove the stronger assertion separately. Do not
   retain the invalid attachment proof as a justification.

The original full-projection functional induced formulation is not silently
proved by the EHN weak-projection theorem. Its relevant TODO must specify this
remaining wording/interface change, not say that the functional EHN result
itself is still missing.

## Validation discipline

CI builds the umbrella and all audit imports, then checks every declaration
in `CheckAxioms.lean`, `CheckClosureAxioms.lean`, and `CheckEHNFunctions.lean`.
Only `propext`, `Classical.choice`, and `Quot.sound` are accepted. Missing audit
results, `sorryAx`, and custom unproved axioms fail. All new EHN modules disable
automatic implicit declarations. Survey markers must be pinned to a successful
immutable proof commit, not a moving branch.
