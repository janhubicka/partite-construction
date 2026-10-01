# Appendix A coverage

The first milestone verifies the non-induced **Partite Lemma** and reusable
bookkeeping used later in the construction. The complete unrestricted
Nešetřil–Rödl theorem is not yet formalized.

| Survey location | Lean declaration | Status |
| --- | --- | --- |
| Relational structures and induced embeddings | `RelLanguage`, `RelStructure`, `RelStructure.Embedding` | Relational-language interface |
| Structural partition arrow | `StructuralRamsey.Arrow`, `Monochromatic` | Definition; embedding formulation |
| Partite System definition | `Partite.System`, `Partite.System.expand` | Partition-map presentation; unary-predicate equivalence checked |
| Transversal system | `Partite.transversal` | Exactly one named vertex per part |
| Fixed-length Hales–Jewett statement | `HalesJewett.finite` | Proved from the pinned `lean-successors` theorem |
| `lem:partite` | `Partite.NonInduced.partiteLemma`, `partiteLemma_expanded` | Proved for every finite colour type |
| Power vertex set and finiteness | `Partite.NonInduced.Vertex`, its `Finite` instance | Proved; tagged powers of the parts |
| `clm1` | `Partite.NonInduced.lineEmbedding`, `lineMap_rel_iff` | Proved, including relation reflection |
| `clm3` | `Partite.NonInduced.lineEmbedding_comp_letter`, `wordEmbedding` | Proved |
| Projected copies before `lem:picture` | `Partite.ProjectedEmbedding`, `projectedEquiv` | Bijection proved |
| Backward-induction paragraph in the proof of `thm:unNR` | `Partite.backwardFusion` | Proved **assuming the explicit local picture properties** |
| `lem:picture` | — | Pending: finite free attachment of copies |
| `thm:unNR`, complete construction | — | Pending: pictures, finite set Ramsey interface, and linear-order completion |
| Induced, iterated, and recursive constructions | — | Later milestones |

All names above are in the `StructuralRamsey` namespace. In the survey,
green markers identify proved statements, blue markers identify the precise
representation interface, and an orange marker on backward induction records
that its picture-existence hypotheses are not yet discharged. No marker asserts
that `thm:unNR` or all of Appendix A has been verified.

## Mathematical scope

* Languages need not be finite. Every relation has finite arity.
* Embeddings preserve **and reflect** relations. “Non-induced” names the
  construction, not a weakening of embeddings.
* Relation tuples may repeat a vertex. Transversality says that two entries
  with equal partition labels must be the same vertex.
* Nullary relations are allowed, though they are not needed in the survey.
* Parts and vertex sets may be empty. The Hales–Jewett bound is positive,
  including for an empty alphabet, and constancy is formulated pairwise.
* `Vertex B N` is finite whenever the partition type and B are finite.
  The witness is the explicit system `power A B N` on that finite type.
* Unary predicates are not merely described in prose: `expandedEquiv` and
  `arrow_iff_expanded` check both directions of the interface.
* Functions and closures are intentionally deferred to the recursive partite
  construction. The present relational API is a reusable reduct layer.

## Trust and dependency

The Hales–Jewett dependency is `janhubicka/lean-successors` at
`ce5ce187ef88e28d84a4a465517b3f9c87a0640a`, imported through
`SuccessorTree.HalesJewett.AlphabetInduction`. It proves
`SuccessorTree.HalesJewett.starHJ_finite`; this project does not postulate HJ.
The fixed-length bridge combines hypothetical bad colourings at each length
into one colouring of all finite words and applies that theorem.

`CheckAxioms.lean` prints the transitive axiom dependencies of the main results.
CI accepts only `propext`, `Classical.choice`, and `Quot.sound`, and checks that
every requested declaration produced a result. In particular, `sorryAx`, a
custom HJ axiom, and native-evaluation axioms cannot pass this audit.

## Survey corrections recorded as inline notes

1. A linearly ordered partite system need not be transversal as defined:
   projection is injective, but some named parts may be empty. Delete unused
   parts and relabel to obtain the defined transversal presentation.
2. In the Picture Lemma's pullback colouring, the quantified embedding has
   codomain C′, not B′.
3. In the unrestricted construction, the set of new predicates is
   `L_P \\ L`, not `L \\ L_P`.
4. The last proof's embeddings of A into a picture must be into its L-reduct,
   since A has not been given the picture's unary predicates. Projections not
   realized by an A-copy need an arbitrary default colour in the induced
   colouring of all injections.

These are proposed corrections in `\todo[inline]{Řehořek: ...}` notes; the
surrounding mathematical prose is retained for author review.
