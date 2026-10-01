# Appendix A coverage

The non-induced construction is checked end to end, with the unconditional
ordered theorem assembled as `Partite.orderedRamsey`. The **relational induced
partite construction** is now checked end to end as well: homomorphism-
embeddings, positive coordinatewise powers, the induced Partite and Picture
Lemmas, initial pictures, based stages, the irreducible-image invariant, finite
iteration, and the final Ramsey extraction are all formalized. The set-valued
function extension is intentionally left to the later recursive construction.

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
| Restriction to selected parts | `Partite.System.restrict`, `Picture.restrictEmbedding` | Proved; empty parts allowed |
| Free attachment in the proof of `lem:picture` | `RelStructure.Attachment.core_rel_iff`, `copy_rel_iff`; `Partite.Attachment.copy_extends` | Core and all attached copies are induced; every specified embedding extends |
| `lem:picture` | `Partite.pictureLemma` | Proved, with a finite witness for every finite colour type |
| Initial picture in the proof of `thm:unNR` | `Partite.Initial.picture`, `copyEmbedding` | Proved for any family of injective placements |
| Repeated application of the Picture Lemma | `Partite.nonInducedConstruction`, `allProjections` | Proved; all local existence hypotheses discharged |
| Backward-induction paragraph | `Partite.backwardFusion` | Proved; its required local properties are now supplied by `pictureLemma` |
| Projected-relation invariant (including increasing order) | `Partite.Picture.respects`, `nonInducedConstruction_preserving` | Proved for every constraint on projected relation tuples |
| Finite Ramsey input | `FiniteRamsey.strictMono` | Proved for strictly increasing tuples and every finite colour type |
| Increasing placements | `Partite.increasingProjectionRamsey` | Proved; finite Ramsey supplies the abstract `ProjectionRamsey` input |
| Monochromatic extraction from the final picture | `Partite.ramseyFromProjections` | Proved, including default colours for unrealized projections |
| Final order completion | `RelStructure.exists_order_extension`, `arrow_completeOrder` | Proved; induced copies and the Ramsey arrow survive |
| `thm:unNR`, assembled ordered conclusion | `Partite.orderedRamsey` | Proved unconditionally for finite ordered relational structures and finite nonempty colour types |
| Relational irreducibility / homomorphism-embedding | `RelStructure.Irreducible`, `IsHomomorphismEmbedding`, `IsHomomorphismEmbedding.comp` | Proved; matches the relational specialization of the survey definition |
| `A`-partite-system projection invariant | `Partite.System.IsPartiteOver` | Proved using a partition map whose projection is a homomorphism-embedding |
| `def:power`, coordinatewise relational power | `Partite.Induced.power`, `power_isPartiteOver` | Proved for positive exponents; positivity is essential |
| `lem:indpartite` | `Partite.Induced.partiteLemma` | Proved for relational languages and every finite colour type |
| Irreducibles under free attachment | `RelStructure.Attachment.irreducible_core_or_copy`, `Partite.Attachment.attach_isPartiteOver` | Proved: every irreducible lies in the core or one attached copy, and the projection invariant survives |
| `def:based` | `Partite.Induced.BasedOn`, `canonical_based` | Formalized as isomorphism to the canonical positive-power free attachment |
| `lem:indpicutre` | `Partite.Induced.pictureLemma` | Proved for relational languages, with a finite based witness |
| Relevant embeddings in the proof of `thm:inducedpartite` | `Partite.Induced.Relevant`, `relevant_iff_image_contained` | Factorization through a `B`-copy is proved equivalent to the manuscript's image-containment formulation |
| Initial picture and invariant (3) | `Partite.Induced.Initial.picture_isPartiteOver`, `picture_covers` | Proved for the disjoint union of all `B`-copies in `D` |
| Preservation of invariant (3) | `Partite.Induced.Attachment.attach_covers`, `pictureStep` | Proved simultaneously with the based-stage Picture property |
| `thm:inducedpartite`, finite construction | `Partite.Induced.Stage`, `Trace`, `inducedConstruction` | Proved end to end for finite relational structures; the trace certifies every intermediate stage and the default-colour extraction is explicit |
| Iterated construction | — | Next milestone |
| Recursive construction / set-valued functions | — | Later milestone; required for the survey's general function language |

All names above are in the `StructuralRamsey` namespace. In the survey,
green markers identify statements proved in the formalized relational setting,
blue markers identify representation interfaces, and orange markers identify
manuscript statements whose stated scope is broader than the theorem checked
in Lean. The non-induced construction is fully green. The induced construction
is complete for relational languages; its theorem-level markers remain orange
where the survey presently quantifies over the general language with genuinely
set-valued function symbols.

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
* The Picture Lemma does not require the full partition type to be finite;
  only the source and initial picture are required to be finite. Finite
  iteration works for an arbitrary finite list of injective projections.
* The Ramsey reduction assumes a finite nonempty colour type. Its default
  colour for unrealized projections is explicit. The Partite and Picture
  Lemmas themselves also handle empty colour types.
* Order is represented by a fresh binary symbol, via `RelLanguage.withOrder`
  and `RelStructure.ordered`. Completion orders the finite carrier by its
  partition label and a numbering within each part. Every induced embedding
  from a linearly ordered source remains induced after completion.
* Low-level attachments, restrictions, and the Picture Lemma are universe
  polymorphic. Iteration and the assembled theorem use a common carrier
  universe, which includes the usual `Type` presentation of finite structures.
* The induced construction is formalized for relational languages. Its
  coordinatewise power requires `N > 0`; at exponent zero relation conditions
  are vacuous and the projection need not remain a homomorphism.
* `Relevant` embeddings are those `A → D` maps factoring through a copy
  `B → D`; Lean proves this is equivalent to the survey's statement that the
  image of the `A`-copy is contained in the image of a `B`-copy.
* The final induced extraction assigns a fixed default colour to embeddings
  `A → D` not contained in any `B`-copy before applying the Ramsey arrow on
  `D`. This is the same bookkeeping issue that appears in the non-induced
  projection argument.
* Functions and closures are intentionally deferred to the recursive partite
  construction. In particular, the coordinatewise argument is not valid for
  arbitrary set-valued functions: different coordinates may choose different
  function values, creating a mixed value not lying in the image of any
  single source function value. The later `U`-transversal machinery is the
  appropriate layer for that case.

## Trust and dependency

The Hales–Jewett dependency is `janhubicka/lean-successors` at
`ce5ce187ef88e28d84a4a465517b3f9c87a0640a`, imported through
`SuccessorTree.HalesJewett.AlphabetInduction`. It proves
`SuccessorTree.HalesJewett.starHJ_finite`; this project does not postulate HJ.
The fixed-length bridge combines hypothetical bad colourings at each length
into one colouring of all finite words and applies that theorem.

`CheckAxioms.lean` prints the transitive axiom dependencies of the main results.
All 38 audited declarations pass. CI accepts only `propext`, `Classical.choice`, and `Quot.sound`, and checks that
every requested declaration produced a result. In particular, `sorryAx`, a
custom HJ axiom, and native-evaluation axioms cannot pass this audit.

## Survey corrections recorded as inline notes

The formalization has identified the following proposed manuscript corrections.
They are recorded in `\todo[inline]{Řehořek: ...}` notes rather than silently
changing the circulation text.

### Non-induced construction

1. A linearly ordered partite system need not be transversal as defined:
   projection is injective, but some named parts may be empty. Delete unused
   parts and relabel to obtain the defined transversal presentation.
2. The definition of a word should use the bound `i < N`, not `i < n`.
   The Partite Lemma proof also needs a positive Hales--Jewett length for the
   assertion that every word lies on a parameter line.
3. In the Picture Lemma's pullback colouring, the quantified embedding has
   codomain C′, not B′.
4. In the unrestricted construction, the set of new predicates is
   `L_P \\ L`, not `L \\ L_P`.
5. Embeddings of the L-structure A into a picture have codomain its L-reduct.
   Projections not realized by an A-copy need an arbitrary default colour in
   the induced colouring of all increasing injections.

### Induced construction

6. The coordinatewise power must use `N > 0` (or separately define the zero
   power). At `N = 0`, relational conditions are vacuous, so the projection
   need not be a homomorphism and the power need not be A-partite.
7. The sentence assuming without loss that every vertex of B lies in an A-copy
   is unnecessary and is not an evident reduction; deleting such vertices
   changes the target B. The checked proof works for arbitrary B.
8. The Hales--Jewett alphabet must consist of part-preserving copies
   `Emb(A′,B)` (equivalently projected A-copies), not arbitrary embeddings of
   the L-reduct A into B. Correspondingly the displayed arrow has source A′.
9. The sentence saying function symbols are analogous is not valid for the
   survey's genuinely set-valued functions without additional hypotheses.
   The relational induced theorem is checked; the set-valued case belongs to
   the later transversality/recursive machinery.
10. In the final induced Ramsey extraction, backward fusion colours only the
    relevant embeddings A→D lying inside B-copies. Assign a fixed default
    colour to the remaining embeddings before applying D→(B)^A.

