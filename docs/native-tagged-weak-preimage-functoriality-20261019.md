# Exact weak functional embeddings are full tagged-pattern embeddings

**19 October 2026 — English proof and adversarial audit, built on the
native functional/U-closed closure dictionary (PR #426).**

The original 2019 U-closed proof works on LITERAL weak vertex sets
and restricts full embeddings by exact preimages. The native
functional construction does the same: the restriction of a
FULL function embedding to a weak preimage is a full embedding
between the weakly induced sets of surviving function fibres
(already verified). But the 2019 picture also retains AMBIENT
active root/domain records omitted by the weak function
restriction. Those records are represented by the canonical
tagged pattern expansion.

## The exact functoriality theorem

Let e:A↪B be a FULL genuine relation/set-valued-function embedding
with arbitrary output multiplicity and repeated input arguments.
For ANY vertex subset S⊆B, let T=e^{-1}[S]. Define canonical
tagged structures

  A† = patternTagExpansion(A.patternGraph),
  B† = patternTagExpansion(B.patternGraph).

The existing kernel-verified map
\`(e.patternGraph).patternTag\` is a FULL tagged relational
embedding A†↪B† on the ORIGINAL underlying vertex map e.
Restrict this full tagged map on exact induced subsets:

       A†|T  ↪  B†|S,

sending a∈T to e(a)∈S. This induced map is FULL on EVERY
tagged relation, including:
* original relations;
* equality-pattern original active function domains;
* positive function-output graph tuples;
* FRESH full input-pattern U-closure tags.

Proof: for any tuple from T, an induced tagged relation holds
on the target precisely when that exact ambient relation holds
on its e-image. The already checked full \`patternTag\`
embedding reflects that exact relation back to A†; induced
relations impose no further condition except that every
displayed vertex belongs to T or S. Injectivity follows
from injectivity of e. The entire argument uses EXACT
vertex subsets and never forms a closure hull.

If A is a partite system and B a larger partite system,
this is the precise ALL-OUTPUT-MASK analogue of the checked
\`Embedding.missingActiveOutputAtPart_preimage_iff\` theorem.

## Use in the native iterated proof

For a genuine FULL functional Hales–Jewett/attachment copy,
the SAME full embedding transports native weak source tests
and the tagged ambient U-domain records at once. The local
root-cut identifications in the 2019 U-closed proof are therefore
valid word-for-word in the function presentation, provided one
keeps the AMBIENT tags rather than recomputing the function
domain after weak restriction.

The closure dictionary in PR #426 then identifies native
function-closed subsets with relative U-substructures; for
singleton-valued functions the resulting induced tagged tests
are exactly U-closed by 2019 Lemma 2.23(1).

This does NOT assert an EHN map is FULL. Source-undefined
input tuples may project to target-defined tuples. It also
does not create a history-compatible STRICT B-tree target
completion for arbitrary mixed HJ attachments: the
arbitrary-stage C5 and marked-edge parity counterexamples
remain valid.

## Adversarial checks

* **Fullness of e is indispensable.** A merely weak or
  original-partial EHN projection can have extra domain
  relations in the target on source-undefined tuples and
  would fail full reflection of tagged relations.
* **Weak source test is exact.** The source subset T is
  the literal inverse image of S; no function closure is
  charged as additional test vertices.
* **Missing ambient outputs remain recorded.** If a
  unary output F(a)=b lies outside S while a∈S, the induced
  tagged domain record persists on S even though the native
  recomputed weak fibre becomes empty.
* **Multivalued functions:** Full e reflects all output
  incidences and domain existence, with a separate tag
  for every complete input pattern. No singleton assumption
  is introduced by this map-level lemma.
* **Nullaries:** The tagged language can carry zero-root OLD
  domain/graph relations. The **positive-root** 2019
  closure dictionary in PR #426 separately excludes
  nullary function symbols; this map-level theorem itself
  has no positivity requirement.
* **No target strict-tree inference:** Exact full
  source/tagged embeddings do not synchronize independently
  chosen target tree completions; the genuine history-dependent
  common-target-root lemma still requires proof.

## Lean deliverables

Define \`Structure.Embedding.taggedPatternWeakPreimage\`;
prove its tagged \`map_rel_iff\` by direct use of the
previously verified \`Embedding.patternGraph.patternTag\`.
Audit the declaration's axioms with the entire umbrella build.
No edits to the frozen survey prose.
