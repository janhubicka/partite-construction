# Canonical full function-root tags preserve genuine relational free amalgams

**19 October 2026 — English proof with adversarial checks, before Lean.**

The new native/U-closed dictionary (PR #426) shows that function-closed
source subsets of a positive-arity function structure are exactly
relative U-substructures of its canonical tagged domain/output-pattern
expansion. Exact full native embeddings also induce exact FULL tagged
weak-preimage embeddings (PR #427).

The essential third compatibility is **free amalgamation**. It is
best proved as a generic lemma for OLD pattern-graph relational structures;
there is NO need to duplicate the native functional Hales–Jewett
construction or rerun the alternative 2019 profile sparsening theorem.

## Statement

Let Root→Left, Root→Right, Left→Whole, Right→Whole form a
genuine FULL relational free amalgam in the OLD pattern-graph language
\`L.patternGraph\`. This language already includes all ordinary relations,
one active-domain relation for each equality-pattern input, and one
function-output graph relation for each equality-pattern input.

Apply the CANONICAL full-pattern tagging functor

    E ↦ patternTagExpansion E,

which adds a fresh closure relation for every COMPLETE full OLD
active input-root pattern, on the very same vertex carrier.

**Theorem:** The resulting four tagged FULL embeddings still
constitute a genuine relational free amalgam.

In particular, a fresh tagged closure tuple of Whole cannot
cross the two sides. Its underlying OLD output-graph relation
belongs to one side by original free amalgamation. The full OLD
root pattern witnessing its tag has all of its root vertices
in that same side, since each such vertex is one of the tagged
tuple's displayed input coordinates. Because the side embedding
is FULL and injective, factor the complete OLD root embedding
back into that side. The tag is therefore present in the
canonical tagged expansion of that side, and the tuple is
precisely the image of a side tagged tuple.

Conversely, every side tagged tuple remains tagged in Whole:
full embeddings of OLD structures preserve-and-reflect the
entire FULL root pattern, so canonical tagging commutes with
the side embeddings. The covering and intersection conditions
are unchanged because tagging introduces **no new vertices**.

This proves the exact additional assertion needed for replaying
the corrected U-closed partite free-amalgam argument using the
genuine functional source Picture. It is a theorem about real
source gluing geometry, not an arbitrary TARGET completion lemma.

## Adversarial audit

1. The FULL OLD side maps are indispensable. Mere homomorphisms
   could lose negative relations on the input root, so a tag
   recognized in Whole need not factor through the side.
2. Complete FULL root patterns matter. If two different
   induced old input-root structures were given the same tag,
   an output tuple could satisfy inconsistent side labels.
3. This argument handles arbitrarily repeated primitive
   function inputs via the distinct-root equality pattern;
   positive arity is NOT required for this generic tag
   free-amalgam lemma, since tags with positive roots are
   already the only fresh symbols in this language.
4. The function fibres may be multivalued at the OLD
   graph level; this proof needs only source-side locality
   of positive output incidences, not singleton-valuedness.
5. Full tagged patterns are **ambient**. An exact weak source
   test may omit a function output while its original active
   domain tuple remains true. The free-amalgam statement
   must be combined with induced AMBIENT tagged weak
   restrictions, never recomputed weak-domain relations.
6. The lemma says NOTHING about independently completed
   STRICT B-tree targets agreeing on the shared weak root.
   The verified K2 parity and arbitrary-stage C5 target
   obstructions remain applicable. We must still transfer
   an actual relative target/history invariant.

## Lean acceptance

Implement
\`RelStructure.IsFreeAmalgam.patternTagExpansion\`
as a purely relational helper. The old relation case uses
\`hFree.rel_iff\`. For each new tag, use the OLD output graph
relation to select a side, then factor the full root embedding
through that side using the previously checked
\`RelStructure.Embedding.factorThroughRangeHeterogeneous\`
(which works for root carriers \`Fin n : Type 0\`).

Audit named theorem axioms and full umbrella Lean build.
Next compose with the genuine FUNCTION free-amalgam → OLD
pattern-graph free-amalgam bridge, preserving actual
Hales–Jewett attached function systems and all weak
vertex/cardinality data. No manuscript edits.
