# Hales–Jewett lines commute with the genuine output-part singleton presentation

**19 October 2026 — English proof and adversarial audit before Lean.**

The full functional construction in Appendix A should follow the
verified U-closed argument via a faithful presentation change, not
a second unrelated Picture construction. We already have:

* genuine multivalued partite functions split into canonical
  per-output-part singleton symbols (F,q), without altering vertices;
* a bijection on all FULL part-preserving embeddings and therefore
  on the finite Hales–Jewett letter alphabets (PR #432);
* a full isomorphism between the singleton split of the ACTUAL
  positive-length native HJ power and the actual HJ power of the
  singleton split (PR #433);
* full control projection compatibility for every output part (PR #431);
* direct native weak-root/free-amalgam correspondence with 2019
  ambient U-tags (PRs #426–429).

The missing structural link is the actual HJ LINE and its
full attaching embedding, which we now verify.

## Exact line translation

For old native partite B with full control A and a true
HJ line W in the alphabet of full part-preserving letters
e:(transversal A)↪B, convert each constant letter e to
the canonical singleton split e^P and leave every
parameter symbol unchanged. Call this line W^P.

Its parameter positions are EXACTLY those of W,
so W^P is a true line of the same length and has no
new constant or variable coordinates.

For every old vertex x in B, the native line map is

  line_W(x)_i =
      x,                         W_i=parameter,
      e_i(part_B(x)),             W_i=constant(e_i).

The split letter e_i^P has the same underlying vertex map
as e_i, and the singleton power vertex conversion preserves
all part labels and coordinates. Therefore the actual
maps agree POINTWISE:

       splitPowerVertex(line_W(x)) = line_(W^P)(x).

This is an equality of real HJ power vertices, not merely
a relation preserving map.

## Full attaching-map naturality

Assume the original native B has the FULL partite projection
to A, as already required by the genuine
\`Induced.lineEmbedding\` constructor. By PR #431 its
split system has the FULL projection to the split control.

The actual line embedding is a full function-language
partite embedding B↪power(B,N). Split it through the
verified full-embedding functor, then compose with the
PR #433 full positive-power isomorphism. The result is
the same full partite embedding as the actual line
embedding of the singletonized system along W^P.

The equality follows from the pointwise line-map
calculation and extensionality of full native partite
embeddings, not from abstract type equivalence.

## Adversarial audit

* **Positive length** is guaranteed by W.hasParameter.
  The zero-power isomorphism is false and not invoked.
* **Fullness** is required of the native projection
  and HJ letters. A merely EHN original-partial
  projection does not supply the verified
  \`Induced.lineEmbedding\` constructor globally.
* **All output parts and whole fibres** are preserved
  because each constant letter and the power map
  are full partite embeddings, not graph-only maps.
* **Repeated and nullary arguments** do not affect
  pointwise line-map equality; output-part
  singletonization already tracks their fibres.
* **No new vertices or closure hulls** enter the
  letter alphabet, line parameter positions or
  coordinate-power carrier. Therefore all weak
  cardinal bounds and the literal tested vertex sets
  are unchanged by the translation.
* **Target completions:** this only transports the
  SOURCE HJ line attachments. It neither proves
  compatible strict target B-tree roots for arbitrary
  mixtures of HJ lines nor permits a globally fixed
  target alpha-mark. The K2-parity and C5 audits
  remain relevant.
* **What comes next:** genuine finite attachment
  lists can be compared inductively by combining
  line naturality, the checked full native
  free-amalgam split, and its exact weak-root diagram.
  The remaining work is to transfer the CORRECT
  2019 profile/relative-root target invariant, not
  to strengthen all intermediate tests to
  globally marked strict B-trees.

## Lean acceptance

Prove \`splitLineSymbol\`, \`splitLine\` and
\`toSplitPowerVertex_lineMap\`, followed by
\`splitPowerEmbedding_comp_lineEmbedding\`.
Audit their axioms and run the full project build.

Do not mark the complete functional n-pass
sparsening theorem verified until the actual
finite attachment-list target-profile step is proved.
