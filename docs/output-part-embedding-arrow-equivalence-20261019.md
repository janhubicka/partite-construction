# Output-part singletonization is an equivalence on full partite embeddings and Ramsey arrows

**19 October 2026 — English-first proof and adversarial audit**

For a fixed functional language L and fixed output-part carrier P,
the canonical singleton split sends each transversal native
partite System B to the same vertex set, with the same part map,
replacing every set-valued function F by all partial singleton
functions (F,q) indexed by output part q.

The already verified direct map construction in PR #430 sends
each genuine FULL part-preserving functional embedding e:A↪B
to a full embedding of the split systems.

## Inverse map on embeddings

Conversely, let e:A^P↪B^P be a FULL part-preserving embedding
between canonical split systems. The same underlying vertex map
is a FULL embedding of the original multivalued systems.

For any original input x and original output z∈F_A(x),
select q=part_A(z). Then z∈F^q_{A^P}(x).
By whole-fibre equality of the split embedding,
e(z)∈F^q_{B^P}(e x), hence e(z)∈F_B(e x).
This proves preservation.

For any target y∈F_B(e x), choose q=part_B(y).
Then y∈F^q_{B^P}(e x). Full split-fibre equality
gives z∈F^q_{A^P}(x) with e(z)=y. In particular
z∈F_A(x). This proves surjectivity of the FULL
original output image. Ordinary relation reflection,
injectivity, and part preservation are inherited
unchanged from the split embedding.

The two translations are literally inverse because
both preserve the underlying vertex map. Thus

  Embedding_native(A,B) ≃ Embedding_split(A^P,B^P)

naturally with respect to identity and composition.

## Ramsey arrows are invariant

For genuine partite systems A,B,C with fixed P and any
color type κ, the abstract partite Ramsey arrow

  C → (B)^A_κ

is equivalent in the original multivalued language
and in the canonical singleton split language.
Transport the coloring through the embedding
bijection and transport the monochromatic
B-embedding back. Naturality under composition
preserves the monochromatic equation exactly.
No new vertices, output ordering, or generated
closure is introduced.

This does NOT prove that a genuine C with the
extra iterated sparsening requirements exists.
It says the arrow property itself is equivalent
for any particular native full-functional C.

## Adversarial audit

* **Part preservation is essential.** An embedding
  which permutes output parts without renaming
  (F,q) is not an embedding of the fixed split language.
* **Whole-fibre equality is essential.** A weak EHN
  map can leave an input undefined while its target
  has values. Such a map is NOT recovered by the
  full embedding equivalence.
* **Genuinely multivalued outputs** are recovered by
  varying q=part(y), so no singleton restriction is
  imposed on the original F.
* **Same part universe P** is required on every stage
  of the native partite construction, and is fixed here.
* **No finiteness or positivity requirement** is needed
  for this embedding or arrow equivalence. Positive
  arity is required separately to apply original 2019
  U-closed closure-root rules, as in PR #426.
* **Option(Set) defined-empty vs undefined** is a
  distinct semantics and cannot be silently
  identified by this Set-valued split.
* **Strict target compatibility** remains a separate
  mathematical condition. Arrow equivalence does not
  imply that independently completed B-trees share a
  full A-root or preserve requested projected histories.

Lean deliverables: \`Embedding.unsplitOutputParts\`,
\`Embedding.outputPartSplitEquiv\`, and
\`arrow_iff_splitOutputParts\` with named axiom checks.
