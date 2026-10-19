# Actual native Hales–Jewett power isomorphic to power of output-part singleton split

**19 October 2026 — English proof and adversarial audit**

For a genuine native transversal set-valued functional partite System
B over a fixed part carrier P, write B^P for the canonical singleton
output-part split, replacing F with (F,q).

For every **positive** length N, there is a canonical
PART-PRESERVING full-function isomorphism

   (power(B,N))^P  ≅  power(B^P,N)

on the *same concrete part labels and coordinate tuples*.
The map sends a power vertex (p,coords,belongs) to precisely
(p,coords,belongs) in the singleton-language power; the
inverse has the same formula.

## Verification of operations

Relations are interpreted coordinatewise on both sides, and
splitting preserves the original ordinary relations, so relation
truth is preserved and reflected.

For the new operation (F,q), the source interpretation is

  y∈F^q_{power(B,N)}(x)
  ↔ [∀i<N, y_i∈F_B(x_i)] ∧ part(y)=q.

The target interpretation is

  y'∈F^{(F,q)}_{power(B^P,N)}(x')
  ↔ ∀i<N, [y_i∈F_B(x_i) ∧ part_B(y_i)=q].

Since N>0 and every native power vertex satisfies
part_B(y_i)=part(y), the two statements are equivalent.
This is the complete fibre equation required of a FULL
native functional embedding, not merely preservation of
definedness or existence of some output.

The coordinate/part identity map is bijective on vertices.
Thus it is a full isomorphism of genuine transversal
functional partite systems, preserving exact vertex
subsets, closure and all finite tested cardinalities.

## Audit

* The positive N assumption is essential. If N=0,
  the target coordinatewise operation is vacuous
  while the singletonized source operation still
  requires output part q; the identity is not a
  full function isomorphism.
* Multi-output primitive functions are handled by
  the part-indexed singleton operators; no arbitrary
  ranking of a fibre or extra vertex is introduced.
* All part labels are fixed P; the isomorphism is
  not valid between unrelated part universes.
* Source-defined EHN control projections are NOT
  asserted full. They must still be treated using
  the previously checked weak/original-partial
  interface, including phantom domains.
* This is a real Hales–Jewett coordinate POWER, not
  a proof that arbitrary completed line-attachment
  target trees have compatible marked roots.
* No 2019 U-closed theorem is used as an unverified
  inference: once this functional isomorphism and
  the #430 closure dictionary are proved, the
  already checked singleton-tagged U-closed closure
  rules can be applied to the *actual native power*.

## Lean deliverables

Define the vertex maps in both directions and the
full partite embedding from singletonized native power
to power of singletonized native System. Prove it is
surjective (and hence an isomorphism of full structures).
Use the independently checked exact positive-power
(F,q) membership equivalence of PR #431.

Prove named axioms, full umbrella CI. After this
the remaining genuine HJ work is attachment-list
history/root synchronization, not the power semantics.
