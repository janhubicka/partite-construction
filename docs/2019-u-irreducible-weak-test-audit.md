# 2019 U-irreducible weak tests: two-copy regression and candidate lemma counterexample

**Scope:** semantic audit of the *literal* Definition 2.15 and the
'unqualified U-irreducibles' invariants in Lemmas 2.28--2.30 of
Hubička--Nešetřil, *All those Ramsey classes* (Adv. Math. 356, 2019).
This is NOT an error claim against the general multiamalgamation
Theorem 2.18: its statement can remain valid under a corrected
intermediate invariant.

The 2019 definition says that a structure is U-irreducible if it
cannot be built by freely amalgamating two **proper U-closed
substructures**. When interpreted literally, both sides must be
intrinsically U-closed. For a non-U-closed induced weak test this
differs from using substructures relatively U-closed **inside the
test** (Definition 2.22).

## The smallest two-copy obstruction

Take a relational language with unary P and binary R. Let U consist
of the closure rule (R, Root), where Root is a single P-vertex.
A U-closed structure has exactly one R-output for each P-vertex and
no R-tuple rooted at a non-P-vertex.

Let B have vertices r,o, with P(r), R(r,o), and no other relation
tuples. This B is U-closed. Freely amalgamate two disjoint copies,
denoting their vertices r_0,o_0 and r_1,o_1.

The weak *induced* substructure on

    S = { r_0, r_1, o_1 }

contains the P-root r_0 but no R-output above r_0. It is thus
intrinsically U-irreducible by
`IsUIrreducible.of_missing_closureTuple` (merged #162). Since
|S|=3>|B|=2, S cannot embed in B. It meets both distinct B-copies.

The explicit Lean model is
`Ramsey/ClosureTwoCopyIntrinsicObstruction.lean` (PR #167), while the
general no-large-test criterion is
`not_allIntrinsicUIrreducibleTestsEmbed_of_large_missing_test`
(merged #165). The finite-model declaration should only be marked
Lean-verified after #167's complete build and permitted-axiom audit.

**Consequence:** on the literal interpretation, the claim in the
initial-picture proof of Lemma 2.29 that a disjoint union of B-copies
has *every* U-irreducible induced substructure contained in a B-copy
does not hold. This refutes that proof invariant; it does not yet,
by itself, refute the existential conclusion of Lemma 2.29.

## Candidate counterexample to the existential Lemma 2.29 (not yet Lean-checked)

A slight enlargement appears to refute the lemma's **unqualified
intrinsic weak-test conclusion**, not just its stated proof invariant.
This argument must be independently reviewed and then formalized:

1. Let A be a singleton with no P. Let B have one P-vertex r and
   three non-P vertices o,a,b, with R(r,o) and no other R-tuples.
   Both A and B are U-closed.
2. Let C_0 consist of five disjoint P-root/output pairs
   (r_i,o_i) with P(r_i) and R(r_i,o_i).
   Every copy of A in C_0 is a U-substructure: it is a singleton
   non-P-vertex and hence contains no closure root.
3. C_0 -> (B)^A_2: every two-colouring of the five non-P vertices
   has three of one colour. Select one of these three as o, its
   associated P-root as r, and the other two as a,b.
4. Suppose a U-closed C had C -> (B)^A_2 and every intrinsically
   U-irreducible induced substructure of C embedded in B.
   C must have at least five non-P vertices: if there were at most
   four, partition them into two classes of size at most two,
   defeating every B-copy (which contains three A-copies).
5. Since C has a B-copy, choose its P-root r and corresponding
   non-P R-output o. The induced test S=C\{o} contains r but
   omits its unique R-output. Because C is U-closed, S has no
   R-tuple above the copied root and is intrinsically U-irreducible.
   It has at least four remaining non-P vertices plus r, so
   |S| >= 5 > |B| = 4, contradiction.

Adding a genuine linear-order relation preserves this argument:
put B's root before the three non-P vertices, and in C_0 put all
P-roots before all outputs, each block ordered. From a monochromatic
triple choose its *first* output as the designated R-output, its
P-root as r, and the next two outputs as a,b. B becomes ordinarily
irreducible (the order links all distinct vertices), so this tests
even the irreducible-B setting.

**Validation boundary:** the two-copy finite obstruction is the Lean
target in #167. The larger A,B,C_0 Ramsey calculation and universal
no-C argument have not yet been encoded end to end in Lean and remain
a candidate refutation pending adversarial review. Do not mark
published Lemma 2.29 or 2.28 as refuted in the formal coverage table
until that check is complete.

## Plausible repairs requiring editorial decisions

- Restrict the claimed copy-coverage invariant and U-HE test
  quantification to **intrinsically U-closed U-irreducible
  substructures**. The closed-test side localization is Lean-checked
  in merged PR #166. But the transfer to Lemma 2.31 and its original
  locally finite completion hypothesis must be rechecked.
- Alternatively, define irreducibility relative to U-substructures
  of the tested structure (Definition 2.22). Exact side localization
  for arbitrary weak tests is Lean-checked in PR #159. The resulting
  relative U-homomorphism-embedding notion needs its own composition,
  Picture refinement and completion-transfer proofs.

Do not silently change Definition 2.15. Keep the 2019 source
frozen and track proposed corrections as explicit TODOs.
