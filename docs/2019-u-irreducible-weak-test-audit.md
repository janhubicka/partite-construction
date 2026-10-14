# 2019 U-irreducible weak tests: Lean-verified counterexample and local-axiom obstruction

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

The explicit finite model is Lean-verified in
`Ramsey/ClosureTwoCopyIntrinsicObstruction.lean` (merged PR #167).
The general no-large-test criterion is
`not_allIntrinsicUIrreducibleTestsEmbed_of_large_missing_test`
(merged #165). Both the model and its axiom audit passed CI.

**Consequence:** on the literal interpretation, the claim in the
initial-picture proof of Lemma 2.29 that a disjoint union of B-copies
has *every* U-irreducible induced substructure contained in a B-copy
does not hold. This refutes that proof invariant; it does not yet,
by itself, refute the existential conclusion of Lemma 2.29.

## Counterexample to the full existential Lemma 2.29 — Lean verified

The next finite construction refutes the **literal published**
Lemma 2.29, not merely the initial-picture proof invariant. Its Ramsey
input and universal nonexistence result are checked against the exact
`IsUClosed`, `IsUIrreducible` and embedding definitions in Lean.
The printed text has no ordinary-irreducibility assumption on B.

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

**Possible ordered strengthening (not Lean-verified):** adding a
linear-order relation and ordering the selected root before the three
non-root vertices may extend the argument to ordinarily irreducible B.
The required ordered finite Ramsey witness and the universal obstruction
must be checked before citing this as a verified stronger statement.
The present full counterexample already refutes Lemma 2.29, which does
not assume B is ordinarily irreducible.

**Lean validation boundary:**
`Ramsey/ClosureFourPointUniversalFailure.lean` (merged PR #168)
proves that no closed C can simultaneously satisfy the Ramsey arrow
and coverage of all intrinsic U-irreducible induced substructures by B.
`Ramsey/ClosureFivePairsRamsey.lean` (merged PR #169) constructs five
closure pairs C0, proves C0 → (B)^A_2 and closure of all A-copy ranges,
and combines the facts into
`lemma229_intrinsic_formulation_false`. PR #169 passed a complete Lean
build and permitted-axiom audit at head `163ae4a`, before its squash
merge `7d213b3`. No full Theorem 2.18 counterexample is claimed.

## Generic obstruction to Definition 2.17(4b) — Lean verified

Published Definition 2.17(1) says every member of K is intrinsically
U-closed, and (4b) requires **every U-irreducible substructure of C**
to belong to K. These two conditions cannot be simultaneously invoked
on a closed C containing a genuine closure output outside its root.

Indeed, if C is closed, e:Root → C is an embedded closure root,
t its unique closure tuple, and t(j) is not a root vertex, take the
exact weak induced test S=C minus the vertex t(j). The root survives
but its unique output does not. The source test S is intrinsically
U-irreducible by the existing missing-output theorem and it is not
U-closed. Therefore S cannot belong to K.

This is the generic Lean theorem pair
`IsUClosed.exists_nonclosed_Uirreducible_test` and
`not_all_intrinsic_Uirred_tests_in_closed_class` in
`ClosureLocalFinitenessNoGo2019.lean` (merged PR #179, CI checked).
It diagnoses **possible vacuity of the locally finite completion
antecedent**, not by itself failure of Theorem 2.18 as an implication.
It applies to any rule with an actual output vertex outside its root,
not just the unary P/R example.

The mismatch is therefore in the statements, not merely the old
Picture proof. Even replacing the decomposition test by a relative
U-substructure version does not alone make (4b) coherent with (1).
The intended correction must specify precisely which **closed tests**
are required to be members of K and which weak tests receive
completions in (4c).

## Plausible repairs requiring editorial decisions

- Restrict the claimed copy-coverage invariant and U-HE test
  quantification to **intrinsically U-closed U-irreducible
  substructures**. The closed-test side localization is Lean-checked
  in merged PR #166. But the transfer to Lemma 2.31 and its original
  locally finite completion hypothesis must be rechecked.
- Alternatively, use relative U-irreducibility in the test itself.
  Exact weak-test side localization was Lean-verified in PR #159.
  **This alone does not fix Definition 2.17(4b):** a nonclosed singleton
  closure root is still relatively irreducible, so the class-membership
  requirement remains impossible in the presence of genuine outputs.
  The tested family in (4b) must also be restricted or otherwise amended,
  and completion-map and local-finiteness implications reverified.

Do not silently change Definition 2.15. Keep the 2019 source
frozen and track proposed corrections as explicit TODOs.
