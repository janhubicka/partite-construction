# Local-finiteness audit: the paired-equivalence example is NOT an example for the repaired theorem

10 October 2026. This note corrects the interpretation of draft PR #182.
The original TeX manuscript, published predicates, and existing Lean modules are
unchanged. Mathematical family below is an independently argued obstruction to
local finiteness under the **proposed closed-test convention**; it has NOT been
formalized in Lean. The script in the conversation tests its finite block
combinatorics, not the full semantics of the theorem.

## Distinguish the three logical assertions

Published Definition 2.17(4) assumes C U-closed and asks:

* (4a) C0 is a U-completion of C;
* (4b) **every U-irreducible substructure of C belongs to K**;
* (4c) every substructure of C with at most n vertices, including nonclosed
  ones, has a (K,U)-completion.

The conclusion is a completion **with respect to B-copies**, which is weaker
than a global (K,U)-completion.

Read literally in the relational language, singleton induced structures are
U-irreducible even if they omit mandatory closure outputs. Hence if K has no
singletons, (4b) fails for every nonempty C, and (4) is vacuous. The original
draft PR #182 invoked precisely this *syntactic* issue. It was misleading to
describe that as verifying any meaningful local finiteness for paired
equivalences.

Under the *intended repaired* convention, (4b) tests only **U-closed**
U-irreducible substructures, and the map notions in (4a),(4c) protect closed
irreducible tests. Then the singleton argument is not available; the paired
equivalence class is NOT locally finite. The weak tests in (4c) remain all
induced subsets. A weak singleton exists in the relational encoding and has
a K-completion by adjoining its mate. In a genuine total-function language,
a singleton is not a substructure. Either way, the size-one condition is
too weak to resolve nontransitive E.

## Fixed class, fixed control, fixed B

Let L={<,E,M} be binary relational. R is the Ramsey class of all finite
structures with a strict linear order < and unrestricted E and M. K is the
subclass where E is an equivalence relation, M is an irreflexive symmetric
total matching, and M(x,y) implies E(x,y). Every K-member consists of
matched pairs, with an arbitrary linear order and arbitrary nonconvex
equivalence classes. The unary closure root is a single E-reflexive vertex,
with M encoding the unique mate. K is U-closed, closed-hereditary, and has
strong amalgamation (union of matchings, equivalence closure of E, and a
common extension of the two finite orders). K is not Ramsey, independently
of the local-finiteness analysis.

Fix B0 in K consisting of three consecutively ordered matched pairs with
E-class pattern X,X,Y: the first two pairs are equivalent, the third is
inequivalent to both.

Fix C0 in R on five ordered matched pairs, with labels

    A < B < T < C < D.

Each label denotes a full matching pair. Put E-positive between **distinct**
pairs precisely on AB, BC, AT, and make E reflexive/symmetric and positive
within each matching pair. All other cross-pair E-relations are absent.
Thus C0 is U-closed and ordered, but E is nontransitive (A~B~C, A!~C).
Its E relation is not assumed an equivalence because C0 belongs only to R.

## For every cutoff n, a bad candidate with locally completable tests

Choose an odd m>=5 with m>n. Use backbone matched pairs
b0,...,b(m-1), labelled

    A,B,A,B,...,B,C,

so b0 has type A, b(m-2) type B, and b(m-1) type C.
For each backbone edge b_i--b_(i+1), add a **private** matched pair t_i
labelled D. Add one more matched pair t_* labelled T.

Form the finite relational C_m as the union of the **induced K-copy B0
diagrams** on the following triples of matched pairs, with no other
cross-gadget tuples:

* for i=0,...,m-2, the triple {b_i,b_(i+1),t_i}, ordered by its labels;
  its label pattern is (A,B,D) or, at the final edge, (B,C,D);
* the closing triple {b0,t_*,b(m-1)}, with label pattern (A,T,C).

Each triple is a copy of B0: its first two pair types are E-equivalent;
the last type is E-inequivalent to both. Their full internal linear orders
and matching relations agree on overlapping backbone pairs. In C_m, all
the root/mate closures exist and are unique, so C_m is U-closed.

The block-interaction graph is a chordless m-cycle of backbone blocks
with a private triangle tag on each edge. Its only cliques on >=3 blocks
are these B0-triangles. An induced U-closed U-irreducible substructure must
have pairwise adjacent matching blocks: if two blocks x,y have no tuple
between them, removing x and removing y gives two proper U-closed sides
that freely cover the test. Consequently every such substructure is a
closed induced substructure of one B0 gadget and belongs to K. This
proves the **repaired** (4b), including the empty test.

The label map f:C_m->C0 collapses equal-labelled blocks, sending each
individual matched pair isomorphically onto its labelled pair in C0.
Every relation tuple belongs to one B0 gadget, on which f is a genuine
induced embedding. Hence f is a positive homomorphism embedding **every
closed U-irreducible test**. Thus C0 is a *closed-test* U-completion of C_m,
establishing repaired (4a). Do NOT substitute this for the literal map
of published Definition 2.15: nonclosed intrinsic U-tests may be larger
and can invalidate reflection.

Let S be an arbitrary induced (possibly nonclosed) substructure of C_m on
at most n vertices. Its closure adds the mates of the represented
vertices, so it contains at most n entire matching blocks. Since m>n,
at least one backbone block is missing. The positive E links on the
represented backbone blocks cannot then connect b0 to b(m-1). Every
negative E constraint in a B0 gadget is compatible with equivalence
closure of the positive E links: private D tags have no positive links,
and the negative constraints in the closing gadget would conflict only
if the entire backbone path were present. Extend E to this equivalence,
keep the matching, and extend the partial order to a total order (using
the fixed C0 label order, breaking ties between equal labels). This
makes a member of K, and the identity on the closed hull is a
closed-test homomorphism-embedding. Restrict it to the ORIGINAL S.
Thus all exact weak tests of at most n vertices have K-completions:
repaired (4c) holds.

However, there is **NO K-completion with respect to copies of B0**.
Any B0-copywise map to a K-member must preserve E on every backbone
positive edge b_i~b_(i+1), forcing the first and final backbone blocks to
be equivalent by transitivity. The *closing* B0-copy requires these two
blocks to be inequivalent and its embedding reflects that absence.
Contradiction. This refutes the local-finiteness implication for the
fixed B0,C0 at EVERY proposed cutoff n.

Therefore K does **not** satisfy the proposed corrected Definition 2.17(4).
Its non-Ramsey property cannot refute the repaired Theorem 2.18.

## Where the definition must change

For an intended meaningful theorem, repair all usages consistently:

* map in (4a): preserve precisely closed U-irreducible tests;
* (4b): require membership only of U-closed U-irreducible substructures;
* (4c): retain ALL exact weak size-<=n substructures, but interpret their
  (K,U)-completions with the same revised test-preservation notion;
* keep the original n(B,C0) quantifier and the B-copywise conclusion.

This is stronger than the literal vacuous local axiom for K without
singletons: it must not be passed off as an implication from printed
Definition 2.17. It agrees with the positive closed-test development in
merged PRs #181, #183--#185. Full theorem proof still requires the rank
increment and unrestricted initial-stage assembly.

## Finite checks and certification boundary

The standard-library finite checker
`paired_equivalence_local_finiteness_audit.py` was run on odd backbone
lengths m=5,7,9,11. It checked maximal block cliques, local E-equivalence
consistency of every block support through sizes 1,3,5,7 respectively,
and the global positive-path/negative-end contradiction. It does not
certify the complete Lean statement, order extensions, or all
weak-substructure completions, which are justified in the argument above.

The existing draft PR #182 contains uncompiled Lean modules addressing
the **literal** singleton vacuity and the non-Ramsey colouring. It is
left open and unmerged. This note supersedes any suggestion there that
the paired-equivalence class is a valid multiamalgamation example under
the corrected convention.