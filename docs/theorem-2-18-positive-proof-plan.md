# Positive proof plan for Theorem 2.18

Updated: 10 October 2026.

## Current validation checkpoint — 10 October 2026

This section supersedes the outdated **future-work** status descriptions
below, which remain as a chronological proof-planning record. All
original/published TeX remains frozen. **The full repaired Theorem 2.18
is NOT yet validated.**

### Verified and merged

- PRs #181 and #183–#185: closed-test protection, semi-closed powers,
  canonical native line ranges, and relative U-closure of selected
  closed-profile copies in the ACTUAL temporarily conflicting Picture.
- PRs #186–#193: weak-source free-cut completion gluing and exact
  root-tagged part-language transport (embeddings, U-closedness,
  closed U-irreducibility, corrected protected maps, closure hulls and
  intrinsic U-generating rank).
- PRs #194–#201: genuine canonical-line little Picture Ramsey property,
  its selected-profile relative closure, ACTUAL tagged recursive repair,
  normalization and descent to an ordinary U-closed protected
  outer D-partite picture, a full finite pass, and the global Ramsey
  witness over an ARBITRARY, possibly non-U-closed Ramsey control D.
- PR #202: repaired class-valued Ramsey implication at original local
  completion cutoff n(B,D) <= 1, with no relative-copy hypothesis.
- PRs #203–#204 and #206, #209, #211–#212, #215, #218:
  the valid source-coordinate retraction cases, weak-free K-boundary
  gluing, the TRUE one-sided intrinsic-weak-to-ambient-hull U-size
  inequality, exact boundary-plus-side generator arithmetic,
  maximal-rank weak-test closure independence, low-rank weak
  completion, ordinary irreducible weak completion, and the
  properly sized relatively closed free-cut trichotomy.
- PR #207: pairwise overlap of disjoint-parameter native HJ lines
  is contained in one U-closed A-word copy. PR #210 records the
  counterexample to combining a FAMILY of such pairwise overlaps
  into a SINGLE word copy.

### Corrected semantic contract

Use **embedded CLOSED U-irreducible tests** for both working
protected completion maps and the repaired local-finiteness
membership clause. Its weak-test size clause continues to range
over ALL induced vertex subsets, whether closed or not. This
strengthens the substantive local-finiteness hypothesis relative
to a literal vacuity reading of the printed Definition 2.17;
equivalence to the printed theorem has NOT been shown. The
paired-equivalence class in the literal-definitions audit is
NOT locally finite under this repaired convention.

### The outstanding rank increment

Published Lemma 2.30 requires completing arbitrary **closed** tests
of intrinsic U-size j+1. Such tests may have MANY more than j+1
vertices. The validated source-cardinality dichotomy completes
an exact weak test on <=j+1 vertices or produces a proper free
decomposition into TWO relatively U-closed weak sides, each of <=j
vertices. It DOES NOT by itself complete the possibly much larger
closed rank-(j+1) test.

To complete the weaker exact-size branch in the ACTUAL HJ attachment,
the needed remaining geometry is: a protected map of the weak test
into one U-closed old picture (or independent compatible side maps),
AND a true proper free cut whose separator maps into a closed
K-boundary contained in a selected A-copy. Strong K-amalgamation
then handles the target completion without falsely setting the
boundary generating cost to zero.

See draft/live follow-ups #216 (ordinary coordinate retractions with
nonclosed support), #217 (two distinct small side projections and
abstract generated boundary), #219/#223 (two transverse old
preimages via A-letters), #220 (merged hereditary maximal weak rank),
#221/#224 (complete small proper cuts with a projected A-boundary),
and #222 (literal native weak-cut overlap lies in its core). **Only
merge after the exact source head passes full Lean build and axiom
audit; do not count green prior patches as certification of a
changed branch.**

### Published supporting sentence needing correction

PR #205 gives a three-vertex counterexample to the published
assertion that an arbitrary weak induced substructure and its ambient
U-closure have equal intrinsic U-size. PR #206 proves the correct
one-sided inequality, USize(cl(B0)) <= USize(B0), which may be strict.
A localized manuscript wording correction is documented but NOT
applied to the frozen TeX.

---


Primary source: Hubicka--Nesetril, *All those Ramsey classes*,
arXiv:1606.07979v4, Sections 2.1.2 and 2.3--2.6;
https://arxiv.org/html/1606.07979v4 .

**Target:** a verified multiamalgamation implication. Counterexample
branches remain separate. No circulation manuscript prose is changed.

## 0. Exact theorem contract and semantic boundary

For finite A,B in K, choose C0 in R with C0 -> (B)^A_k, then fix
n=n(B,C0). The construction must produce a finite C with:

1. U-closedness and C -> (B)^A_k;
2. the specified completion/projection to the ORIGINAL C0;
3. precisely the test-membership condition of the local-finiteness axiom;
4. K-completions of all induced weak tests on at most n vertices.

Local finiteness then supplies ONE map C -> D, D in K, preserving all
B-copies. A strict full-functional B-tree is not the required endpoint.

**Semantic boundary:** `IsUHomomorphismEmbedding` and `IsUIrreducible`
from the literal 2019 audit remain unchanged. The positive construction
now has an explicitly named working map `IsClosedUHomomorphismEmbedding`,
which protects embedded intrinsically U-closed U-irreducible tests.
`HasClosedUKCompletion` supplies a finite irreducible K-target for such a
map. These are candidate repaired conventions, not asserted equivalents
of the unrestricted printed definition.

The bridge must be checked in BOTH Definition 2.15 and Definition
2.17(4). Altering tests in (4b) changes the antecedent of local finiteness.
Prove that the original hypotheses imply the working axiom, or explicitly
state the corrected theorem hypothesis. Do not silently relabel a theorem
under that corrected hypothesis as the literal published Theorem 2.18.

## 1. Completed foundation: transfer and generating rank

PR #170 passed the full build and permitted-axiom audit on proof head
0b1fdecbb0e35593283f03b1a484c5ca45ee6d74 (workflow 37931903527),
and is merged.

`CopywiseRamseyTransfer.lean` proves that B-copywise preservation ALONE
transfers the Ramsey arrow. Non-liftable A-copies receive a default
colour; all A-copies in the final B-copy lift. No irreducibility or
all-A-copy coverage assumption is needed for this final colour transfer.
This does not remove condition (4b) from local finiteness.

`ClosureGeneratedHullRank.lean` proves that S generates its induced
ambient closure H, and USize(C induced on H) <= |S|. The hull can have
more than |S| vertices. Neither hull-cardinality bounds nor equality
between the weak-test and hull U-sizes are asserted.

## 2. Working completion maps and weak-test extraction

`ClosureClosedMap.lean` represents protected tests by full embeddings
of their own structures. This proves composition, source restriction
along ANY full relational embedding, exact induced codomain restriction,
and the weak-to-weak map from S to f[S]. No image hull is generated.

A source restriction need not be U-closed: any protected closed test in
that restriction is still the same embedded protected test in the larger
source. This proves the necessary restriction property rather than
assuming it. This statement concerns relational induced structures,
not weak functional restrictions pretending to be full function embeddings.

`ClosureClosedCompletionRank.lean` proves that the SAME finite K-target
completes an embedded weak test. Its `of_closed_USize` theorem discharges
the hereditary/restriction premise of the earlier generic rank bridge:
closed rank-n completion control gives completions of exact weak
n-vertex tests, under the explicitly named working convention.

## 3. Revised mixed-case argument: a fixed projected boundary

The original plan demanded simultaneous relative completions too early.
There is a usable, more precise case in which independent completions
already supply their compatibility.

Let F=E amalgam_R F2 be the source free amalgam. Suppose there are
projected side sources DL,DR, source projection maps pL,pR, and ONE fixed
closed Q in K with embeddings rL:Q->DL and rR:Q->DR such that

    pL restricted to R = rL composed with q,
    pR restricted to R = rR composed with q

for a map q:R->Q. Choose K-completions cL:DL->TL and cR:DR->TR
INDEPENDENTLY. Since Q is closed and K consists of ordinary irreducibles,
each completion restricts to a full embedding eL:Q->TL or eR:Q->TR.
These embeddings agree with cL rL and cR rR on the ORIGINAL Q carrier.
Strongly amalgamate TL,TR over these embeddings of Q. The resulting
side maps agree on R, even when q is not injective.

Where does Q come from? If the projected separator vertices lie in a
closed A-copy a(A) in a closed ambient D, their closure Q in D still
embeds into A. Closed hereditariness of K puts Q in K, and THEN Q is
irreducible. Containment in an irreducible A alone would not suffice.
`closedHull_factor_closed_copy` and `closedHull_in_class_of_subset_copy`
formalize these assertions.

`ClosureClosedMapGlue.lean` proves that compatible side maps glue to a
positive map preserving ALL protected closed tests. It pulls the side
ranges back into each test's own carrier; those preimages are closed,
so intrinsic irreducibility forces the test into one side. Source sides
need only be U-semi-closed and their common root must be U-closed.
The target is not required to be a free amalgam.

`ClosureProjectedCompletion.lean` combines these facts into
`HasClosedUKCompletion.of_independent_projected_completions`.
This constructs a full closed-test K-completion, not merely a B-copywise
map. Its premise supplies independent side completions, NOT a shared
completion diagram or relative-extension oracle. The earlier B-copywise
version remains in `ClosureProjectedBoundary.lean`.

**Scope:** this removes the compatibility obstacle when the fixed common
closed K-member Q embeds in both projected sources. It does not make
arbitrary independently completed reducible separators compatible.

## 4. Remaining construction and rank obligations

The next actual Lemma 2.30 work is to produce the hypotheses of the
mixed theorem from the concrete Picture geometry:

- construct the displayed projections preserving protected tests;
- prove the projected separator's closure lies in the selected A-copy;
- embed the SAME Q into both projected side closures;
- prove each projected side closure has U-size <= j, not merely that
  its source has fewer vertices or that its hull has bounded cardinality.

For a generator set G of size at most j+1, a collision in p[G] supplies
a strict cardinal drop in the exact weak projected support. Its closure
may then be used to invoke the rank invariant. In the injective-label
case, the cut must be chosen so that both sides lose a generator after
projection. This must be proved; minimal counterexample language alone
does not supply the two rank inequalities.

The full closure-respecting Hales--Jewett/Picture pass is still required.
Use the existing finite combinatorics but prove the general relational
closure-rule interface. Keep intermediate semi-closed and final closed
structures distinct. Do not import full hereditariness of K or hereditary
graph-irreducibility of A as hidden assumptions.

## 5. Iterate, invoke local finiteness, and transport the language

Handle zero rank and the empty structure explicitly. After a proved
j-to-j+1 step, iterate n times and compose maps to the original C0.
Use the working weak-test extraction from Section 2. Resolve the semantic
boundary, verify all three local-finiteness conditions with one fixed
n(B,C0), and apply the B-only colour transfer from Section 1.

Transport the relational result to genuine partial functions only through
a separately verified Proposition 2.20 interface, preserving finite weak
tests and completion hypotheses. Current positive modules are relational.

## Validation discipline

PR #171 adds the closed-test calculus, boundary construction, and gluing
modules. All seventeen new theorem declarations have individual axiom
checks in CheckClosureAxioms; every previous audit line is retained.
The first fourteen declarations passed workflow 37935674006 at head
1fae63a8a231bb745fcc44c9ead5031a59e18563. The final combined head must
pass its own build/audit before merge; consult the PR for that status.

No theorem identified as Theorem 2.18 or Lemma 2.30 is marked validated.
Remaining obligations are the actual source geometry/rank step, full
Ramsey pass, literal-hypothesis bridge, and language transport. No
circulation manuscript text has been modified.
