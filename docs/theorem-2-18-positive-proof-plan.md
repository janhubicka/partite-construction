# Positive proof plan for Theorem 2.18

Updated: 9 October 2026.
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
