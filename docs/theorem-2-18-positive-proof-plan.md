# Positive proof plan for Theorem 2.18

Date: 9 October 2026.
Primary source: Hubicka--Nesetril, *All those Ramsey classes*,
arXiv:1606.07979v4, Sections 2.1.2 and 2.3--2.6;
https://arxiv.org/html/1606.07979v4 .

**Target:** a verified multiamalgamation implication, not another
conditional strict-functional-tree theorem. Existing counterexample
branches remain separate. No circulation manuscript text is changed.

## 0. Fix the exact theorem contract before declaring success

For finite A,B in K, first obtain C0 in R with C0 -> (B)^A_k from
R's Ramsey property. Then choose n = n(B,C0) from local finiteness.
The construction must produce a finite C with:

1. C is U-closed and C -> (B)^A_k;
2. the specified completion/projection C -> C0;
3. exactly the irreducible-test membership required by the local axiom;
4. a K-valued completion for every induced weak vertex test S of size <= n.

Local finiteness then supplies ONE map C -> D, D in K, preserving
all B-copies simultaneously. This map, not a strict B-tree target,
is the endpoint needed for the Ramsey transfer.

### Semantic gate (still open)

The current intrinsic `IsUIrreducible` and its obstruction modules are
not silently redefined. A working closed-test repair would protect
intrinsically U-closed U-irreducible source substructures in the global
projection and class-membership invariants. On those tests the existing
intrinsic/relative equivalence is applicable. Another possibility is a
relative irreducibility convention, but this is not automatically the
same theorem.

This must be audited in **both Definition 2.15 and Definition 2.17(4)**,
not just in the auxiliary Lemma 2.29. In particular, changing the tests
in (4b) changes the antecedent of the local-completion axiom. One must
prove that the given hypotheses imply the working axiom, or explicitly
state a corrected theorem hypothesis. A proof with a repaired (4b) is
NOT by itself a proof of the literal published formulation. Relative
irreducibility alone does not make a weak root-only test intrinsically
U-closed or a member of K.

The formal work in the first patch below is independent of this gate.

## 1. Finish the end of the proof first

Prove Ramsey transfer using only B-copywise preservation. For a colouring
of A-embeddings into D, colour an A-embedding a into C by its image under
the completion map when this image is an embedding; otherwise choose a
fixed default colour. In the B-copy produced by the Ramsey property,
every A-subcopy is in the first case. Thus D -> (B)^A_k.

This removes the `IrreduciblesExtendTo B C` and irreducibility assumptions
from the *colour-transfer* lemma. It does NOT remove test-membership (4b)
from local finiteness. It also avoids requiring all A-copies in C to lie
in B-copies merely for the last colouring step.

Implementation: `Ramsey/CopywiseRamseyTransfer.lean`:
`arrow_of_BCopywiseCompletion` and its class-valued version.

## 2. Map calculus and one complete closure-respecting Ramsey pass

Establish for the explicitly chosen test convention:

- invariance under full relational isomorphisms;
- composition of the relevant homomorphism-embeddings;
- restriction along full embeddings, including arbitrary induced weak
  source tests when used for local completions;
- restriction of the codomain to the exact image, without closing it;
- closure of selected A-supports in the native Picture construction.

Use the existing finite Hales--Jewett and Picture combinatorics, but prove
the general relational closure-rule interface. Do not identify arbitrary
closure descriptions with graph encodings of functions without a proved
encoding equivalence. Keep the intermediate semi-closed and final closed
structures distinct. Reuse the checked free-amalgam closure calculus and
closed-test side-localization lemmas.

Deliverable: an actual finite Ramsey witness with the selected projection
and protected-test coverage, constructed from A,B,C0, not supplied as an
oracle. Its dependency closure must not assume Theorem 2.18 itself.

## 3. Prove the rank-increment lemma directly with K-completions

At outer rank j, assume every closed substructure of U-size <= j has the
specified K-completion. One complete induced Ramsey pass must raise this
to j+1, while retaining the Ramsey arrow and original C0 projection.

Retain a generator set G, |G| <= j+1, and the concrete construction
history. In the small projected-support case, use the exact weak image
p[G], whose cardinality drops when labels collide, and the closure/rank
transport lemmas. Never infer that p[G] itself is closed. The closure may
be used to invoke a rank invariant, not to assert a false vertex bound.

### The central mixed-attachment obligation

For a source free amalgam E amalgam_R F, build a finite *compatible*
completion diagram:

    R --q--> Q in K
    |        | eE                | eF
    E --fE-> KE in K       F --fF-> KF in K

Here fE and fF agree on R through the SAME q, and eE,eF are full
embeddings of Q. Apply K's strong amalgamation to eE,eF, then fold the
source map into the resulting K-target. The protected tests that localize
to one side remain embeddings there.

The existence of these compatible diagrams is the hard lemma. Independent
completions of E,F,R do not supply it. Nor may strong amalgamation be
applied over a reducible separator that has not been realised in K.
Construct the diagram by replaying the selected Picture/Hales--Jewett
history with a common boundary completion; prove its existence and all
compatibility equations before using it as a stage invariant. If that
invariant is too strong, revise the construction rather than assuming an
unproved relative-extension oracle.

No strict full-functional B-tree conclusion is required for this route.
Target-side amalgamation happens in K, which need not freely amalgamate.

## 4. Convert closed rank control to the exact weak local tests

For a weak induced test on a finite S in C, put H = cl_U^C(S). The
inequality actually needed is

    USize(C induced on H) <= |S|,

NOT equality of weak-test and hull U-sizes, and NOT |H| <= |S|.
C is U-closed, so its induced H is U-closed. Complete H by the rank
invariant, then restrict that completion map to the original induced S.
The test used by local finiteness is still exactly S.

The first patch implements the generating-rank argument in
`ClosureGeneratedHullRank.lean`, and the general extraction theorem
`local_property_of_closed_USize` in `ClosureLocalCompletionRank.lean`.
The latter has an explicit hereditary-under-embeddings premise. Proving
that premise for the chosen completion notion belongs to Step 2; it is
not assumed to follow from a change of terminology.

This use of a temporary source hull does not change the separate rule
that projected images in the Picture argument are weakly induced on
exactly their original image vertices.

## 5. Iterate and apply the actual local-finiteness axiom

Handle rank zero and the empty structure explicitly. Iterate the proved
rank step n times; compose the projections back to the ORIGINAL C0, not
just to the most recent stage. Derive weak local completions via Step 4.
Verify all of (4a), (4b), (4c) with their precise quantifiers and one fixed
choice n(B,C0). Invoke the axiom, then use Step 1.

Finally transport the relational proof to languages with genuine partial
functions through a separately checked version of Proposition 2.20.
Preserve full embeddings, source-domain semantics, finite vertex tests,
and the class/local-completion hypotheses. The current first patch is
relational; it is not the arbitrary-language theorem.

## Validation and immediate next patch

The current branch adds actual proofs of the B-only transfer, relative
closure transitivity, the induced-hull generating property, the generator
bound, and the hereditary closed-rank-to-weak-test bridge. Each declaration
is listed in `CheckClosureAxioms.lean`. No `sorry`, new axioms, or provisional
main-theorem validation markers are introduced.

Immediate next patch: implement the chosen completion map calculus and
state the exact compatible K-completion diagram with its commuting maps.
Then prove the free-gluing preservation theorem for such a diagram before
attempting the simultaneous-existence part of Step 3. Keep the semantic
bridge and the unproved construction theorem visibly separate.

A full build certifies the submitted Lean statements, not their fidelity
to an unsettled interpretation of the paper. Theorem 2.18 remains open in
the coverage table until the semantic gate, witness construction, rank
increment, local-finiteness application and language transport are all
closed by checked proofs.
