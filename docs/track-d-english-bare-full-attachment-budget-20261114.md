# Track D — English proof FIRST: full native bare mixed-rank successor with a paid control trace budget

**14 November 2026.** This is an explicit *one full-functional free attachment*
rank theorem, stacked on the bare pure-side transport PR #680. This does not
edit the frozen numbered survey, and does not restore removed collaborator TODOs.

## Theorem

Let the exact full native free-amalgam source diagram be

    Whole = Left *_Root Right,

with all four source embeddings FULL. Fix a FULL control embedding
`alpha:A↪D` with `A` finite and irreducible, a global actual EHN
control map `p:Whole→D` such that the entire true common root
projects into alpha[A], and a full-functional target base `Base`.

Fix m≥0. Let `F_A(m)=m+|A|(m+1)^|A|`.
Assume the three *BARE* strict functional weak-tree hypotheses:

    AtMostBare(Base,Left,m+1),
    AtMostBare(Base,Right,m+1),
    AtMostBare(Base,D,F_A(m)).

Then the whole full-functional source has

    AtMostBare(Base,Whole,m+1).

No source root injectivity, source-root irreducibility, source-root
generator budget, protected unoccupied target A-marks, or control
projected-history lists are assumed.

## Complete proof (three disjoint cases, no cheating)

Fix an EXACT weak test S⊆Whole with |S|≤m+1.

**Pure Left.** If every tested vertex lies in the range of the FULL
left source embedding, use the bare witness of Left at rank m+1
on the exact inverse-image subset iL⁻¹[S]. This set has size
≤|S|≤m+1. The English-first lemma in PR #680 transports the
ambient-relative weak HE across the full embedding to a witness
of Whole on the literal S, preserving every retained multivalued
source function fibre and every irreducible FULL ambient source
test whose WHOLE image lies in S. No ambient partial A-copy
certificate is requested. Thus no cross-copy A-trace condition.

**Pure Right.** Identical, using the full right source embedding
and its rank-(m+1) bare witness.

**Mixed.** Otherwise S contains a tested point outside the left
side and another point outside the right side. The exact verified
`projectedSideBudgets_of_mixed` yields two projected-control
side image subsets of size ≤m; no function closure is added.
The validated finite-trace restoration theorem in PR #671
converts `AtMostBare(Base,D,F_A(m))` into
`AtMostNoHistory(A,Base,D,id,m)`, with actual full target A-marks
on all relevant control A-copies.
Apply the verified full functional mixed weak rank successor
`IsFreeAmalgam.noHistory_weakRankSucc_mixed` (#642) to the
same exact literal S and actual EHN part map. It gives a strict
full-functional Base-tree target, ambient-relative weak HE on S,
and full ambient A-copy certificates. Forget the last condition:
the result is exactly the BARE witness of Whole on S.

These cases are exhaustive by classical excluded middle on the
actual set inclusion S⊆range(iL) and S⊆range(iR), and every
conclusion uses the ORIGINAL vertex set S.

**Result:** one true mixed full-functional HJ binary attachment
preserves BARE rank m+1, provided its whole control D pays
the larger rank F_A(m) and both actual full sides have BARE
rank m+1.

## Why this is progress but not yet the complete theorem

This removes the *pure-side* newly appearing ambient A-copy
obstruction by choosing a weaker output invariant, rather than
postulating a global EHN/copywise full trace lift of all earlier
HJ lines.

The only numerical price is an explicit requirement on the
fixed original control D, NOT an illegal increase in the
counted weak test S. This price is substantial and cannot be
deduced from `AtMostBare(Base,D,m)` alone.

To obtain a full native HJ Picture pass, we still need to
check the following genuinely independent facts:

1. The genuine HJ power core has BARE rank every n via its
   verified one-copy EHN→A→Base projection (the stronger
   AtMostNoHistory one-copy #643 is already checked).
2. The original copied OLD stage has BARE rank n;
   each succeeding binary attachment has the same old stage,
   the same fixed D, and the same selected alpha.
3. The actual finite list of line attachments preserves
   this bare stage predicate through the previously verified
   `EHN.attachAll_preserving` API. This is now plausible
   without arbitrary HJ line-history compatibility.
4. The outer choice of D with both the Ramsey arrow and
   BARE control budget F_A(n-1) must be made NONCIRCULARLY
   in the full iterated construction; e.g. check a reverse
   rank schedule against the existing native iteration proof.
5. At the final output, the finite-trace restoration theorem
   may recover ambient A marks at a further rank cost,
   but this must be separately budgeted. Final
   B-copy coverage and full original-2019 partial projection
   must not be inferred from bare rank alone.

The previously documented genuine three-line C7 demonstrates
that arbitrary HJ line attachments cannot preserve strict
K2-tree *same-rank* locality solely from Old being a forest,
but its control K3 fails the necessary high-rank predecessor.
Thus it does not contradict the new theorem's stronger
control-budget hypothesis. A counterexample satisfying
ALL displayed new hypotheses would be required to refute it.

## Lean acceptance

Prove a single named theorem
`IsFreeAmalgam.AtMostBare.of_control_budget_mixed_full_cut`,
with exact hPureL/hPureR/mixed case split and direct use of
the three already checked modules. Then package it into
the actual native `EHN.Stage.attach` with the genuine
`UnitAttachD` part projection, and ultimately the finite
line list. Do not green-mark that later packaging before
the new Lean proof compiles.

Two named axioms checks at most; full exact-head build,
source/no-admissions and standard logical axiom inventory.
