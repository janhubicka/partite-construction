# Track D — English proof FIRST: no-history exact weak rank-(m+1) mixed successor

**12 November 2026.** This is the rank-budget application of the
English-first no-history mixed-gluing theorem (PRs #640/#641).
No numbered Nešetřil survey manuscript or collaborator TODO is edited.

## Proposed exact invariant

For a genuine full functional structure C with a fixed part map
p:C→D, a finite test S⊆C and irreducible A, let W(C,p,S)
mean the existing
`SetAmbientRelativeWeakTreeWitness A Base C p S []`.
The empty history is **intentional**: W retains all three
mathematically substantive outputs

* a strict full-functional Base-tree T,
* a genuine `IsAmbientRelativeWeakHE C S T` on the literal WEAK S,
* full target A-copy witnesses for all ACTUAL ambient full A-copies
  intersecting S,

but DOES NOT demand that every equal target image has equal
projected control parts or that an A-target mark has no extra hits.

Define `AtMostNoHistory m` by requiring W on every literal
finite weak S with |S|≤m. This is weaker than the already known
`SetAmbientRelativeWeakTreeWitness.AtMost m` quantifying over
arbitrary finite projected histories.

## The mixed rank successor

Take a genuine FULL functional source free diagram
`Whole = Left *_Root Right` with fully embedded source sides.
Fix an actual EHN control part map p:Whole→D, any selected FULL
alpha:A↪D containing the projected common root, and assume A
irreducible. Suppose D satisfies `AtMostNoHistory m` for the
identity control map.

Let S be an arbitrary EXACT weak vertex test of Whole with
|S|≤m+1 which genuinely meets both exclusive source sides
(i.e. there is a tested point outside each of the two side
embedding ranges).

Write

    S_L = i_L^{-1}[S]     S_R = i_R^{-1}[S].

These are LITERAL weak subsets, not function-closed. The verified
`projectedSideBudgets_of_mixed` proves

    |p[i_L(S_L)]| ≤ m,   |p[i_R(S_R)]| ≤ m

using nothing beyond the original finite S and injectivity
of the FULL source-side embeddings. Even if a function-closure
of S_L has more than m vertices, it is irrelevant: it is NOT
substituted for S_L.

Query the ordinary control `AtMostNoHistory m` invariant
separately for the two exact vertex image subsets
`I_L=p[i_L(S_L)]`, `I_R=p[i_R(S_R)]`. Each result is an
ordinary **unprotected** strict ambient weak-tree certificate,
with full target copies of every actual control A-copy,
including the selected alpha.

The side EHN projections are simply
`p_L=p∘i_L` and `p_R=p∘i_R`. Their restrictions to S_L,
S_R have exact images I_L,I_R; no domain reflection or
closedness is assumed. The existing weak EHN composition
lemma makes these valid side projections. Their maps agree
on the actual common root because p is a single function.
All projected root positions are in alpha(A) by the explicit
selected-support hypothesis.

Apply the already isolated theorem
`IsFreeAmalgam.ambientRelativeWeakTree_noHistory_of_ordinaryControlSideImages`
(PR #641): it extracts FULL target A-marks on the occupied root
and glues the two strict targets over these marks. It returns

    SetAmbientRelativeWeakTreeWitness A Base Whole p S [].

This closes the **mixed** rank-(m+1) step for arbitrary exact
WEAK tests and fully set-valued functions. It tolerates a
multi-generated, reducible, NONINJECTIVE source root q,
nonclosed projected images, and false target collisions on
unoccupied A-mark positions. No full source image-fibre
surjectivity is assumed on undefined inputs.

## Explicit adversarial limit

This is a theorem about ONE genuine full native free-attachment
cut with an ordinary control predecessor. To conclude the
entire induced Hales–Jewett Picture and n-pass strict iteration,
we must *also* formally validate:

1. the pure-copy exact weak case using the OLD moving stage's
   `AtMostNoHistory (m+1)` and full side restriction;
2. the pure-core exact weak case, using the genuine HJ power's
   one-copy ambient-relative functional A→Base target and the
   irreducibility-based protection of full ambient A-copies;
3. induction over EVERY selected line in the finite actual HJ
   attachment history, whose control p stays an EHN projection,
   with no change to the Ramsey arrow or class membership;
4. rebase the completed stage to the identity control before
   the next pass, and transfer the source-defined
   original-partial projection and final B-copy coverage.

**Do not infer these four items solely from the mixed lemma.**
The earlier arbitrary-history/ProtectedAMark invariant still
may be too strong or fail; proving no-history is a different
mathematical route. The printed relational Appendix A and
separate verified two-pass closure-profile functional theorem
are unaffected.

## Lean validation

First prove `SetAmbientRelativeWeakTreeWitness.AtMostNoHistory`
and the generic named mixed theorem
`IsFreeAmalgam.noHistory_weakRankSucc_mixed` using
the VERIFIED `projectedSideBudgets_of_mixed` and pending
#641 occupied mark extraction. Keep a root-level
`#print axioms` test. If the parent #641 fails CI, fix it first.
No sorry/admit/new axiom and no TeX manuscript edits.
