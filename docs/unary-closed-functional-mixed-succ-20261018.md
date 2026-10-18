# Unary partial functions: genuine strict mixed successor for CLOSED source tests

**18 October 2026 — English proof and adversarial audit before Lean.**

This note concerns the genuine native iterated partite construction in
the full function language, using the already verified recursive
Ramsey control and real transversal set-valued output fibres.
It does not turn the iteration into the alternative relational/U-closed
profile construction. The tested finite vertex set is exact.

## 1. General closed-image lemma for FULL function homomorphisms

Let p:C→D be a full function homomorphism in the survey's
\`Structure.IsHomomorphism\` sense (whole-fibre equality at EVERY
input). For any function-closed S⊆C, its *actual* image p[S]
is function-closed in D, even when p is not injective or onto D.

Proof: for arguments d_i∈p[S], choose x_i∈S with p(x_i)=d_i.
Every y∈F_D(d) lies in p[F_C(x)] by the whole-fibre equality,
so y=p(z) for some z∈F_C(x). Since S is closed, z∈S and
therefore y∈p[S]. Nullary inputs work by the same argument.
No output or source vertex is added to S.

NOTE: This lemma is false for an arbitrary original-2019
source-defined/EHN projection: an undefined source input may
map to a defined control input. The difference is critical.

## 2. Why unary EHN projections are enough

For a language in which every function symbol is UNARY,
the repository already proves
\`IsEHNHomomorphismEmbedding.isHomomorphism_of_unary\` in
\`Functional/UnaryEHNCompletion.lean\`.
The generated closure of a SINGLE input vertex is irreducible;
hence the EHN restriction to it is a full embedding and reflects
the unary function domain. Thus EVERY unary EHN projection is
a full homomorphism, not merely source-defined partial.

This fails for arity≥2 (the verified two-disjoint-B-copy
cross-copy input), and is not asserted for \`Option(Set)\`
defined-empty operations.

## 3. Closed mixed functional test: automatic occupied A-closure

Fix a genuine FULL functional free attachment
C=L*_{R}M, EHN p:C→D, selected full α:A↪D containing
the common root labels, A↪B FULL, B irreducible. Assume
A irreducible as required by the current verified ambient-A-copy
history EHN pullback. Let S⊆C be FINITE and genuinely
function-closed, mixed between both sides, with |S|≤m+1.
Assume D has the verified ordinary STRICT full-functional
weak-test history predecessor invariant at rank m.

Because side embeddings are FULL, their ranges are function-closed.
Consequently the EXACT side weak tests

   S_L = i_L^{-1}(S),    S_R = i_R^{-1}(S)

are closed in their respective sides. By the unary EHN-to-full
lemma, both projected maps p∘i_L and p∘i_R are FULL function
homomorphisms. Their actual image sets

   I_L = (p∘i_L)[S_L],  I_R = (p∘i_R)[S_R]

are therefore function-closed in D by Step 1.
The full α-preimages

   H_L=α^{-1}[I_L],    H_R=α^{-1}[I_R]

are function-closed in A.

Apply the already verified
\`IsFreeAmalgam.weakTree_of_closedOccupied_alpha_mixed_succ\`:
the exact mixed-side projected cardinalities are automatically ≤m
by genuine mixedness, and H_L,H_R are closed. This obtains a
STRICT full-functional B-tree completion of the ORIGINAL weak
S, retaining all actual A-copy intersections and arbitrary
projected histories.

Finally, because S itself is closed, the previously verified
closed-test bridge upgrades the same witness to an
original-2019 partial HE of the full induced S; in this unary
language the result is actually a FULL function homomorphism-
embedding by the checked unary EHN-to-full theorem.

## 4. Adversarial checks and limits

* The initial projected control D need not be B or a forest;
  only the stated rank-m predecessor history invariant is used.
* CLOSED S is essential. For weak S with unary F(a)=b and
  a∈S but b∉S, p[S] need not be closed even if p is FULL.
  The theorem does not solve the all-weak-test rank step.
* UNARY is essential for upgrading EHN to FULL globally.
  Binary cross-copy phantom domains provide a verified
  counterexample to that upgrade in higher arities.
* Mixedness is essential for proper side-cardinality drop.
  Pure tests use the already checked core/copy branches.
* Set-valued unary functions may have multiple values in
  distinct output parts; nothing assumes singleton values.
* The SOURCE full embedding ranges are closed. We do not glue
  target B-trees over a nonclosed weak root or use a globally
  prescribed α-mark.
* This is a LOCAL closed-test strict successor theorem, NOT
  a complete unary native n-pass theorem: the rank-m
  predecessor property used here still quantifies over ALL
  weak tests. To derive an unconditional end-to-end unary
  theorem, one must establish that the initial/Picture/pure
  induction supplies the requisite (possibly reduced
  closed-test) predecessor invariant.

## Lean acceptance

Formalize the general full-homomorphism image-closed lemma,
reuse the checked unary EHN-to-full theorem on both sides,
show the two exact Finset projected image sets are closed in D,
pull their closure back through full α, call the certified
mixed successor rank theorem and then upgrade the closed test
to a full unary HE into the same strict B-tree target.

No universal full functional sparsening marker is added to
the frozen survey circulation manuscript.
