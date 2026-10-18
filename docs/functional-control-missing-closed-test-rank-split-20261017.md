# A missing CONTROL output on a closed finite source test gives a strict rank split

**17 October 2026 — English proof and adversarial audit before Lean.**

This is a useful strengthened consequence of the just-verified
control/source output-defect dichotomy. Unlike the current
diagnostic input-hull reducibility theorem, it decomposes the
WHOLE original finite test and certifies strict vertex-cardinality
drops on its three free-amalgam pieces.

Let C be a genuine functional partite System with an
original-partial/EHN part projection to the control D, let
S⊆V(C) be a FINITE **function-closed** test, and let
\(\bar x\in S^{\mathrm{arity}(F)}\).
Suppose the control has an output \(q\in F_D(p\bar x)\) which
is absent from the exact weak source test at part q.

## English proof

By function-closedness of S, every actual value
\(y\in F_C(\bar x)\) already lies in S. If the ambient
source function fibre were nonempty, EHN defined-fibre
surjectivity would lift q to a source output y of part q.
This y would survive the exact weak test, contradiction.
Hence \(F_C(\bar x)=\varnothing\), while
\(F_D(p\bar x)\ne\varnothing\).

The already formally checked
\`IsEHNHomomorphismEmbedding.closedTest_decompose_of_domainFailure\`
applies to exactly these hypotheses. It yields a
PROPER full functional free decomposition

\[
 C|_S = E *_G H
\]

where each of the left, right, and common carriers has
strictly fewer vertices than S:

\[
  |E|<|S|,\qquad |H|<|S|,\qquad |G|<|S|.
\]

No closure of S is needed: S is already genuinely closed,
and the theorem decomposes \`C.induce S\` **on the same
finite carrier**. The result is a correct rank-decrease
bridge for the closed-test branch of the published induction.

## Independent adversarial audit

1. **Closedness is essential.** For unary F(a)={b},
   S={a}, and b∉S, the weak test lacks the actual output,
   but its ambient source fibre is nonempty. No domain-failure
   reducibility conclusion follows.
2. **The EHN invariant is essential.** A merely weak
   homomorphism need not reflect even defined source fibres,
   so target q cannot necessarily be lifted when C is defined.
3. **The D-side active part q matters.** Mere absence of
   an output in the source without a projected target output
   supplies no domain-reflection failure.
4. **Properness/cardinality:** the old verified decomposition
   theorem provides strict inequalities on the actual test
   carrier, NOT a generated closure; thus the n-vertex budget
   is maintained.
5. **No artificial irreducibility assumption on weak tests.**
   A closed test with this domain failure is genuinely
   reducible; the proof makes the decomposition explicit.
6. **Scope of the result:** the induction must still handle
   all NONCLOSED weak intermediate tests; their omitted-source
   outputs prevent this shortcut. In particular this theorem
   neither constructs a strict B-tree TARGET root nor
   synchronizes arbitrary attached HJ lines.
7. **Defined-empty convention:** this statement uses
   nonempty source fibre as defined, matching original-2019
   partial functions. An independent \`Option (Set)\`
   defined-empty extension must track its extra domain bit.

## Formalization plan

Specialize \`System.controlMissing_of_closed_iff_projectedUndefined\`
to a finite S, extract a target nonempty-fibre witness and a
source empty-fibre certificate, then invoke
\`IsEHNHomomorphismEmbedding.closedTest_decompose_of_domainFailure\`.
Expose the resulting entire-test free decomposition with all three
strict cardinal inequalities; check named Lean axioms and full CI.

This closes one rank-split *case*, NOT the global strict functional
n-pass sparsening theorem. The remaining nonclosed projected A-root
history/profile compatibility must be proved separately.
