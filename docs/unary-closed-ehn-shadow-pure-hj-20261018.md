# Closed unary EHN shadow transfer and strict locality of the genuine Hales–Jewett power

**18 October 2026. English proof and adversarial audit before Lean.**

The native iterated Appendix A proof uses an actual FULL functional
Hales–Jewett power as the Picture core and then attaches copies of the
old stage. We retain that construction in the original set-valued
function language, including transversal output fibres; no alternative
relational or U-closed Picture is introduced.

The last validated improvement gave a strictly weaker rank-m predecessor
invariant \`AtMostClosed\`, asking strict B-tree completions with
projected histories only on genuinely function-CLOSED finite tests.
To use this through the real Picture, we must transport its history
certificates through native EHN projections, and eventually through
the finite Hales–Jewett line-attachment list.

## 1. The stage-relative closed-test invariant

For an arbitrary native functional stage C with part projection
p_C:C→P into a fixed **external original control carrier** P,
define

\`AtMostClosedWithPart(A,Base,C,p_C,m)\`

to say: for each finite EXACT function-CLOSED vertex subset
S⊆C with |S|≤m, and every finite list of projected history
predicates H⊆P, there is a genuine STRICT full-functional
Base-tree target, an ambient-relative weak function map from S,
completed full A-copy intersection certificates, and preservation
of all membership histories of p_C[S].

This is the same history predicate already kernel-verified for the
stronger exact-weak \`AtMost\`; only closedness is added to the
quantifier. The existing \`AtMostClosed\` on the functional control
D is exactly the special case p_D=id.

## 2. Unary EHN shadows preserve closed-test strict locality

Let q:C→D be an EHN / original-2019 partial-function projection
commuting with the fixed original-control projections:

   p_C = p_D ∘ q.

Assume all primitive function symbols are unary. The separately
verified \`IsEHNHomomorphismEmbedding.isHomomorphism_of_unary\`
says that q is actually a FULL function homomorphism, including
reflection of domains. The already verified general
\`IsHomomorphism.image_isClosed\` therefore shows that for each
genuinely closed EXACT S⊆C, its image q[S] is function-CLOSED in D.

Its cardinality is bounded by |S|, and the image is a literal
Finset image—not a generated function closure. Apply the
rank-m closed-only witness of D to the exact q[S]. Then pull it
back to S using the previously kernel-checked
\`SetAmbientRelativeWeakTreeWitness.pullback_ehn_commutingParts\`.
This preserves:
* the STRICT full-functional target tree;
* all actual ambient FULL A-copy intersection certificates
  (A is irreducible);
* every requested projected-history predicate of the ORIGINAL P;
* all surviving set-valued function fibres under exact weak
  restriction.

The result is the same rank-m \`AtMostClosedWithPart\` invariant
for C. No rank loss and no intermediate closed-hull enlargement.

## 3. Actual Hales–Jewett power

Let B be a real transversal functional \`System L P V\`, EHN
partite over some functional control D. Let N>0 and
C=\`FunctionalPartite.Induced.power B N\` be the ACTUAL
coordinatewise function power, not a relational proxy.
Choose one genuine coordinate i:Fin N.

The verified \`Induced.coordinateEHN\` theorem gives an EHN
homomorphism-embedding from this power to B via coordinate
evaluation q_i(z)=z.coord(i), and the power part projection
commutes exactly with B's part projection:

   part_C(z)=part_B(z.coord(i)).

Thus the unary closed-shadow transfer of Section 2 applies
to this ACTUAL HJ power. A rank-m closed-only strict witness
of B is inherited by the whole power at the SAME m,
with all original part histories and actual full A-copy
intersections protected.

This completes the PURE CORE rank-m predecessor transfer
for unary closed tests inside the native power.

## 4. Adversarial audit and remaining work

* This theorem is valid only for a **CLOSED source test**.
  Even a FULL unary map does not send arbitrary weak subsets
  to closed images; unary F(a)=b with S={a} remains the
  regression showing why AtMostClosed is genuinely weaker.
* For higher arity, EHN q can map undefined cross-copy
  source tuples to defined D-tuples, so q[S] need not be
  closed. The unary assumption cannot be removed without
  a separate domain-reflection hypothesis.
* The coordinate map itself is EHN, not an injective
  global embedding. The proof uses the verified full
  embeddings ON IRREDUCIBLE A-copies for intersection
  histories, never injectivity of q on all C.
* No multi-valued function is replaced by a singleton.
  Actual output-fibre transversality of the native power
  remains in force; the result uses the entire function
  fibres of true structures, not merely graph relations.
* This does NOT yield an unconditional whole Picture step.
  Its remaining cases include copied-old pure tests and
  actual mixed line attachments. For the latter, the
  rank-(m−1) protected target-mark gluing still needs
  compatible markers for actual projected side histories.
  The old arbitrary-stage C5 and K2 marked-parity audits
  forbid installing an unconditional target root oracle.
* The history list is attached to the ORIGINAL P, not to
  the moving previous stage's carrier. This bookkeeping
  is essential for a genuine n-pass construction and must
  not be discarded as a harmless rewriting.
* No complete sparsening or final B-coverage theorem is
  claimed here; the published survey prose remains frozen.

## Lean acceptance

Formalize the stage-relative predicate, its equivalence with the
existing closed-control identity case, unary EHN pullback with
separate commuting original-part projections, and the specialization
to a REAL Hales–Jewett coordinate power. Print named axioms and
require the complete umbrella project build before merging.
