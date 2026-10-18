# Closed-only unary functional mixed successor: no weak-test predecessor needed

**18 October 2026 — English proof and adversarial audit BEFORE Lean.**

The published-order native Appendix A iteration already has a verified
closed functional Ramsey control and a genuine Hales–Jewett functional
partite Picture. All actual partite systems retain transversal
set-valued function output fibres. The weak-test induction uses
EXACT finite vertex sets and source-defined original-2019 EHN maps;
no intermediate U-closed relational Picture is introduced.

The verified unary local mixed theorem (#419) uses the STRONG
predecessor \`AtMost\`, requiring strict B-tree histories for every
exact weak control test of size ≤m. This requirement is unnecessarily
strong for genuinely CLOSED unary source tests: their projected
side images are CLOSED, so the weaker, newly verified
\`AtMostClosed\` (#420) suffices.

## 1. Separate the numerical mixedness lemma

Let i_L:Left↪Whole, i_R:Right↪Whole be FULL embeddings (for
the numerical calculation only their injectivity matters).
Let S⊆Whole be a finite EXACT test with |S|≤m+1,
containing one vertex outside range(i_L) and another outside
range(i_R). Put

  S_L = {x∈Left : i_L(x)∈S},
  S_R = {y∈Right : i_R(y)∈S}.

The maps i_L:S_L→S and i_R:S_R→S are injective but not
surjective, so |S_L|,|S_R|<|S|≤m+1.
For any function p:Whole→P, even a NONinjective EHN
projection, the images I_L=(p∘i_L)[S_L],
I_R=(p∘i_R)[S_R] satisfy

   |I_L|≤m,  |I_R|≤m.

Package this as a reusable \`projectedSideBudgets_of_mixed\`.
The existing closed-boundary mixed successor proof (#415)
can call it directly, deleting its duplicated filter/Finset
cardinality bookkeeping without changing the theorem statement.

## 2. Projected unary closed side images

Assume every function symbol of L is UNARY.
Let Whole=Left *_{Root} Right be an ACTUAL FULL functional
free amalgam, with selected FULL alpha:A↪D and EHN p:Whole→D.
Take an EXACT finite S⊆Whole that is genuinely CLOSED
under all set-valued function outputs and is mixed as above.

Because the FULL side embeddings are function-closed, the
literal side preimages S_L,S_R are CLOSED in their sides.
EHN maps p∘i_L, p∘i_R are FULL function homomorphisms
by the verified unary EHN theorem. Full homomorphisms send
CLOSED vertex sets to CLOSED image sets. Therefore the
literal projected side images I_L,I_R are CLOSED in D.

No closure of I_L or I_R is computed. Their cardinal
bounds from Step 1 are unchanged. In particular, the
occupied selected A-preimages alpha^{-1}[I_L] and
alpha^{-1}[I_R] are automatically closed as alpha is FULL.

## 3. Use ONLY the closed-control rank-m predecessor

Let the old functional control D satisfy
\`AtMostClosed(A,Base,D,m)\`. It supplies STRICT full
functional B-tree weak-history witnesses for EXACT CLOSED
control tests of size at most m, including all actual
ambient full A-copy intersection certificates and every
arbitrary list of projected-history predicates.

Apply the verified
\`AtMostClosed.protected_of_closedOccupiedA\` to the
two ACTUAL closed projected side tests I_L,I_R.
This creates two protected FULL alpha-marks in strict
TARGET B-trees, by attaching one fresh target Base-copy
along the closed occupied A-substructure.
The marked target witnesses preserve any requested
projected histories; no source vertex or counted
control test vertex is added.

Now apply the independently checked and extracted
\`IsFreeAmalgam.weakTree_of_protected_projected_side_witnesses\`
(PR #421). That theorem pulls the protected control
side witnesses back along the actual EHN side maps and
glues their strict full-functional targets over the
FULL protected TARGET A-marks. It gives a STRICT
full-functional B-tree completion of the ORIGINAL exact
weak S, preserving its actual ambient full A-copy
intersections, all surviving multi-output function fibres,
and every requested original-control projected history.

Since S is CLOSED and the language unary, the verified
closed-test bridge plus unary EHN-to-full upgrades
the same completion map to a FULL function
homomorphism-embedding of Whole.induce S into that tree.

**Result:** For genuinely closed unary mixed tests, the
rank-(m+1) strict completion follows from the WEAKER
closed-only rank-m control predecessor. No globally
protected A-mark, no arbitrary weak-test predecessor,
no artificial closure hull, and no unproved relative
TARGET root oracle are required.

## 4. Adversarial checks and scope

1. **Weak S remains open.** If unary F(a)=b but a∈S,
   b∉S, the image p[S] need not be closed even for a
   FULL unary homomorphism. The closed-only predecessor
   cannot supply a protected control-side witness.
2. **Higher arity remains open.** A binary cross-copy
   input can be source-undefined but control-defined.
   Unary EHN-to-FULL is specifically used to guarantee
   projected side-image closedness.
3. **B irreducible and A irreducible:** We keep the
   technical irreducibility hypotheses of the existing
   ambient-A-copy history gluing and EHN pullback;
   no false assumption is dropped.
4. **Target FULL roots:** The actual weak source-side
   roots need not be function-closed. Only the two
   protected TARGET full A-copy embeddings are freely
   glued, exactly as in the previously checked lemma.
5. **The K2 parity and arbitrary-stage C5 obstructions**
   do not refute this statement: the protected marks
   are extracted only for the particular CLOSED side
   images, and the strict rank-m predecessor is explicit.
6. **No global n-pass claim:** This proves the genuine
   mixed binary attachment case. A complete unary
   Picture pass must also certify the initial stage,
   pure copied-old tests, pure native Hales–Jewett
   core tests, and the attachment-list composition
   of all projected A-copy histories. The power
   transfer is being validated separately in #422.
7. **Set-valued function outputs remain transversal**
   throughout native stages. We never replace
   multivalued fibres by singleton relational graphs.
8. **No weakening of the original projection semantics.**
   The EHN map is used globally, full only after
   invoking the proved unary theorem. Undefined
   inputs are not silently reflected in higher arities.

## Lean acceptance

Formalize the cardinal bound as a reusable helper,
refactor the existing #415 successor to use it, derive
both actual closed projected side Finsets for unary EHN,
take two protected witnesses from \`AtMostClosed\`,
and invoke the previously verified exact projected-side
target gluing of #421. Prove both the strict WEAK and
full CLOSED unary output variants, with named axiom
audits and full CI. Replace the body of the old #419
unary strict mixed theorem by this new theorem plus
the \`AtMost.toClosed\` weakening, keeping its exported
statement stable.

The frozen published survey text remains unchanged.
