# All-arity functional mixed successor from two CLOSED projected side images

**18 October 2026 — English proof, independent adversarial audit before Lean.**

The native iterated Appendix A construction now has:
* a verified recursive full-functional Ramsey control D;
* genuine transversal set-valued-function partite systems;
* a checked strict full-functional closed-control-only predecessor
  \`AtMostClosed(A,Base,D,m)\` (#420);
* a checked conditional strict mixed target glue consuming two
  protected FULL alpha:A↪D control-side witnesses (#421);
* a checked finite exact mixed-side cardinal bound independent of
  the injectivity of the EHN projection (draft #423).

This note isolates a particularly clean ALL-ARITY maximal mixed
rank hypothesis. It does NOT use the unary EHN-to-FULL
domain-reflection shortcut and does NOT enlarge exact weak tests
to a generated closure.

## Theorem (all arities, closed PROJECTED side images)

Let Whole=Left*_{Root}Right be an actual FULL functional free
attachment, with a genuine EHN/original-2019 partial map
p:Whole→D into the previous functional control. Fix a FULL
selected alpha:A↪D containing the projected attaching root,
A irreducible, A↪Base FULL, and Base irreducible. Let m≥0.

Assume D satisfies the WEAKER rank-m
\`AtMostClosed(A,Base,D,m)\` strict B-tree weak-history
predecessor, with arbitrary projected histories and all
actual ambient full A-copy intersections.

Take ANY exact finite weak S⊆Whole with |S|≤m+1.
It need NOT be function-closed. Assume it is genuinely
mixed, i.e. S has a point outside each of the two FULL
source-side embeddings. Define literal projected sides

   I_L = (p∘i_L)[i_L^{-1} S],
   I_R = (p∘i_R)[i_R^{-1} S].

**Additional semantic condition:** I_L and I_R are each
FUNCTION-CLOSED inside D. There is no requirement that
p be a full homomorphism globally, and no requirement
that S itself be closed.

**Conclusion:** S has a STRICT full-functional Base-tree
weak completion with all surviving set-valued output fibres,
actual ambient FULL A-copy intersection certificates and
every requested finite projected-history predicate.

### English proof

First the verified finite mixed-side budget shows

          |I_L|≤m,   |I_R|≤m,

using only injectivity of the source-side embeddings.
For each i∈{L,R}, invoke the weaker \`AtMostClosed\`
predecessor of D on the EXACT closed test I_i.
Because alpha is FULL, the occupied partial A-substructure
alpha^{-1}[I_i] is automatically function-closed.
The verified relative closed-root TARGET extension
\`AtMostClosed.protected_of_closedOccupiedA\` produces a
genuine STRICT B-tree witness on EXACT I_i with a safe FULL
marked alpha(A), including the original projected history
and all actual full A-copy intersections. It does not charge
any newly attached TARGET vertices to the rank budget.

Use the independently checked projected-side mixed gluing
(#421): EHN-pull these two marks back to the actual
source weak side tests i_i^{-1}S, then freely glue the
two STRICT TARGET trees over the FULL target alpha(A)
marks. The source weak root is never used as a full
functional amalgamation map, and no source closure
is generated. This yields the required witness on S.

All of the reasoning works with **arbitrary arities,
nullaries, repeated inputs and multivalued values**;
transversality is retained by the actual native partite
systems. No unary-domain shortcut is used.

## Corollary / relationship to the local phantom criterion

For a genuinely CLOSED source S, each exact source-side
preimage i_i^{-1}S is closed. The separately proved
all-arity local EHN no-phantom criterion (draft #424)
says that if the corresponding source-side projection
reflects target domain nonemptiness ON THOSE tested
input tuples, then I_i is closed in D.
Under that explicit side-local hypothesis the theorem
therefore supplies an ALL-ARITY strict mixed successor
from the closed-only rank-m predecessor.

Unary languages are an important automatic special case:
all EHN maps are FULL there, so no-phantom holds on
every closed side test. Hence the earlier unary theorem
(draft #423) is recovered without repeating the mixed
gluing or cardinal arithmetic.

The projected-image-closed hypothesis is actually
WEAKER than local no-phantom: p[S] may be closed even if
some source-undefined cross-copy tuple projects to a
defined target tuple whose output label happens to
be represented elsewhere in S.

## Independent adversarial audits

1. **Not a universal rank step.** For all-arity EHN
   projections, the projected I_i need not be closed,
   even when S is closed, due to phantom target-defined
   input tuples. The current rank-(m+1) statement
   is explicitly conditional on closure of BOTH I_i.
2. **K2 parity obstruction:** An arbitrary strict-tree
   predecessor cannot be endowed with a fixed protected
   alpha-mark on every NONCLOSED projected side.
   We require I_i closed and construct the fresh target
   marks only under this legitimate functional root.
3. **Arbitrary-stage C5:** Independent arbitrary
   projected side completions need not glue over one
   target root. Our two side witnesses carry safe FULL
   alpha marks with the SAME alpha and requested
   histories, and the checked gluing theorem is invoked.
4. **No source test closure:** Weak S may omit actual
   output values. That does not invalidate the two
   GIVEN closed projected image sets, nor the verified
   ambient-relative EHN source-defined weak pullback.
5. **No total-fibre projection:** The EHN projection
   need not reflect undefined source operations
   outside the tested/projected image closure condition.
6. **Rank preservation:** Cardinality is calculated
   ONLY on literal finite vertex sets S, I_L, I_R,
   never on a generated closure hull.
7. **Source maps versus target maps:** Only genuine
   FULL attaching embeddings and FULL protected TARGET
   A-marks are used for functional free amalgamation.
   The partial source weak root is not illegitimately
   treated as a FULL functional substructure.

## Lean acceptance

Create a reusable all-arity theorem
\`IsFreeAmalgam.weakTree_of_closedProjected_alpha_mixed_succ\`
using exactly the numeric budget helper, two
\`AtMostClosed.protected_of_closedOccupiedA\` witnesses,
and \`weakTree_of_protected_projected_side_witnesses\`.
No copied construction of the target amalgam.

Refactor the existing closed unary mixed successor
(#423) to first derive closure of the two literal
projected side images using unary EHN-to-FULL and
full homomorphic closed-image transport, and THEN
invoke the new all-arity theorem. Keep both the
old strong-predecessor unary public API and the
weaker closed-only unary public API stable.

Only these explicitly scoped theorems should receive
green validation markers after fresh CI; the global
native function-language n-pass strict sparsening
still requires handling the remaining NONCLOSED
projected images and genuine Hales–Jewett history
compatibility of target root profiles.
