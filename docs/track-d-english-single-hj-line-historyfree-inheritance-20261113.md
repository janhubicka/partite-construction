# Track D — English proof FIRST: a genuine single Hales–Jewett line inherits the entire no-history invariant

**13 November 2026.** The numbered Nešetřil programme survey Appendix A
is frozen, and previously removed author TODOs remain untouched.

## Theorem

Let Old be a genuine finite full relation/set-valued-function
partite system over D with an EHN part map, let alpha:A↪D
be a full selected A-placement, and let W be ONE actual
Hales–Jewett line of the coordinatewise functional power
of R=Old.weakRestrict(D,alpha), with parameter coordinate i.

Write New for the full native one-copy attachment of Old
along the FULL line embedding W into the selected power core.
Assume A is irreducible and Old has the strict history-free
ambient-relative functional weak-tree invariant at rank n:

    AtMostNoHistory(A,Base,Old,Old.part,n).

Then the WHOLE NEW attached stage, including pure core,
pure copied-old and genuinely mixed weak tests, also satisfies

    AtMostNoHistory(A,Base,New,New.part,n).

No predecessor rank (n-1), root injectivity, partial A-trace
extension hypothesis, or full function-domain reflection
is assumed. The source weak vertex set remains exact.

## Complete proof

The already kernel-checked
`EHN.lineUnitAttachment_EHN_retraction` constructs the
literal full support line embedding f and a GLOBAL EHN
retraction

    q:New→Old

which fixes the attached Old copy vertexwise, evaluates
the chosen parameter coordinate on the HJ power core,
and preserves every original control part.

Our new `AtMostNoHistory.pullback_ehn` theorem (PR #648)
proves that the weak strict functional tree invariant with
EMPTY projected history transfers along ANY EHN map,
using only the exact finite image bound

    |q[S]|≤|S|≤n

and the original full irreducible A-copy preservation
clause of the EHN map. This theorem does not require
an independent full ambient A-copy trace extraction:
it gets the required target full A embedding by first
lifting each genuine A-copy of NEW along q to an actual
full A-copy in OLD.

Apply this pullback theorem to q with the Old invariant.
The result is the asserted rank-n NEW invariant for
every literal weak vertex subset, including those
wholly inside the copied Old picture.

This is stronger than merely invoking the separate mixed
rank-successor lemma on mixed tests, but works only for
one chosen line parameter coordinate.

## Exact obstruction to the whole finite HJ Picture

If a second HJ line W' has a DIFFERENT parameter coordinate,
the previous retraction q:New→Old need not fix W' on its
entire closed support. Consequently
`unitAttach_extend_partPreserving_EHN_retraction`
cannot be invoked with this q without the extra equality
`q(f_{W'}(x))=x` on EVERY selected support vertex.

The verified `EHNCommonParameterLineFamily` gives a
positive family extension when all lines SHARE one
parameter coordinate; the verified colour-at-coordinate
obstruction proves that restricting to such a family
does NOT supply the Ramsey Picture lemma for a
nontrivial letter alphabet.

Therefore the theorem proves an entire single-line
history-free native functional step, not an arbitrary
multi-line Hales–Jewett Picture pass or the optional
unrestricted native n-pass strict-functional sparsening.

The full corrected 2019 two-pass closure-profile proof
of the survey theorem remains separately validated.

## Lean gate

Use only the checked actual single-line retraction
and the small-image EHN no-history pullback from PR #648.
One additive named theorem and root `#print axioms` check;
full exact-head build and standard-axiom inventory required.
