# Track D — English-first bare weak-functional EHN transfer (15 November 2026)

The frozen Nešetřil-programme survey is not edited. This is a
standalone helper for the *weaker* strict full-functional B-tree
invariant developed in Track D.

## Claim 1: exact EHN pullback, no A-copy hypotheses

Let C,D be genuine full relation/set-valued-function structures,
q:C→D an EHN projection (weak globally, full on every genuine
full irreducible source copy). Suppose every literal weak set
I⊆D of at most n vertices has a strict full-functional Base-tree
T and an ambient-relative weak HE g:I→T:

    AtMostBare(Base,D,n).

Then AtMostBare(Base,C,n) holds, without any separate irreducible
ambient A, target part map, or projected history.

Fix the ORIGINAL finite source test S⊆C of ≤n vertices. Take the
literal target image I=q[S], not its closure, so |I|≤|S|≤n.
Choose the strict target T and map g:I→T from AtMostBare(D,n).
The already proved and axiom-checked lemma
`IsAmbientRelativeWeakHE.pullback_ehn_exact`
gives a genuine map g∘q:S→T with the ambient-relative weak
property for all set-valued output fibres. In particular:
positive function incidences are preserved even for truncated
weak input fibres; complete nonempty ambient source fibres
are mapped exactly when all their outputs remain in S; and
each full irreducible ambient source copy whose entire image
lies inside S has a full target embedding.
No reflection of source-undefined function domains is used.
The target is still the strict Base-tree T. This proves the claim.

## Claim 2: bare initial tree and one-copy EHN power

Any structure C which itself is a strict full-functional
Base-tree has AtMostBare(Base,C,n) for every n, by restricting
the identity full embedding on each exact weak S. No auxiliary
A or assumption on the original control part map is needed.

If q:C→Base is EHN, choose a one-copy strict tree Base
and use Claim 1. Hence every EHN one-copy HJ power core
with a composable full A↪Base embedding has the bare
strict weak-tree property at every finite rank.

This is a simplification of the previously checked stronger
history-free one-copy lemma #643: the BARE invariant
needs no ambient A-copy intersection certificates.

## Precise limitation

The bare EHN pullback has no external A-trace marks.
It does not imply the full `AtMostNoHistory` invariant,
a global common-parameter retraction for arbitrary
HJ lines, or a strict full-function B-tree completion
of every mixed test WITHOUT the enlarged rank budget.
The latter still uses finite trace restoration #671
and the quantitative rank step #683. The control's
rank F_A(m)=m+|A|(m+1)^|A| must be provided
noncircularly; a Ramsey arrow alone does not provide it.

## Lean obligations

Formalize:
* `AtMostBare.pullback_ehn`, by finite image counting
  and the previously checked exact EHN weak pullback;
* `AtMostBare.of_strictTree`, using identity weak
  restriction;
* `AtMostBare.of_ehn_oneCopy`, using the previous two.

Add three named `#print axioms` tests and verify
the full exact-head Lean/source/allowed-axiom gates.
Do not change the numbered survey or re-add removed TODOs.
