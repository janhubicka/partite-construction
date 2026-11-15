# Track D — English proof FIRST: entire finite Hales–Jewett Picture with BARE strict functional rank

**14 November 2026.** Stacked on native one-attachment PR #685.
Frozen numbered Nešetřil programme survey text remains unchanged;
previously removed author TODOs are not restored.

## Conditional finite Picture Lemma

Fix a finite full relation/set-valued-function language,
a hereditary free-amalgamation class K, a finite FULL irreducible
test A in K, a finite irreducible full target Base, and a full
embedding e:A↪Base. Fix a finite control D and a
Stage K D called Old, with arbitrary true EHN part projection.

For n=m+1, assume:
1. the genuine old picture has
   `AtMostBare(Base,Old.toStructure,n)`;
2. the control D has
   `AtMostBare(Base,D,F_A(m))`,
   where F_A(m)=m+|A|(m+1)^|A|;
3. the original class/Ramsey hypotheses of the already
   verified native functional `pictureLemma_lines_preservingSupport`.

**Claim.** For any finite number of colours, there exists
a genuine native functional Stage K D called New satisfying
both the usual `PictureProperty(A,Old,New,alpha,kappa)`
and `AtMostBare(Base,New.toStructure,n)`.

The family is the COMPLETE finite set of true Hales–Jewett
LINE embeddings supplied by the verified functional
partite lemma; no restricted common-parameter-coordinate
family is used.

## Complete proof

Invoke the checked
`EHN.pictureLemma_lines_preservingSupport` with the
stage predicate

    Q(T) := AtMostBare(Base,T.toStructure,m+1).

That theorem already constructs the real coordinatewise
set-valued function power, its genuine EHN partite
projection to selected A, the true FULL attaching maps
indexed by the finite genuine HJ lines, all class
membership/free-amalgamation data, and the ordinary
Hales–Jewett PictureProperty.

Only its hCore and hAttach obligations remain:

**Core:** for any HJ power length N>0, the verified
`power_weaklyPartiteOver` gives an EHN map from the
whole genuine power structure to the selected A. The
FULL embedding A↪Base yields a one-copy strict Base
tree witness of EVERY exact weak subset via the checked
`of_ehn_oneCopy_noHistory` theorem (#643).
Forget the external A-copy marks and empty projected
history. The relabelled core differs only in its part
map, not its full structure. Hence Q holds at EVERY
rank n, with truly multivalued transversal output
fibres and no source weak-set closure.

**Attachment:** for ANY intermediate Stage T with Q(T)
and ANY full partite embedding of Old's true closed
selected support into T, the checked native
`UnitAttachD_bareRank_of_controlBudget` (PR #685)
applies. Its full source sides are the OLD picture
(with Q(Old)) and the current core T (with Q(T));
its fixed control is D with the explicitly paid
larger bare F_A(m) bound. Thus Q(T.attach) holds.
There is NO hypothesis that the attaching line
shares a parameter coordinate with any other line,
and NO partial-A trace lemma is needed in Q.

The existing checked `attachAll_preserving` API
then proves Q for all successive genuine HJ line
attachments. Its colouring argument gives the
PictureProperty simultaneously. This proves
the conditional finite Picture lemma.

## Adversarial boundary: what this does and does not solve

This would close the *internal* multi-line coherence
problem for the deliberately WEAKER BARE invariant
at a quantitative CONTROL price. It is much
stronger than separate one-line EHN retractions,
because no global retraction of the full HJ
multi-line Picture is used or required.

But it is NOT an unconditional native strict
functional n-pass theorem:

* An arbitrary Ramsey-arrow control D has NOT
  been proved to have the BARE budget F_A(m).
  Merely assuming D's weaker rank-m tree
  locality and restoring A traces would be
  circular. The control D must be selected
  by a separately verified **noncircular
  rank-budget schedule**.
* A strict initial Stage representing all
  Base placements with nullary functions
  needs a checked FULL native tree argument;
  the existing positive-arity initial tree
  is verified, but do not automatically claim
  the nullary case from it.
* The outer iterated Ramsey-arrow bridge,
  final full B-copy coverage, all genuine
  original-2019 source-defined partial
  function projection clauses and final
  structure-class membership must be
  transported through the new rank-scheduled
  Picture, not inferred from bare locality.

The verified 2019 two-pass closure-profile
proof already provides an alternative route
to the corrected printed theorem without
this optional native strict-tree intermediate.

## Lean gate

Use the exact checked
`pictureLemma_lines_preservingSupport`,
and prove a new named theorem
`EHN.pictureLemma_lines_preservingBareRank_of_controlBudget`.
No new finite Ramsey argument should be copied.
One additive module and named `#print axioms`
check; keep DRAFT until all parents and exact
full Lean/axiom checks are green.
