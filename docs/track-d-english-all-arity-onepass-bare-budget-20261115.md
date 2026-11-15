# Track D — English first: complete all-arity native Ramsey pass with explicit bare control budget

15 November 2026. Standalone follow-up stacked on native finite HJ-line bare Picture candidate #687 (itself stacked on #685). This note precedes the proposed Lean theorem. The numbered Twenty Years survey is frozen: no mathematical prose, existing validation markers or author-deleted TODOs are changed.

## Statement, including actual quantifiers

Let K be a genuine hereditary free-amalgamation class of finite structures over a relation/set-valued-function language L of arbitrary arities **including nullaries**. Let A, Base be finite *full* structures in K, both irreducible, and fix a full embedding e:A -> Base. Let D be an arbitrary finite full structure, and let κ be a finite nonempty colour type. Assume the **actual full functional Ramsey arrow** D -> (Base)^A_κ. Set

  F_A(m) = m + |A|(m+1)^|A|.

For an integer m >= 0, assume separately

  AtMostBare(Base,D,F_A(m)).

Then there exists a genuine finite native EHN partite Stage T over D, with class membership K(T), such that simultaneously:

  1. AtMostBare(Base,T.toStructure,m+1) holds on every *literal weak* finite vertex test S of size <=m+1, with a genuine strict full-functional Base-tree target and ambient-relative weak HE;
  2. the ordinary full-function Ramsey arrow T -> (Base)^A_κ holds;
  3. T carries the genuine EHN part projection to D.

There is **no PositiveFuncArity hypothesis**. Source and target functions may be multivalued with transverse output fibres, and nullary function roots are the genuine canonical full nullary roots.

## Proof

Invoke the already checked `EHN.inducedConstruction_preserving` with stage predicate

  Q(T) := AtMostBare(Base,T.toStructure,m+1).

Its two hypotheses have now been isolated in earlier Track D work:

**Initial stage.** For each full Base-placement β0:Base↪D, apply the checked all-arity strict initial-tree theorem `EHN.initial_allArity_tree` (merged #690). This produces a *single actual* EHN Stage S over D that is itself a strict full-functional TreeAmalgam of Base-copies, retains K membership, and represents *every* full Base-placement into D. For every exact weak vertex test R⊆S, restrict the identity full embedding S↪S to R. This is an ambient-relative weak HE into the same strict Base-tree S, so Q(S) holds, without asking anything of the control's local structure. This step does not require an empty nullary root.

**Picture step.** For every current EHN Stage Old with Q(Old) and every full α:A↪D, apply the *conditional* native finite HJ-line Picture theorem `EHN.pictureLemma_lines_preservingBareRank_of_controlBudget` (candidate #687). It returns New with Q(New) and the actual `PictureProperty A Old New α κ`. Its hypotheses are met: Old has rank m+1, the fixed D has the explicit rank F_A(m), and A is irreducible with full embedding into Base. The complete set of HJ lines is allowed. No common coordinate, history, closure-inflated weak source set or total-fibre surjectivity is introduced.

The generic canonicalization and backward-colouring argument in `inducedConstruction_preserving` now constructs the final T with Q(T) and the full Ramsey arrow. This is a **single complete native Ramsey pass**, not just one HJ attachment, and class membership/EHN projection are inherited from `Stage K D`.

## Critical adversarial nonclaims

The input D is assumed to have **both** a Ramsey arrow and bare rank F_A(m). This is a substantial joint hypothesis. The result cannot be used to assert an unconditional strict n-pass sparsening theorem, because a forward step from an arbitrary rank-m Ramsey control to rank-(m+1) would require its rank to be F_A(m), generally larger than m.

The previous graph-tree n-pass induction used the already established predecessor rank m; it does **not** provide F_A(m). Nor does the tree-like initial Stage above automatically carry the Ramsey arrow before the induced canonicalization. A proposed reverse finite schedule only works **conditional on obtaining its initial Ramsey control at the larger prebudgeted rank**; it does not construct that control.

Separately remain: a noncircular input-control selection or stronger invariant that eliminates this budget, final irreducible Base-copy coverage if required, the exact passage through the original 2019 partial-function convention for the *global* projection (Stage EHN gives this through existing semantics), and the author's printed theorem contract. The existing corrected two-pass closure-profile route remains independent of this optional stronger native strict-tree development.

## Acceptance

Add exactly one theorem `EHN.inducedConstruction_allArity_bareRank_of_controlBudget` and one direct named root `#print axioms` check. Require exact-head full Lean compilation, standard logical axioms only, and source/no-admission checks before integration. Keep both this PR and its predecessors draft until those gates pass.
