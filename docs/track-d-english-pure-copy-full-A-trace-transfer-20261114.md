# Track D — English-first exact pure-copy ambient-A trace transfer

**14 November 2026.** Separate proof-development note for the native
functional Appendix A construction. The numbered survey and Sofia's
previously removed TODOs remain unchanged.

## 1. Exact pure-side target-mark transfer

Let `i:Old↪Whole` be a FULL function-language embedding,
`S⊆Whole` an arbitrary LITERAL weak tested vertex set, and
`S_O=i⁻¹[S]`. Let `T` be a strict full-functional B-tree target.

Suppose `f_O:S_O→T` has the genuine
`SetAmbientACopyIntersections(A,Old,T,S_O,f_O)` property.
Let `f:S→T` be ANY already constructed exact weak-test map
agreeing with `f_O` along `i`:

    f(i(x)) = f_O(x)    for each x∈S_O.

The SOURCE lifting hypothesis is:

> For EVERY genuine FULL embedding `gamma:A↪Whole` there exists
> a genuine FULL embedding `gamma_O:A↪Old` such that, for every
> a∈A whose image gamma(a) is actually in S,
> `i(gamma_O(a))=gamma(a)`.

**Then `f` preserves all ambient full A-copy intersections in
Whole.** Proof: for each gamma choose gamma_O, apply the old
copy-intersection certificate to gamma_O to get a full target
A-embedding, then use the displayed equalities at precisely
the tested vertices. The old target copy is already contained
in an irreducible B-constituent, so no new target gluing is
needed. No `S`-closure, extension of a weak partial source
embedding, global retraction, or injectivity of a part map is used.

This theorem is only about the A-copy *certificate*. It does
not pretend to construct the ambient-relative weak homomorphism
`f`; that is a separate pure-side weak-set transport task.
In particular its assumptions are not circular with the
general native strict B-tree target-existence question.

## 2. Reduce lifting across one ACTUAL full free cut

Suppose `Whole = Left *_Root Right` is a genuine FULL native
functional source free amalgam, with source embeddings `iL,iR`,
and A is irreducible.

To produce the above lifting property on a PURE RIGHT test
`S⊆iR[Right]`, it suffices to show the **cross-copy trace
condition**:

> For every genuine FULL `gamma_L:A↪Left` there is a genuine
> FULL `gamma_R:A↪Right` such that
> `iR(gamma_R(a))=iL(gamma_L(a))`
> whenever `iL(gamma_L(a))∈S`.

**Proof.** By irreducibility, every full ambient A-copy in the
free amalgam factors through either the Left or Right source
embedding. If it is already in Right, use its full
factorization. If it lies in Left, use the cross-copy trace
condition. The equalities follow from the full factorization
and require no source/root closure of S. Combining with §1
transfers any already constructed pure-right target
A-copy certificate to the whole native attachment.

This cleanly isolates the previously hidden pure-case
hypothesis: **full A-copies from the opposite side must admit
full lifts into the pure tested side, at least on the tested
intersection**. A merely injective canonical part map,
an EHN chart only for each irreducible input hull, or
agreement of local embeddings on overlaps does not imply
this property.

## 3. Application and remaining hard case

For ONE genuine Hales–Jewett line attachment to the full
coordinate power, the verified parameter-coordinate EHN
retraction and the now merged #652 irreducible line trace
lift yield precisely the needed cross-copy lifts.
The independently merged #656 gives the stronger direct
single-line whole-stage invariance.

For an ARBITRARY ORDERED family of lines, an ambient A-copy
can sit in an earlier attached Old copy and meet the later
line through a proper partial A-trace. The 2-line overlap
dichotomy says the overlap is either a closed agreement root
or contained in one A-letter copy, but it does NOT guarantee
that a specified full source A-copy's **index map** extends
to a full A-copy of the next Old stage. Multiple pairwise
intersections can occupy different A-letter words.

That is the genuine unsolved cross-copy trace condition,
rather than a missing free-amalgam target-gluing constructor.
The absolute colliding-root completion (#635/#637/#638)
and history-free mixed weak step (#640–#643) are validated;
they do not supply this pure-copy condition.

The class-preserving relational iteration and the original
2019 two-pass closure-profile route remain independently
validated; the optional unrestricted native strict functional
n-pass theorem has NOT been deduced.

## 4. Formal verification

Implement two additive source-independent named Lean theorems:

* `SetAmbientACopyIntersections.pureSide_of_fullTraceLift`:
  transfers target A-copy certificates through a full source
  embedding if full ambient A-copies admit full lifts on S.
* `IsFreeAmalgam.pureRight_fullTraceLift_of_crossSide`:
  reduces the full-lift condition for a pure right test to the
  explicit full cross-side A-trace condition using actual
  full-functional source free-amalgam irreducible localization.

Include named `#print axioms` checks. Do not change the
frozen manuscript; do not green-mark a complete n-pass theorem.
