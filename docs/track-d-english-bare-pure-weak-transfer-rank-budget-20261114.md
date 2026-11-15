# Track D — English proof FIRST: pure-side bare weak-tree transport for full functional attachments

**14 November 2026.** This proof is the missing pure-side interface for a
prospective *bare* strict functional B-tree induction. The numbered survey
and author-removed TODOs remain unchanged.

## Lemma: full source-side image transports a bare ambient-relative weak witness

Let (j:L\hookrightarrow C) be a FULL embedding of genuine
relation/set-valued-function structures, and let a literal weak test
(S\subseteq C) be entirely contained in (j[L]).
Put (S_L=j^{-1}[S]). Suppose the FULL source L has an
ambient-relative weak homomorphism-embedding
(g:S_L\to T) into a genuine strict B-tree (T).

**Claim:** On the *same target* T, there is an ambient-relative weak
homomorphism-embedding (f:S\to T), without taking any closure or enlarging
the tested source set. This carries ALL genuinely multivalued function
fibres satisfying the ambient-relative law and ALL full irreducible
ambient source tests whose vertices lie in S.

### Full English proof

The restriction of a FULL functional embedding j induces a FULL
embedding of weak structures

    j_S : L|^w S_L  -->  C|^w S.

Because S is entirely contained in the range of j, this is
surjective and hence an isomorphism of the weakly induced
function structures. Let k be its FULL inverse. Put (f=g\circ k).

The weak positive-relation/function preservation follows by
composing g's weak homomorphism with the FULL k.

For the *ambient-relative complete fibre law*, take an input tuple
x in S with a nonempty ambient C-fibre C.F(x) entirely contained
in S. Since j is FULL, every input x_i comes from the unique
k(x_i) in L and the ENTIRE ambient C-fibre is exactly the
j-image of L.F(kx). It follows:

* L.F(kx) is nonempty;
* every element of L.F(kx) lies in S_L;
* k maps the complete weak C fibre bijectively onto the complete
  weak L fibre.

Apply the ambient-relative whole-fibre equation of g at kx,
then transport along the FULL weak inverse k. Thus

    f[C.F(x)]=T.F(fx).

No reflection of source-undefined inputs is asserted.

Finally, if `e:E↪C` is a genuine FULL irreducible ambient
source embedding with image entirely in S, its image lies
inside j[L]. Cancel FULL j to obtain a FULL embedding
`e_L:E↪L`. Apply g's ambient irreducible-test condition
to e_L, then note that k(e(x))=e_L(x) at every vertex x.
This gives the required FULL target copy.

**Importantly**, this result does NOT give full A-copy
intersection certificates for ambient copies that meet S
only PARTIALLY; those are deliberately absent from the bare
invariant. It proves pure-copy and pure-core transfer for
BARE local strict trees without the cross-A partial-trace
hypothesis of PRs #664/#668.

## Finite-cardinality corollary

Let L and C have finite carriers, let (S\subseteq C)
be any finite pure-side tested subset, and let
`AtMostBare(Base,L,n)` hold. The set (S_L=j^{-1}[S])
has cardinality at most |S| by injectivity of j.
Request the bare witness of L on the literal (S_L),
then transfer it along j as above. This yields a bare
strict functional B-tree witness on S at the same bound n.

## Targeted iteration strategy

The verified finite-trace restoration theorem #671 states

    AtMostBare(Base,D,F_A(m))
        => AtMostNoHistory(A,Base,D,id,m),

where (F_A(m)=m+|A|(m+1)^{|A|}).

The already merged mixed exact weak successor #642 consumes
`AtMostNoHistory m` on D and yields a strict
ambient-relative weak target for each genuinely mixed S
with |S|≤m+1.

Hence, **conditional on the newly proved pure-side transport**,
a full native one-copy attachment C=Old*_Root Core has
`AtMostBare(Base,C,m+1)` whenever:

* Old has AtMostBare(Base,Old,m+1);
* Core has AtMostBare(Base,Core,m+1);
* D has AtMostBare(Base,D,F_A(m));
* the true global C→D EHN part map and selected A↪D
  containing the common root are present;
* A is irreducible and Base is irreducible so a full
  A↪Base one-copy power target exists.

For a PURE S, use this lemma on its full source side.
For MIXED S, restore the D-marked predecessor with #671
and apply #642, then forget its A-copy marks.
No pure-copy A-trace lifting is needed in the BARE output.

This could be iterated over every genuine full Hales–Jewett
line attachment using the existing class-preserving
`Stage.attachList_preserving`, provided the control's larger
bare bound is supplied. **This larger bound is a real
hypothesis**: the old rank-m→m+1 induction does NOT
automatically satisfy it.

## Adversarial noncircularity audit

The statement does not itself produce a control D with
the necessary (F_A(m))-vertex bare bound or give the final
Ramsey-arrow/class/final-B-coverage bridge. It may allow
reverse rank scheduling or an outer closure-profile pass,
but until those dependencies are constructed the optional
native strict n-pass theorem remains open.

No unqualified pure-side A-mark transfer is claimed:
the verified three-line HJ C7 shows why unrestricted
strict K2-tree locality cannot survive *arbitrary*
line attachments from only old-stage locality. That
example's control K3 fails high-rank B-tree
predecessor conditions. Thus it neither proves nor
refutes the proposed **stronger control-rank** route.

## Validation order

1. Prove `IsAmbientRelativeWeakHE.of_full_pure_side` for
   a literal weak S contained in the FULL side range.
2. Prove `AtMostBare.pure_side_of_full_embedding`
   with the exact finite cardinality bound.
3. Then combine with the merged mixed/restoration theorems
   into one binary attachment `AtMostBare` successor.
4. Only then attempt finite HJ list integration.

All Lean endpoints require exact-head full build and
`#print axioms`. The frozen survey is not edited.
