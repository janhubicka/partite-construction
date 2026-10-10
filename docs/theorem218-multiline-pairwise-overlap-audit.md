# Hales--Jewett multi-line audit: pairwise word boundaries do not unify

10 October 2026. Independent small adversarial regression for the
remaining higher-rank j-to-j+1 step in the repaired Lemma 2.30.
This is a construction-strategy check, not a counterexample to
the theorem or to the proved pairwise overlap lemma #207.

## Genuine two-coordinate induced partite power

A is the two-vertex edge with parts 0 and 1. B is the disjoint union
of TWO copies of A, with vertices (p,i), p,i in {0,1} and an edge
between (0,i) and (1,i) for each i. The part map is (p,i) -> p.
Both e_0:p->(p,0) and e_1:p->(p,1) are full induced
part-preserving embeddings of A into B.

Work in the actual coordinatewise induced power B^2. The word
image of letters (i,j) is

    Word(i,j) = { ((0,i),(0,j)), ((1,i),(1,j)) }.

Each Word(i,j) is an induced copy of A. Consider native lines

    W0=(parameter,e0),
    W1=(e0,parameter),
    W2=(e1,parameter).

Their native line maps are full induced embeddings B -> B^2.
The parameter-coordinate sets of W0 and W1, and of W0 and W2,
are disjoint. The pairwise intersections satisfy

    range(W0) ∩ range(W1) = Word(0,0),
    range(W0) ∩ range(W2) = Word(1,0).

Thus each pair is contained in ONE A-word copy, exactly as
asserted by the Lean theorem #207.

But the union of these two intersections has four vertices,
two in each part, whereas every individual A-word copy has
exactly two vertices. Hence

    range(W0) ∩ (range(W1) ∪ range(W2))

is **not contained in ANY one canonical A-word copy**.

The standard-library executable regression
`scripts/check_multiline_word_overlap_union.py` independently checks:
full induced edge reflection for e0,e1, all word embeddings,
all three native line embeddings, both disjointness conditions,
the exact two intersections and the failure of one-word coverage
for their union. The finite computation was executed before
recording the script. It has no effect on the Lean kernel.

## Mathematical consequences for the rank increment

The pairwise geometry theorem #207 identifies a real closed A-word
COPY for each pair of transverse lines. It does not identify one
common word A-copy containing a separator against a WHOLE FAMILY
of other active lines. Different pairwise overlaps can lie in
different A-word copies, even in the simplest 2-coordinate example.

This does not prevent the *outer projection* of all selected-profile
vertices into one fixed copy of A in the original control D. That
fact follows from their parts, and the existing closed projected
boundary lemma uses it correctly.

The remaining obstruction is NUMERICAL: a source side generated
OVER its separator by t vertices need not have absolute projected
U-size <=t. The projected separator can require q more generators.
Draft #209's explicit correct criterion is q+t<=j on BOTH sides.
The native construction must show how that budget is met, or
replace the absolute-rank induction by a separately proved
relative-boundary completion invariant.

For the full multi-line history, do NOT deduce from #207 that
the separator sits in a single A-word of the core or that the
closed K-boundary has zero generator cost. Likewise, neither
of these observations refutes corrected Theorem 2.18.

The published manuscript remains frozen. No Lean theorem or axiom
is altered in this computational audit.
