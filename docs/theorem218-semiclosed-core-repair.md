# Closed-test repair: semi-closed cores inside conflicting little pictures

Continuation of merged PR #184. The literal published predicates and frozen
manuscript are unchanged. All protection assertions use the explicitly
named CLOSED-test convention. The higher-rank increment remains open.

## Why the rank shortcut was not used

Replacing generating rank by the number of vertices of an exact weak test
makes the two proper source sides smaller. It does not ensure that their
projected targets contain the SAME CLOSED boundary Q needed for independent
completion gluing. Adding that boundary's hull has an uncontrolled cost.
Thus this change alone is not a proof of the rank increment. No new
rank-increment theorem is asserted in this patch.

The positive progress below addresses the other remaining construction
obligation: the recursive initial repair over a nonclosed control, where
the selected support in a closed old picture may itself be nonclosed.

## 1. Protected powers of exact nonclosed restrictions

Let p:B->D protect closed U-irreducible tests, with B closed. Let alpha:A->D
be a full induced embedding, and R the EXACT restriction of B to the parts
in alpha[A]. The restriction R need not be closed, and neither A nor D is
assumed closed in this assertion.

For every N there is a native partite embedding, after relabelling,

    power(R,N) -> power(B,N),

which sends the tag q to alpha(q) and forgets the subtype proof in each
coordinate. Injectivity and relation reflection are coordinatewise.
For N>0, the full power's projection is protected by #181. Restrict this
map along the displayed embedding and factor each protected test embedding
through alpha. This proves that power(R,N)->A is protected, WITHOUT
applying the closed-base theorem directly to the nonclosed R.

Separately, positive powers of a semi-closed system are semi-closed:
coordinate roots are valid, and any two closure tuples with the same roots
agree at every coordinate. One coordinate also identifies their tags.
There is no assertion that missing outputs have become defined.

## 2. Native lines are relatively closed

Let R be semi-closed and ordinarily A-partite. Every canonical Hales--Jewett
line embedding R->power(R,N) has relatively U-closed range. To prove this,
take a closure tuple whose root belongs to the line, and choose a variable
coordinate k0. Its tuple y at k0 is an existing closure tuple in R.

At every other variable coordinate, partial uniqueness forces the same
coordinate tuple y. At a constant coordinate carrying a letter e, the
projection of y is a positive closure tuple in A, so its letter image
is a tuple in R. It has the same roots as the given coordinate tuple;
partial uniqueness therefore identifies them. The entire tuple is the
line image of y, including every output position.

The finite Ramsey lemma is proved with these EXACT line embeddings in its
conclusion. It is not silently changed to arbitrary partite embeddings,
whose relative closedness has not been established.

## 3. Safe core tuples in an attachment which may have conflicts

Let Base and Core be semi-closed, S an arbitrary induced support in Base,
and m_i:Base|S->Core full embeddings with relatively closed ranges in Core.
Form the ACTUAL Attachment.attach. The support S need not be relatively
closed in Base. Consequently the whole attachment can have multiple
closure outputs above one root; it is NOT asserted semi-closed.

**Core-tuple lemma.** If a closure root has a tuple already in Core, that
same tuple is its only closure tuple in the whole attachment.

If another tuple comes from Core, use Core's partial uniqueness. If it
comes from copy i, its root vertices belong to m_i[S]. Relative closedness
of m_i[S] forces the entire core tuple to lie in that image. Pull it back
to S. It is a Base tuple over the same root as the competing copy tuple,
so Base's partial uniqueness identifies the two. Therefore the supposedly
competing tuple was the core tuple all along.

This argument does not assume a closed common root, a closed support,
a globally semi-closed attachment, or a bound on the number of copies.

**Closed-core-test corollary.** Every closed Test embedded entirely in
Core has relatively closed range in the whole attachment. All closure
tuples in the whole still have valid prescribed roots, by validity in the
piece supplying the tuple. A tuple rooted in Test therefore gives a root
embedding in Test. Closedness of Test supplies a core tuple; the preceding
lemma forces every competing tuple to equal it and remain in Test.

## 4. Selected-profile copies satisfy the required relative condition

Suppose S is exactly p^{-1}(J), where J is the selected set of part labels,
and use the usual folded labels on the attachment. Every embedded Test
whose vertices all have labels in J lies in Core: every exterior copy
vertex comes from Base outside S and therefore has a label outside J.

If Test is closed, the corollary above proves that its range is a relative
U-substructure of the whole little picture. The native specialization
uses the semi-closed restricted power as Core and the canonical line
embeddings as m_i. All its premises are established by the preceding
power and line theorems. In particular no closed-support or closed-control
assumption has reappeared in the specialization.

This proves the structural selected-profile assertion needed before the
recursive application of the repaired relative-copy theorem. The formal
transport to the language with named parts and the complete recursive
colour extraction are NOT part of this patch. Do not declare the
unrestricted Lemma 2.28 or Theorem 2.18 finished from this local assertion.

## Finite regression with genuine conflicts

The executable conversation artifact check_semiclosed_core.py uses unary
P, binary closure R and a true nullary relation. Base has vertices 0..5,
P={0,2}, and R={(0,1),(2,3)}. Its labels are

    0:r, 1:o, 2:r, 3:u, 4:f, 5:f.

The control has P={r} and conflicting tuples (r,o),(r,u). The selected
closed A uses labels {r,o,f}. Thus the exact old support omits vertex 3,
leaving the root 2 without its output. Two letters choose free vertex 4
or 5. The checker constructs ALL native lines and their actual attachment.

Exponent | Core vertices | Lines | Whole vertices | Conflicting roots | Closed core tests | Selected A-copies | Two-colourings
--- | ---: | ---: | ---: | ---: | ---: | ---: | ---:
1 | 5 | 1 | 6 | 0 | 12 | 2 | not tested
2 | 9 | 5 | 14 | 2 | 48 | 4 | 16
3 | 17 | 19 | 36 | 6 | 768 | 8 | 256

Every checked native line range is relatively closed. Every checked closed
core test and selected-profile A-copy remains relatively closed in the
whole attachment. Every tested two-colouring has a monochromatic native
old-copy line. The N=2 and N=3 whole attachments really fail semi-closedness;
this is not merely a conditional example assuming such a failure.
These are computational regressions, not additional Lean model certificates.

## Formal declarations and validation

Three modules, ten individually audited declarations (nine theorems and
one embedding construction):

* ClosureWeakRestrictionPower: restrictedPowerEmbedding,
  restricted_power_part_protected, power_isUSemiClosed.
* ClosureSemiClosedLines: line_range_isUSubstructure_of_semiClosed,
  semiClosed_partiteLemma_lines.
* ClosureSemiClosedAttachment: closureTuple_rootMatches,
  closureTuple_eq_core_of_core_witness,
  closed_core_test_range_isUSubstructure,
  closed_profile_range_isUSubstructure,
  closed_profile_in_native_line_attachment.

All previous audit lines are retained in their original order. The final
full-project build and permitted-axiom audit are recorded on PR #185; source
existence and earlier partial builds are not certification. Direct semantic
review checked exact supports, relative versus intrinsic closure, the line
family, source/target maps, and the difference between safe core roots and
global partial uniqueness. No separate independent referee process is claimed.

## Suggested local manuscript wording, not applied to frozen source

Use only the canonical line copies in the little picture. Their ranges in
the semi-closed core are U-substructures. If a closure tuple is already
present in the core, any tuple from an attached copy over the same root
coincides with it: the core tuple pulls back to the attaching support,
and uniqueness in the old picture identifies the tuples. Every U-closed
copy of the selected profile lies in the core and is consequently a
U-substructure of the whole little picture, even though the latter may
have conflicting closures elsewhere.

Keep the subsequent named-part transport and recursive Ramsey application
explicit. The higher-rank/boundary construction is an independent remaining
obligation; the safe-root lemma does not prove it.
