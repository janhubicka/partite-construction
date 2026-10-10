# Minimal U-generators versus completion of their prescribed closed hull

10 October 2026. Adversarial companion to
`ClosureMinimalGeneratorIndependence.lean` (PR #229).

## The correct positive theorem

If `S` is a minimum U-generating vertex set of a finite
relational structure T, then the **exact weak induced**
`T|S` has intrinsic USize equal to `|S|`; hence every
vertex subset of `T|S` is relatively U-closed.

This follows from the previously proved identity that an intrinsic
generator of `T|S` generates the SAME AMBIENT U-closure as S.
A proper smaller weak generator would contradict minimality of S.

This fact applies to any finite U-closed source T of intrinsic
U-size j+1, however large T itself is. Therefore the structural
part of the weak-(j+1)-vertex argument is genuinely relevant to
the published Lemma 2.30.

## Genuine obstruction to completion extension

But `HasClosedUKCompletion(T|S)` does **NOT** in general imply
`HasClosedUKCompletion(T)`, even if S minimally generates the
entire U-closed T. Here is a two-vertex example.

Language: strict linear order <, unary P and Bad, binary R.
Closure description U: one irreducible one-vertex root carrying
P, with R(x,y) the UNIQUE prescribed tuple above x.
No closure rule is associated with Bad.

Let K be the class of finite linearly ordered U-closed
structures satisfying Bad = empty. Thus members of K are
ordinarily irreducible by the order, U-closed and hereditary
under U-closed induced substructures. They have strong
amalgamation over closed common substructures: merge the
orders and the two R-relations, with common P-roots already
possessing their uniquely prescribed R-output in the common
closed root. No new Bad-tuples can arise.

Let T have vertices r<b, unary P(r), Bad(b), and exactly R(r,b).
It is U-closed; the root r has its unique prescribed output b,
and b is not a P-root. The singleton S={r} generates T,
so USize(T)=1. Its weak induced structure T|S is also
intrinsically rank-one (and is **not** U-closed).

Yet T|S embeds **fully** into the ordered Bad-free
two-vertex K-structure K0 with u<v, P(u), R(u,v),
and empty Bad, by r->u. In particular T|S has a
corrected K-completion with no changes to its weak carrier.

The closed T has NO homomorphism, and therefore NO
corrected K-completion, into ANY K-member: its positive
unary Bad(b) would have to map into Bad(target), which is
empty in every K-member.

This disproves any blanket claim that an arbitrary completion
of a minimum weak generating set extends to the ambient
specified closed hull. The finite assertion was checked
by explicit standard-library Python evaluation in the
verification conversation; it is not a Lean model certificate.

## Consequence for the repaired Theorem 2.18

A prospective exact-weak-vertex induction needs more than the
unrooted completion property of `T|S`. It must construct a
completion map of the FULL generated hull, or carry an explicit
relative/anchored completion record that fixes the prescribed
closure tuples outside S.

The class K in this example is not asserted to satisfy the
repaired local-finiteness axiom; this is NOT a counterexample
to repaired Theorem 2.18. It is a counterexample to a
potentially false intermediate implication.

The published TeX remains frozen; the correct usage and
remaining proof obligation are recorded here only.
