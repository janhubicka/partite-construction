# Track D — English audit and the correct small-image / pure-trace split (13 November 2026)

**Scope:** strict original-2019 partial-function B-tree completion on literal
weak vertex tests in the native functional Picture. The corrected printed
relational Appendix A is frozen and separately verified. This file does
not change the manuscript or re-add any removed author TODO.

## I. Completed positive small-image branch, with no history

Let C,D be true full relation/set-valued-function structures and
p:C→D an EHN (original-2019 source-defined) homomorphism-embedding.
Fix irreducible A, irreducible Base, and an EXACT finite weak test
S⊆C, not necessarily function-closed. Assume D has the genuine
history-free rank-m strict weak-tree invariant

    AtMostNoHistory(A,Base,D,id,m)

and that the literal projected image satisfies |p[S]|≤m.

**Theorem:** C has a strict functional Base-tree ambient-relative weak
witness on the SAME S, with full target A-copy certificates for every
genuine full ambient A↪C intersecting S. This is
`SetAmbientRelativeWeakTreeWitness(A,Base,C,p,S,[])`.

**Proof.** Choose I:=p[S] as an exact finite subset of D; its
cardinality is bounded by |S| and by m by hypothesis. Apply the
predecessor to I and pull back using the already checked
`SetAmbientRelativeWeakTreeWitness.pullback_ehn`. Its ambient
A-copy certificate transfers because the original A is irreducible
and each full source A-copy lifts along an EHN map as a FULL
control A-copy. The result is entirely on S; it neither adds
function closure vertices nor asks for domain reflection on
source-undefined inputs. The projected history list is empty.

This directly covers ALL small-projected-image tests of the next
Picture, pure or mixed. A function-closed S additionally yields a
strict original-partial completion by the verified
`SetAmbientRelativeWeakTreeWitness.closed_test` theorem.

## II. Why the pure-copy case does NOT follow just by old-stage restriction

The merged mixed theorem #642 and the initial/power theorem #643
are genuine positive results. But they do not imply that the whole
new native Picture is AtMostNoHistory(n). A test wholly inside
the copied old source can intersect a new genuine ambient A-copy
which lies on the power side. Irreducibility of A implies that
the A-copy is contained in one whole source side; it does **not**
make its intersection with the other side into a full A-copy there.

Thus restricting a completion that protects every old full
A-copy does NOT automatically protect every newly appearing
ambient A-copy. The missing condition is a compatible target
FULL A mark for the partial selected-support trace of each
new core A-copy. For truly functional structures, that trace
may not be function-closed. It is mathematically wrong to
replace it by a full induced closed root at the same
exact-vertex budget.

The analogous **relational** argument works because it stores
`ProjectedPartialIntersections` for all relevant partial
A-copies; see verified
`Iterated/PureCopyProjectedCompatible.lean`.
In the functional language, the existing
`FunctionalProjectedPartialIntersections` assumes a FULL
function-closed partial A-root and is insufficient on an
arbitrary weak nonclosed trace.

### Diagnostic finite example (English only, not a Lean counterexample)

Take a language with a symmetric binary adjacency relation E
and one ternary relation R. Let A=Base be the three-vertex
path u–v–w, with R(u,v,w) true. The ternary tuple makes the
FULL Base irreducible, although the endpoint pair {u,w} is
a reducible (independent) proper partial trace.

Build the old stage O as a three-edge path
o₀–o₁–o₂–o₃ by gluing two full Base copies along one common
edge; it is a strict Base-tree. Select the FULL old support
{ o₀,o₃ }, which is two independent vertices. Embed it
FULLY into the endpoints of a fresh Base core
o₀–c–o₃ and make one actual FULL free binary attachment
C=O*_{ {o₀,o₃} } Base. The old path of length 3 and
the core path of length 2 form an induced 5-cycle.

The literal pure-old weak test S=O has four vertices.
Its old-stage strict tree witness exists (the old stage
itself). However an ambient full A-copy on the core side
meets S at both independent endpoints o₀,o₃.
The target A-copy certificate would require images of those
two endpoints to be the endpoints of a target Base path,
hence at the SAME bipartite parity. Positivity of the old
three-edge path forces their images to have OPPOSITE parity.

Every strict tree built from full copies of this decorated
Base remains bipartite: gluing roots are fully embedded into
a single irreducible Base-piece on each side, so all root
vertices have matching pairwise bipartition parities on
both sides, and the two bipartitions can be oriented
consistently. Hence the required pure-old target certificate
cannot exist.

This illustrates that the *unqualified* transfer
old-stage AtMostNoHistory(n) ⇒ new-stage pure-old
AtMostNoHistory(n) is false without additional control
predecessor or trace hypotheses. It does NOT refute the
conditional rank-(m+1) Picture theorem: a control D
admitting the required rank-m predecessor has not been
exhibited for this graph, and the predecessor may exclude
the parity pattern at m=3.

## III. Correct remaining rank split

For each exact weak tested S of size ≤n=m+1 in a genuine
native one-copy attachment:

1. If |p[S]|≤m, use the new small-image EHN pullback
   theorem from I, including all ambient A-copy data.
2. If |p[S]|=n and S is MIXED, merged #642 covers it
   (in fact #642 covers all mixed tests).
3. If |p[S]|=n and S is PURE POWER, the power
   one-copy EHN map supplies the weak functional target
   on the power alone, but new old-side A-copy
   intersection traces still need checking.
4. If |p[S]|=n and S is PURE OLD, the old rank-n
   witness is available but may omit full A marks
   for NEW power A-copies meeting its weak support.
   This is the sharp remaining pure-copy compatibility
   obligation.

The last two issues cannot be erased simply by forgetting
the projected-history list. They call for either (a) a
functionally correct weak partial-A trace profile invariant,
(b) an additional test-dependent collar extraction directly
from the rank-m control with no budget violation, or
(c) the already validated 2019 two-pass closure-profile
proof of the final survey theorem, which avoids the optional
native strict-functional n-pass intermediate invariant.

## IV. Validation policy

Formalize the positive small-image theorem and EHN
pullback of the weakened rank-n invariant FIRST, with
named exact-head Lean axiom checks. This is independent
of the unproved pure maximal case.

Do not add a green marker to unrestricted native n-pass
iteration. Preserve the source-defined set-valued
function semantics, all transversality hypotheses on
actual stages, and the exact weak vertex cutoff.
