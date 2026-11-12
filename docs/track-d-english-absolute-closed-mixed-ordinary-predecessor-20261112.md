# Track D — English proof first: absolute closed mixed completion from the ORDINARY predecessor

**12 November 2026.** This is a new mathematical reduction, not merely the
marked-gluing wrapper of PR #635. It is stacked on the English-first marked
target-gluing proof. The numbered Nešetřil programme survey and removed
collaborator TODOs remain frozen.

## 1. The theorem worth proving

Let `Base` be an irreducible full finite relation/set-valued-function
structure, let `A↪D` be a FULL selected control copy, and suppose `D`
has the verified **ordinary rank-m strict weak-history predecessor**
`SetAmbientRelativeWeakTreeWitness.AtMost A Base D id m`. In
particular every exact weak control test `I⊆D` of at most m vertices,
for each selected history list, has a strict full-functional Base-tree
witness with (i) an ambient-relative weak EHN map, (ii) FULL marks
for each actual ambient A-copy intersecting I, and (iii) projected
history compatibility. **The predecessor is NOT assumed to have
protected marks**.

Consider an actual full functional free amalgam
`C=L *_R M`, together with EHN projections of its two full sides
`p_L:L→D` and `p_M:M→D`. Assume they agree on the exact FULL common
source root `R`, and every root image lies in the selected
`alpha(A)`.

Suppose the EXACT projected **whole side** vertex images `I_L=p_L[L]`,
`I_M=p_M[M]` each have at most m elements. Then:

> **Absolute closed-mixed completion.** There exists a strict FULL
> functional Base-tree T and an original-2019 source-defined partial
> homomorphism-embedding `C→T`.

No injection of the canonical map `R→A`, irreducibility or
one-generation of R, full domain reflection of p_L/p_M,
function-closedness of I_L/I_M, or protected-mark predecessor
is assumed.

For a genuine exact function-closed mixed test S of size ≤m+1 in
one full Hales–Jewett attachment, the exact full closed pullback
gives L,M,R. Mixedness makes each side's source test have ≤m vertices
and therefore its exact projected image has ≤m vertices. That
numerical application requires no bound on the ambient closure
outside S and no generator-rank substitution.

## 2. Complete proof of the absolute claim

Choose `history` to include the empty list or any particular caller
history (the final absolute theorem forgets it).

For each side `i∈{L,M}`, take the ordinary predecessor witness for
the **literal** control image `I_i=p_i[Side_i]` (not its function
closure). Write its target `T_i` and exact weak map
`g_i:D|^w I_i→T_i`. The verified predecessor also supplies for the
selected FULL embedding `alpha:A↪D` a **FULL target mark**
`m_i:A↪T_i` contained in an irreducible Base-piece and satisfying

```
m_i(a) = g_i(alpha(a)) whenever alpha(a) belongs to I_i.
```

This is exactly the existing `SetAmbientACopyIntersections`
certificate, without any closedness assumption on the *occupied*
subset of A. Crucially it is NOT yet a *ProtectedAMark*:
unoccupied positions of m_i can coincide with images of other
tested vertices.

Pull the weak map `g_i` back along the EHN part projection
`p_i:Side_i→D` on the exact ENTIRE vertex carrier of that full
side. The theorem `IsAmbientRelativeWeakHE.pullback_ehn_exact`
produces a genuine ambient-relative weak HE
`f_i:Side_i→T_i`. Since its tested set is the whole side,
every source-defined function fibre survives, and
`IsAmbientRelativeWeakHE.toOriginalPartialHE_of_closed`
upgrades this SAME map to a valid original-2019
partial homomorphism-embedding, without requiring reflection of
source-undefined inputs. A harmless full induced-universe
identification changes the subtype presentation back to Side_i.

By hypothesis, on each root vertex r the two control labels agree
and lie in `alpha[A]`. Choose a single (potentially COLLIDING)
map `q:R→A` with

```
alpha(q(r)) = p_L(s_L(r)) = p_M(s_M(r)).
```

Each root position belongs to each exact projected side image
because it has a literal source representative in that side. Hence
the *occupied mark equations* give

```
f_L(s_L(r)) = m_L(q(r)),
f_M(s_M(r)) = m_M(q(r)).
```

Now apply the English-audited and Lean-candidate
`originalPartialTreeCompletion_of_marked_partialSides_noninjective`
(PR #635). Glue the **TARGET** trees over their full marked A
embeddings `m_L,m_M`. The result remains a strict B-tree because
the full TARGET A-images are contained in irreducible B-constituents.
The original source-root q need not be a full embedding and may
identify vertices. The genuine full source free-amalgam gluing
combines f_L,f_M into an original-2019 partial HE `C→T`.
This proves the claimed absolute strict completion.

## 3. Adversarial scope check

**This is genuine progress:** it derives the required marked SIDE maps
from the ORDINARY (unprotected) weak-history predecessor on the
control, not from a newly postulated compatible-mark oracle.
It discharges the previous *closed occupied control boundary*
hypothesis for **ABSOLUTE** completion of a full mixed test.

**It does NOT prove the full optional strict native n-pass
iteration.** In the target pushout, an UNoccupied `m_L(a)` may
identify with an image of a left source vertex at a DIFFERENT
control label, or similarly on the right. After gluing both marks
these can create *new cross-side wrong hits*, violating
`SetRespectsProjectedHistory` and future ambient A-copy protection.
Consequently the result does **not** re-establish the predecessor
`SetAmbientRelativeWeakTreeWitness.AtMost` at rank m+1.
The earlier K2 path/parity counterexample forbids imposing one fixed
protected alpha mark for every weak test. The correct remaining
induction needs a *test-dependent protected boundary* or a different
history invariant compatible with nonclosed occupied A-roots.

**No rank cheating.** In the rank-(m+1) corollary only the
original exact mixed tested full pullback's side vertex counts are
≤m; projected images cannot have larger cardinality. The proof
never closes a nonclosed weak side image at the same numerical
budget and never counts the potentially much larger generated
hull against |S|.

**No wrong 2026 total-fibre map.** For source-undefined function
inputs the partial HE imposes no equation, even if the target
application becomes defined after gluing. Full set-valued fibres
are preserved exactly on nonempty *source* inputs. Genuine
Option(Set) defined-empty values are distinct and require the
separate complete-mask dictionary.

**No full HJ history claim.** The lemma is for one FULL source
free-amalgam cut and its side image cardinal bounds. It applies
to individual actual full closed-test pullbacks but does NOT
construct one common mark across all Hales–Jewett parameter lines.

## 4. Minimal Lean acceptance

First prove an all-carrier helper
`IsAmbientRelativeWeakHE.univ_toOriginalPartialHE`, identifying
`C.induce Set.univ` with the original full C via an explicit
full structure embedding, without any new axiom.

Then prove:
1. `IsFreeAmalgam.originalPartialTreeCompletion_of_controlMarkedSideImages`
   with explicit ordinary exact control-image weak witnesses on L/M;
2. a rank-m corollary `..._of_controlPredecessor` taking
   `AtMost A Base D id m` and the two exact projected side image
   cardinal bounds;
3. only after both compile, specialize to one actual native closed
   `closedTestPullback` using the verified mixed-side budget
   lemma. The optional history-preserving strength remains marked
   OPEN rather than smuggled into these conclusions.

Maintain a DRAFT PR until exact-head full Lean and named axiom audits
pass. No frozen survey annotations are to be edited.
