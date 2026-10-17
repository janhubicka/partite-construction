# Functional Appendix A: replacing the relational partial A-boundary extension

**English proof and adversarial audit, 17 October 2026.**
This is the first genuinely new **relative** construction needed for
the functional version of the verified 2019/Appendix A
\`ProjectedRelativeLabelledLocallyTreeLike.ofProjectedHistory\`.
Everything below uses actual FULL function structures and their
genuine free amalgams, not relational intermediate Pictures.

## Precise theorem: closed occupied A-boundary

Let \(D\) be the preceding functional control, \(A\hookrightarrow B\)
a FULL embedding with \(B\) irreducible, and
\(\alpha:A\hookrightarrow D\) the selected full control placement.

Fix an EXACT weak control test \(I\subseteq D\) and let
\[
 H = \{a\in A:\alpha(a)\in I\}.
\]
Suppose **\(H\) is function-closed in \(A\)**. This is the direct
functional analogue of a legitimate \(U\)-closed partial boundary.

Assume the ordinary verified predecessor projected-history
witness on \(I\): a strict full-functional \(B\)-tree \(T\) and an
ambient-relative weak completion map \(f:I\to T\), together with
actual full ambient \(A\)-copy intersection certificates.
Request **all singleton projected histories** as part of the
finite history. In particular, \(f\) is INJECTIVE on the exact
weak test \(I\).

The ambient-copy certificate for \(\alpha\) gives a FULL mark
\(a_T:A\hookrightarrow T\) contained in a \(B\)-constituent
such that \(f(\alpha(a))=a_T(a)\) for each \(a\in H\).

Since \(H\) is function-closed, the canonical embedding
\(A|_H\hookrightarrow A\) is FULL. Hence both
\[
 A|_H \stackrel{a_T}{\hookrightarrow} T,
 \qquad
 A|_H \stackrel{e_{AB}}{\hookrightarrow} B
\]
are full functional embeddings whose images lie in irreducible
constituents. Form the genuine FULL functional free amalgam
\[
       T' = T *_{A|_H} B .
\]
This is again a STRICT \(B\)-tree.

The old test map becomes \(f'=j_T f:I\to T'\), retaining all
function-fibre, irreducible-intersection and history certificates.
Use the new full copy
\(a'_T=j_B e_{AB}:A\hookrightarrow T'\) as the marked A-copy.

**Exact protected trace:**
\[
    f'(x)=a'_T(a)
       \quad\Longleftrightarrow\quad x=\alpha(a)
       \qquad (x\in I,\ a\in A).
\]
For \(a\in H\), the two embedded copies agree on the gluing
root, hence the reverse implication holds. Conversely, if a
test point in the OLD target collides with a new marked vertex,
the FULL free-amalgam overlap theorem forces
\(a\in H\) and \(f(x)=a_T(a)\); the singleton history
then forces \(x=\alpha(a)\). If \(a\notin H\), the fresh marked
vertex cannot lie in the image of the old target at all.

This does **not** add any vertices to \(I\), does not take a
function closure of \(I\), and does not consume any of the
predecessor's numerical vertex budget. It is a direct analogue
of the relational relative-labelled extension lemma,
provided the occupied partial A-boundary is truly closed.

## Independent adversarial audit

* **Why H-closed is essential.** For \(F(a)=b\) with \(a\in H\),
  \(b\notin H\), the weak restriction on H has discarded an
  output. The map \(A|^w_H\hookrightarrow A\) is not a FULL
  functional embedding; the proposed free amalgam along this
  weak root would be illegitimate and could produce two
  different values for the same input.
* **Rigid-mark parity counterexample.** For A=B=K₂, the
  edge language has NO functions, so every H is closed.
  Nevertheless the previous globally fixed-mark request was
  impossible for a two-edge source path labelled 0–2–1
  against an active α(0,1). Our theorem instead starts from
  the ordinary preceding-control WITNESS on the entire exact
  projected I, INCLUDING ambient α-copy and singleton
  histories. No such strict witness exists for that
  problematic rank-3 D=K₃ configuration. Thus there is
  no contradiction; the predecessor requirement is real.
* **Wrong target hits.** Arbitrary marked witnesses can hit an
  unoccupied α-position with another tested vertex. The
  fresh-B-copy construction above repairs exactly that: only
  occupied H is glued; all other α-vertices are new.
* **Genuine set-valued functions.** Full closed attaching
  roots retain their ENTIRE multivalued fibres, so no
  temporary inconsistent function state appears. Every
  function output part remains unique in the source partite
  Systems by the independent transversality invariant.
* **History and ambient A-copies.** Postcomposition with
  the FULL target embedding \(T\hookrightarrow T'\)
  preserves the ambient-relative weak HE and the actual
  ambient A-copy certificates. Injectivity transports every
  projected-history diary. These exact postcomposition
  theorems are already verified.
* **Empty occupied boundary.** If H=∅ and there are no
  nullary function obligations, a fresh disjoint B-copy is
  legitimate. Positive function arities are part of the
  intended Appendix hypothesis; the Lean lemma requests
  literal closure of H and thus does not silently assume
  emptiness is always closed for languages with nullaries.

## Mathematical frontier after this theorem

The **closed-H mixed boundary** is now handled by a direct native
function-language relative-labelled construction, without
budgeting the unoccupied α-vertices. The remaining case has
\[
        H\text{ NOT function-closed in }A.
\]
By the already verified exact active-mask equivalence, this
means precisely that an active function-output-part root has
its inputs among the occupied boundary vertices but its unique
output outside the boundary.

That is the genuine **unfulfilled U-closure root** situation.
It needs a synchronized target completion of the missing
functional output slots, rather than gluing a B-copy along a
nonclosed weak root. A separate finite root profile/partial
closure lemma for actual HJ histories is still required.

**Formalization target:** prove the closed-H relative marked
completion from the predecessor's ordinary
\`SetAmbientRelativeWeakTreeWitness\` plus singleton histories;
then specialize from \`AtMost\` with I-card ≤ m. Verify the
strict B-tree, protected mark, exact weak map, actual A-copy
intersections and history clauses with named axiom checks.
No validation marker for the full unrestricted functional
sparsening theorem follows from this partial case.
