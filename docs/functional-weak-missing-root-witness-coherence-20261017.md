# Exact omitted-output witnesses on weak functional attaching roots

**17 October 2026 — English proof, independent adversarial audit and Lean candidate.**

This note follows \`functional-missing-root-profile-preimage-20261017.md\`.
The source remains a genuine transversal partite system with FULL
set-valued-function attaching maps; the vertex test is the EXACT weak
subset, not a function-closed hull. The goal is the functional-language
iterated Appendix A, preserving the already established recursive
Ramsey witness and the 2019 weak/original-partial projection convention.

## Statement 1: a missing slot is a unique outside output

For an operation \(F\), an input \(\bar x\) entirely in a weak vertex
set \(S\), and an output part \(q\), define

\[
 \mathrm{Missing}_{F,q}(\bar x;S)
 = \mathrm{Active}^{B}_{F,q}(\bar x)
   \wedge \neg\mathrm{Active}^{B|^w_S}_{F,q}(\bar x).
\]

Then this predicate is equivalent to

\[
 \exists y\notin S\;[\,y\in F_B(\bar x),\
                             \mathrm{part}(y)=q\,].
\]

In fact there is **exactly one** such \(y\). Forward: choose the
ambient active value; if it belonged to \(S\), it would survive
weak induction, contradicting missingness. Reverse: if an outside
value \(y\) and an inside value \(z\) of the same part both belonged
to \(F_B(\bar x)\), output transversality would force \(y=z\).
Thus no inside value survives. Uniqueness uses exactly the same
transversality argument.

The statement holds for *multivalued* functions with distinct output
parts, arbitrary input arity including nullaries, and nonclosed \(S\).

## Statement 2: missing-slot coherence across a full shared root

Let \(i_L:R\hookrightarrow L\) and \(i_R:R\hookrightarrow R'\)
be FULL partite functional embeddings. Let \(S_L\subseteq L\) and
\(S_R\subseteq R'\) be arbitrary exact weak subsets such that

\[
  i_L^{-1}[S_L]=i_R^{-1}[S_R]\subseteq R.
\]

Then for every root input tuple supported in this common weak root,
and every output part \(q\), the missing-slot predicates computed
in \(L|^w_{S_L}\) and \(R'|^w_{S_R}\) are equal.

**Proof:** Full embeddings identify their ambient fibres exactly
with the image of the source root fibre. In particular every side
output of an input tuple from the root comes from a unique root
output. By Statement 1, the slot is missing precisely when this
root output lies outside the appropriate inverse-image weak set.
Those inverse-image sets are equal, so the two missing predicates
agree. The currently verified full-preimage theorem
\`Embedding.missingActiveOutputAtPart_preimage_iff\` supplies the
same equivalence mechanically. The new theorem removes the need
to manually rewrite dependent weak-subtype tuples at every
attachment step.

If \(L\) and \(R'\) are full embedded sides of a common ambient
system \(C\) and their root-image embeddings agree, then taking
the two side tests as the exact preimages of ONE weak \(S\subseteq C\)
automatically satisfies the common-root hypothesis.

## Independent adversarial audit

1. **Fullness is essential.** A non-full EHN projection can introduce
   new function outputs in the target on source-undefined inputs.
   The theorem is NOT stated for arbitrary weak projections.
2. **Exact inverse images are essential.** If one weak side test
   retains a root output and the other omits it, their missing
   predicates differ. Hence the root-cut equality cannot be dropped.
3. **Part transversality is essential for uniqueness and the
   outside-witness equivalence.** Merely preserving nonempty
   domains loses information about which output part is absent
   in multivalued fibres.
4. **Defined-empty partial functions.** For an \`Option (Set)\`
   presentation, a defined empty fibre carries a separate defined
   bit but no active output slot. These lemmas track output slots;
   the independent defined bit must be handled by the existing
   partial-domain bridge.
5. **Nullaries.** A nullary operation may have an output missing
   from a weak empty vertex test. No imaginary empty-root
   exemption is asserted.
6. **The C5 and parity obstructions survive.** Equal source
   missing-slot profiles do NOT imply existence of compatible
   strict TARGET B-tree completions. The geometric
   Hales–Jewett/history predecessor lemma at nonclosed occupied
   A-boundaries remains unproved.

## Formalization scope

\`Functional/WeakMissingRootCoherence.lean\` should provide the
outside-witness characterization, uniqueness, common weak-root
coherence, and its specialization to the actual common ambient
side-restriction geometry. A root-level Check module audits their
Lean axioms. Neither this result nor the prior closed-boundary
mixed step certifies the full functional n-pass sparsening theorem.

**Next target:** use the explicit omitted-output witnesses to
formulate a relative TARGET root-completion profile that also
remembers prescribed projected histories and actual ambient A-copy
intersections. Then establish common profile *existence* for the
genuine Hales–Jewett Picture under the rank-(n−1) predecessor;
do not replace that assertion with the known-false arbitrary-stage
schema.
