# Functional Appendix A in the language of functions: the missing weak-boundary information

**17 October 2026. English proof and adversarial audit, before Lean work.**

## 1. Exact comparison with the verified All Those Ramsey Classes argument

We retain the published order: a closed genuine functional Ramsey control \(D\)
(from the already verified recursive construction), an initial Picture of full
\(B\)-copies, a Hales–Jewett functional power, finite full
selected-support attachments, induction on the **number of vertices of a
weak test**, \(n\) passes, and the already proved final \(B\)-coverage pass.
\(B\) is **irreducible**. All functional partite systems retain the
transversal output-fibre invariant.

The verified relational argument
\`PartiteConstruction/Iterated/WeakStepTreeCompletion.lean\`
uses \`ProjectedHistoryLocallyTreeLike\`,
\`ProjectedPartialIntersections\`, and the **relative labelled**
completion step in
\`Iterated/ProjectedRelativeLabelledLocalTreeLike.lean\`.
For a mixed test with \(|p[S]|=|S|=n\), its exact two projected sides
have at most \(n-1\) vertices; the predecessor controls their partial
\(A\)-boundaries. In a relational tree one can freely attach another
\(B\)-copy along an induced partial \(A\)-boundary, since every induced
relational embedding is a legitimate gluing root.

**This final sentence is false for genuine functions.** A weak induced
partial \(A\)-boundary may have lost an output of a function and is not
a full/function-closed embedding into the target. Free amalgamating two
full functional \(B\)-trees along such a weak root need not preserve
function fibres or the part-transversality invariant. The verified
relational relative-labelled lemma cannot simply be applied with
\`Embedding\` replaced by \`WeakEmbedding\`.

## 2. The precise weak/\(U\)-closed correspondence

For a function symbol \(F\), input tuple \(\bar x\), and ambient
functional structure \(C\), the ordinary output graph relation is

    Graph_F(bar x, y)   iff   y ∈ F_C(bar x).

The root/domain relation for a **nonempty** fibre is

    Dom_F(bar x)        iff   F_C(bar x) is nonempty.

The repository already implements both (with repeated-input equality
patterns) in
\`Functional/PartialFunctionPatternGraph2019.lean\`;
\`Functional/PatternClosureTags2019.lean\` also constructs closure-rule
tags on FULL induced root patterns. For the genuinely partial
\`Option (Set V)\` syntax,
\`Structure/PartialSetFunctionsDomainGraph.lean\` records the
independent **defined** bit even for \`some ∅\`.

On the exact weak vertex set \(S\):

* The **output graph** of \(C|^w_S\) agrees with the induced output
  graph of \(C\) on \(S\). This is already kernel-verified as
  \`Structure.weakInduce_graph_rel_iff\`.
* The **domain relation is different**:
  \(\mathrm{Dom}_{C|^w_S}(\bar x)\) says that **some output survived
  in \(S\)**, while \(\mathrm{Dom}_{C}(\bar x)\) can remain true
  because of an output **outside \(S\)**.
* Therefore the correct analogue of an induced **weak**
  \(\mathcal U\)-structure is the exact weak vertex structure
  **together with its AMBIENT domain/root mask**. The mask is
  inherited on the same vertices; it is not recomputed after
  discarding the function outputs.
* On a genuinely **function-closed** \(S\), all ambient output
  incidences with inputs in \(S\) remain inside \(S\); the masks
  coincide and the usual full functional induced structure is
  recovered. This is where the ordinary EHN/original-partial
  homomorphism-embedding corresponds to the corrected
  closed-\(\mathcal U\)-test homomorphism-embedding.

In other words, *weak tests are the analogues of potentially
non-\(\mathcal U\)-closed induced relational tests*, not themselves
\(\mathcal U\)-closed objects. Their ambient function-domain obligations
must remain visible, exactly as active closure roots remain visible
when the corresponding closure tuple leaves an induced vertex set.

For genuinely multivalued functions, a **single global domain bit
does not specify each missing output**. Since a partite output fibre
is transversal, use one active-output mask
\(\mathrm{Active}_{F,q}(\bar x)\) for each output part \(q\), asserting
that a value of part \(q\) exists. Transversality supplies uniqueness
of this value. Keep the separate general defined bit for
\`Option (Set V)\`, where \`some ∅\` is defined but has no active
output masks. Singleton/ranked presentations are an alternative to
per-part masks, but must not be confused with a proof for arbitrary
multivalued fibres.

## 3. Audit: a two-point unary failure of the naive correspondence

Take \(C=\{a,b\}\) and a unary partial function \(F(a)=\{b\}\).
Set \(S=\{a\}\). The original function graph has the active root
\(\mathrm{Dom}_F(a)\), but its weak restriction has
\(F_{C|^w_S}(a)=\varnothing\), so the domain predicate recomputed
from the weak function is FALSE. The induced ambient domain predicate
remains TRUE.

Thus

    (C|^w_S).patternGraph != C.patternGraph|_S

already for one unary singleton-valued function, while the
**output-only** graph restriction is exactly correct.

The defined-empty example is independent: if \(F(a)=\mathrm{some}\,\varnothing\),
the independent defined bit is true but no output obligation exists.
If \(F(a)=\mathrm{some}\,\{b\}\) and \(b\notin S\),
the current weak restriction gives \`none\`; the **ambient** root bit
must therefore still be retained in the marked weak test. It cannot
be recovered from \`none\` or \`some ∅\` alone.

This demonstrates the necessity of the additional mask data; it is
not a counterexample to the 2019 theorem.

## 4. Corrected English strategy (full theorem NOT YET proved)

Retain each weak test \(S\) on its EXACT vertex set and equip it with
the restrictions of all **ambient** positive domain/output-part masks.
Define a *relative functional root profile* to consist of:

1. A finite strict full-functional \(B\)-tree \(\mathrm{Start}\)
   completing the actual weak common boundary, with a
   possibly noninjective partial map \(q\) from the boundary.
2. The induced kernel/equality pattern of \(q\), the ambient
   active-output masks, and the prescribed projections to the
   fixed control \(D\) on all **occupied** boundary vertices.
3. Compatibility certificates for the **whole** function-closed
   root completion: any source-defined operation agrees on its
   full target value set, with distinct outputs in distinct parts.
   Source-undefined inputs are NOT required to reflect target
   undefinedness.
4. Root-hit safety: no source vertex with a different projected
   history is unintentionally identified through the completed
   root. The root may freely identify nonadjacent vertices when
   their masks and history allow it.

Relative target extensions of two weak sides are admissible only
when they use the SAME such profile. The already checked
\`ambientRelativeWeakTreeHistory_glue_sharedRoot\` proves that
compatible relative extensions yield the desired strict
full-functional weak-test completion.

**Induction:** if \(|p[S]|<n\), apply the predecessor at the exact
weak image and pull back the mask-compatible relative witness.
If \(|p[S]|=|S|=n\), use pure core/pure old witnesses, or split a
genuine mixed test along the actual full selected support.
Each side has at most \(n-1\) projected vertices. The missing
mathematical step is that these two predecessor side witnesses
can be **chosen with one common admissible root profile**.
This must use the true Hales–Jewett line/history geometry or an
equivalent finite profile amalgamation lemma, not arbitrary stages.

An important verified special case is the **budgeted boundary**:
when each side's projected set together with \(\alpha(A)\) has
at most \(n-1\) vertices, complete the auxiliary
\(I\cup\alpha(A)\) weak control test, obtain a full protected
\(A\)-mark and then restrict the target witness to the original
weak \(I\). This is the PR #393 route; it explicitly pays for
missing \(A\)-vertices and does not solve the general case.

The genuinely hard case has an **unaffordable missing boundary**.
It must be handled by profiles with freely completed outputs,
rather than a prescribed rigid full \(\alpha\)-mark.

## 5. Independent adversarial checks

* **Fixed full \(\alpha\)-mark is false:** the Lean-verified
  two-edge-path parity obstruction (#385) shows why a marked \(A\)
  cannot be demanded for every weak test of a strict \(B\)-tree.
* **Arbitrary-stage maximal mixed schema is false:** the documented
  \(C_5\) construction defeats side-local completion alone, even with
  irreducible \(B\). Therefore the profile compatibility lemma must
  retain the **predecessor rank-\((n-1)\)** condition and/or actual
  Hales–Jewett history, not just separate completability of Old/Core.
* **One global HJ coordinate is false:** the three-line \(C_7\)
  example shows that distinct lines may have no common parameter,
  but its seven vertices project to only three parts, hence it
  does not refute the rank-seven small-image branch.
* **Partial functional gluing cannot ignore domain masks:** a
  weak root containing an input but omitting its output is NOT
  full/function-closed. Gluing over it as if it were a full
  functional substructure changes fibres and can violate
  transversality.
* **Induced intrinsic irreducibles can be spurious:** truncating
  an ambient function output can make the remaining weak induced
  test intrinsically irreducible with no full realization in a
  strict \(B\)-tree. Protect only genuine full ambient
  irreducible embeddings; this matches the corrected
  \(\mathcal U\)-closed embedding convention.
* **No rank inflation:** the marked domain masks live on tuples
  of the SAME tested vertex set, and the auxiliary root completion
  is target-side data. Never count a function-closure hull of \(S\)
  in place of \(|S|\).

## 6. Exact next formalization and proof status

Before claiming the mixed rank step, prove the elementary
native-function-language **domain-mask comparison**:

1. For all input equality patterns and exact weak \(S\), output
   graph relations commute with weak restriction.
2. The ambient domain predicate is equivalent to *some output in
   the ambient structure*; the recomputed weak-domain predicate
   is equivalent to *some retained output in \(S\)*.
3. Closed \(S\) makes the two domain predicates equal. For arbitrary
   \(S\) they need not be equal; prove the unary regression explicitly.
4. Extend this boundary record to per-output-part active masks
   using the existing \`System.funcTransversal\` uniqueness.

Then define one common-root profile (not a fixed full \(A\)-mark)
and verify that the existing functional gluing theorem consumes it.
Only then attempt the **existence** of a common root profile for the
genuine Hales–Jewett Picture. The completed profile-existence proof
is NOT currently available, including in the published functional
manuscript. The already verified 2019 relational/profile proof is an
important oracle but is NOT a direct proof of this native lemma.

No Green \`\\leanverified\` marker should be added for the global
strict functional sparsening assertion while this compatibility gap
remains; the survey circulation text is frozen except for TODO and
validation comments.
