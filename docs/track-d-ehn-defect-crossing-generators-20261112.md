# Track D — actual source input generators cross defect decompositions

**12 November 2026, supplementary research note.** Companion to
`EHNDefectCrossingGenerators.lean`, stacked on PR #589. This is **not**
an edit to the frozen numbered Appendix A manuscript.

## Mathematical content

Take any index type `I` (including nullary `I=Fin 0`), original
source tuple `xs:I→C`, and the *full native function-closed hull*
`H=closure(range xs)` with induced structure `C|H`.

If `C|H` admits a proper FULL free decomposition with left/right
embeddings `j_L:L↪C|H` and `j_R:R↪C|H`, then

```
∃ i_L:I, xs(i_L) ∉ range(j_L)
∃ i_R:I, xs(i_R) ∉ range(j_R).
```

Here `xs(i)` denotes its canonical element of the actual full hull.
The indices can differ. The proof is elementary but has an important
source-faithfulness property: if all original generators belonged to
one FULL closed side, closure would put every vertex of `H` on that
side, contradicting properness.

The lemma is reused for two concrete EHN defects:

* A target-only positive relation on a particular original input tuple
  yields a proper decomposition of that exact source input hull, and
  the tuple misses *both* decomposition sides on at least one index.
* A target-defined but source-undefined function input tuple has the
  analogous crossing certificate. Defined source fibres have already
  been proved fibre-exact, so this case does not include extra target
  outputs at a defined input.

There is no assumption about a common irreducible collar, a global
injective EHN root map, finite hull **cardinality**, or any external
target retraction. The input hull is a *diagnostic full source object*;
it must **not** replace the literal weak tested vertex set in the
rank-bound argument.

## Remaining obstacle

The source decomposition does not, by itself, yield a simultaneously
chosen root `Start` and two relative ORIGINAL-PARTIAL strict
`B`-tree extensions for the actual ordered Hales–Jewett attachment.
The proof of that construction must preserve earlier line histories
and cannot simply complete the left and right decomposition sides
independently. This is the Track D open target after this work.

Status: **DRAFT** until parent PR #589 and this exact-head full Lean,
named-axiom and no-admissions checks pass. Do not green-mark the
unrestricted strict functional iteration.
