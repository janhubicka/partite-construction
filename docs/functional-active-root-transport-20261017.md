# Functional active-output roots: a verified target for the next lemma

**English first, 17 October 2026.** This is the local root-coherence
statement required by the direct functional weak-boundary repair.

Let \(R,L,H\) be genuine functional partite systems over the SAME
control-parts \(P\), with **full part-preserving embeddings**
\(i_L:R\hookrightarrow L\), \(i_H:R\hookrightarrow H\). Every
individual function output fibre is transverse over \(P\).

For each function symbol \(F\), tuple \(\bar r\in R^k\), and possible
output part \(p\in P\), set

    Active_p(F,bar r)  iff
      there is y ∈ F_R(bar r) with part(y)=p.

**Claim (unconditional).**
\[
  \operatorname{Active}^{L}_{p}(F,i_L\bar r)
   \iff
  \operatorname{Active}^{R}_{p}(F,\bar r)
   \iff
  \operatorname{Active}^{H}_{p}(F,i_H\bar r).
\]
Full functional embeddings preserve entire set-valued fibres, and
part-preservation proves both directions. By transversal images there
is **at most one** output per part, so these active bits identify
the individual potential function-closure slots exactly.

For an arbitrary weak subset of the root the ambient active bits
should be **inherited**, not recomputed from outputs that happen
to survive on the tested vertices. Thus the root mask is the SAME
on both sides of a genuine closed functional free attachment, even
if its exact tested weak overlap omits closure outputs.

**Audit and scope.** If either \(i_L\) or \(i_H\) is only a weak EHN
projection, the reverse implication can fail: an input undefined in
the source can acquire an output in the target. Hence FULL attaching
maps are essential. Transversality is needed for uniqueness of
the output in each part, not for preservation of existence.
No identification/compatibility of arbitrary strict B-tree
completion profiles is claimed. This is a proof of coherent
*source-root masks*, not yet a proof of coherent *target-root
embeddings*.

This lemma is the direct function-language counterpart of saying
that an actual common closed \(\mathcal U\)-boundary carries the same
set of active closure roots in both sides. Keep it separate from the
unproved relative-completion existence lemma.
