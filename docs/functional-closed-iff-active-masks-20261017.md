# Functional U-closedness is exact preservation of active output-part masks

**English theorem, proof and adversarial audit — 17 October 2026.**

Let \(B\) be a TRUE functional partite system over \(P\), with
transversal set-valued output fibres, and let \(S\subseteq V(B)\)
be ANY vertex set. Keep the exact weak substructure \(B|^w_S\);
do not generate closure vertices.

For every function symbol \(F\), input tuple \(\bar x\in S^k\),
and control output part \(q\), let
\(\operatorname{Act}_B(F,\bar x;q)\) mean that the ambient fibre
contains an output in part \(q\). Similarly let
\(\operatorname{Act}_{B|^w_S}(F,\bar x;q)\) mean that such an output
**survives** inside \(S\).

**Exact characterization:**
\[
 S\text{ is function-closed in }B
 \quad\Longleftrightarrow\quad
 \forall F,\bar x\in S^k,q\in P:
 \operatorname{Act}_B(F,\bar x;q)
 \Longleftrightarrow \operatorname{Act}_{B|^w_S}(F,\bar x;q).
\]

**Proof.** If \(S\) is closed, every ambient output over inputs
from \(S\) stays in \(S\), so every active mask survives. Conversely,
take any ambient output \(y\in F_B(\bar x)\) with \(\bar x\in S^k\)
and write \(q=\pi_B(y)\). The mask equivalence gives an output
\(z\in S\cap F_B(\bar x)\) in part \(q\). **Transversality of
the ambient fibre** gives \(z=y\), hence \(y\in S\).
This proves function-closedness with no finiteness, singleton
or generated-hull hypothesis.

The reverse direction from a surviving mask to an ambient mask
is automatic for EVERY weak \(S\). Thus it is enough to ask for
reflection of ambient masks in the weak restriction.

## Why this fixes the semantic analogy with U-closed structures

For ordinary function graphs, the weak structure on \(S\) has exactly
the induced *output incidences*. The OLD induced ambient domain/root
record, however, may retain an active root whose output was discarded.

A weak set is the analogue of a \(\mathcal U\)-closed vertex
substructure **if and only if** no such active per-output-part
closure slot is missing. The equivalence above recovers exactly
that condition for multivalued, part-transversal operations.
It must not be replaced by equality of a SINGLE global
nonempty-domain bit: a multivalued fibre could lose one output part
while retaining another.

## Adversarial audit

* **Unary lost-output example:** \(F(a)=\{b\}\) and \(S=\{a\}\).
  Ambient part of \(b\) is active but the weak mask is inactive.
  \(S\) is not closed. This matches the existing domain-mask
  regression in Lean.
* **Multiple outputs:** \(F(a)=\{b_0,b_1\}\) with \(b_i\) in distinct
  parts, and \(S=\{a,b_0\}\). The global DOMAIN bit remains true,
  but the active mask for the part of \(b_1\) is lost. The new
  criterion correctly detects nonclosedness.
* **Missing transversality:** if two outputs lie in the SAME part
  and just one survives, both active masks agree while the set
  is not function-closed. Hence transversality is indispensable.
* **Source-undefined EHN projection:** an EHN projection need not
  reflect newly active target masks. The theorem is internal to
  one true functional system, not a claim that any EHN weak map
  is a full map.
* **Defined-empty:** for \`Option (Set V)\`, \`some ∅\` has
  NO active output mask but still carries an independent
  definedness bit. The corresponding enriched U-closure
  comparison must retain that bit. No such bit is present in
  the legacy empty=undefined syntax addressed here.

This equivalence is a genuine **native functional theorem** and a
reusable validation point for the user-requested corrected Appendix
A. It does not, by itself, produce compatible strict B-tree
completions of a reducible weak root in a mixed HJ attachment.


## Stronger three-way characterization of a weak boundary

The same condition is equivalent to the canonical weak inclusion
being a GENUINE FULL functional partite embedding:
\[
 S\text{ function-closed in }B
 \quad\Longleftrightarrow\quad
 (B|^w_S \hookrightarrow B)\text{ is a full function embedding}
 \quad\Longleftrightarrow\quad
 \text{all ambient active output-part masks survive on }S.
\]

The weak inclusion exists as an ordinary *function-graph embedding*
for any \(S\) (already verified). It can be upgraded to a FULL
functional embedding when \(S\) is closed: every complete function
fibre in \(B\) over inputs from \(S\) is entirely inside \(S\),
so the full functional inclusion is well-defined.

Conversely, suppose a full functional embedding has the SAME
underlying map as the canonical weak inclusion. For any ambient
\(y\in F_B(\bar x)\) with \(\bar x\in S^k\), full target-fibre
surjectivity gives an output \(z\in F_{B|^w_S}(\bar x)\) mapped
to \(y\). Since the underlying map is inclusion, \(y=z\in S\).
Thus \(S\) is closed.

This is a map-level equivalence—not merely a Boolean closure
predicate—and separates the already valid graph/weak embedding
from the additional closure obligation required by genuine
functional free-amalgamation roots.

**Audit:** This equivalence is about the canonical SAME-VERTEX
inclusion. It does not say there cannot be some unrelated full
embedding of the abstract weak substructure into \(B\): such an
embedding might relocate vertices to another closed part.
Nor does it apply to an EHN map that does not preserve all
source undefined domains.
