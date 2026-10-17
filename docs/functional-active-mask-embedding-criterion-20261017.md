# A direct functional replacement for closed U-root embedding checks

**English proof and adversarial audit, 17 October 2026.**

Let \(A,B\) be genuine functional partite systems over the same
part carrier \(P\), with transversal set-valued output fibres.
Let \(f:V(A)\to V(B)\) be a vertex map satisfying:

1. \(f\) is injective and preserves all part labels.
2. Ordinary relations are preserved **and reflected**.
3. Every positive source function incidence is preserved:
   \(y\in F_A(\bar x)\) implies \(f(y)\in F_B(f\bar x)\).
4. For EVERY output part \(q\in P\), the active root mask is
   preserved **and reflected**:
   \[
   (\exists y\in F_A(\bar x):\pi_A(y)=q)
   \iff
   (\exists z\in F_B(f\bar x):\pi_B(z)=q).
   \]

**Theorem.** These conditions imply \(f\) is a FULL functional
partite embedding:
\[
    f[F_A(\bar x)] = F_B(f\bar x)
\]
for every function symbol and input tuple.

**Proof.** Positive preservation gives inclusion from left to right.
Conversely choose target output \(z\) and put \(q=\pi_B(z)\).
By mask reflection there is a source output \(y\) of part \(q\).
Its image is a target output by positive preservation and lies in
part \(q\) by part preservation. **Target transversality** forces
\(f(y)=z\). Hence the reverse inclusion. Injectivity and relation
reflection establish all the remaining full embedding conditions.
The forward implication follows from an existing full embedding.

## Functional/U-closure significance

An induced weak U-test retains ambient active closure ROOTS even when
its outputs leave the tested vertex set. The active output-part masks
are precisely these obligations in the genuine functional partite
language. Preserving positive incidences AND the exact masks on an
actual closed full root is enough to recover a full functional
embedding. No relational intermediate Picture, new closure vertices
on the tested set, or temporarily multivalued target is introduced.

On an arbitrary EHN projection, source-undefined inputs may acquire
new active target masks: mask reflection must NOT be assumed.
This criterion is for actual FULL attaching maps and completed
full target boundaries.

## Adversarial audit

* Without reverse mask preservation the target may have a new
  output in a previously inactive part.
* Without target transversality two distinct target outputs could
  share one part; the Boolean active mask would not detect the
  extra output.
* Without relation reflection, the result is not an embedding.
* Without part preservation, target transversality does not compare
  the required outputs.
* For the enriched partial-function syntax Option (Set V),
  defined-empty (some empty set) and undefined (none) have the
  SAME inactive output masks. A separate definedness bit must
  additionally be preserved. The theorem here is for the genuine
  legacy System syntax where the empty output set is undefined.

This characterizes full function-embedding MAPS in the
transversal language. It does NOT construct compatible strict
B-tree target completions for an arbitrary weak A-boundary.
The function-free C5/C7 history obstructions have vacuous masks:
the remaining geometric compatibility step is independent of
this correct map characterization.

**Lean task:** prove the converse embedding constructor and a
bi-implication for fixed underlying maps, with named axiom checks.
