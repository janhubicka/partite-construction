# Arbitrary relational (L,U) to functional language: adversarial statement audit

Date: 4 November 2026  
Target: survey Appendix A, \`thm:models2\` and associated closure lemmas.

## 1. Why the first same-carrier dictionary is not an arrow theorem

Let \`U={R}\` with \`R\` binary and encode it redundantly by both
the relation \`R(x,y)\` and a unary multivalued function
\`F_R(x)={y:R(x,y)}\`. For a source/target already constructed this
way, full functional embeddings are exactly U-closed relational embeddings.

But a *new* functional Ramsey witness does not have to satisfy that
equation. On a one-point carrier \`{a}\`, take
\`R_C = ∅\` and \`F_C(a)={a}\`.
Its function-decoded relational structure satisfies \`R(a,a)\`,
while its retained duplicate relation does not. A coherent one-point
source with \`R(a,a)\` and \`F(a)={a}\` embeds in the decoded relational
target but not in the unreduced functional target. Thus simply deleting
the duplicate or resetting it after the Ramsey construction creates
new copies not controlled by the original colouring.

This is a finite semantic obstruction to the *naive proof transfer*,
not to the printed relational Ramsey theorem.

The initial \`GenericUFunctionalDictionary.lean\` is therefore
restricted to **coherent source/target comparisons**. Its theorem
types do NOT assert an unrestricted Ramsey arrow transfer.

## 2. Nonredundant language

Fix a relational language \`L\`, a subset \`U\` of its symbols
with \`arity(R)≥2\` for every \`R∈U\`.
Define \`L_f\` with
\`RelSymbol = {R : L.Symbol // R∉U}\`,
\`FuncSymbol = {R : L.Symbol // R∈U}\`,
\`relArity(R)=arity_L(R)\`, and
\`funcArity(F_R)=arity_L(R)-1\`.

On the **same vertex set** interpret each new function by
\[
  y\in F_R(\bar x)\iff R(\bar x,y).
\]
Conversely, from an arbitrary \`L_f\`-structure (no coherence premise)
recover \`R\` directly from \`F_R\` membership for \`R∈U\`,
and non-U relations from the unchanged relation interpretations.

The split/recombine lemmas for \`Fin (arity R)\` and
\`Fin (arity R-1)\` are the entire finite-index bookkeeping.
They preserve repeated coordinates, empty value sets, and the same
carrier. The new module \`GenericUReducedLanguage.lean\` contains
candidate Lean proofs of both relation and function round-trip laws.

## 3. Embeddings and closure

Let \`e:A↪B\` be an induced relational embedding.
The condition that its image is U-closed means:
for every \`R∈U\`, every root tuple \`x\` of source vertices,
and every target \`y\`,
\[
 R^B(e\bar x,y)\ \Longrightarrow\ y=e z
 \text{ for some } z\in A.
\]
Reflection of \`R\` by \`e\` then gives \`R^A(\bar x,z)\`.
Hence \`e[F_R^A(\bar x)] = F_R^B(e\bar x)\`.
The reverse direction is immediate from equality of value sets.
For \`R∉U\`, the relation is unchanged.

Conversely, for **arbitrary** \`L_f\` structures \`C,D\`,
a full functional embedding \`f:C↪D\` induces an embedding
of their decoded relational structures: on a distinguished
\`R\`, induced reflection follows from
\`f(y)\in F_R^D(f\bar x)\iff y\in F_R^C(\bar x)\`,
using injectivity; full-function equality also supplies U-closedness.
The candidate Lean implementation is in
\`Structure.Embedding.toRelU\` and
\`Structure.Embedding.toRelU_uClosed\`.

**Still needed:** a formal \`Equiv\` between the two embedding types
for *arbitrary decoded targets*, natural under composition; and the
induced equivalence of structural Ramsey arrows.

## 4. The named order must also be nonredundant

The survey's relational language contains a symbol \`<\` interpreted
as the full strict linear order. The usual functional ordered Ramsey
theorem supplies a **new carrier order**, not a guarantee that an
independently retained relation symbol named \`<\` agrees with it.

Therefore, to derive the literal survey theorem:
- Assume a distinguished \`ord:L.Symbol\` of arity 2 and \`ord∉U\`.
- Remove \`ord\` from the ordinary relation symbol sort while
  performing the U→function translation.
- Interpret \`ord\` in each source as its already fixed external
  \`LinearOrder\`. Reconstruct \`ord\` on the output carrier from the
  ordered Ramsey witness's \`LinearOrder\`.
- Prove the ordered embedding equivalence and the Ramsey-arrow
  equivalence, then apply the already checked
  \`Structure.orderedClosedGraphRamsey\`.

This avoids duplicated U-relations **and** duplicated order symbols.
No closure hull, ad hoc extra vertices, new transversality hypothesis,
or singleton-output assumption is permitted.

## 5. Formalization / review gates

1. Compile the tuple and encode/decode modules with the root
   \`CheckGenericUFunctionalDictionary.lean\` #print axioms commands.
2. Compile nonredundant full embedding iff U-closed relational embedding
   on arbitrary targets and prove composition/naturality.
3. Add a genuine \`(L,U,ord)\` ordered Ramsey theorem wrapper;
   do not cite the pre-existing functional special case as a
   complete proof of the printed quantifiers until this passes.
4. Update the survey marker only after an **exact-head Lean CI** and
   source-delta check. Do not restore author-removed TODOs.

Tracks C (ambient-relative local-completion) and D (strict
full-functional B-trees) remain independent.


## 6. Independent finite semantic regression (not a Lean certificate)

As a sanity check of the **nonredundant** function/relation dictionary,
I exhaustively enumerated **132,680** configurations with a single
designated relation of arity 2 or 3, source and target carriers of
sizes 1 or 2, and every injective map. For each configuration I
independently tested:

- the induced relational embedding condition (preserve **and reflect** R);
- the U-closedness condition on the image relative to each root tuple;
- exact equality of source/target set-valued function fibres under the map.

In all 132,680 configurations, \`(induced relational embedding AND
U-closed range) iff full set-valued-function embedding\` held. This also
covers zero/empty outputs, loops, repeated coordinates and arbitrary
multivalued fibres on two vertices. This finite enumeration does not
establish the general theorem, that the proposed Lean source compiles,
or the ordered Ramsey-arrow transfer; the root-level Lean checks and
exact-head CI remain mandatory.
