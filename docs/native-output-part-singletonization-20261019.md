# Transversal multivalued functions as singleton-valued output-part operations

**19 October 2026 — English proof and adversarial audit before Lean.**

This is the structural reduction most closely matching the user's
observation: the functional iterated partite construction and the
2019 U-closed construction present the same closure geometry.

The current true native partite System B has a fixed part
carrier P and genuinely set-valued functions F_B(x), satisfying

    y,z∈F_B(x) and part(y)=part(z) ⇒ y=z.

All intermediate native Pictures use the SAME output-part carrier P.

## Canonical output-part split

Replace every original function symbol F by one new function symbol
(F,q) for every output part q∈P, with unchanged arity. Define

    F_B^q(x) = {y∈F_B(x): part(y)=q}.

Keep all original relations, all vertices, and the SAME part map.

**Theorem A (singletonization):** every fibre F_B^q(x)
contains at most one value, by genuine function-output
transversality. No arbitrary linear ordering, ranking or
additional vertex labels are needed.

**Theorem B (exact reconstruction):** for every original F,x,y,

    y∈F_B(x)  iff  y∈F_B^{part(y)}(x),

and equivalently the original fibre is the union over
all part-indexed singleton fibres.

**Theorem C (closure):** for ANY exact vertex subset S of B,

    S is function-closed for the original multivalued structure
    iff S is function-closed for the split singleton structure.

Forward: each new output is an original output.
Reverse: each original value y belongs to the split
operation indexed by q=part(y), hence must stay inside S.

This equivalence uses no closure hull or rank change and
works for arbitrary positive arities, repeated inputs and
nullaries. The older 2019 closure-description formalization
requires positive arity to give proper nonempty roots, so
its use is separately restricted to that convention.

**Theorem D (full map functoriality):** if e:A↪B is a
FULL partite functional embedding, it induces a FULL
primitive function-language embedding between the
split singleton structures. Since e preserves PARTS,
the reflected target fibre for (F,q) cannot contain
an extra target value in part q not in e[F_A(x)].

**Theorem E (exact weak tests):** splitting commutes with
native weak restriction to ANY vertex subset S, in the
sense of pointwise equality of all original/part-indexed
function membership predicates on the same weak vertices.
The weak restriction can lose outputs, but cannot
invent an output in another part or merge two output
parts. No original active-domain root is silently
recomputed when later comparing with the induced
ambient 2019 tagged language: that comparison uses
the AMBIENT split structure, not the split of an
independently chosen target projection.

## Adversarial referee checks

1. **Transversality is essential.** Without it,
   F_B^q(x) could contain multiple vertices and the
   split would NOT be singleton-valued.
2. **Part-preserving maps are essential.** A generic
   full embedding of the reduct need not map q-values
   to q-values, so the split embedding theorem uses
   genuine partite embeddings.
3. **No rank bound or linear order.** This split
   is canonical and avoids the existing finite-order
   ranked singleton reduction's arbitrary ordering.
4. **Same part carrier across stages.** This holds
   for our iterated partite construction over fixed
   functional control D, not for unrelated functional
   systems with incompatible part universes.
5. **Original empty/undefined convention:** the
   current Set-valued partial functions interpret
   an empty fibre as undefined. A separately defined
   empty-valued operation in an Option(Set)
   presentation needs its independent domain bit;
   this split does NOT identify \`some ∅\` with \`none\`.
6. **Tree target compatibility remains open.**
   Singletonizing SOURCE operations does not force
   two arbitrary strict target B-tree completions to
   agree on a nonclosed weak common root. The
   verified K2 marked parity and C5 hard-root
   obstructions still apply.
7. **No alternative Picture.** We do NOT rerun
   the relational 2019 profile sparsening construction.
   The split is an internal, vertex-exact presentation
   of the SAME native partite Hales–Jewett stages.

## Next theorem interface

The output-part split allows us to apply the already verified
single-valued canonical full-root tag construction to each
native stage, for positive function arities. The native
closedness/2019 U-closedness dictionary (merged PR #426)
then applies to the split and, by Theorem C, is equivalent
to closure in the ORIGINAL multivalued functional stage.

Formally prove the singleton split, closure/reconstruction,
full embedding transport, and weak-membership bridge.
Then compare the actual native free attachments and
coordinate powers with those of the split language.
Only then attempt the protected target-root rank step;
no full n-pass \leanverified marker is justified yet.
