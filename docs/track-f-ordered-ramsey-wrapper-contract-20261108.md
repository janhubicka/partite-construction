# Track F — exact ordered `(L,U)` wrapper: English proof and adversarial contract

**Date:** 8 November 2026. **Status:** English argument; Lean components staged
in separate drafts [#563](https://github.com/janhubicka/partite-construction/pull/563)
(nonredundant U-functional dictionary), [#577](https://github.com/janhubicka/partite-construction/pull/577)
(named-order deletion/restoration), and this stacked PR (unoriented arrow **iff**).
**Do not mark the printed survey `thm:models2` green until the combined exact
Lean wrapper compiles and its full theorem type is audited.**

## Original theorem contract

Let `L` be **any** relational signature with a distinguished symbol `ord`
of arity exactly 2. Let `U` be any family of symbols such that `ord ∉ U`
and each `R∈U` has arity at least 2. For any finite `L`-structures `A,B`
on linearly ordered carriers, with `ord` interpreted **exactly** as the strict
linear order, there is a finite ordered `L`-structure `C` such that every
two-colouring of **induced relational embeddings with U-closed range**
`A→C` has a monochromatic U-closed embedding `B→C`.
There is no irreducibility or `B`-closedness assumption.

The proof must not add symbols to an arbitrary target witness which could
be interpreted inconsistently. It must preserve the original carrier, empty
output sets, non-U relations (including nullary), repeated tuple coordinates,
and literal map composition.

## Reduction and witness

1. Define `L− = {R∈L : R≠ord}` with original arities and
   `U−={R∈L−:R∈U}`. Since `ord∉U`, the restriction `U≃U−` is bijective,
   preserving arities. The renamed **mixed** language is
   `M.RelSymbol={R∈L−:R∉U−}` and
   `M.FuncSymbol=U−`, with `funcArity R=arity(R)−1≥1`.
   **Neither** `ord` nor any `U`-relation appears as a second independent
   relational symbol in `M`.
2. Encode an ordered source `A` as an `M`-structure `F(A)` on its
   **original vertex carrier**: retain each non-`U`, non-order relation,
   set `F_R(\bar a)={y:R^A(\bar a,y)}`, and keep the **external**
   `LinearOrder` rather than the original named-order relation.
   This representation admits defined empty fibres and all repeated
   coordinates.
3. Apply the already verified positive-function-arity theorem
   `StructuralRamsey.Structure.orderedRamsey` to `F(A),F(B),Fin 2`.
   It yields a finite carrier `X` with an external strict linear order
   and an **arbitrary** mixed `M`-structure `C_F`, with a genuine
   full-embedding Ramsey arrow for the canonical ordered expansions.
4. Decode `C_F`: recover every `R∈U` by
   `R(\bar x,y) ⟺ y∈F_R^{C_F}(\bar x)`; copy the other non-order
   relations verbatim, and interpret `ord(x,y) ⟺ x<y` using the
   **external witness order**. Call this structure `C`. Every mixed
   witness is decodable, without requiring an extra coherence hypothesis.

## Embedding dictionary — proof

For an arbitrary functional target `C_F` and correctly ordered original
source `A`, compare the literal underlying injections

`e : A ↪ decode(C_F)` whose image is U-closed, and

`e : F(A).withLinearOrder ↪ C_F.withLinearOrder` which preserve all
function value **sets** exactly.

For `R∈U`, U-closedness and inducedness imply both inclusions:

- `e[F_R^A(\bar a)] ⊆ F_R^{C_F}(e\bar a)` follows by relation preservation.
- If `y∈F_R^{C_F}(e\bar a)`, all root coordinates lie in the range
  of `e`, so U-closedness gives `y=e(z)`. Reflection of the original
  relation shows `z∈F_R^A(\bar a)`.

Conversely, equality of entire output sets immediately yields image
U-closedness; injectivity and membership then give reflection of every
distinguished `R`. All other relations agree by construction. The
named order agrees **precisely** when the reduced map is strictly monotone,
which is exactly the extra relation of the canonical ordered expansion.

The two constructions preserve the **same injection**. They are inverse
by embedding extensionality, and they commute with composition because
compositions of the actual vertex maps agree pointwise. This also handles
empty A/B and empty fibres.

**Necessary bridge between the parallel Lean conventions:** the
original range-set condition `IsUClosedSetOn B U (Set.range e)` from #577
is equivalent, for induced relational `e`, to the source-fibre
condition `IsUClosedEmbedding A B U hU e` from #563. To prove
range-set⇒source-fibre use a given root `\bar a`, choose the last
coordinate in the range, then reflect the tuple; to prove the reverse
choose source preimages of each of the finitely many root coordinates
of an arbitrary target tuple, apply source-fibre U-closedness and conclude
the output is in the range. This is a **distinct named Lean obligation**,
not a definitional equality, and must be proven before the final theorem.

## Colour and arrow transfer

Let `E_A(C)` and `E_B(C)` denote the resulting embedding-type
equivalences into the arbitrary target. Given
`χ : Emb_U(A,C)→Fin 2`, colour a full functional A-embedding `g`
by `χ(E_A(C)^{-1}(g))`. The already verified functional Ramsey arrow
yields `f:F(B)↪C_F` with all full A-subcopies monochromatic.
Set `\bar f=E_B(C)^{-1}(f)`. For each U-closed
`e:A↪B`, use its full functional image `F(e)`.
The composites `E_A(C)^{-1}(f∘F(e))` and `\bar f∘e` have exactly
the same vertex map and both are U-closed relational embeddings;
hence they coincide. Therefore `\bar f` is a genuine monochromatic
U-closed B-embedding in `C`.

**Adversarial exclusions:**

- Merely copying `ord` into `M` is incorrect for an arbitrary target;
  a witness could interpret it differently from its external `LinearOrder`.
- Retaining an independent `R∈U` relation as well as `F_R` is incorrect
  for arbitrary targets; an inconsistent witness may introduce or remove
  embeddings upon decoding.
- Replacing set-valued `F_R` by a single output would fail when a root has
  multiple last-coordinate witnesses.
- Weakening induced embeddings to one-way homomorphisms invalidates the
  reflection used above.
- Arity-one `U` relations would produce nullary functions; the verified
  `orderedRamsey` only supports positive input arities.
- The established generic unpartite arrow does **not** alone prove the
  survey's intermediate partite-power/Picture/half-closed lemmas under
  arbitrary `(L,U)`. These require separate partite-system and
  attachment naturality checks (issue #558).
- A source with a merely acyclic, rather than *exactly equal*, named
  order does not satisfy the order-embedding equivalence.

## Machine-checking gate

A complete named Lean theorem must quantify over **original** arbitrary
relational `L,ord,U,A,B`, with no extra hypothesis other than the stated
order correctness, `ord∉U`, `arity(ord)=2`, `∀R∈U,arity(R)≥2`,
and finiteness of the carriers. It must return an original relational `C`
whose named order equals the strict witness order and the actual
two-colour original `U`-closed Ramsey arrow.

Run exact-head full Lean compilation, the root `#print axioms` checks,
and compare the **elaborated final type** with this contract. Keep the
survey's frozen prose, markers and existing TODO decisions untouched
until all gates pass.
