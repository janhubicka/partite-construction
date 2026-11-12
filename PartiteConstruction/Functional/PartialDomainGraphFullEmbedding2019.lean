import PartiteConstruction.Functional.PartialDomainGraphExactHom2019

/-!
# Track A: full partial-function embeddings versus induced domain/output graphs

The independent domain/output relational encoding admits an exact
full-embedding dictionary only with an output-fibre condition.

Every genuine full functional embedding gives an induced embedding of
the domain/output relational structures. Conversely an induced
relational embedding plus the condition that target function outputs
over source-defined tuples come from actual source values reconstructs
a genuine full `Option (Set)` embedding on the SAME underlying map.

The induced relational embedding reflects which input tuples are
defined; the extra output condition supplies equality of the entire
value set, including `some ∅`. This distinction is essential when
using ordinary induced relational copies in a partite argument.

Nothing here asserts an arbitrary (L,U) completion or a functional
B-tree theorem.
-/

namespace StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {V : Type v} {W : Type w}
variable {A : PartialSetStructure L V} {B : PartialSetStructure L W}

namespace Embedding

/-- A FULL partial-function embedding induces an ordinary relational
embedding of the independent domain-and-output graph, on the same map.
In particular it reflects the operation-domain predicate, unlike a
mere source-defined homomorphism. -/
def domainGraph (e : Embedding A B) :
    RelStructure.Embedding
      (PartialSetStructure.domainGraph A)
      (PartialSetStructure.domainGraph B) where
  toFun := e.toFun
  injective := e.injective
  map_rel_iff := by
    intro symbol x
    cases symbol with
    | inl R =>
        exact e.map_rel_iff R x
    | inr symbol =>
        cases symbol with
        | inl F =>
            change B.Defined F (e.toFun ∘ x) ↔ A.Defined F x
            cases hA : A.func F x with
            | none =>
                have hB : B.func F (e.toFun ∘ x) = none := by
                  simpa [hA] using (e.map_func F x).symm
                constructor
                · rintro ⟨T, hT⟩
                  rw [hB] at hT
                  cases hT
                · rintro ⟨U, hU⟩
                  rw [hA] at hU
                  cases hU
            | some U =>
                constructor
                · intro _
                  exact ⟨U, hA⟩
                · intro _
                  refine ⟨Structure.imageSet e.toFun U, ?_⟩
                  simpa [hA] using (e.map_func F x).symm
        | inr F =>
            let xs : Fin (L.funcArity F) → V :=
              fun i => x i.castSucc
            let y : V := x (Fin.last (L.funcArity F))
            change B.HasOutput F (e.toFun ∘ xs) (e.toFun y) ↔
              A.HasOutput F xs y
            cases hA : A.func F xs with
            | none =>
                have hB : B.func F (e.toFun ∘ xs) = none := by
                  simpa [hA] using (e.map_func F xs).symm
                constructor
                · rintro ⟨T, hT, _⟩
                  rw [hB] at hT
                  cases hT
                · rintro ⟨U, hU, _⟩
                  rw [hA] at hU
                  cases hU
            | some U =>
                have hB : B.func F (e.toFun ∘ xs) =
                    some (Structure.imageSet e.toFun U) := by
                  simpa [hA] using (e.map_func F xs).symm
                constructor
                · rintro ⟨T, hT, hy⟩
                  have hTU : T = Structure.imageSet e.toFun U :=
                    Option.some.inj (hT.symm.trans hB)
                  have hImage : e.toFun y ∈
                      Structure.imageSet e.toFun U := by
                    simpa only [hTU] using hy
                  obtain ⟨z, hz, hzy⟩ := hImage
                  exact ⟨U, hA, (e.injective hzy) ▸ hz⟩
                · rintro ⟨T, hT, hy⟩
                  have hTU : T = U :=
                    Option.some.inj (hT.symm.trans hA)
                  have hyU : y ∈ U := by
                    simpa only [hTU] using hy
                  exact ⟨Structure.imageSet e.toFun U, hB, ⟨y, hyU, rfl⟩⟩

/-- Full embeddings have no extra target outputs over a defined input. -/
theorem noExtraTargetOutputsOnDefined (e : Embedding A B) :
    NoExtraTargetOutputsOnDefined A B e.toFun := by
  intro F xs U hU y hy
  obtain ⟨T, hT, hyT⟩ := hy
  have hB : B.func F (e.toFun ∘ xs) =
      some (Structure.imageSet e.toFun U) := by
    simpa [hU] using (e.map_func F xs).symm
  have hTU : T = Structure.imageSet e.toFun U :=
    Option.some.inj (hT.symm.trans hB)
  simpa only [hTU] using hyT

/-- An induced embedding of domain/output graphs need not be a full
functional embedding if the target adds outputs outside the range.
The exact missing hypothesis is no extra target output over any
source-defined input. On SOURCE-UNDEFINED inputs, the induced graph
embedding's reflected domain predicate already rules out a new
defined target application. -/
def ofDomainGraphNoExtra
    (g : RelStructure.Embedding
      (PartialSetStructure.domainGraph A)
      (PartialSetStructure.domainGraph B))
    (hExtra : NoExtraTargetOutputsOnDefined A B g.toFun) :
    Embedding A B where
  toFun := g.toFun
  injective := g.injective
  map_rel_iff R xs := g.map_rel_iff (.inl R) xs
  map_func := by
    intro F xs
    have hMap :
        (PartialSetStructure.domainGraph A).IsHomomorphism
          (PartialSetStructure.domainGraph B) g.toFun := by
      intro R x h
      exact (g.map_rel_iff R x).mpr h
    have hPartial : IsOriginalPartialHomomorphism A B g.toFun :=
      (originalPartialHom_iff_domainGraphHom_and_noExtra A B g.toFun).mpr
        ⟨hMap, hExtra⟩
    cases hA : A.func F xs with
    | none =>
        have hB : B.func F (g.toFun ∘ xs) = none := by
          cases ht : B.func F (g.toFun ∘ xs) with
          | none => exact ht
          | some T =>
              have hDomain : (PartialSetStructure.domainGraph B).rel
                  (.inr (.inl F)) (g.toFun ∘ xs) := ⟨T, ht⟩
              have hSource := (g.map_rel_iff (.inr (.inl F)) xs).mp
                hDomain
              obtain ⟨U, hU⟩ := hSource
              rw [hA] at hU
              cases hU
        simpa only [hA, Option.map_none] using hB.symm
    | some U =>
        have hB := hPartial.2 F xs U hA
        simpa only [hA, Option.map_some] using hB.symm

end Embedding

/-- Exact map-level FULL-embedding dictionary. Both sides use the same
vertices and function, not a closure hull or an enlarged target. -/
theorem fullEmbedding_iff_domainGraphEmbedding_noExtra
    (A : PartialSetStructure L V) (B : PartialSetStructure L W)
    (f : V → W) :
    (∃ e : Embedding A B, e.toFun = f) ↔
      (∃ g : RelStructure.Embedding
        (PartialSetStructure.domainGraph A)
        (PartialSetStructure.domainGraph B), g.toFun = f) ∧
      NoExtraTargetOutputsOnDefined A B f := by
  constructor
  · rintro ⟨e, he⟩
    subst f
    exact ⟨⟨e.domainGraph, rfl⟩, e.noExtraTargetOutputsOnDefined⟩
  · rintro ⟨⟨g, hg⟩, hExtra⟩
    subst f
    exact ⟨Embedding.ofDomainGraphNoExtra g hExtra, rfl⟩

end StructuralRamsey.PartialSetStructure
