import PartiteConstruction.Iterated.ControlCompletionCompatible
import PartiteConstruction.Partite.InducedPicture

/-! # Coherent witnesses for tests contained in the Picture core

In the hard equal-cardinality case of the iterated Picture step, a tested set
may lie wholly in the power core.  Here no hereditary irreducibility of the
control structure is needed.

The partite projection is an induced embedding on every *whole* ambient
irreducible A-copy.  On a tested intersection lying in the core, this
projection factors through the current alpha : A -> D.  Hence the
intersection embeds canonically into A and then into B.  The resulting
one-copy B witness supplies exactly the embedded-intersection certificates
needed by compatible control completion.
-/
namespace StructuralRamsey.Partite.Iterated

open RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V P X Y : Type v}

/-- A test lying wholly in the core has a B-valued homomorphism-embedding
whose restriction to every ambient A-intersection is an induced embedding
contained in the irreducible copy eAB[A] of B. -/
theorem pureCore_embeddedWitness
    (A : RelStructure L U) (B : RelStructure L V) (D : RelStructure L P)
    (C₀ : Partite.System L P X) (α : RelStructure.Embedding A D)
    (E : Partite.System L U Y)
    (hA : A.Irreducible)
    (eAB : RelStructure.Embedding A B)
    (hE : E.IsPartiteOver A)
    (hC₁Partite :
      (Partite.Picture.build C₀ α.toFunctionEmbedding E).IsPartiteOver D)
    (Test : Finset (Partite.Picture.Vertex C₀ α.toFunctionEmbedding E))
    (hcore :
      ∀ z : ↥(↑Test : Set (Partite.Picture.Vertex C₀ α.toFunctionEmbedding E)),
        ∃ w : Y,
          z.1 =
            Partite.Picture.coreEmbedding
              C₀ α.toFunctionEmbedding E w) :
    let C₁ := Partite.Picture.build C₀ α.toFunctionEmbedding E
    let TestSet : Set (Partite.Picture.Vertex C₀ α.toFunctionEmbedding E) :=
      ↑Test
    let Small := C₁.toRelStructure.induce TestSet
    ∃ f : ↥TestSet → V,
      Small.IsHomomorphismEmbedding B f ∧
      RelStructure.LocallyTreeLike.EmbeddedIntersections
        (A := A) (C := C₁.toRelStructure) (T := B) Test f := by
  classical
  let αf := α.toFunctionEmbedding
  let Core := E.relabel αf
  let C₁ := Partite.Picture.build C₀ αf E
  let Tset : Set (Partite.Picture.Vertex C₀ αf E) := ↑Test
  let Small := C₁.toRelStructure.induce Tset
  let smallIncl : RelStructure.Embedding Small C₁.toRelStructure :=
    RelStructure.inclusion C₁.toRelStructure Tset
  let coreEmb : Partite.Embedding Core C₁ :=
    Partite.Picture.coreEmbedding C₀ αf E
  let eCore : RelStructure.Embedding Small Core.toRelStructure :=
    smallIncl.factorThroughRange coreEmb.toEmbedding hcore
  have heCore (z : Tset) :
      smallIncl z = coreEmb.toEmbedding (eCore z) := by
    exact Classical.choose_spec (hcore z)

  let toA : Tset → U := fun z => E.part (eCore z)
  have hToA : Small.IsHomomorphismEmbedding A toA := by
    change Small.IsHomomorphismEmbedding A (E.part ∘ eCore)
    have hCoreToA :
        Core.toRelStructure.IsHomomorphismEmbedding A E.part := by
      change E.toRelStructure.IsHomomorphismEmbedding A E.part
      exact hE
    exact hCoreToA.comp eCore.isHomomorphismEmbedding

  let f : Tset → V := fun z => eAB (toA z)
  have hf : Small.IsHomomorphismEmbedding B f := by
    change Small.IsHomomorphismEmbedding B (eAB ∘ toA)
    exact eAB.isHomomorphismEmbedding.comp hToA

  refine ⟨f, hf, ?_⟩
  intro γ
  obtain ⟨γD, hγD⟩ :=
    hC₁Partite.after_irreducible_embedding hA γ
  let Hset : Set U := {a : U | γ a ∈ Test}
  let γDH : RelStructure.Embedding (A.induce Hset) D :=
    γD.comp (RelStructure.inclusion A Hset)
  have hRange :
      ∀ x : Hset, ∃ a : U, γDH x = α a := by
    intro x
    let z : Tset := ⟨γ x.1, x.2⟩
    refine ⟨E.part (eCore z), ?_⟩
    calc
      γDH x = γD x.1 := rfl
      _ = C₁.part (γ x.1) := hγD x.1
      _ = C₁.part (coreEmb (eCore z)) := by
        exact congrArg C₁.part (heCore z)
      _ = Core.part (eCore z) := coreEmb.map_part (eCore z)
      _ = α (E.part (eCore z)) := rfl
  let eHA : RelStructure.Embedding (A.induce Hset) A :=
    γDH.factorThroughRange α hRange
  let eHB : RelStructure.Embedding (A.induce Hset) B :=
    eAB.comp eHA

  have heHB :
      ∀ x : Hset, eHB x = f ⟨γ x.1, x.2⟩ := by
    intro x
    let z : Tset := ⟨γ x.1, x.2⟩
    change eAB (eHA x) = eAB (E.part (eCore z))
    apply congrArg eAB
    apply α.injective
    have hfactor : γDH x = α (eHA x) :=
      Classical.choose_spec (hRange x)
    calc
      α (eHA x) = γDH x := hfactor.symm
      _ = γD x.1 := rfl
      _ = C₁.part (γ x.1) := hγD x.1
      _ = C₁.part (coreEmb (eCore z)) := by
        exact congrArg C₁.part (heCore z)
      _ = Core.part (eCore z) := coreEmb.map_part (eCore z)
      _ = α (E.part (eCore z)) := rfl

  have hcHB : eHB.ContainedInIrreducible := by
    apply RelStructure.Embedding.containedInIrreducible_of_range_subset
      hA eAB eHB
    intro x
    exact ⟨eHA x, rfl⟩

  exact ⟨eHB, heHB, hcHB⟩

end StructuralRamsey.Partite.Iterated
