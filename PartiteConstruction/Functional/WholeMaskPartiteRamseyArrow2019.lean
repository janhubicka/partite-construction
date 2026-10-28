import PartiteConstruction.Functional.WholeMaskPartPreservingEmbeddingEquiv2019
import PartiteConstruction.Ramsey.Basic

/-!
# Ramsey arrows are equivalent under the full part-labelled mask encoding

For genuinely partial Option(Set) operations, every source vertex part
is encoded by an independent unary relation before taking the complete
OLD mask graph. The already checked canonical full embedding
equivalence is therefore literally the identity on underlying maps,
including isolated vertices and defined-empty operations.

We show it also COMMUTES WITH COMPOSITION. This is the precise
combinatorial ingredient needed to transfer a Ramsey arrow between
the true part-preserving functional embeddings and the ordinary
relational embeddings used by the verified 2019 two-pass profile proof.

This theorem is about CANONICAL sources and targets. It does not
assume an intermediate relational Picture decodes to a partial
function. The final target requires the separate closed B-copy
decoder and part predicates.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V W X : Type v}

namespace Embedding

/-- Image of a complete output set through a composition of maps,
with no injectivity or nonemptiness assumptions. -/
private theorem imageSet_comp (f : V → W) (g : W → X) (S : Set V) :
    Structure.imageSet (g ∘ f) S =
      Structure.imageSet g (Structure.imageSet f S) := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨f x,⟨x,hx,rfl⟩,rfl⟩
  · rintro ⟨z,⟨x,hx,rfl⟩,rfl⟩
    exact ⟨x,hx,rfl⟩

/-- Full genuine partial-function embeddings compose without changing
the states none and some-empty or discarding any value coordinates. -/
def comp {A : PartialSetStructure L V}
    {B : PartialSetStructure L W} {C : PartialSetStructure L X}
    (g : Embedding B C) (f : Embedding A B) : Embedding A C where
  toFun := g.toFun ∘ f.toFun
  injective := g.injective.comp f.injective
  map_rel_iff := by
    intro R xs
    calc
      C.rel R ((g.toFun ∘ f.toFun) ∘ xs) ↔
          B.rel R (f.toFun ∘ xs) := by
        simpa only [Function.comp_assoc] using
          (g.map_rel_iff R (f.toFun ∘ xs))
      _ ↔ A.rel R xs := f.map_rel_iff R xs
  map_func := by
    intro F xs
    have hf := f.map_func F xs
    have hg := g.map_func F (f.toFun ∘ xs)
    calc
      (A.func F xs).map (Structure.imageSet (g.toFun ∘ f.toFun)) =
        ((A.func F xs).map (Structure.imageSet f.toFun)).map
          (Structure.imageSet g.toFun) := by
        cases hv : A.func F xs with
        | none => rfl
        | some S =>
            simpa [hv] using
              congrArg some (imageSet_comp f.toFun g.toFun S)
      _ = (B.func F (f.toFun ∘ xs)).map
          (Structure.imageSet g.toFun) := by rw [hf]
      _ = C.func F ((g.toFun ∘ f.toFun) ∘ xs) := by
        simpa only [Function.comp_assoc] using hg

end Embedding

namespace PartPreservingEmbedding

variable {A : PartialSetStructure L V}
variable {B : PartialSetStructure L W}
variable {C : PartialSetStructure L X}
variable {partA : V → P} {partB : W → P} {partC : X → P}

/-- Composition of genuinely FULL partite embeddings on the same
underlying vertices, without any new closure operation. -/
def comp (g : PartPreservingEmbedding B partB C partC)
    (f : PartPreservingEmbedding A partA B partB) :
    PartPreservingEmbedding A partA C partC :=
  ⟨g.1.comp f.1, by
    intro x
    change partC (g.1.toFun (f.1.toFun x)) = partA x
    rw [g.2 (f.1.toFun x),f.2 x]⟩

/-- The already verified full OLD encoding preserves the actual
composition of two part-preserving genuine partial function maps. -/
theorem encode_comp
    (g : PartPreservingEmbedding B partB C partC)
    (f : PartPreservingEmbedding A partA B partB) :
    (g.comp f).encode = g.encode.comp f.encode := by
  apply RelStructure.Embedding.ext
  intro x
  rfl

end PartPreservingEmbedding

/-- Ramsey property defined on TRUE full, part-preserving, genuinely
partial function embeddings; neither undefinedness nor the empty
defined function value is erased. -/
def PartPreservingArrow
    (A : PartialSetStructure L V) (partA : V → P)
    (B : PartialSetStructure L W) (partB : W → P)
    (C : PartialSetStructure L X) (partC : X → P)
    (κ : Type*) : Prop :=
  ∀ χ : PartPreservingEmbedding A partA C partC → κ,
    ∃ f : PartPreservingEmbedding B partB C partC,
      ∀ a₁ a₂ : PartPreservingEmbedding A partA B partB,
        χ (f.comp a₁) = χ (f.comp a₂)

/-- Exact equivalence of the genuine partial-function PARTITE Ramsey
arrow and the OLD unary-part-labelled complete-mask RELATIONAL arrow.
The same vertices, embeddings and composition equations are used.

This does not require functional coherence of an arbitrary
intermediate U-closed picture: it compares the canonical sources and
canonical witnesses only. -/
theorem partPreservingArrow_iff_withPartsWholeMaskOld
    (A : PartialSetStructure L V) (partA : V → P)
    (B : PartialSetStructure L W) (partB : W → P)
    (C : PartialSetStructure L X) (partC : X → P)
    [Finite V] [Finite W] [Finite X]
    (hA : FibreTransversal A partA)
    (hB : FibreTransversal B partB)
    (hC : FibreTransversal C partC) (κ : Type*) :
    PartPreservingArrow A partA B partB C partC κ ↔
      StructuralRamsey.Arrow
        (withPartsWholeMaskOld A partA)
        (withPartsWholeMaskOld B partB)
        (withPartsWholeMaskOld C partC) κ := by
  classical
  let eAB := PartPreservingEmbedding.encodingEquiv
    (A := A) (B := B) (partA := partA) (partB := partB) hA hB
  let eBC := PartPreservingEmbedding.encodingEquiv
    (A := B) (B := C) (partA := partB) (partB := partC) hB hC
  let eAC := PartPreservingEmbedding.encodingEquiv
    (A := A) (B := C) (partA := partA) (partB := partC) hA hC
  have hNatural (g : PartPreservingEmbedding B partB C partC)
      (a : PartPreservingEmbedding A partA B partB) :
      eAC (g.comp a) = (eBC g).comp (eAB a) := by
    apply RelStructure.Embedding.ext
    intro x
    rfl
  constructor
  · intro hArrow χ
    obtain ⟨f,hf⟩ := hArrow (fun a => χ (eAC a))
    refine ⟨eBC f, ?_⟩
    intro a₁ a₂
    let f₁ : PartPreservingEmbedding A partA B partB := eAB.symm a₁
    let f₂ : PartPreservingEmbedding A partA B partB := eAB.symm a₂
    have h1 : eAB f₁ = a₁ := eAB.apply_symm_apply a₁
    have h2 : eAB f₂ = a₂ := eAB.apply_symm_apply a₂
    have hnat₁ : eAC (f.comp f₁) = (eBC f).comp a₁ := by
      rw [← h1]
      exact hNatural f f₁
    have hnat₂ : eAC (f.comp f₂) = (eBC f).comp a₂ := by
      rw [← h2]
      exact hNatural f f₂
    rw [← hnat₁, ← hnat₂]
    exact hf f₁ f₂
  · intro hArrow χ
    obtain ⟨f,hf⟩ := hArrow (fun a => χ (eAC.symm a))
    let g : PartPreservingEmbedding B partB C partC := eBC.symm f
    refine ⟨g, ?_⟩
    intro a₁ a₂
    have hgf : eBC g = f := eBC.apply_symm_apply f
    have hnat (a : PartPreservingEmbedding A partA B partB) :
        eAC (g.comp a) = f.comp (eAB a) := by
      rw [← hgf]
      exact hNatural g a
    have hχ (a : PartPreservingEmbedding A partA B partB) :
        χ (g.comp a) = χ (eAC.symm (f.comp (eAB a))) := by
      calc
        χ (g.comp a) =
            χ (eAC.symm (eAC (g.comp a))) :=
          congrArg χ (eAC.symm_apply_apply (g.comp a)).symm
        _ = χ (eAC.symm (f.comp (eAB a))) :=
          congrArg χ (congrArg eAC.symm (hnat a))
    rw [hχ a₁, hχ a₂]
    exact hf (eAB a₁) (eAB a₂)

end StructuralRamsey.PartialSetStructure
