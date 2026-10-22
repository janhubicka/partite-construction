import PartiteConstruction.Functional.WholeMaskPartialDecode2019
import PartiteConstruction.Structure.PartialSetFunctionsWholeMaskPatterns
import PartiteConstruction.Structure.PartialSetFunctionsClosed

/-!
# Source-defined genuine partial projections preserve complete OLD masks

A positive original-2019 partial homomorphism already preserves every
DEFINED source Option(Set) fibre as the entire image of that fibre.
If it also respects the part map and is injective on EACH active OLD
distinct-input root, then its canonical whole-mask relational graph
interpretation is a positive relational homomorphism.

This is the exact complement of OLD-homomorphism-to-original-partial
decoding: both directions need the same complete value semantics, but
no reflection of source-undefined domains is requested. Arbitrary
positive homomorphisms are NOT enough to preserve OLD distinct root
injectivity. That additional property corresponds to protecting
irreducible source roots in the real partite stage.

The theorem preserves zero-length output sets, repeated primitive
inputs and nullary symbols. It does not close any weak carrier or
produce the missing strict B-tree mixed target completion.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey.RelStructure
open StructuralRamsey.Structure

universe u v w z
variable {L : Language.{u}} {P : Type z} [Fintype P]
variable {V : Type v} {W : Type w}

/-- A source-defined partial homomorphism sends complete OLD values
exactly to complete OLD values in the control, assuming that every
active distinct-input root remains injective after projection and
the part of each output is preserved. No domain reflection. -/
theorem IsOriginalPartialHomomorphism.wholeMaskPatternGraph_hom
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    {f : V → W}
    (hf : IsOriginalPartialHomomorphism A B f)
    (partA : V → P) (partB : W → P)
    (hPart : ∀ x : V, partB (f x) = partA x)
    (hRoots : ∀ (p : Language.FunctionInputPattern L)
      (q : Language.CompleteOutputParts P)
      (root : Fin p.rootSize → V),
      (A.wholeMaskPatternGraph partA).rel
        (.inr (.inl (p,q))) root →
      Function.Injective (f ∘ root)) :
    (A.wholeMaskPatternGraph partA).IsHomomorphism
      (B.wholeMaskPatternGraph partB) f := by
  classical
  have hPartsImage (U : Set V) :
      partB '' Structure.imageSet f U = partA '' U := by
    ext q
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (hPart x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨f x, ⟨x, hx, rfl⟩, hPart x⟩
  intro R t ht
  rcases R with R | R
  · exact hf.1 R t ht
  rcases R with pq | pq
  · rcases pq with ⟨p,q⟩
    have hInjective : Function.Injective (f ∘ t) :=
      hRoots p q t ht
    change Function.Injective t ∧
      ∃ U : Set V,
        A.func p.symbol (t ∘ p.argMap) = some U ∧
        partA '' U = Set.range q.label at ht
    obtain ⟨_,U,hVal,hMask⟩ := ht
    have hTarget : B.func p.symbol (f ∘ (t ∘ p.argMap)) =
        some (Structure.imageSet f U) :=
      hf.2 p.symbol (t ∘ p.argMap) U hVal
    change Function.Injective (f ∘ t) ∧
      ∃ T : Set W,
        B.func p.symbol ((f ∘ t) ∘ p.argMap) = some T ∧
        partB '' T = Set.range q.label
    refine ⟨hInjective, Structure.imageSet f U, ?_, ?_⟩
    · have hInputEq :
          ((f ∘ t) ∘ p.argMap) = f ∘ (t ∘ p.argMap) := by
        funext i
        rfl
      rw [hInputEq]
      exact hTarget
    · rw [hPartsImage, hMask]
  · rcases pq with ⟨p,q⟩
    let root : Fin p.rootSize → V :=
      fun i => t (Fin.castAdd q.size i)
    have hDomain : (A.wholeMaskPatternGraph partA).rel
        (.inr (.inl (p,q))) root :=
      A.wholeMaskPatternGraph_output_has_domain partA p q t ht
    have hInjective : Function.Injective (f ∘ root) :=
      hRoots p q root hDomain
    have hValue : A.func p.symbol (root ∘ p.argMap) =
        some (Set.range (fun j : Fin q.size =>
          t (Fin.natAdd p.rootSize j))) := ht.2.1
    have hTarget : B.func p.symbol
        (f ∘ (root ∘ p.argMap)) =
        some (Structure.imageSet f
          (Set.range (fun j : Fin q.size =>
            t (Fin.natAdd p.rootSize j)))) :=
      hf.2 p.symbol (root ∘ p.argMap) _ hValue
    have hOutputs : Structure.imageSet f
        (Set.range (fun j : Fin q.size =>
          t (Fin.natAdd p.rootSize j))) =
        Set.range (fun j : Fin q.size =>
          f (t (Fin.natAdd p.rootSize j))) := by
      ext y
      constructor
      · rintro ⟨x, ⟨j, rfl⟩, rfl⟩
        exact ⟨j,rfl⟩
      · rintro ⟨j,rfl⟩
        exact ⟨t (Fin.natAdd p.rootSize j), ⟨j,rfl⟩,rfl⟩
    change
      Function.Injective
        (fun i : Fin p.rootSize =>
          (f ∘ t) (Fin.castAdd q.size i)) ∧
      B.func p.symbol
        ((fun i : Fin p.rootSize =>
          (f ∘ t) (Fin.castAdd q.size i)) ∘ p.argMap) =
        some (Set.range (fun j : Fin q.size =>
          (f ∘ t) (Fin.natAdd p.rootSize j))) ∧
      (∀ j : Fin q.size,
        partB ((f ∘ t) (Fin.natAdd p.rootSize j)) = q.label j)
    refine ⟨hInjective, ?_, ?_⟩
    · have hInputEq :
          ((fun i : Fin p.rootSize =>
            (f ∘ t) (Fin.castAdd q.size i)) ∘ p.argMap) =
            f ∘ (root ∘ p.argMap) := by
          funext i
          rfl
      rw [hInputEq]
      exact hTarget.trans (congrArg some hOutputs)
    · intro j
      exact (hPart (t (Fin.natAdd p.rootSize j))).trans (ht.2.2 j)

end StructuralRamsey.PartialSetStructure
