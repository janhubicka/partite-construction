import PartiteConstruction.Functional.WholeMaskFullEmbeddingFromCovered2019
import PartiteConstruction.Functional.WholeMaskProjectionOldHom2019

/-!
# Full part-preserving genuinely partial embeddings give full OLD mask embeddings

For complete-mask genuinely partial Option(Set) structures, every FULL
function embedding preserves and reflects the independent domain masks
and the COMPLETE output tuple relations, assuming it preserves output
part labels. The proof uses the ENTIRE Option(Set) value, not one
output-incidence at a time.

This is the source-to-relational half of the full-embedding
correspondence used by the verified two-pass 2019 Ramsey construction.
The reverse half for a normalized relational target was already
proved in WholeMaskFullEmbeddingFromCovered2019.

Crucially, the part-preservation premise is explicit: an isolated
vertex has no complete-value tuple recording its assigned part.
No weak source subset is enlarged, and defined-empty (some empty)
is not confused with undefined (none).
-/

namespace StructuralRamsey.PartialSetStructure.Embedding

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.Structure

universe u v w z
variable {L : Language.{u}} {P : Type z} [Fintype P]
variable {V : Type v} {W : Type w}
variable {A : PartialSetStructure L V} {B : PartialSetStructure L W}

/-- Injective vertex maps induce injective maps of ENTIRE vertex sets. -/
private theorem imageSet_injective (f : V → W) (hf : Function.Injective f) :
    Function.Injective (Structure.imageSet f) := by
  intro S T h
  ext x
  have hMem (U : Set V) :
      f x ∈ Structure.imageSet f U ↔ x ∈ U := by
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hEq : y = x := hf hxy
      simpa [hEq] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  calc
    x ∈ S ↔ f x ∈ Structure.imageSet f S := (hMem S).symm
    _ ↔ f x ∈ Structure.imageSet f T := by rw [h]
    _ ↔ x ∈ T := hMem T

/-- Every full part-preserving genuinely partial function embedding
lifts to an induced/full OLD complete-mask relational embedding on the
SAME vertices. The reflected domain relation is genuinely partial:
none in the source cannot correspond to some empty in the target.

This implication handles repeated function arguments, multivalued
transversal fibres, defined-empty fibres and nullary functions.
Neither fibre transversality nor finiteness is required to prove
preservation of a given already-existing complete OLD relation. -/
def wholeMaskPatternGraph
    (e : Embedding A B)
    (partA : V → P) (partB : W → P)
    (hPart : ∀ x : V, partB (e.toFun x) = partA x) :
    RelStructure.Embedding
      (A.wholeMaskPatternGraph partA)
      (B.wholeMaskPatternGraph partB) where
  toFun := e.toFun
  injective := e.injective
  map_rel_iff := by
    classical
    have hPartImage (U : Set V) :
        partB '' Structure.imageSet e.toFun U = partA '' U := by
      ext p
      constructor
      · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, (hPart x).symm⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨e.toFun x, ⟨x, hx, rfl⟩, hPart x⟩
    intro R t
    rcases R with R | R
    · exact e.map_rel_iff R t
    rcases R with pq | pq
    · rcases pq with ⟨p,q⟩
      have hInputEq :
          ((e.toFun ∘ t) ∘ p.argMap) = e.toFun ∘ (t ∘ p.argMap) := by
        funext i
        rfl
      change
        (Function.Injective (e.toFun ∘ t) ∧
          ∃ U : Set W,
            B.func p.symbol ((e.toFun ∘ t) ∘ p.argMap) = some U ∧
              partB '' U = Set.range q.label) ↔
        (Function.Injective t ∧
          ∃ T : Set V,
            A.func p.symbol (t ∘ p.argMap) = some T ∧
              partA '' T = Set.range q.label)
      constructor
      · rintro ⟨hInj, U, hValue, hLabel⟩
        have hSourceInj : Function.Injective t := by
          intro i j hij
          apply hInj
          exact congrArg e.toFun hij
        cases hA : A.func p.symbol (t ∘ p.argMap) with
        | none =>
            have hMap := e.map_func p.symbol (t ∘ p.argMap)
            rw [hA] at hMap
            change (none : Option (Set W)) =
                B.func p.symbol (e.toFun ∘ (t ∘ p.argMap)) at hMap
            rw [hInputEq, ← hMap] at hValue
            cases hValue
        | some T =>
            have hMap := e.map_func p.symbol (t ∘ p.argMap)
            rw [hA] at hMap
            change some (Structure.imageSet e.toFun T) =
                B.func p.symbol (e.toFun ∘ (t ∘ p.argMap)) at hMap
            rw [← hInputEq] at hMap
            have hSet : Structure.imageSet e.toFun T = U :=
              Option.some.inj (hMap.trans hValue)
            refine ⟨hSourceInj, T, rfl, ?_⟩
            rw [← hPartImage, hSet]
            exact hLabel
      · rintro ⟨hInj,T,hA,hLabel⟩
        have hTargetInj : Function.Injective (e.toFun ∘ t) :=
          e.injective.comp hInj
        have hMap := e.map_func p.symbol (t ∘ p.argMap)
        rw [hA] at hMap
        change some (Structure.imageSet e.toFun T) =
            B.func p.symbol (e.toFun ∘ (t ∘ p.argMap)) at hMap
        rw [← hInputEq] at hMap
        refine ⟨hTargetInj, Structure.imageSet e.toFun T, hMap.symm, ?_⟩
        rw [hPartImage]
        exact hLabel
    · rcases pq with ⟨p,q⟩
      let root : Fin p.rootSize → V :=
        fun i => t (Fin.castAdd q.size i)
      let out : Fin q.size → V :=
        fun j => t (Fin.natAdd p.rootSize j)
      have hInputEq :
          ((e.toFun ∘ root) ∘ p.argMap) = e.toFun ∘ (root ∘ p.argMap) := by
        funext i
        rfl
      have hImageRange :
          Structure.imageSet e.toFun (Set.range out) =
            Set.range (fun j : Fin q.size => e.toFun (out j)) := by
        ext y
        constructor
        · rintro ⟨x, ⟨j, rfl⟩, rfl⟩
          exact ⟨j, rfl⟩
        · rintro ⟨j, rfl⟩
          exact ⟨out j, ⟨j, rfl⟩, rfl⟩
      change
        (Function.Injective (e.toFun ∘ root) ∧
          B.func p.symbol ((e.toFun ∘ root) ∘ p.argMap) =
            some (Set.range (fun j : Fin q.size => e.toFun (out j))) ∧
          (∀ j : Fin q.size, partB (e.toFun (out j)) = q.label j)) ↔
        (Function.Injective root ∧
          A.func p.symbol (root ∘ p.argMap) =
            some (Set.range out) ∧
          (∀ j : Fin q.size, partA (out j) = q.label j))
      constructor
      · rintro ⟨hInj,hValue,hLabels⟩
        have hSourceInj : Function.Injective root := by
          intro i j hij
          apply hInj
          exact congrArg e.toFun hij
        cases hA : A.func p.symbol (root ∘ p.argMap) with
        | none =>
            have hMap := e.map_func p.symbol (root ∘ p.argMap)
            rw [hA] at hMap
            change (none : Option (Set W)) =
                B.func p.symbol (e.toFun ∘ (root ∘ p.argMap)) at hMap
            rw [hInputEq, ← hMap] at hValue
            cases hValue
        | some T =>
            have hMap := e.map_func p.symbol (root ∘ p.argMap)
            rw [hA] at hMap
            change some (Structure.imageSet e.toFun T) =
                B.func p.symbol (e.toFun ∘ (root ∘ p.argMap)) at hMap
            rw [← hInputEq] at hMap
            have hImg :
                Structure.imageSet e.toFun T =
                  Set.range (fun j : Fin q.size => e.toFun (out j)) :=
              Option.some.inj (hMap.trans hValue)
            have hOutput : T = Set.range out :=
              imageSet_injective e.toFun e.injective
                (hImg.trans hImageRange.symm)
            refine ⟨hSourceInj, ?_, ?_⟩
            · rw [← hOutput]
            · intro j
              exact (hPart (out j)).symm.trans (hLabels j)
      · rintro ⟨hInj,hValue,hLabels⟩
        have hTargetInj : Function.Injective (e.toFun ∘ root) :=
          e.injective.comp hInj
        have hMap := e.map_func p.symbol (root ∘ p.argMap)
        rw [hValue] at hMap
        change some (Structure.imageSet e.toFun (Set.range out)) =
            B.func p.symbol (e.toFun ∘ (root ∘ p.argMap)) at hMap
        rw [← hInputEq, hImageRange] at hMap
        refine ⟨hTargetInj, hMap.symm, ?_⟩
        intro j
        exact (hPart (out j)).trans (hLabels j)

end StructuralRamsey.PartialSetStructure.Embedding
