import PartiteConstruction.Functional.WholeMaskCoveredPartialDecoding2019
import PartiteConstruction.Relational.Homomorphism

/-!
# Positive OLD graph homomorphisms become original-2019 partial maps

The 2019 partial-function projection preserves a defined source
application with its COMPLETE output set, but deliberately does NOT
reflect undefined source applications. In particular the source can
have F(x)=none while the control defines F(pi x).

The old complete-mask relational language is suited to precisely this
asymmetric projection semantics: each positive OLD output-tuple
relation records the ENTIRE value of one genuinely partial function
application (also when that value is empty). An OLD relational
homomorphism to the canonical complete-mask graph of a genuine
partial control therefore maps each defined decoded source value
onto exactly the full target value, not just into a subset.

The source decoder needs complete-value uniqueness. This is a
separate property of arbitrary OLD graphs, provided by the final
U-closed canonical-B-copy coverage theorem. Nothing below infers
domain reflection, constructs target B-tree completions, changes
the exact tested weak carrier, or asserts the HJ-stage projection
has the OLD homomorphism property without checking it.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey.Structure

universe u v w z
variable {L : Language.{u}} {P : Type z} [Fintype P]
variable {V : Type v} {W : Type w}

/-- A positive OLD relational homomorphism from a UNIQUE complete
value OLD source graph into a canonical genuine partial target graph
is exactly an original-2019 source-defined partial function
homomorphism after decoding the source.
Undefined inputs remain free to map to defined target inputs. -/
theorem wholeMaskPartialDecode_originalPartial_of_oldHom
    (E : RelStructure (L.wholeMaskPatternLanguage P) V)
    (Target : PartialSetStructure L W) (targetPart : W → P)
    (f : V → W)
    (hValUnique : ∀ (F : L.FuncSymbol)
      (x : Fin (L.funcArity F) → V) (U T : Set V),
      HasWholeMaskValue E F x U →
      HasWholeMaskValue E F x T → U = T)
    (hOld : E.IsHomomorphism (Target.wholeMaskPatternGraph targetPart) f) :
    PartialSetStructure.IsOriginalPartialHomomorphism
      E.wholeMaskPartialDecode Target f := by
  classical
  constructor
  · intro R xs hR
    exact hOld (.inl R) xs hR
  · intro F xs U hSource
    have hValue : HasWholeMaskValue E F xs U :=
      (E.wholeMaskPartialDecode_func_some_iff
        F xs (hValUnique F xs) U).mp hSource
    obtain ⟨m,r,hr,q,t,hRel,hArgs,hSet⟩ := hValue
    let pat : Language.FunctionInputPattern L :=
      ⟨F,m,r,hr⟩
    have hRelTarget :
        (Target.wholeMaskPatternGraph targetPart).rel
          (.inr (.inr (pat,q))) (f ∘ t) :=
      hOld (.inr (.inr (pat,q))) t hRel
    have hTargetValue : Target.func F
        ((fun i : Fin m => f (t (Fin.castAdd q.size i))) ∘ r) =
        some (Set.range (fun j : Fin q.size =>
          f (t (Fin.natAdd m j)))) := hRelTarget.2.1
    have hArgsTarget :
        ((fun i : Fin m => f (t (Fin.castAdd q.size i))) ∘ r) =
          f ∘ xs := by
      funext i
      exact congrArg f (hArgs i).symm
    have hOutputSet :
        Set.range (fun j : Fin q.size => f (t (Fin.natAdd m j))) =
          Structure.imageSet f U := by
      rw [hSet]
      ext y
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨t (Fin.natAdd m j), ⟨j, rfl⟩, rfl⟩
      · rintro ⟨a, ⟨j, hja⟩, ha⟩
        exact ⟨j, by rw [hja, ha]⟩
    rw [hArgsTarget, hOutputSet] at hTargetValue
    exact hTargetValue

/-- The final U-closed canonical-B-covered target has coherent
complete values, so a checked OLD homomorphism into a genuine control
supplies the original 2019 partial-function projection for the
decoded target. This is NOT total-fibre/domain-reflecting. -/
theorem wholeMaskPartialDecode_originalPartial_of_covered_oldHom
    {Q : Type v}
    (C : RelStructure (L.wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L Q) (basePart : Q → P)
    (hC : IsUClosed (L.wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure (L.wholeMaskTagLanguage P) X),
      IsUClosed (L.wholeMaskClosureRules P) Test →
      IsUIrreducible (L.wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion (Base.wholeMaskPatternGraph basePart))))
    (Target : PartialSetStructure L W) (targetPart : W → P)
    (f : V → W)
    (hOld : (wholeMaskTagReduct C).IsHomomorphism
      (Target.wholeMaskPatternGraph targetPart) f) :
    PartialSetStructure.IsOriginalPartialHomomorphism
      (wholeMaskTagReduct C).wholeMaskPartialDecode Target f := by
  exact wholeMaskPartialDecode_originalPartial_of_oldHom
    (wholeMaskTagReduct C) Target targetPart f
    (fun F xs U T hU hT =>
      wholeMaskValue_unique_of_closed_coverage
        C Base basePart hC hPos hCover F xs U T hU hT)
    hOld

end StructuralRamsey.RelStructure
