import PartiteConstruction.Functional.WholeMaskCoveredTargetDomains2019
import PartiteConstruction.Functional.PartialSetFunctionsPartPredicates2019
import PartiteConstruction.Ramsey.ClosureWeakIrreducibleCoverage

/-!
# Recover each vertex part of a final U-closed, B-covered tagged target

The verified 2019 two-pass construction works in the unary-part
expanded OLD complete-mask language. An arbitrary intermediate
relational picture need not have a meaningful genuine part map.
But a FINAL U-closed picture with protected closed U-irreducible
B-copy coverage has exactly one active unary part predicate
at EACH original vertex.

The exact singleton support is ordinarily irreducible. Its closed
U-irreducible hull therefore embeds into the canonical tagged B,
so the exact singleton itself has a FULL embedding into B. The
canonical part unary relations on B are total and exclusive;
reflection by that one full embedding yields both existence and
uniqueness in the final target.

No source weak test is replaced by its closure hull, and no
mixed-root strict functional B-tree completion is required.
-/

namespace StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V W : Type v}

/-- The unary part relation on an OLD complete-mask target with
named parts: the outer `inl` forgets the fresh closure tag,
the next `inl` selects an old primitive relation, and
`inr p` names the unary part predicate. -/
def WholeMaskVertexPartHolds
    (C : RelStructure ((L.withParts P).wholeMaskTagLanguage P) V)
    (x : V) (p : P) : Prop :=
  C.rel (.inl (.inl (.inr p))) (fun _ : Fin 1 => x)

/-- Every vertex in the final U-closed, canonical B-covered
whole-mask tagged picture has EXACTLY ONE unary part label.
The protected-copy condition is the identical final condition
already used to derive coherent genuinely partial function domains.
It is not required of intermediate profile-sparsening pictures. -/
theorem wholeMask_vertexPart_existsUnique_of_closed_coverage
    (C : RelStructure ((L.withParts P).wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L W) (basePart : W → P)
    (hC : IsUClosed ((L.withParts P).wholeMaskClosureRules P) C)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure ((L.withParts P).wholeMaskTagLanguage P) X),
      IsUClosed ((L.withParts P).wholeMaskClosureRules P) Test →
      IsUIrreducible ((L.withParts P).wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart)))) :
    ∀ x : V, ∃! p : P, WholeMaskVertexPartHolds C x p := by
  classical
  intro x
  let S : Set V := {x}
  have hIrred : (C.induce S).Irreducible := by
    intro a b hab
    have habEq : a = b := by
      apply Subtype.ext
      exact (Set.mem_singleton_iff.mp a.2).trans
        (Set.mem_singleton_iff.mp b.2).symm
    exact (hab habEq).elim
  obtain ⟨g⟩ := weak_irreducible_embeds_base_of_closed_coverage
    hC hCover S hIrred
  let vx : S := ⟨x, Set.mem_singleton x⟩
  let p : P := basePart (g vx)
  have hLocal : (C.induce S).rel
      (.inl (.inl (.inr p))) (fun _ : Fin 1 => vx) := by
    apply (g.map_rel_iff (.inl (.inl (.inr p)))
      (fun _ : Fin 1 => vx)).mp
    change basePart (g vx) = p
    rfl
  have hExists : WholeMaskVertexPartHolds C x p := hLocal
  refine ⟨p, hExists, ?_⟩
  intro q hq
  have hqLocal : (C.induce S).rel
      (.inl (.inl (.inr q))) (fun _ : Fin 1 => vx) := hq
  have hqBase : basePart (g vx) = q := by
    have h := (g.map_rel_iff (.inl (.inl (.inr q)))
      (fun _ : Fin 1 => vx)).mpr hqLocal
    exact h
  exact hqBase.symm

/-- Choose the actual part label of every final-target vertex.
The existence/uniqueness theorem makes the choice independent
of the particular closed B-copy used to check the singleton. -/
noncomputable def wholeMaskCoveredPart
    (C : RelStructure ((L.withParts P).wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L W) (basePart : W → P)
    (hC : IsUClosed ((L.withParts P).wholeMaskClosureRules P) C)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure ((L.withParts P).wholeMaskTagLanguage P) X),
      IsUClosed ((L.withParts P).wholeMaskClosureRules P) Test →
      IsUIrreducible ((L.withParts P).wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))))
    (x : V) : P :=
  Classical.choose
    (wholeMask_vertexPart_existsUnique_of_closed_coverage
      C Base basePart hC hCover x)

/-- The reconstructed part label holds as its unary relation on the
ORIGINAL target vertex, not on a closure-enlarged subtype. -/
theorem wholeMaskCoveredPart_holds
    (C : RelStructure ((L.withParts P).wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L W) (basePart : W → P)
    (hC : IsUClosed ((L.withParts P).wholeMaskClosureRules P) C)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure ((L.withParts P).wholeMaskTagLanguage P) X),
      IsUClosed ((L.withParts P).wholeMaskClosureRules P) Test →
      IsUIrreducible ((L.withParts P).wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))))
    (x : V) :
    WholeMaskVertexPartHolds C x
      (wholeMaskCoveredPart C Base basePart hC hCover x) :=
  (Classical.choose_spec
    (wholeMask_vertexPart_existsUnique_of_closed_coverage
      C Base basePart hC hCover x)).1

end StructuralRamsey.RelStructure
