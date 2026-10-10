import PartiteConstruction.Ramsey.ClosureIrreducibleHulls
import PartiteConstruction.Ramsey.ClosureRankOneBase

/-!
# Complete ordinary irreducible weak tests from protected closed coverage

A major simplification for the possible exact-weak-size proof of
Theorem 2.18: the existing closed-test coverage invariant is much
stronger than rank-one completion. It completes EVERY ordinary
irreducible induced weak test, regardless of its intrinsic U-size,
size, or whether it is U-closed.

Let C be U-closed and suppose every embedded U-closed
U-irreducible test of C embeds in a fixed ordinary irreducible
Base in K. If S is any vertex subset with C|S ordinarily
irreducible, then its AMBIENT closure H=cl_U^C(S) is itself
U-closed and U-irreducible. The coverage hypothesis embeds C|H
into Base. Precompose with the exact induced inclusion C|S->C|H.
The resulting ordinary full embedding is a corrected K-completion
of C|S with precisely the SAME tested vertex carrier.

The complementary unresolved branch therefore concerns ordinary
REDUCIBLE weak tests. In the maximal-U-rank branch of #211, every
subset is relatively U-closed, so proper free sides of such tests
are also exact weak sources. This alone does not supply compatible
completions over arbitrary nonclosed separators.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {U V : Type v}

/-- Every ordinary irreducible weak induced substructure of a closed
picture is covered by the ORIGINAL Base if all closed U-irreducible
tests are covered. No U-closedness of the weak test or generator
bound is required. -/
theorem weak_irreducible_embeds_base_of_closed_coverage
    {rules : ClosureDescription L}
    {C : RelStructure L U} {Base : RelStructure L V}
    (hC : IsUClosed rules C)
    (hCover : ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test C → Nonempty (Embedding Test Base))
    (S : Set U) (hIrred : (C.induce S).Irreducible) :
    Nonempty (Embedding (C.induce S) Base) := by
  let H : Set U := UClosureHull rules C S
  have hHClosed : IsUClosed rules (C.induce H) :=
    hC.induce_UClosureHull S
  have hHIrred : IsUIrreducible rules (C.induce H) :=
    hC.irreducibleSeed_hull_isUIrreducible S hIrred
  obtain ⟨g⟩ := hCover (C.induce H) hHClosed hHIrred
    (inclusion C H)
  let e : Embedding (C.induce S) (C.induce H) := {
    toFun := fun x => ⟨x.1, subset_UClosureHull rules C S x.2⟩
    injective := by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : H => z.1) hxy
    map_rel_iff := fun _ _ => Iff.rfl
  }
  exact ⟨g.comp e⟩

/-- Ordinary irreducible weak tests have corrected K-completions,
even if their intrinsic U-rank is arbitrarily large. This is a
global consequence of the SAME original Base-copy coverage used
throughout the repaired finite Ramsey construction. -/
theorem weak_irreducible_completion_of_closed_coverage
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {C : RelStructure L U} {Base : RelStructure L V}
    [Finite V]
    (hC : IsUClosed rules C)
    (hBaseK : K Base) (hBaseIrred : Base.Irreducible)
    (hCover : ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test C → Nonempty (Embedding Test Base))
    (S : Set U) (hIrred : (C.induce S).Irreducible) :
    HasClosedUKCompletion K rules (C.induce S) := by
  obtain ⟨g⟩ := weak_irreducible_embeds_base_of_closed_coverage
    hC hCover S hIrred
  exact ⟨V, inferInstance, Base, hBaseK, hBaseIrred,
    g, g.isClosedUHomomorphismEmbedding rules⟩

end StructuralRamsey.RelStructure
