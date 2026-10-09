import PartiteConstruction.Ramsey.ClosureClosedMap
import PartiteConstruction.Ramsey.ClosureLocalCompletionRank

/-! # Closed-test K-completions and exact weak local tests

This module uses the explicitly named closed-test convention. It neither
changes the literal 2019 U-completion predicate nor assumes the repaired
local-finiteness axiom follows from the printed one.

Unlike the generic theorem in ClosureLocalCompletionRank, the final theorem
here has NO hereditary-property oracle: inheritance under full relational
embeddings is proved from the completion map itself. The same finite target
is used for the original weak test, not a new target or a larger tested set.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {U V : Type v}

/-- A finite irreducible K-target with a closed-test preserving positive
map. This working completion notion is distinct from the literal IsUCompletion. -/
def HasClosedUKCompletion
    (K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L) (A : RelStructure L U) : Prop :=
  ∃ (V : Type v) (_ : Finite V) (Target : RelStructure L V),
    K Target ∧ Target.Irreducible ∧
      ∃ f : U → V, IsClosedUHomomorphismEmbedding rules A Target f

/-- Restriction keeps the SAME finite K-target, even for a weak source
which is not U-closed. Only the original embedding is precomposed. -/
theorem HasClosedUKCompletion.pullback_embedding
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {A : RelStructure L U} {B : RelStructure L V}
    (hB : HasClosedUKCompletion K rules B)
    (e : Embedding A B) :
    HasClosedUKCompletion K rules A := by
  obtain ⟨W, hW, Target, hK, hIrred, f, hf⟩ := hB
  exact ⟨W, hW, Target, hK, hIrred, f ∘ e, hf.precomp_embedding e⟩

/-- Closed generating-rank control now yields completions of every
exact weak n-vertex test. The restriction premise of the earlier
abstract bridge is discharged, not assumed. -/
theorem HasClosedUKCompletion.of_closed_USize
    {K : StructureClass.{u,v} (L := L)}
    [Finite U]
    (rules : ClosureDescription L) (A : RelStructure L U)
    (hA : IsUClosed rules A) (n : ℕ)
    (hRank : ∀ (T : Set U) [Fintype T],
      IsUClosed rules (A.induce T) →
      USize rules (A.induce T) ≤ n →
        HasClosedUKCompletion K rules (A.induce T))
    (S : Finset U) (hS : S.card ≤ n) :
    HasClosedUKCompletion K rules (A.induce (↑S : Set U)) := by
  exact local_property_of_closed_USize rules A hA
    (fun {_} D => HasClosedUKCompletion K rules D)
    (fun _ _ e hD => hD.pullback_embedding e) n hRank S hS

/-- A closed-test completion preserves all copies of a protected Base.
This is precisely the input to the B-only final Ramsey transfer. -/
theorem HasClosedUKCompletion.toCopywise
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {A : RelStructure L U}
    (hA : HasClosedUKCompletion K rules A)
    (Base : RelStructure L V)
    (hClosed : IsUClosed rules Base)
    (hIrred : IsUIrreducible rules Base) :
    HasCopywiseCompletion K Base A := by
  obtain ⟨W, hW, Target, hK, _, f, hf⟩ := hA
  exact ⟨W, hW, Target, hK, f, hf.copywise Base hClosed hIrred⟩

end StructuralRamsey.RelStructure
