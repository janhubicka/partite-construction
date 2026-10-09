import PartiteConstruction.Ramsey.ClosureRootCover
import PartiteConstruction.Ramsey.ClosureClosedCover
import PartiteConstruction.Partite.InducedInitial

/-! # The native closed initial picture over an arbitrary control

The disjoint-copy initial picture is closed whenever its base is closed.
Its closed irreducible tests lie in one indexed copy, so a family of full
embeddings of the base into ANY control gives a protected part projection.
The control is not assumed closed. Positive root size is used explicitly
when showing that any union of index fibres is relatively closed.
-/

namespace StructuralRamsey.Partite.Induced.Initial

open RelStructure
universe u v
variable {L : RelLanguage.{u}} {P V I X : Type v}

/-- Any union of index fibres is a relative U-substructure of the
native disjoint-copy picture. The base itself need not be closed. -/
theorem index_fibres_isUSubstructure
    (rules : ClosureDescription L)
    (B : RelStructure L V) (beta : I → V ↪ P) (J : Set I) :
    IsUSubstructure rules (Partite.Initial.picture B beta).toRelStructure
      {z : I × V | z.1 ∈ J} := by
  intro rule hrule t ht hRoot j
  rcases ht with ⟨i, y, hy, rfl⟩
  exact hRoot ⟨0, rule.rootPositive⟩

/-- Every embedded CLOSED U-irreducible test lies in one indexed
base copy. Empty tests are covered using the nonempty index type. -/
theorem closed_test_same_index
    {rules : ClosureDescription L}
    (B : RelStructure L V) (beta : I → V ↪ P) [Nonempty I]
    (Test : RelStructure L X) (hClosed : IsUClosed rules Test)
    (hIrred : IsUIrreducible rules Test)
    (e : RelStructure.Embedding Test
      (Partite.Initial.picture B beta).toRelStructure) :
    ∃ i : I, ∀ x : X, (e x).1 = i := by
  classical
  by_cases hX : Nonempty X
  · obtain ⟨a⟩ := hX
    let i : I := (e a).1
    let S : Set X := {x | (e x).1 = i}
    let T : Set X := {x | (e x).1 ≠ i}
    have hS : IsUSubstructure rules Test S := by
      intro rule hrule t ht hRoot j
      exact index_fibres_isUSubstructure rules B beta ({i} : Set I)
        rule hrule (e ∘ t) ((e.map_rel_iff rule.symbol t).mpr ht) hRoot j
    have hT : IsUSubstructure rules Test T := by
      intro rule hrule t ht hRoot j
      exact index_fibres_isUSubstructure rules B beta (({i} : Set I)ᶜ)
        rule hrule (e ∘ t) ((e.map_rel_iff rule.symbol t).mpr ht) hRoot j
    have hCover : ∀ x : X, x ∈ S ∨ x ∈ T := fun x => em ((e x).1 = i)
    have hTuples : ∀ R (z : Fin (L.arity R) → X), Test.rel R z →
        (∀ k, z k ∈ S) ∨ (∀ k, z k ∈ T) := by
      intro R z hz
      rcases (e.map_rel_iff R z).mpr hz with ⟨j, y, hy, heq⟩
      have hIndex (k : Fin (L.arity R)) : (e (z k)).1 = j :=
        congrArg Prod.fst (congrFun heq k)
      by_cases hji : j = i
      · exact Or.inl (fun k => (hIndex k).trans hji)
      · exact Or.inr (fun k h => hji ((hIndex k).symm.trans h))
    rcases hIrred.closed_cover hClosed S T hS hT hCover hTuples with hAll | hAll
    · exact ⟨i, hAll⟩
    · exact False.elim (hAll a rfl)
  · refine ⟨Classical.choice (inferInstance : Nonempty I), ?_⟩
    intro x
    exact False.elim (hX ⟨x⟩)

/-- Carrier-independent factorization through an actual initial copy. -/
theorem closed_test_factor_copy
    {rules : ClosureDescription L}
    (B : RelStructure L V) (beta : I → V ↪ P) [Nonempty I]
    (Test : RelStructure L X) (hClosed : IsUClosed rules Test)
    (hIrred : IsUIrreducible rules Test)
    (e : RelStructure.Embedding Test
      (Partite.Initial.picture B beta).toRelStructure) :
    ∃ i : I, ∃ g : RelStructure.Embedding Test B,
      ∀ x, Partite.Initial.copyEmbedding B beta i (g x) = e x := by
  obtain ⟨i, hi⟩ := closed_test_same_index B beta Test hClosed hIrred e
  let c := Partite.Initial.copyEmbedding B beta i
  have hRange (x : X) : ∃ y : V, e x = c y :=
    ⟨(e x).2, Prod.ext (hi x) rfl⟩
  exact ⟨i, e.factorThroughRange c hRange,
    fun x => (Classical.choose_spec (hRange x)).symm⟩

/-- Closedness of the native initial picture, with no condition on
its partition-label carrier or on any ambient control structure. -/
theorem picture_isUClosed
    {rules : ClosureDescription L}
    (B : RelStructure L V) (beta : I → V ↪ P) [Nonempty I]
    (hB : IsUClosed rules B) :
    IsUClosed rules (Partite.Initial.picture B beta).toRelStructure := by
  let C := (Partite.Initial.picture B beta).toRelStructure
  let c : I → RelStructure.Embedding B C :=
    Partite.Initial.copyEmbedding B beta
  apply isUClosed_of_closed_root_cover rules C (fun _ : I => B) c (fun _ => hB)
  · intro i
    have heq : Set.range (c i) = {z : I × V | z.1 ∈ ({i} : Set I)} := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact Set.mem_singleton i
      · intro hz
        exact ⟨z.2, Prod.ext (Set.mem_singleton_iff.mp hz).symm rfl⟩
    rw [heq]
    exact index_fibres_isUSubstructure rules B beta {i}
  · intro rule hrule t ht
    exact ht
  · intro rule hrule e
    obtain ⟨i, hi⟩ := irreducible_same_index B beta (Set.range e)
      (rule.rootIrreducible.range_embedding e)
    have hRange (x : Fin rule.rootSize) : ∃ y : V, e x = c i y :=
      ⟨(e x).2, Prod.ext (hi ⟨e x, ⟨x, rfl⟩⟩) rfl⟩
    let r : RelStructure.Embedding rule.root B := e.factorThroughRange (c i) hRange
    refine ⟨i, r, ?_⟩
    intro x
    exact (Classical.choose_spec (hRange x)).symm

/-- Full base embeddings give a protected initial part projection even
when the control is nonclosed. Closedness of a test, not of the control,
is what prevents that test from crossing between initial copies. -/
theorem picture_isClosedPartiteOver
    {rules : ClosureDescription L}
    (B : RelStructure L V) (D : RelStructure L P)
    (gamma : I → RelStructure.Embedding B D) [Nonempty I] :
    IsClosedUHomomorphismEmbedding rules
      (Partite.Initial.picture B (fun i => (gamma i).toFunctionEmbedding)).toRelStructure
      D (Partite.Initial.picture B (fun i => (gamma i).toFunctionEmbedding)).part := by
  constructor
  · intro R z hz
    rcases hz with ⟨i, y, hy, rfl⟩
    exact ((gamma i).map_rel_iff R y).mpr hy
  · intro Y Test hClosed hIrred e
    obtain ⟨i, g, hg⟩ := closed_test_factor_copy B
      (fun j => (gamma j).toFunctionEmbedding) Test hClosed hIrred e
    refine ⟨(gamma i).comp g, ?_⟩
    intro x
    rw [← hg x]
    rfl

end StructuralRamsey.Partite.Induced.Initial
