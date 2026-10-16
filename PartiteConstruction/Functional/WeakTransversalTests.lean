import PartiteConstruction.Functional.WeakOperations
import PartiteConstruction.Functional.OriginalPartialSemantics
import PartiteConstruction.Structure.WeakSubstructure

/-!
# Transversal set-valued function images in weak partite tests

A genuine functional partite system carries TWO independent
transversality requirements: ordinary relation tuples are transversal
and, for each input tuple, distinct function outputs are in distinct
parts. This second condition is ESSENTIAL for Hales–Jewett
coordinate powers and full functional free attachments.

Exact WEAK vertex restrictions preserve BOTH conditions without any
closure assumption. A weak partite test need not be function-closed,
nor need its map to the control be an EHN homomorphism-embedding;
it is nevertheless a valid transversal partite system.

The image of each individual function fibre under its part map is
injective, including when some output vertices are omitted by the
weak restriction. This does not imply surjectivity onto the control's
weak fibre for arbitrary weak sets: a missing output may have the
same part as a non-output vertex retained in the test.

We isolate the sufficient condition for exact weak fibre mapping:
the tested subset S is saturated under its occupied parts. The
canonical selected support in a native HJ Picture is automatically
part-saturated, since it is the full inverse image of an embedded
A-copy's parts. Consequently its weak projection is an original-2019
source-defined partial function homomorphism, even for genuinely
MULTIVALUED operations; no singleton reduction is needed.

This is a functional-language certificate for the selected support,
not an assertion of a uniform hard-root extension in mixed tests.
-/

namespace StructuralRamsey.FunctionalPartite

open Structure

universe u v
variable {L : Language.{u}} {P : Type v} {V : Type v}

/-- The part map is injective on EACH set-valued function output
fibre. Different input tuples can, of course, have outputs in the
same part; no global injectivity is claimed. -/
theorem System.func_part_injOn (B : System L P V)
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → V) :
    Set.InjOn B.part (B.func F x) := by
  intro y hy z hz heq
  exact B.funcTransversal F x y z hy hz heq

/-- An arbitrary exact WEAK restriction of a transversal functional
partite system is itself a transversal functional partite system.
Unlike full induced functional substructures, S need NOT be closed
under operation images. -/
def System.weakInduce (B : System L P V) (S : Set V) :
    System L P S where
  toStructure := B.toStructure.weakInduce S
  part x := B.part x.1
  relTransversal := by
    intro R x hx i j hp
    apply Subtype.ext
    exact B.relTransversal R (Subtype.val ∘ x) hx i j hp
  funcTransversal := by
    intro F x y z hy hz hp
    apply Subtype.ext
    exact B.funcTransversal F (Subtype.val ∘ x) y.1 z.1 hy hz hp

/-- Weak restriction does not change the underlying weak structure
nor add closure vertices. -/
@[simp] theorem System.weakInduce_toStructure
    (B : System L P V) (S : Set V) :
    (B.weakInduce S).toStructure = B.toStructure.weakInduce S := rfl

/-- In every weak partite test, the surviving outputs remain
transversal in their parts, independently of closedness of S. -/
theorem System.weakInduce_func_part_injOn
    (B : System L P V) (S : Set V)
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → S) :
    Set.InjOn (B.weakInduce S).part ((B.weakInduce S).func F x) :=
  (B.weakInduce S).func_part_injOn F x

/-- A vertex set is a union of whole parts among the parts it
occupies. This property concerns the *vertex set*, not closure
under function outputs. -/
def System.PartSaturated (B : System L P V) (S : Set V) : Prop :=
  ∀ y, B.part y ∈ B.part '' S → y ∈ S

/-- The selected support of a full copy in the control is a union
of whole parts and hence automatically part-saturated. -/
theorem System.support_partSaturated
    (B : System L P V) {Q : Type v} (α : Q ↪ P) :
    B.PartSaturated (B.support α) := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hy
  change B.part y ∈ Set.range α
  obtain ⟨a, ha⟩ := hx
  exact ⟨a, ha.trans hxy⟩

/-- If a weak vertex set is part-saturated, its part projection
maps all SURVIVING defined function fibres ONTO the corresponding
weak control fibres. Without saturation only positive incidence
preservation, not fibre equality, is available in general.

Assumptions are:
  - the actual System's function-image transversality;
  - the already verified EHN projection to the functional control;
  - part saturation of the precise weak test subset.

In particular no singleton-valuedness or closure hull is assumed. -/
theorem System.partSaturated_weakImage_originalPartial
    (B : System L P V) (D : Structure L P)
    (hB : B.WeaklyPartiteOver D)
    (S : Set V) (hSat : B.PartSaturated S) :
    IsOriginalPartialHomomorphism
      (B.toStructure.weakInduce S)
      (D.weakInduce (B.part '' S))
      (fun x : S =>
        (⟨B.part x.1, ⟨x.1, x.2, rfl⟩⟩ : B.part '' S)) := by
  let q : S → B.part '' S :=
    fun x => ⟨B.part x.1, ⟨x.1, x.2, rfl⟩⟩
  have hp : B.toStructure.IsEHNHomomorphismEmbedding D B.part := hB
  change IsOriginalPartialHomomorphism
    (B.toStructure.weakInduce S)
    (D.weakInduce (B.part '' S)) q
  constructor
  · intro R x hx
    change D.rel R (B.part ∘ (Subtype.val ∘ x))
    exact hp.1.1 R (Subtype.val ∘ x) hx
  · intro F x hWeakDefined
    obtain ⟨y₀, hy₀⟩ := hWeakDefined
    have hDefined : (B.toStructure.func F (Subtype.val ∘ x)).Nonempty :=
      ⟨y₀.1, hy₀⟩
    have hFull :
        imageSet B.part (B.toStructure.func F (Subtype.val ∘ x)) =
          D.func F (B.part ∘ (Subtype.val ∘ x)) :=
      hp.map_func_of_nonempty F (Subtype.val ∘ x) hDefined
    ext z
    constructor
    · rintro ⟨y, hy, hEq⟩
      change z.1 ∈ D.func F (B.part ∘ (Subtype.val ∘ x))
      have hIn : B.part y.1 ∈ D.func F (B.part ∘ (Subtype.val ∘ x)) := by
        rw [← hFull]
        exact ⟨y.1, hy, rfl⟩
      have heq : z.1 = B.part y.1 :=
        (congrArg Subtype.val hEq).symm
      rw [heq]
      exact hIn
    · intro hz
      have hzD : z.1 ∈ D.func F (B.part ∘ (Subtype.val ∘ x)) := hz
      rw [← hFull] at hzD
      obtain ⟨y, hy, hEq⟩ := hzD
      have hyS : y ∈ S := by
        apply hSat y
        rw [hEq]
        exact z.2
      refine ⟨(⟨y, hyS⟩ : S), hy, ?_⟩
      apply Subtype.ext
      exact hEq

/-- Under part saturation, the part map is a BIJECTION on each
SURVIVING defined weak function fibre: exact weak fibre surjectivity
comes from the original-2019 EHN map and part saturation, and
injectivity comes specifically from the required transversal-image
axiom of the functional partite system. Thus distinct set-valued
outputs never collapse to the same part. -/
theorem System.partSaturated_weakFibre_bijOn
    (B : System L P V) (D : Structure L P)
    (hB : B.WeaklyPartiteOver D)
    (S : Set V) (hSat : B.PartSaturated S)
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → S)
    (hDef : ((B.toStructure.weakInduce S).func F x).Nonempty) :
    let q : S → B.part '' S :=
      fun y => ⟨B.part y.1, ⟨y.1, y.2, rfl⟩⟩
    Set.BijOn q
      ((B.toStructure.weakInduce S).func F x)
      ((D.weakInduce (B.part '' S)).func F (q ∘ x)) := by
  dsimp only
  let q : S → B.part '' S :=
    fun y => ⟨B.part y.1, ⟨y.1, y.2, rfl⟩⟩
  have hp : IsOriginalPartialHomomorphism
      (B.toStructure.weakInduce S)
      (D.weakInduce (B.part '' S)) q :=
    B.partSaturated_weakImage_originalPartial D hB S hSat
  have hMap := hp.2 F x hDef
  have hInj : Set.InjOn q
      ((B.toStructure.weakInduce S).func F x) := by
    intro y hy z hz heq
    apply Subtype.ext
    apply B.funcTransversal F (Subtype.val ∘ x) y.1 z.1 hy hz
    exact congrArg Subtype.val heq
  refine ⟨?_, hInj, ?_⟩
  · intro y hy
    have hyImage :
        q y ∈ imageSet q ((B.toStructure.weakInduce S).func F x) :=
      ⟨y, hy, rfl⟩
    rw [hMap] at hyImage
    exact hyImage
  · intro z hz
    rw [← hMap] at hz
    exact hz

/-- The actual selected full-part support therefore has exact
source-defined weak fibre projection, even with multivalued
functions. Its input/output partite structure remains transversal. -/
theorem System.support_originalPartial_weakProjection
    (B : System L P V) (D : Structure L P)
    (hB : B.WeaklyPartiteOver D)
    {Q : Type v} (α : Q ↪ P) :
    IsOriginalPartialHomomorphism
      (B.toStructure.weakInduce (B.support α))
      (D.weakInduce (B.part '' B.support α))
      (fun x : B.support α =>
        (⟨B.part x.1, ⟨x.1, x.2, rfl⟩⟩ :
          B.part '' B.support α)) :=
  B.partSaturated_weakImage_originalPartial D hB
    (B.support α) (B.support_partSaturated α)

end StructuralRamsey.FunctionalPartite
