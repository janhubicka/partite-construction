import PartiteConstruction.Structure.PartialSetFunctions

/-!
# Basic algebra for partial set-valued homomorphisms and weak tests

These lemmas are the minimum bridges needed before revisiting the
published-style functional partite construction. In particular:
* original-2019 source-defined homomorphisms COMPOSE, even with
  defined-empty values;
* on a genuinely function-closed carrier, weak restriction does NOT
  change the independent operation domain bit;
* the full closed inclusion preserves and reflects both `none`
  and `some ∅`, as well as every nonempty value set.

The unrestricted weak inclusion is intentionally not asserted to
be a partial-function homomorphism: the weak operation may discard
outputs or become undefined.
-/

namespace StructuralRamsey.PartialSetStructure

universe u v w z
variable {L : Language.{u}}
variable {V : Type v} {W : Type w} {X : Type z}

/-- Original-partial homomorphisms compose, without any reflection of
undefined inputs. Defined-empty source values are preserved at both
stages of the composition. -/
theorem IsOriginalPartialHomomorphism.comp
    {A : PartialSetStructure L V}
    {B : PartialSetStructure L W}
    {C : PartialSetStructure L X}
    {f : V → W} {g : W → X}
    (hg : IsOriginalPartialHomomorphism B C g)
    (hf : IsOriginalPartialHomomorphism A B f) :
    IsOriginalPartialHomomorphism A C (g ∘ f) := by
  constructor
  · intro R x hRel
    exact hg.1 R (f ∘ x) (hf.1 R x hRel)
  · intro F x T hF
    have h1 := hf.2 F x T hF
    have h2 := hg.2 F (f ∘ x) (Structure.imageSet f T) h1
    have hImage :
        Structure.imageSet g (Structure.imageSet f T) =
          Structure.imageSet (g ∘ f) T := by
      ext z
      constructor
      · rintro ⟨b, ⟨a, ha, rfl⟩, rfl⟩
        exact ⟨a, ha, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨f a, ⟨a, ha, rfl⟩, rfl⟩
    simpa only [Function.comp_assoc, hImage] using h2

/-- For a closed set of vertices, the exact weak value equals the
full value restricted to the subtype. The empty-defined case is
proved separately; it must not be confused with lost nonempty
outputs. -/
theorem weakValue_of_subset
    (S T : Set V) (hT : T ⊆ S) :
    weakValue S (some T) =
      some {y : S | y.1 ∈ T} := by
  classical
  by_cases hNonempty : T.Nonempty
  · have hMeet : (T ∩ S).Nonempty := by
      obtain ⟨y, hy⟩ := hNonempty
      exact ⟨y, hy, hT hy⟩
    simp [weakValue, hNonempty, hMeet]
  · have hEmpty : T = ∅ := by
      ext y
      constructor
      · intro hy
        exact (hNonempty ⟨y, hy⟩).elim
      · simp
    subst T
    simp [weakValue]

/-- The genuine substructure on a FUNCTION-CLOSED set retains
the exact `Option` state of every operation. -/
def induceClosed (A : PartialSetStructure L V)
    (S : Set V) (hS : IsClosed A S) :
    PartialSetStructure L S where
  rel R x := A.rel R (Subtype.val ∘ x)
  func F x := (A.func F (Subtype.val ∘ x)).map
    (fun T => {y : S | y.1 ∈ T})

/-- A weak test on a closed set has the SAME partial operation
domain and value set as the genuine full induced substructure.
This includes originally defined-empty inputs. -/
theorem weakInduce_closed_func
    (A : PartialSetStructure L V)
    (S : Set V) (hS : IsClosed A S)
    (F : L.FuncSymbol)
    (x : Fin (L.funcArity F) → S) :
    (weakInduce A S).func F x =
      (induceClosed A S hS).func F x := by
  change weakValue S (A.func F (Subtype.val ∘ x)) =
    (A.func F (Subtype.val ∘ x)).map
      (fun T => {y : S | y.1 ∈ T})
  cases hv : A.func F (Subtype.val ∘ x) with
  | none =>
      simp [hv, weakValue]
  | some T =>
      have hSubset : T ⊆ S :=
        hS F (Subtype.val ∘ x) T (fun i => (x i).property) hv
      simpa [hv] using weakValue_of_subset S T hSubset

/-- Full inclusion of the closed induced structure. In contrast to
an arbitrary weak restriction, this is a genuine embedding and
preserves `none`, `some ∅` and all nonempty values exactly. -/
def closedInclusion
    (A : PartialSetStructure L V)
    (S : Set V) (hS : IsClosed A S) :
    Embedding (induceClosed A S hS) A where
  toFun := Subtype.val
  injective := Subtype.val_injective
  map_rel_iff := fun _ _ => Iff.rfl
  map_func := by
    intro F x
    change
      (Option.map (Structure.imageSet Subtype.val)
        ((A.func F (Subtype.val ∘ x)).map
          (fun T => {y : S | y.1 ∈ T}))) =
        A.func F (Subtype.val ∘ x)
    cases hv : A.func F (Subtype.val ∘ x) with
    | none => simp [hv]
    | some T =>
        have hSubset : T ⊆ S :=
          hS F (Subtype.val ∘ x) T (fun i => (x i).property) hv
        simp only [hv, Option.map_some]
        congr 1
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact hz
        · intro hy
          exact ⟨⟨y, hSubset hy⟩, hy, rfl⟩

end StructuralRamsey.PartialSetStructure
