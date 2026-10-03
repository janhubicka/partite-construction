import PartiteConstruction.Iterated.BoundaryControlCompletion

/-! # Completing all ambient controls from explicit boundary systems

If every ambient A-copy has an induced tested boundary embedded in the current
target, all ordinary A-copy controls can be added by finite iteration without
hereditary irreducibility of A.

The one-step boundary completion exposes the old-target embedding.  Hence all
unprocessed boundary embeddings are transported forward functorially while
processed A-copies accumulate in the ordinary Controls predicate.
-/
namespace StructuralRamsey.RelStructure.LocallyTreeLike

universe u v
variable {L : RelLanguage.{u}}
variable {U V W Y : Type v}
variable {A : RelStructure L U} {B : RelStructure L V}
variable {C : RelStructure L W} {T : RelStructure L Y}

/-- Boundary data for every ambient A-copy. -/
structure BoundarySystem
    (A : RelStructure L U) (C : RelStructure L W)
    (T : RelStructure L Y)
    (S : Finset W) (f : ↥(↑S : Set W) → Y) where
  get : ∀ α : Embedding A C,
    BoundaryEmbedding (A := A) (C := C) (T := T) S f α

/-- Containment in an irreducible target substructure survives postcomposition
with an embedding. -/
theorem Embedding.ContainedInIrreducible.postcomp
    {X Z : Type v} {D : RelStructure L X} {T' : RelStructure L Z}
    (b : Embedding D T)
    (hb : b.ContainedInIrreducible)
    (e : Embedding T T') :
    (e.comp b).ContainedInIrreducible := by
  rcases hb with ⟨R, hR, hsub⟩
  let eR : Embedding (T.induce R) T' :=
    e.comp (inclusion T R)
  refine ⟨Set.range eR, hR.range_embedding eR, ?_⟩
  intro x
  obtain ⟨r, hr⟩ := hsub x
  let rr : R := ⟨b x, hr⟩
  exact ⟨rr, rfl⟩

/-- Boundary embeddings transport through an embedding of targets. -/
noncomputable def BoundaryEmbedding.postcomp
    {Z : Type v} {T' : RelStructure L Z}
    (S : Finset W) (f : ↥(↑S : Set W) → Y)
    (α : Embedding A C)
    (hbd : BoundaryEmbedding (A := A) (C := C) (T := T) S f α)
    (e : Embedding T T') :
    BoundaryEmbedding (A := A) (C := C) (T := T') S (e ∘ f) where
  boundary := e.comp hbd.boundary
  agrees := fun x => congrArg e (hbd.agrees x)
  contained := hbd.boundary.ContainedInIrreducible.postcomp
    hbd.contained e

/-- A whole boundary system transports through an embedding of targets. -/
noncomputable def BoundarySystem.postcomp
    {Z : Type v} {T' : RelStructure L Z}
    (S : Finset W) (f : ↥(↑S : Set W) → Y)
    (hbd : BoundarySystem A C T S f)
    (e : Embedding T T') :
    BoundarySystem A C T' S (e ∘ f) where
  get := fun α => (hbd.get α).postcomp S f α e

/-- Process a finite list of ambient A-copies while preserving the boundary
system for every ambient A-copy. -/
theorem completeControlList_of_boundaries
    (hA : A.Irreducible)
    (eAB : Embedding A B)
    (S : Finset W)
    (xs : List (Embedding A C))
    (hTree : TreeAmalgam B Y T)
    (f : ↥(↑S : Set W) → Y)
    (hf : (C.induce (↑S : Set W)).IsHomomorphismEmbedding T f)
    (hbd : BoundarySystem A C T S f) :
    ∃ (Z : Type v) (T' : RelStructure L Z),
      TreeAmalgam B Z T' ∧
      ∃ f' : ↥(↑S : Set W) → Z,
        (C.induce (↑S : Set W)).IsHomomorphismEmbedding T' f' ∧
        ∃ hbd' : BoundarySystem A C T' S f',
          Controls (A := A) (C := C) (T := T') S f' xs := by
  classical
  induction xs with
  | nil =>
      refine ⟨Y, T, hTree, f, hf, hbd, ?_⟩
      intro α hα
      exact (List.not_mem_nil hα).elim
  | cons α xs ih =>
      obtain ⟨Y₁, T₁, hTree₁, f₁, hf₁, hbd₁, hctrl₁⟩ :=
        ih hTree f hf hbd
      obtain ⟨Z, T₂, hTree₂, e, f₂, hfEq, hf₂, hctrl₂⟩ :=
        addControl_of_boundary_with_embedding
          (A := A) (B := B) (C := C)
          hA eAB S hTree₁ f₁ hf₁ xs hctrl₁ α (hbd₁.get α)
      have hbd₂ :
          BoundarySystem (A := A) (C := C) (T := T₂) S f₂ := by
        rw [hfEq]
        exact hbd₁.postcomp S f₁ e
      exact ⟨Z, T₂, hTree₂, f₂, hf₂, hbd₂, hctrl₂⟩

/-- Complete the ordinary ambient-A control clause for all A-copies from a
boundary system.  Only irreducibility of A is required. -/
theorem completeControl_of_boundaries
    [Finite U] [Finite W]
    (hA : A.Irreducible)
    (eAB : Embedding A B)
    (S : Finset W)
    (hTree : TreeAmalgam B Y T)
    (f : ↥(↑S : Set W) → Y)
    (hf : (C.induce (↑S : Set W)).IsHomomorphismEmbedding T f)
    (hbd : BoundarySystem A C T S f) :
    ∃ (Z : Type v) (T' : RelStructure L Z),
      TreeAmalgam B Z T' ∧
      ∃ f' : ↥(↑S : Set W) → Z,
        (C.induce (↑S : Set W)).IsHomomorphismEmbedding T' f' ∧
        ∀ α : Embedding A C,
          ∃ α' : Embedding A T',
            ∀ a : U, ∀ ha : α a ∈ S,
              ∃ a' : U, f' ⟨α a, ha⟩ = α' a' := by
  classical
  letI : Fintype (Embedding A C) := Fintype.ofFinite _
  let xs : List (Embedding A C) := Finset.univ.toList
  obtain ⟨Z, T', hTree', f', hf', _, hctrl⟩ :=
    completeControlList_of_boundaries
      (A := A) (B := B) (C := C)
      hA eAB S xs hTree f hf hbd
  refine ⟨Z, T', hTree', f', hf', ?_⟩
  intro α
  exact hctrl α (by simp [xs])

end StructuralRamsey.RelStructure.LocallyTreeLike
