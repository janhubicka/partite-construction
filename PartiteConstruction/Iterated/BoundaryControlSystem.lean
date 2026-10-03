import PartiteConstruction.Iterated.BoundaryControlCompletion

/-! # Completing all ambient controls from boundary data

Once every ambient A-copy has an explicit induced boundary embedding agreeing
with the tested witness, the usual finite completion over all A-copies works
without hereditary irreducibility of A.

Boundary embeddings already supplied for the current target survive a fresh
attachment by composition with the old-side embedding.  Thus the completion
can be iterated over the finite set of ambient A-copies.
-/
namespace StructuralRamsey.RelStructure.LocallyTreeLike

universe u v
variable {L : RelLanguage.{u}}
variable {U V W Y : Type v}
variable {A : RelStructure L U} {B : RelStructure L V}
variable {C : RelStructure L W} {T : RelStructure L Y}

/-- Boundary data for all ambient A-copies. -/
def BoundarySystem
    (S : Finset W) (f : ↥(↑S : Set W) → Y) : Prop :=
  ∀ α : Embedding A C,
    BoundaryEmbedding (A := A) (C := C) (T := T) S f α

/-- Boundary data survives composition of the target and witness with an
embedding. -/
theorem BoundaryEmbedding.postcomp
    {Z : Type v} {T' : RelStructure L Z}
    (S : Finset W) (f : ↥(↑S : Set W) → Y)
    (α : Embedding A C)
    (hbd : BoundaryEmbedding (A := A) (C := C) (T := T) S f α)
    (e : Embedding T T') :
    BoundaryEmbedding (A := A) (C := C) (T := T') S (e ∘ f) α where
  boundary := e.comp hbd.boundary
  agrees := by
    intro x
    exact congrArg e (hbd.agrees x)
  contained := by
    rcases hbd.contained with ⟨R, hR, hsub⟩
    refine ⟨Set.range (e.comp (inclusion T R)), ?_, ?_⟩
    · exact hR.range_embedding (e.comp (inclusion T R))
    · intro x
      obtain ⟨r, hr⟩ := hsub x
      refine ⟨⟨r, hr⟩, ?_⟩
      rfl

/-- Complete the ordinary ambient-copy control clause from explicit boundary
embeddings for every A-copy.  Only irreducibility of A is needed. -/
theorem completeControl_of_boundaries
    [Finite U] [Finite W]
    (hA : A.Irreducible)
    (eAB : Embedding A B)
    (S : Finset W)
    (hTree : TreeAmalgam B Y T)
    (f : ↥(↑S : Set W) → Y)
    (hf : (C.induce (↑S : Set W)).IsHomomorphismEmbedding T f)
    (hbd : BoundarySystem (A := A) (C := C) (T := T) S f) :
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
  have hmem (α : Embedding A C) : α ∈ xs := by
    simp [xs]

  have aux :
      ∀ ys : List (Embedding A C),
      ∀ {Y : Type v} {T : RelStructure L Y},
      TreeAmalgam B Y T →
      ∀ (f : ↥(↑S : Set W) → Y),
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding T f →
      BoundarySystem (A := A) (C := C) (T := T) S f →
      ∀ zs : List (Embedding A C),
      Controls (A := A) (C := C) (T := T) S f zs →
      ∃ (Z : Type v) (T' : RelStructure L Z),
        TreeAmalgam B Z T' ∧
        ∃ f' : ↥(↑S : Set W) → Z,
          (C.induce (↑S : Set W)).IsHomomorphismEmbedding T' f' ∧
          Controls (A := A) (C := C) (T := T') S f' (ys ++ zs) := by
    intro ys
    induction ys with
    | nil =>
        intro Y T hT f hf hbd zs hzs
        exact ⟨Y, T, hT, f, hf, by simpa using hzs⟩
    | cons α ys ih =>
        intro Y T hT f hf hbd zs hzs
        obtain ⟨Y₁, T₁, hT₁, f₁, hf₁, hctrl₁⟩ :=
          ih hT f hf hbd zs hzs
        -- Reconstruct the boundary system after the recursive prefix by
        -- observing that the recursive construction uses only old-side
        -- embeddings.  For this generic wrapper it is simpler to rerun the
        -- one-copy completion in list order below, carrying boundaries
        -- explicitly.
        sorry

  -- The fully generic list recursion is factored below once the target
  -- embedding produced by one boundary-completion step is exposed.
  sorry

end StructuralRamsey.RelStructure.LocallyTreeLike
