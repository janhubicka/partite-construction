import PartiteConstruction.Iterated.ControlCompletionCompatible

/-! # Compatible control completion with the target embedding exposed

Relative completion data (distinguished A-copies, quotient roots, finite
history constraints) survives ordinary control completion by postcomposition
with the embedding of the old target into the completed target.

The existing compatible completion theorem hides that embedding.  This file
provides the transport-friendly variant and accumulates the embeddings through
the finite list of ambient A-copies.
-/
namespace StructuralRamsey.RelStructure.LocallyTreeLike

universe u v
variable {L : RelLanguage.{u}}
variable {U V W Y : Type v}
variable {A : RelStructure L U} {B : RelStructure L V}
variable {C : RelStructure L W} {T : RelStructure L Y}

/-- Process a finite list of ambient A-copies while exposing the embedding of
the initial target into the final target. -/
theorem completeControlList_of_embeddedIntersections_with_embedding
    (hA : A.Irreducible)
    (eAB : Embedding A B)
    (S : Finset W)
    (ys : List (Embedding A C))
    (hTree : TreeAmalgam B Y T)
    (f : ↥(↑S : Set W) → Y)
    (hf : (C.induce (↑S : Set W)).IsHomomorphismEmbedding T f)
    (hInt : EmbeddedIntersections (A := A) (C := C) (T := T) S f)
    (zs : List (Embedding A C))
    (hctrl : Controls (A := A) (C := C) (T := T) S f zs) :
    ∃ (Z : Type v) (T' : RelStructure L Z),
      TreeAmalgam B Z T' ∧
      ∃ j : Embedding T T',
        (C.induce (↑S : Set W)).IsHomomorphismEmbedding T' (j ∘ f) ∧
        EmbeddedIntersections (A := A) (C := C) (T := T') S (j ∘ f) ∧
        Controls (A := A) (C := C) (T := T') S (j ∘ f)
          (ys.reverse ++ zs) := by
  classical
  induction ys generalizing Y zs with
  | nil =>
      let j : Embedding T T := Embedding.id T
      have hjf : j ∘ f = f := by
        funext x
        rfl
      refine ⟨Y, T, hTree, j, ?_, ?_, ?_⟩
      · rw [hjf]
        exact hf
      · rw [hjf]
        exact hInt
      · rw [hjf]
        simpa using hctrl
  | cons α ys ih =>
      obtain ⟨Y₁, T₁, hTree₁, j₁, hf₁, hctrl₁⟩ :=
        addControl_of_embeddedIntersection
          (A := A) (B := B) (C := C)
          hA eAB S hTree f hf zs hctrl α (hInt α)
      have hInt₁ :
          EmbeddedIntersections (A := A) (C := C) (T := T₁)
            S (j₁ ∘ f) :=
        hInt.postcomp S f j₁
      obtain ⟨Z, T₂, hTree₂, j₂, hf₂, hInt₂, hctrl₂⟩ :=
        ih hTree₁ (j₁ ∘ f) hf₁ hInt₁ (α :: zs) hctrl₁
      let j : Embedding T T₂ := j₂.comp j₁
      refine ⟨Z, T₂, hTree₂, j, ?_, ?_, ?_⟩
      · simpa [j, Function.comp_def] using hf₂
      · simpa [j, Function.comp_def] using hInt₂
      · simpa [j, Function.comp_def, List.reverse_cons, List.append_assoc] using hctrl₂

/-- Complete all ambient A-copy controls while retaining the embedding of the
original target into the completed one.  Only irreducibility of A is used. -/
theorem completeControl_of_embeddedIntersections_with_embedding
    [Finite U] [Finite W]
    (hA : A.Irreducible)
    (eAB : Embedding A B)
    (S : Finset W)
    (hTree : TreeAmalgam B Y T)
    (f : ↥(↑S : Set W) → Y)
    (hf : (C.induce (↑S : Set W)).IsHomomorphismEmbedding T f)
    (hInt : EmbeddedIntersections (A := A) (C := C) (T := T) S f) :
    ∃ (Z : Type v) (T' : RelStructure L Z),
      TreeAmalgam B Z T' ∧
      ∃ j : Embedding T T',
        (C.induce (↑S : Set W)).IsHomomorphismEmbedding T' (j ∘ f) ∧
        ∀ α : Embedding A C,
          ∃ α' : Embedding A T',
            ∀ a : U, ∀ ha : α a ∈ S,
              ∃ a' : U, (j ∘ f) ⟨α a, ha⟩ = α' a' := by
  classical
  letI : Fintype (Embedding A C) := Fintype.ofFinite _
  let xs : List (Embedding A C) := Finset.univ.toList
  obtain ⟨Z, T', hTree', j, hf', _hInt', hctrl'⟩ :=
    completeControlList_of_embeddedIntersections_with_embedding
      (A := A) (B := B) (C := C)
      hA eAB S xs hTree f hf hInt [] (by
        intro α hmem
        exact (List.not_mem_nil hmem).elim)
  refine ⟨Z, T', hTree', j, hf', ?_⟩
  intro α
  exact hctrl' α (by simp [xs])

end StructuralRamsey.RelStructure.LocallyTreeLike
