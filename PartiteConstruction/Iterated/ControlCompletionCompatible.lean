import PartiteConstruction.Iterated.ControlCompletion

/-! # Control completion from explicit embedded intersections

The old `completeControl` derives an embedding of every tested ambient
A-intersection from hereditary irreducibility of A.  This file separates the
real requirement: it is enough to be given those intersection embeddings,
with their images contained in irreducible pieces of the current tree.

This formulation uses only irreducibility of A itself.  The data is stable
under postcomposition by target embeddings, so all ambient A-copies can be
processed successively.
-/
namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V W Y Z : Type v}
variable {A : RelStructure L U} {B : RelStructure L V}
variable {C : RelStructure L W} {T : RelStructure L Y}

namespace Embedding.ContainedInIrreducible

/-- Containment in an irreducible piece is preserved by postcomposition with
an induced embedding of the target. -/
theorem postcomp
    {H : Type v} {D : RelStructure L H}
    {e : Embedding D T} (hc : e.ContainedInIrreducible)
    {T' : RelStructure L Z} (j : Embedding T T') :
    (j.comp e).ContainedInIrreducible := by
  rcases hc with ⟨S, hS, hRange⟩
  let eS : Embedding (T.induce S) T' :=
    j.comp (inclusion T S)
  let R : Set Z := Set.range eS
  refine ⟨R, hS.range_embedding eS, ?_⟩
  intro x
  have hxS : e x ∈ S := hRange x
  refine ⟨(⟨e x, hxS⟩ : S), ?_⟩
  rfl

end Embedding.ContainedInIrreducible

namespace LocallyTreeLike

/-- Explicitly embedded tested intersections for all ambient A-copies. -/
def EmbeddedIntersections
    (S : Finset W) (f : ↥(↑S : Set W) → Y) : Prop :=
  ∀ α : Embedding A C,
    let Hset : Set U := {a : U | α a ∈ S}
    ∃ eHT : Embedding (A.induce Hset) T,
      (∀ x, eHT x = f ⟨α x.1, x.2⟩) ∧
      eHT.ContainedInIrreducible

/-- Embedded-intersection data survives postcomposition of the witness with
an embedding of the target. -/
theorem EmbeddedIntersections.postcomp
    (S : Finset W) (f : ↥(↑S : Set W) → Y)
    (h : EmbeddedIntersections (A := A) (C := C) (T := T) S f)
    {T' : RelStructure L Z} (j : Embedding T T') :
    EmbeddedIntersections (A := A) (C := C) (T := T') S (j ∘ f) := by
  intro α
  obtain ⟨eHT, heHT, hcHT⟩ := h α
  refine ⟨j.comp eHT, ?_, hcHT.postcomp j⟩
  intro x
  change j (eHT x) = j (f ⟨α x.1, x.2⟩)
  exact congrArg j (heHT x)

/-- Add control for one ambient A-copy from an explicitly embedded
intersection, with no hereditary irreducibility assumption on A. -/
theorem addControl_of_embeddedIntersection
    (hA : A.Irreducible)
    (eAB : Embedding A B)
    (S : Finset W)
    (hTree : TreeAmalgam B Y T)
    (f : ↥(↑S : Set W) → Y)
    (hf : (C.induce (↑S : Set W)).IsHomomorphismEmbedding T f)
    (xs : List (Embedding A C))
    (hctrl : Controls (A := A) (C := C) (T := T) S f xs)
    (α : Embedding A C)
    (hInt :
      let Hset : Set U := {a : U | α a ∈ S}
      ∃ eHT : Embedding (A.induce Hset) T,
        (∀ x, eHT x = f ⟨α x.1, x.2⟩) ∧
        eHT.ContainedInIrreducible) :
    ∃ (Z : Type v) (T' : RelStructure L Z),
      TreeAmalgam B Z T' ∧
      ∃ j : Embedding T T',
        (C.induce (↑S : Set W)).IsHomomorphismEmbedding T' (j ∘ f) ∧
        Controls (A := A) (C := C) (T := T') S (j ∘ f) (α :: xs) := by
  classical
  let Hset : Set U := {a : U | α a ∈ S}
  let H := A.induce Hset
  obtain ⟨eHT, heHT, hcT⟩ := hInt
  let eHB : Embedding H B :=
    eAB.comp (inclusion A Hset)
  have hcB : eHB.ContainedInIrreducible := by
    apply Embedding.containedInIrreducible_of_range_subset hA eAB eHB
    intro x
    exact ⟨x.1, rfl⟩
  let T' := FreeAmalgam.amalgam H T B eHT eHB
  let l : Embedding T T' :=
    FreeAmalgam.leftEmbedding H T B eHT eHB
  let r : Embedding B T' :=
    FreeAmalgam.rightEmbedding H T B eHT eHB
  have hTree' : TreeAmalgam B _ T' :=
    FreeAmalgam.treeAmalgam H T B eHT eHB B
      hTree (TreeAmalgam.copy (Iso.refl B)) hcT hcB
  have hf' :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding T' (l ∘ f) :=
    l.isHomomorphismEmbedding.comp hf
  refine ⟨_, T', hTree', l, hf', ?_⟩
  · intro β hβ
    rcases List.mem_cons.mp hβ with hβα | hβ
    · subst β
      let α' : Embedding A T' := r.comp eAB
      refine ⟨α', ?_⟩
      intro a ha
      refine ⟨a, ?_⟩
      let ah : Hset := ⟨a, ha⟩
      change l (f ⟨α a, ha⟩) = r (eAB a)
      calc
        l (f ⟨α a, ha⟩) = l (eHT ah) :=
          congrArg l (heHT ah).symm
        _ = r (eHB ah) :=
          FreeAmalgam.left_right_overlap H T B eHT eHB ah
        _ = r (eAB a) := rfl
    · obtain ⟨β', hβ'⟩ := hctrl β hβ
      refine ⟨l.comp β', ?_⟩
      intro a ha
      obtain ⟨a', ha'⟩ := hβ' a ha
      exact ⟨a', congrArg l ha'⟩


/-- Complete control for every ambient A-copy from a coherent family of
embedded intersections.  Hereditary irreducibility of A is not used. -/
theorem completeControl_of_embeddedIntersections
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
      ∃ f' : ↥(↑S : Set W) → Z,
        (C.induce (↑S : Set W)).IsHomomorphismEmbedding T' f' ∧
        ∀ α : Embedding A C,
          ∃ α' : Embedding A T',
            ∀ a : U, ∀ ha : α a ∈ S,
              ∃ a' : U, f' ⟨α a, ha⟩ = α' a' := by
  classical
  letI : Fintype (Embedding A C) := Fintype.ofFinite _
  let xs : List (Embedding A C) := Finset.univ.toList
  have aux :
      ∀ ys : List (Embedding A C),
      ∀ {Y₀ : Type v} {T₀ : RelStructure L Y₀},
      TreeAmalgam B Y₀ T₀ →
      ∀ (f₀ : ↥(↑S : Set W) → Y₀),
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding T₀ f₀ →
      EmbeddedIntersections (A := A) (C := C) (T := T₀) S f₀ →
      ∀ zs : List (Embedding A C),
      Controls (A := A) (C := C) (T := T₀) S f₀ zs →
      ∃ (Z₀ : Type v) (T₁ : RelStructure L Z₀),
        TreeAmalgam B Z₀ T₁ ∧
        ∃ f₁ : ↥(↑S : Set W) → Z₀,
          (C.induce (↑S : Set W)).IsHomomorphismEmbedding T₁ f₁ ∧
          EmbeddedIntersections (A := A) (C := C) (T := T₁) S f₁ ∧
          Controls (A := A) (C := C) (T := T₁) S f₁
            (ys.reverse ++ zs) := by
    intro ys
    induction ys with
    | nil =>
        intro Y₀ T₀ hTree₀ f₀ hf₀ hInt₀ zs hctrl₀
        exact ⟨Y₀, T₀, hTree₀, f₀, hf₀, hInt₀, by simpa using hctrl₀⟩
    | cons α ys ih =>
        intro Y₀ T₀ hTree₀ f₀ hf₀ hInt₀ zs hctrl₀
        obtain ⟨Y₁, T₁, hTree₁, j, hf₁, hctrl₁⟩ :=
          addControl_of_embeddedIntersection
            (A := A) (B := B) (C := C)
            hA eAB S hTree₀ f₀ hf₀ zs hctrl₀ α (hInt₀ α)
        have hInt₁ :
            EmbeddedIntersections (A := A) (C := C) (T := T₁)
              S (j ∘ f₀) :=
          hInt₀.postcomp S f₀ j
        obtain ⟨Z₀, T₂, hTree₂, f₂, hf₂, hInt₂, hctrl₂⟩ :=
          ih hTree₁ (j ∘ f₀) hf₁ hInt₁ (α :: zs) hctrl₁
        refine ⟨Z₀, T₂, hTree₂, f₂, hf₂, hInt₂, ?_⟩
        simpa [List.reverse_cons, List.append_assoc] using hctrl₂
  obtain ⟨Z, T', hTree', f', hf', _hInt', hctrl'⟩ :=
    aux xs hTree f hf hInt [] (by
      intro α hmem
      exact (List.not_mem_nil hmem).elim)
  refine ⟨Z, T', hTree', f', hf', ?_⟩
  intro α
  apply hctrl' α
  simp [xs]


end LocallyTreeLike
end StructuralRamsey.RelStructure
