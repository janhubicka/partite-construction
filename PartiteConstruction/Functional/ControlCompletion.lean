import PartiteConstruction.Functional.FullFreeAmalgam
import PartiteConstruction.Functional.ProjectedHistoryTreeCompletion

/-! # Functional control completion

Full-function analogue of the relational control-completion construction.
A closed tested intersection with an ambient A-copy is itself a genuine
closed substructure of A.  If such an intersection is already embedded in a
controlled irreducible piece of the current B-tree, we may attach one fresh
copy of B over it.  Repeating this for all ambient A-copies turns all future
mixed gluing roots into strict tree roots without changing the tested map.
-/

namespace StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {U V W Y Z : Type v}
variable {A : Structure L U} {B : Structure L V}
variable {C : Structure L W} {T : Structure L Y}

/-- Explicitly embedded intersections of a closed finite test with every
ambient A-copy. -/
def FunctionalEmbeddedIntersections
    (S : Finset W) (hS : C.IsClosed (↑S : Set W))
    (f : ↥(↑S : Set W) → Y) : Prop :=
  ∀ α : Embedding A C,
    let Hset : Set U := {a : U | α a ∈ S}
    let hH : A.IsClosed Hset := closed_preimage α (↑S : Set W) hS
    ∃ eHT : Embedding (A.induce Hset hH) T,
      (∀ x, eHT x = f ⟨α x.1, x.2⟩) ∧
      eHT.ContainedInIrreducible

/-- A finite list of ambient A-copies is controlled by whole A-copies in the
target tree. -/
def FunctionalControls
    (S : Finset W) (f : ↥(↑S : Set W) → Y)
    (xs : List (Embedding A C)) : Prop :=
  ∀ α ∈ xs, ∃ α' : Embedding A T,
    ∀ a : U, ∀ ha : α a ∈ S,
      ∃ a' : U, f ⟨α a, ha⟩ = α' a'

namespace FunctionalEmbeddedIntersections

/-- Embedded-intersection data survives postcomposition by a full target
embedding. -/
theorem postcomp
    {S : Finset W} {hS : C.IsClosed (↑S : Set W)}
    {f : ↥(↑S : Set W) → Y}
    (h : FunctionalEmbeddedIntersections
      (A := A) (C := C) (T := T) S hS f)
    {T' : Structure L Z} (j : Embedding T T') :
    FunctionalEmbeddedIntersections
      (A := A) (C := C) (T := T') S hS (j ∘ f) := by
  intro α
  dsimp
  obtain ⟨eHT, heHT, hcHT⟩ := h α
  refine ⟨j.comp eHT, ?_, hcHT.postcomp j⟩
  intro x
  change j (eHT x) = j (f ⟨α x.1, x.2⟩)
  exact congrArg j (heHT x)

end FunctionalEmbeddedIntersections

namespace FunctionalProjectedPartialIntersections

/-- Projected-partial certificates give ordinary ambient intersection
certificates whenever the ambient projection is an EHN projection and A is
irreducible.  The EHN invariant supplies the full projected A-copy used by the
certificate. -/
theorem toEmbeddedIntersections
    {P : Type v} {D : Structure L P}
    {Base : Structure L V} {Target : Structure L Y}
    {p : W → P}
    {S : Finset W} {hS : C.IsClosed (↑S : Set W)}
    {f : ↥(↑S : Set W) → Y}
    (hA : A.Irreducible)
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (h :
      FunctionalProjectedPartialIntersections
        (A := A) (D := D) (C := C) (T := Target)
        p S f) :
    FunctionalEmbeddedIntersections
      (A := A) (C := C) (T := Target) S hS f := by
  intro α
  dsimp
  obtain ⟨β, hβ⟩ := hp.2 A hA α
  let Hset : Set U := {a : U | α a ∈ S}
  let hH : A.IsClosed Hset :=
    closed_preimage α (↑S : Set W) hS
  let eH : Embedding (A.induce Hset hH) C :=
    α.comp (inclusion A Hset hH)
  have hproj : ∀ x, p (eH x) = β x.1 := by
    intro x
    exact (hβ x.1).symm
  have hRange : ∀ x, eH x ∈ S := by
    intro x
    exact x.2
  exact h β Hset hH eH hproj hRange

/-- Projected-partial certificates specialize to ordinary ambient
intersection certificates when the projection is the identity on the ambient
structure. -/
theorem toEmbeddedIntersections_identity
    {P : Type v} {D : Structure L P}
    {Base : Structure L V} {Target : Structure L Y}
    {S : Finset P} {hS : D.IsClosed (↑S : Set P)}
    {f : ↥(↑S : Set P) → Y}
    (h :
      FunctionalProjectedPartialIntersections
        (A := A) (D := D) (C := D) (T := Target)
        id S f) :
    FunctionalEmbeddedIntersections
      (A := A) (C := D) (T := Target) S hS f := by
  intro α
  dsimp
  let Hset : Set U := {a : U | α a ∈ S}
  let hH : A.IsClosed Hset :=
    closed_preimage α (↑S : Set P) hS
  let eH : Embedding (A.induce Hset hH) D :=
    α.comp (inclusion A Hset hH)
  have hproj : ∀ x, (id : P → P) (eH x) = α x.1 := by
    intro x
    rfl
  have hRange : ∀ x, eH x ∈ S := fun x => x.2
  exact h α Hset hH eH hproj hRange

end FunctionalProjectedPartialIntersections

namespace LocallyClosedTreeCompletable

/-- Add strict control for one ambient A-copy. -/
theorem addControl_of_embeddedIntersection
    (hA : A.Irreducible)
    (eAB : Embedding A B)
    (S : Finset W) (hS : C.IsClosed (↑S : Set W))
    (hTree : TreeAmalgam B Y T)
    (f : ↥(↑S : Set W) → Y)
    (hf : (C.induce (↑S : Set W) hS).IsHomomorphismEmbedding T f)
    (xs : List (Embedding A C))
    (hctrl : FunctionalControls
      (A := A) (C := C) (T := T) S f xs)
    (α : Embedding A C)
    (hInt :
      let Hset : Set U := {a : U | α a ∈ S}
      let hH : A.IsClosed Hset :=
        closed_preimage α (↑S : Set W) hS
      ∃ eHT : Embedding (A.induce Hset hH) T,
        (∀ x, eHT x = f ⟨α x.1, x.2⟩) ∧
        eHT.ContainedInIrreducible) :
    ∃ (Z : Type v) (T' : Structure L Z),
      TreeAmalgam B Z T' ∧
      ∃ j : Embedding T T',
        (C.induce (↑S : Set W) hS).IsHomomorphismEmbedding T' (j ∘ f) ∧
        FunctionalControls
          (A := A) (C := C) (T := T') S (j ∘ f) (α :: xs) := by
  classical
  let Hset : Set U := {a : U | α a ∈ S}
  let hH : A.IsClosed Hset :=
    closed_preimage α (↑S : Set W) hS
  let H := A.induce Hset hH
  obtain ⟨eHT, heHT, hcT⟩ := hInt
  let eHB : Embedding H B :=
    eAB.comp (inclusion A Hset hH)
  have hcB : eHB.ContainedInIrreducible := by
    refine ⟨U, A, hA, eAB, ?_⟩
    intro x
    exact ⟨x.1, rfl⟩
  let T' := FreeAmalgam.amalgam H T B eHT eHB
  let l : Embedding T T' :=
    FreeAmalgam.leftEmbedding H T B eHT eHB
  let r : Embedding B T' :=
    FreeAmalgam.rightEmbedding H T B eHT eHB
  have hfree : IsFreeAmalgam eHT eHB l r :=
    FreeAmalgam.isFreeAmalgam H T B eHT eHB
  have hTree' : TreeAmalgam B _ T' :=
    FreeAmalgam.treeAmalgam H T B eHT eHB B
      hTree
      (TreeAmalgam.copy (Embedding.id B) (by
        intro b
        exact ⟨b, rfl⟩))
      hcT hcB
  have hf' :
      (C.induce (↑S : Set W) hS).IsHomomorphismEmbedding T' (l ∘ f) :=
    l.isHomomorphismEmbedding.comp hf
  refine ⟨_, T', hTree', l, hf', ?_⟩
  intro β hβ
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
      _ = r (eHB ah) := by
        exact
          (hfree.overlap (eHT ah) (eHB ah)).mpr
            ⟨ah, rfl, rfl⟩
      _ = r (eAB a) := rfl
  · obtain ⟨β', hβ'⟩ := hctrl β hβ
    refine ⟨l.comp β', ?_⟩
    intro a ha
    obtain ⟨a', ha'⟩ := hβ' a ha
    exact ⟨a', congrArg l ha'⟩

/-- Complete strict control for every ambient A-copy while retaining the
embedding of the original tree target. -/
theorem completeControl_of_embeddedIntersections_with_embedding
    [Finite U] [Finite W]
    (hA : A.Irreducible)
    (eAB : Embedding A B)
    (S : Finset W) (hS : C.IsClosed (↑S : Set W))
    (hTree : TreeAmalgam B Y T)
    (f : ↥(↑S : Set W) → Y)
    (hf : (C.induce (↑S : Set W) hS).IsHomomorphismEmbedding T f)
    (hInt : FunctionalEmbeddedIntersections
      (A := A) (C := C) (T := T) S hS f) :
    ∃ (Z : Type v) (T' : Structure L Z),
      TreeAmalgam B Z T' ∧
      ∃ j : Embedding T T',
        (C.induce (↑S : Set W) hS).IsHomomorphismEmbedding T' (j ∘ f) ∧
        ∀ α : Embedding A C,
          ∃ α' : Embedding A T',
            ∀ a : U, ∀ ha : α a ∈ S,
              ∃ a' : U, (j ∘ f) ⟨α a, ha⟩ = α' a' := by
  classical
  letI : Fintype (Embedding A C) := Fintype.ofFinite _
  let ys : List (Embedding A C) := Finset.univ.toList
  have aux :
      ∀ ys0 : List (Embedding A C),
      ∀ {Y0 : Type v} {T0 : Structure L Y0},
      TreeAmalgam B Y0 T0 →
      ∀ (f0 : ↥(↑S : Set W) → Y0),
      (C.induce (↑S : Set W) hS).IsHomomorphismEmbedding T0 f0 →
      FunctionalEmbeddedIntersections
        (A := A) (C := C) (T := T0) S hS f0 →
      ∀ zs : List (Embedding A C),
      FunctionalControls
        (A := A) (C := C) (T := T0) S f0 zs →
      ∃ (Z0 : Type v) (T1 : Structure L Z0),
        TreeAmalgam B Z0 T1 ∧
        ∃ j : Embedding T0 T1,
          (C.induce (↑S : Set W) hS).IsHomomorphismEmbedding T1 (j ∘ f0) ∧
          FunctionalEmbeddedIntersections
            (A := A) (C := C) (T := T1) S hS (j ∘ f0) ∧
          FunctionalControls
            (A := A) (C := C) (T := T1) S (j ∘ f0)
              (ys0.reverse ++ zs) := by
    intro ys0
    induction ys0 with
    | nil =>
        intro Y0 T0 hTree0 f0 hf0 hInt0 zs hctrl0
        let j : Embedding T0 T0 := Embedding.id T0
        have hjf : j ∘ f0 = f0 := by
          funext x
          rfl
        refine ⟨Y0, T0, hTree0, j, ?_, ?_, ?_⟩
        · rw [hjf]
          exact hf0
        · rw [hjf]
          exact hInt0
        · rw [hjf]
          simpa using hctrl0
    | cons α ys1 ih =>
        intro Y0 T0 hTree0 f0 hf0 hInt0 zs hctrl0
        obtain ⟨Y1, T1, hTree1, j1, hf1, hctrl1⟩ :=
          addControl_of_embeddedIntersection
            (A := A) (B := B) (C := C)
            hA eAB S hS hTree0 f0 hf0 zs hctrl0 α (hInt0 α)
        have hInt1 :
            FunctionalEmbeddedIntersections
              (A := A) (C := C) (T := T1) S hS (j1 ∘ f0) :=
          hInt0.postcomp j1
        obtain ⟨Z0, T2, hTree2, j2, hf2, hInt2, hctrl2⟩ :=
          ih hTree1 (j1 ∘ f0) hf1 hInt1 (α :: zs) hctrl1
        let j : Embedding T0 T2 := j2.comp j1
        refine ⟨Z0, T2, hTree2, j, ?_, ?_, ?_⟩
        · simpa [j, Function.comp_def] using hf2
        · simpa [j, Function.comp_def] using hInt2
        · simpa [j, Function.comp_def,
            List.reverse_cons, List.append_assoc] using hctrl2
  obtain ⟨Z0, T', hTree', j, hf', _hInt', hctrl'⟩ :=
    aux ys hTree f hf hInt [] (by
      intro α hmem
      exact (List.not_mem_nil hmem).elim)
  refine ⟨Z0, T', hTree', j, hf', ?_⟩
  intro α
  exact hctrl' α (by simp [ys])

end LocallyClosedTreeCompletable

end StructuralRamsey.Structure
