import PartiteConstruction.Functional.FunctionClosedLocalTree
import PartiteConstruction.Iterated.ControlCompletionCompatible

/-! # Control completion for function-closed graph trees

This is the closure-aware analogue of relational control completion.  A tested
intersection with an ambient A-copy is represented by a closed embedding into
the current target tree whose image already lies in an irreducible piece.
Attaching one fresh Base-copy over that boundary preserves both the strict
tree geometry and function-closedness.
-/

namespace StructuralRamsey.RelStructure

open Structure

universe u v

variable {L : Language.{u}}
variable {U V W Y Z : Type v}
variable {A : RelStructure L.graph U}
variable {Base : RelStructure L.graph V}
variable {C : RelStructure L.graph W}
variable {T : RelStructure L.graph Y}

/-- Explicit closed tested intersections for every ambient closed A-copy. -/
def FunctionClosedEmbeddedIntersections
    (S : Finset W) (hS : FunctionClosedSet C (↑S : Set W))
    (f : ClosedEmbedding (C.induce (↑S : Set W)) T) : Prop :=
  ∀ α : ClosedEmbedding A C,
    let Hset : Set U := {a : U | α a ∈ S}
    let hH : FunctionClosedSet A Hset :=
      α.toEmbedding.functionClosedSet_preimage hS
    ∃ eHT : ClosedEmbedding (A.induce Hset) T,
      (∀ x, eHT x = f ⟨α x.1, x.2⟩) ∧
      eHT.toEmbedding.ContainedInIrreducible

/-- Closed control for a finite list of ambient A-copies. -/
def FunctionClosedControls
    (S : Finset W)
    (f : ClosedEmbedding (C.induce (↑S : Set W)) T)
    (xs : List (ClosedEmbedding A C)) : Prop :=
  ∀ α ∈ xs, ∃ α' : ClosedEmbedding A T,
    ∀ a : U, ∀ ha : α a ∈ S,
      ∃ a' : U, f ⟨α a, ha⟩ = α' a'

namespace FunctionClosedEmbeddedIntersections

/-- Closed embedded-intersection data survives postcomposition by a closed
target embedding. -/
theorem postcomp
    {S : Finset W} {hS : FunctionClosedSet C (↑S : Set W)}
    {f : ClosedEmbedding (C.induce (↑S : Set W)) T}
    (h : FunctionClosedEmbeddedIntersections
      (A := A) (C := C) (T := T) S hS f)
    {T' : RelStructure L.graph Z}
    (j : ClosedEmbedding T T') :
    FunctionClosedEmbeddedIntersections
      (A := A) (C := C) (T := T') S hS
      (ClosedEmbedding.comp j f) := by
  intro α
  dsimp
  obtain ⟨eHT, heHT, hcHT⟩ := h α
  refine ⟨ClosedEmbedding.comp j eHT, ?_, hcHT.postcomp j.toEmbedding⟩
  intro x
  change j (eHT x) = j (f ⟨α x.1, x.2⟩)
  exact congrArg j (heHT x)

end FunctionClosedEmbeddedIntersections

namespace FunctionClosedHasTreeCompletion

/-- Add strict closed control for one ambient A-copy. -/
theorem addControl_of_embeddedIntersection
    (hA : A.Irreducible)
    (eAB : ClosedEmbedding A Base)
    (S : Finset W) (hS : FunctionClosedSet C (↑S : Set W))
    (hTree : FunctionClosedTreeAmalgam Base Y T)
    (f : ClosedEmbedding (C.induce (↑S : Set W)) T)
    (xs : List (ClosedEmbedding A C))
    (hctrl : FunctionClosedControls
      (A := A) (C := C) (T := T) S f xs)
    (α : ClosedEmbedding A C)
    (hInt :
      let Hset : Set U := {a : U | α a ∈ S}
      let hH : FunctionClosedSet A Hset :=
        α.toEmbedding.functionClosedSet_preimage hS
      ∃ eHT : ClosedEmbedding (A.induce Hset) T,
        (∀ x, eHT x = f ⟨α x.1, x.2⟩) ∧
        eHT.toEmbedding.ContainedInIrreducible) :
    ∃ (Z0 : Type v) (T' : RelStructure L.graph Z0),
      FunctionClosedTreeAmalgam Base Z0 T' ∧
      ∃ j : ClosedEmbedding T T',
        FunctionClosedControls
          (A := A) (C := C) (T := T') S
          (ClosedEmbedding.comp j f) (α :: xs) := by
  classical
  let Hset : Set U := {a : U | α a ∈ S}
  let hH : FunctionClosedSet A Hset :=
    α.toEmbedding.functionClosedSet_preimage hS
  let H := A.induce Hset
  obtain ⟨eHT, heHT, hcHT⟩ := hInt
  let incA : ClosedEmbedding H A :=
    ClosedEmbedding.inclusion A Hset hH
  let eHB : ClosedEmbedding H Base :=
    ClosedEmbedding.comp eAB incA
  have hcHB : eHB.toEmbedding.ContainedInIrreducible := by
    apply Embedding.containedInIrreducible_of_range_subset
      hA eAB.toEmbedding eHB.toEmbedding
    intro x
    exact ⟨x.1, rfl⟩
  let T' :=
    FreeAmalgam.amalgam H T Base eHT.toEmbedding eHB.toEmbedding
  let l : Embedding T T' :=
    FreeAmalgam.leftEmbedding H T Base eHT.toEmbedding eHB.toEmbedding
  let r : Embedding Base T' :=
    FreeAmalgam.rightEmbedding H T Base eHT.toEmbedding eHB.toEmbedding
  have hfree :
      IsFreeAmalgam eHT.toEmbedding eHB.toEmbedding l r :=
    FreeAmalgam.isFreeAmalgam
      H T Base eHT.toEmbedding eHB.toEmbedding
  have hsides :
      FunctionClosedMap T T' l ∧ FunctionClosedMap Base T' r :=
    FunctionClosedTreeAmalgam.glue_sides_closed
      eHT.closed eHB.closed hfree
  let lClosed : ClosedEmbedding T T' := ⟨l, hsides.1⟩
  let rClosed : ClosedEmbedding Base T' := ⟨r, hsides.2⟩
  have hTree' :
      FunctionClosedTreeAmalgam Base _ T' :=
    FunctionClosedTreeAmalgam.glue
      hTree
      (FunctionClosedTreeAmalgam.copy (RelStructure.Iso.refl Base))
      eHT.toEmbedding eHB.toEmbedding
      eHT.closed eHB.closed hcHT hcHB l r hfree
  refine ⟨_, T', hTree', lClosed, ?_⟩
  intro β hβ
  rcases List.mem_cons.mp hβ with hβα | hβ
  · subst β
    let α' : ClosedEmbedding A T' :=
      ClosedEmbedding.comp rClosed eAB
    refine ⟨α', ?_⟩
    intro a ha
    refine ⟨a, ?_⟩
    let ah : Hset := ⟨a, ha⟩
    change l (f ⟨α a, ha⟩) = r (eAB a)
    calc
      l (f ⟨α a, ha⟩) = l (eHT ah) :=
        congrArg l (heHT ah).symm
      _ = r (eHB ah) :=
        (hfree.overlap (eHT ah) (eHB ah)).mpr
          ⟨ah, rfl, rfl⟩
      _ = r (eAB a) := rfl
  · obtain ⟨β', hβ'⟩ := hctrl β hβ
    let β'' : ClosedEmbedding A T' :=
      ClosedEmbedding.comp lClosed β'
    refine ⟨β'', ?_⟩
    intro a ha
    obtain ⟨a', ha'⟩ := hβ' a ha
    exact ⟨a', congrArg l ha'⟩

/-- Complete strict closed control for every ambient closed A-copy while
retaining a closed embedding of the original target tree. -/
theorem completeControl_of_embeddedIntersections
    [Finite U] [Finite W]
    (hA : A.Irreducible)
    (eAB : ClosedEmbedding A Base)
    (S : Finset W) (hS : FunctionClosedSet C (↑S : Set W))
    (hTree : FunctionClosedTreeAmalgam Base Y T)
    (f : ClosedEmbedding (C.induce (↑S : Set W)) T)
    (hInt : FunctionClosedEmbeddedIntersections
      (A := A) (C := C) (T := T) S hS f) :
    ∃ (Z0 : Type v) (T' : RelStructure L.graph Z0),
      FunctionClosedTreeAmalgam Base Z0 T' ∧
      ∃ j : ClosedEmbedding T T',
        FunctionClosedEmbeddedIntersections
          (A := A) (C := C) (T := T') S hS
          (ClosedEmbedding.comp j f) ∧
        ∀ α : ClosedEmbedding A C,
          ∃ α' : ClosedEmbedding A T',
            ∀ a : U, ∀ ha : α a ∈ S,
              ∃ a' : U,
                (ClosedEmbedding.comp j f) ⟨α a, ha⟩ = α' a' := by
  classical
  letI : Fintype (ClosedEmbedding A C) := Fintype.ofFinite _
  let xs : List (ClosedEmbedding A C) := Finset.univ.toList
  have aux :
      ∀ ys : List (ClosedEmbedding A C),
      ∀ {Y0 : Type v} {T0 : RelStructure L.graph Y0},
      FunctionClosedTreeAmalgam Base Y0 T0 →
      ∀ (f0 : ClosedEmbedding (C.induce (↑S : Set W)) T0),
      FunctionClosedEmbeddedIntersections
        (A := A) (C := C) (T := T0) S hS f0 →
      ∀ zs : List (ClosedEmbedding A C),
      FunctionClosedControls
        (A := A) (C := C) (T := T0) S f0 zs →
      ∃ (Z1 : Type v) (T1 : RelStructure L.graph Z1),
        FunctionClosedTreeAmalgam Base Z1 T1 ∧
        ∃ j : ClosedEmbedding T0 T1,
          FunctionClosedEmbeddedIntersections
            (A := A) (C := C) (T := T1) S hS
            (ClosedEmbedding.comp j f0) ∧
          FunctionClosedControls
            (A := A) (C := C) (T := T1) S
            (ClosedEmbedding.comp j f0) (ys.reverse ++ zs) := by
    intro ys
    induction ys with
    | nil =>
        intro Y0 T0 hTree0 f0 hInt0 zs hctrl0
        let j : ClosedEmbedding T0 T0 := ClosedEmbedding.id T0
        have hjf : ClosedEmbedding.comp j f0 = f0 := by
          apply ClosedEmbedding.ext
          intro x
          rfl
        refine ⟨Y0, T0, hTree0, j, ?_, ?_⟩
        · rw [hjf]
          exact hInt0
        · rw [hjf]
          simpa using hctrl0
    | cons α ys ih =>
        intro Y0 T0 hTree0 f0 hInt0 zs hctrl0
        obtain ⟨Y1, T1, hTree1, j1, hctrl1⟩ :=
          addControl_of_embeddedIntersection
            (A := A) (Base := Base) (C := C)
            hA eAB S hS hTree0 f0
            zs hctrl0 α (hInt0 α)
        have hInt1 :
            FunctionClosedEmbeddedIntersections
              (A := A) (C := C) (T := T1) S hS
              (ClosedEmbedding.comp j1 f0) :=
          hInt0.postcomp j1
        obtain ⟨Z1, T2, hTree2, j2, hInt2, hctrl2⟩ :=
          ih hTree1 (ClosedEmbedding.comp j1 f0)
            hInt1 (α :: zs) hctrl1
        let j : ClosedEmbedding T0 T2 :=
          ClosedEmbedding.comp j2 j1
        have hjf :
            ClosedEmbedding.comp j f0 =
              ClosedEmbedding.comp j2
                (ClosedEmbedding.comp j1 f0) := by
          apply ClosedEmbedding.ext
          intro x
          rfl
        refine ⟨Z1, T2, hTree2, j, ?_, ?_⟩
        · rw [hjf]
          exact hInt2
        · rw [hjf]
          simpa [List.reverse_cons, List.append_assoc] using hctrl2
  obtain ⟨Z0, T', hTree', j, hInt', hctrl'⟩ :=
    aux xs hTree f hInt [] (by
      intro α hmem
      exact (List.not_mem_nil hmem).elim)
  refine ⟨Z0, T', hTree', j, hInt', ?_⟩
  intro α
  exact hctrl' α (by simp [xs])

end FunctionClosedHasTreeCompletion

end StructuralRamsey.RelStructure
