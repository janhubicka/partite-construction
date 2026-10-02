import PartiteConstruction.Iterated.FreeAmalgam
import PartiteConstruction.Iterated.LocalTreeLike

/-! # Completing the A-copy control clause

The local-tree-like definition asks for more than a homomorphism-embedding of
the tested finite substructure into a tree amalgam: the intersection with every
ambient A-copy must land inside some A-copy of the target.  Under hereditary
irreducibility of A this extra control can always be added afterwards by
successively freely amalgamating a copy of B over each such intersection.
-/
namespace StructuralRamsey.RelStructure.LocallyTreeLike

universe u v
variable {L : RelLanguage.{u}}
variable {U V W Y : Type v}
variable {A : RelStructure L U} {B : RelStructure L V}
variable {C : RelStructure L W} {T : RelStructure L Y}

/-- Control condition for a finite list of ambient A-copies. -/
def Controls
    (S : Finset W) (f : ↥(↑S : Set W) → Y)
    (xs : List (Embedding A C)) : Prop :=
  ∀ α ∈ xs, ∃ α' : Embedding A T,
    ∀ a : U, ∀ ha : α a ∈ S,
      ∃ a' : U, f ⟨α a, ha⟩ = α' a'

/-- Add control for one more ambient A-copy while preserving all previously
controlled copies. -/
theorem addControl
    (hA : HereditarilyIrreducible A)
    (eAB : Embedding A B)
    (S : Finset W)
    (hTree : TreeAmalgam B Y T)
    (f : ↥(↑S : Set W) → Y)
    (hf : (C.induce (↑S : Set W)).IsHomomorphismEmbedding T f)
    (xs : List (Embedding A C))
    (hctrl : Controls (A := A) (C := C) (T := T) S f xs)
    (α : Embedding A C) :
    ∃ (Z : Type v) (T' : RelStructure L Z),
      TreeAmalgam B Z T' ∧
      ∃ f' : ↥(↑S : Set W) → Z,
        (C.induce (↑S : Set W)).IsHomomorphismEmbedding T' f' ∧
        Controls (A := A) (C := C) (T := T') S f' (α :: xs) := by
  classical
  let Hset : Set U := {a | α a ∈ S}
  let H := A.induce Hset
  have hH : H.Irreducible := hA Hset
  let eHS : Embedding H (C.induce (↑S : Set W)) := {
    toFun := fun a => ⟨α a.1, a.2⟩
    injective := by
      intro x y hxy
      apply Subtype.ext
      apply α.injective
      exact congrArg Subtype.val hxy
    map_rel_iff := by
      intro R x
      change C.rel R (α ∘ (Subtype.val ∘ x)) ↔
        A.rel R (Subtype.val ∘ x)
      exact α.map_rel_iff R (Subtype.val ∘ x)
  }
  obtain ⟨eHT, heHT⟩ :=
    hf.after_irreducible_embedding hH eHS
  let eHB : Embedding H B :=
    eAB.comp (RelStructure.inclusion A Hset)
  have hcT : eHT.ContainedInIrreducible := by
    let Rng : Set Y := Set.range eHT
    exact ⟨Rng, hH.range_embedding eHT, fun x => ⟨x, rfl⟩⟩
  have hcB : eHB.ContainedInIrreducible := by
    let Rng : Set V := Set.range eHB
    exact ⟨Rng, hH.range_embedding eHB, fun x => ⟨x, rfl⟩⟩
  let T' := FreeAmalgam.amalgam H T B eHT eHB
  let l : Embedding T T' :=
    FreeAmalgam.leftEmbedding H T B eHT eHB
  let r : Embedding B T' :=
    FreeAmalgam.rightEmbedding H T B eHT eHB
  have hTree' : TreeAmalgam B _ T' :=
    FreeAmalgam.treeAmalgam H T B eHT eHB B
      hTree (TreeAmalgam.copy (Iso.refl B)) hcT hcB
  let f' : ↥(↑S : Set W) → _ := l ∘ f
  have hf' :
      (C.induce (↑S : Set W)).IsHomomorphismEmbedding T' f' :=
    l.isHomomorphismEmbedding.comp hf
  refine ⟨_, T', hTree', f', hf', ?_⟩
  intro β hβ
  rcases List.mem_cons.mp hβ with hβα | hβ
  · subst β
  · let α' : Embedding A T' := r.comp eAB
    refine ⟨α', ?_⟩
    intro a ha
    refine ⟨a, ?_⟩
    let ah : H := ⟨a, ha⟩
    have he : eHT ah = f (eHS ah) := heHT ah
    change l (f ⟨α a, ha⟩) = r (eAB a)
    calc
      l (f ⟨α a, ha⟩) = l (eHT ah) := congrArg l he.symm
      _ = r (eHB ah) :=
        FreeAmalgam.left_right_overlap H T B eHT eHB ah
      _ = r (eAB a) := rfl
  · obtain ⟨β', hβ'⟩ := hctrl β hβ
    let β'' : Embedding A T' := l.comp β'
    refine ⟨β'', ?_⟩
    intro a ha
    obtain ⟨a', ha'⟩ := hβ' a ha
    refine ⟨a', ?_⟩
    exact congrArg l ha'

/-- Add the A-copy control clause for every ambient A-copy. -/
theorem completeControl
    [Finite U] [Finite W]
    (hA : HereditarilyIrreducible A)
    (eAB : Embedding A B)
    (S : Finset W)
    (hTree : TreeAmalgam B Y T)
    (f : ↥(↑S : Set W) → Y)
    (hf : (C.induce (↑S : Set W)).IsHomomorphismEmbedding T f) :
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
        intro Y T hT f hf zs hzs
        exact ⟨Y, T, hT, f, hf, by simpa using hzs⟩
    | cons α ys ih =>
        intro Y T hT f hf zs hzs
        obtain ⟨Y₁, T₁, hT₁, f₁, hf₁, hctrl₁⟩ :=
          ih hT f hf zs hzs
        obtain ⟨Z, T', hT', f', hf', hctrl'⟩ :=
          addControl (A := A) (B := B) (C := C)
            hA eAB S hT₁ f₁ hf₁ (ys ++ zs) hctrl₁ α
        refine ⟨Z, T', hT', f', hf', ?_⟩
        simpa only [List.cons_append] using hctrl'
  obtain ⟨Z, T', hT', f', hf', hctrl'⟩ :=
    aux xs hTree f hf [] (by
      intro α h
      exact (List.not_mem_nil h).elim)
  refine ⟨Z, T', hT', f', hf', ?_⟩
  intro α
  exact hctrl' α (by simpa [xs])

end StructuralRamsey.RelStructure.LocallyTreeLike
