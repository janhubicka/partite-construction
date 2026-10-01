import PartiteConstruction.Iterated.LocalTreeLike
import PartiteConstruction.Relational.Attachment

/-! # Concrete free amalgams of relational structures

The free amalgam of `A` and `B` over `D` is a one-copy instance of the
already verified free-attachment construction.  Vertices of the embedded copy
of `D` in `B` are identified with their corresponding vertices in `A`;
all other vertices of `B` remain fresh.
-/
namespace StructuralRamsey.RelStructure.FreeAmalgam

open Attachment

universe u v
variable {L : RelLanguage.{u}}
variable {U V W X Y : Type v}
variable (D : RelStructure L U) (A : RelStructure L V) (B : RelStructure L W)
variable (fA : Embedding D A) (fB : Embedding D B)

def support : Set W := Set.range fB

noncomputable def preimage (x : support D A B fA fB) : U :=
  Classical.choose x.property

@[simp] theorem preimage_spec (x : support D A B fA fB) :
    fB (preimage D A B fA fB x) = x.1 :=
  Classical.choose_spec x.property

/-- The copy of the common substructure inside `B`, transported into `A`. -/
noncomputable def overlapEmbedding :
    Embedding (B.induce (support D A B fA fB)) A where
  toFun x := fA (preimage D A B fA fB x)
  injective := by
    intro x y hxy
    apply Subtype.ext
    apply fB.injective
    rw [← preimage_spec D A B fA fB x,
      ← preimage_spec D A B fA fB y]
    exact fA.injective hxy
  map_rel_iff := by
    intro R x
    let d : Fin (L.arity R) → U :=
      fun k => preimage D A B fA fB (x k)
    have hBx : fB ∘ d = Subtype.val ∘ x := by
      funext k
      exact preimage_spec D A B fA fB (x k)
    change A.rel R (fA ∘ d) ↔ B.rel R (Subtype.val ∘ x)
    rw [← hBx]
    exact (fA.map_rel_iff R d).trans (fB.map_rel_iff R d).symm

abbrev Vertex :=
  Attachment.Vertex (support D A B fA fB) (W := V) (I := Unit)

noncomputable def structure : RelStructure L (Vertex D A B fA fB) :=
  Attachment.attach B (support D A B fA fB) A
    (fun _ : Unit => overlapEmbedding D A B fA fB)

noncomputable def leftEmbedding : Embedding A (structure D A B fA fB) :=
  Attachment.coreEmbedding B (support D A B fA fB) A
    (fun _ : Unit => overlapEmbedding D A B fA fB)

noncomputable def rightEmbedding : Embedding B (structure D A B fA fB) :=
  Attachment.copyEmbedding B (support D A B fA fB) A
    (fun _ : Unit => overlapEmbedding D A B fA fB) ()

/-- The two canonical side embeddings agree on the common copy. -/
theorem left_right_overlap (d : U) :
    leftEmbedding D A B fA fB (fA d) =
      rightEmbedding D A B fA fB (fB d) := by
  classical
  let S := support D A B fA fB
  let g := overlapEmbedding D A B fA fB
  change Sum.inl (fA d) =
    Attachment.copyMap B S A (fun _ : Unit => g) () (fB d)
  have hd : fB d ∈ S := ⟨d, rfl⟩
  rw [Attachment.copyMap_mem () (fB d) hd]
  apply congrArg Sum.inl
  change fA d = fA (preimage D A B fA fB ⟨fB d, hd⟩)
  apply congrArg fA
  apply fB.injective
  rw [preimage_spec D A B fA fB]

section Map

variable (A₂ : RelStructure L X) (B₂ : RelStructure L Y)
variable (gA : Embedding D A₂) (gB : Embedding D B₂)
variable (hA : V → X) (hB : W → Y)

/-- Canonical map between free amalgams induced by compatible maps on their
two sides. -/
noncomputable def map :
    Vertex D A B fA fB → Vertex D A₂ B₂ gA gB
  | .inl a => leftEmbedding D A₂ B₂ gA gB (hA a)
  | .inr p => rightEmbedding D A₂ B₂ gA gB (hB p.2.1)

@[simp] theorem map_left (a : V) :
    map D A B fA fB A₂ B₂ gA gB hA hB
        (leftEmbedding D A B fA fB a) =
      leftEmbedding D A₂ B₂ gA gB (hA a) := rfl

/-- On the right-hand copy the canonical map is exactly the prescribed side
map, including vertices in the glued overlap. -/
theorem map_right
    (hcompatA : ∀ d, hA (fA d) = gA d)
    (hcompatB : ∀ d, hB (fB d) = gB d)
    (b : W) :
    map D A B fA fB A₂ B₂ gA gB hA hB
        (rightEmbedding D A B fA fB b) =
      rightEmbedding D A₂ B₂ gA gB (hB b) := by
  classical
  let S := support D A B fA fB
  by_cases hb : b ∈ S
  · let d := preimage D A B fA fB ⟨b, hb⟩
    have hfb : fB d = b := preimage_spec D A B fA fB ⟨b, hb⟩
    have hsource :
        rightEmbedding D A B fA fB b =
          leftEmbedding D A B fA fB (fA d) := by
      rw [← hfb]
      exact (left_right_overlap D A B fA fB d).symm
    rw [hsource, map_left, hcompatA d, ← left_right_overlap D A₂ B₂ gA gB d,
      ← hcompatB d, hfb]
  · change map D A B fA fB A₂ B₂ gA gB hA hB
        (Attachment.copyMap B S A
          (fun _ : Unit => overlapEmbedding D A B fA fB) () b) =
        rightEmbedding D A₂ B₂ gA gB (hB b)
    rw [Attachment.copyMap_not_mem () b hb]
    rfl

/-- Compatible homomorphisms on the two sides induce a homomorphism of free
amalgams. -/
theorem map_isHomomorphism
    (hcompatA : ∀ d, hA (fA d) = gA d)
    (hcompatB : ∀ d, hB (fB d) = gB d)
    (hhA : A.IsHomomorphism A₂ hA)
    (hhB : B.IsHomomorphism B₂ hB) :
    (structure D A B fA fB).IsHomomorphism
      (structure D A₂ B₂ gA gB)
      (map D A B fA fB A₂ B₂ gA gB hA hB) := by
  intro R z hz
  rcases hz with ⟨x, hx, rfl⟩ | ⟨i, y, hy, rfl⟩
  · have hA₂ : A₂.rel R (hA ∘ x) := hhA R x hx
    have htarget :=
      ((leftEmbedding D A₂ B₂ gA gB).map_rel_iff R (hA ∘ x)).mpr hA₂
    convert htarget using 1
    funext k
    rfl
  · have hi : i = () := Subsingleton.elim _ _
    subst i
    have hB₂ : B₂.rel R (hB ∘ y) := hhB R y hy
    have htarget :=
      ((rightEmbedding D A₂ B₂ gA gB).map_rel_iff R (hB ∘ y)).mpr hB₂
    convert htarget using 1
    funext k
    exact map_right D A B fA fB A₂ B₂ gA gB hA hB
      hcompatA hcompatB (y k)

end Map

/-- The concrete attachment is the free amalgam in the explicit sense used by
the tree-amalgam definition. -/
theorem isFreeAmalgam :
    IsFreeAmalgam fA fB
      (leftEmbedding D A B fA fB) (rightEmbedding D A B fA fB) := by
  classical
  let S := support D A B fA fB
  let g := overlapEmbedding D A B fA fB
  constructor
  · intro z
    cases z with
    | inl a =>
        exact Or.inl ⟨a, rfl⟩
    | inr p =>
        rcases p with ⟨i, b⟩
        refine Or.inr ⟨b.1, ?_⟩
        change Sum.inr (i, b) =
          Attachment.copyMap B S A (fun _ : Unit => g) () b.1
        have hi : i = () := Subsingleton.elim _ _
        subst i
        symm
        exact Attachment.copyMap_not_mem () b.1 b.2
  · intro a b
    constructor
    · intro h
      change Sum.inl a =
        Attachment.copyMap B S A (fun _ : Unit => g) () b at h
      have hb : b ∈ S :=
        Attachment.mem_of_copyMap_eq_inl h.symm
      let d : U := Classical.choose hb
      have hd : fB d = b := Classical.choose_spec hb
      refine ⟨d, ?_, hd.symm⟩
      have hcopy :
          Attachment.copyMap B S A (fun _ : Unit => g) () b =
            Sum.inl (g ⟨b, hb⟩) :=
        Attachment.copyMap_mem () b hb
      rw [hcopy] at h
      have ha : a = g ⟨b, hb⟩ := Sum.inl.inj h
      change a = fA (preimage D A B fA fB ⟨b, hb⟩)
      rw [ha]
      apply congrArg fA
      apply fB.injective
      rw [preimage_spec D A B fA fB]
      exact hd.symm
    · rintro ⟨d, rfl, rfl⟩
      change Sum.inl (fA d) =
        Attachment.copyMap B S A (fun _ : Unit => g) () (fB d)
      have hb : fB d ∈ S := ⟨d, rfl⟩
      rw [Attachment.copyMap_mem () (fB d) hb]
      apply congrArg Sum.inl
      change fA d = fA (preimage D A B fA fB ⟨fB d, hb⟩)
      apply congrArg fA
      apply fB.injective
      rw [preimage_spec D A B fA fB]
  · intro R z
    constructor
    · rintro (⟨x, hx, hzx⟩ | ⟨i, y, hy, hzy⟩)
      · exact Or.inl ⟨x, hx, hzx⟩
      · exact Or.inr ⟨y, hy, by
          have hi : i = () := Subsingleton.elim _ _
          subst i
          exact hzy⟩
    · rintro (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
      · exact Or.inl ⟨x, hx, rfl⟩
      · exact Or.inr ⟨(), y, hy, rfl⟩

/-- Free amalgams of two tree amalgams are again tree amalgams whenever the
gluing images satisfy the irreducible-containment condition. -/
theorem treeAmalgam
    {Q : Type v} (Base : RelStructure L Q)
    (hA : TreeAmalgam Base V A) (hB : TreeAmalgam Base W B)
    (hcA : fA.ContainedInIrreducible)
    (hcB : fB.ContainedInIrreducible) :
    TreeAmalgam Base (Vertex D A B fA fB) (structure D A B fA fB) :=
  TreeAmalgam.glue hA hB fA fB hcA hcB
    (leftEmbedding D A B fA fB) (rightEmbedding D A B fA fB)
    (isFreeAmalgam D A B fA fB)

end StructuralRamsey.RelStructure.FreeAmalgam
