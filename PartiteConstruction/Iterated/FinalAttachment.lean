import PartiteConstruction.Iterated.FreeAmalgam

/-! # Projection through a final free attachment

The final sparsening step attaches a copy of `B` over an irreducible
substructure while keeping a homomorphism-embedding into the original Ramsey
witness.  This file supplies the reusable one-step projection lemma.

Two homomorphism-embeddings of the sides of a concrete free amalgam can be
folded to a common target whenever they agree on the overlap.
-/
namespace StructuralRamsey.RelStructure.FreeAmalgam

open Attachment

universe u v
variable {L : RelLanguage.{u}}
variable {U V W Y : Type v}
variable {D : RelStructure L U} {A : RelStructure L V}
variable {B : RelStructure L W} {Q : RelStructure L Y}
variable {fA : Embedding D A} {fB : Embedding D B}

/-- Fold a concrete free amalgam to a common target. -/
def fold
    (pA : V → Y) (pB : W → Y)
    (_hcompat : ∀ d, pA (fA d) = pB (fB d)) :
    Vertex D A B fA fB → Y
  | .inl a => pA a
  | .inr (_, b) => pB b.1

@[simp] theorem fold_left
    (pA : V → Y) (pB : W → Y)
    (hcompat : ∀ d, pA (fA d) = pB (fB d))
    (a : V) :
    fold (D := D) (A := A) (B := B) (fA := fA) (fB := fB)
      pA pB hcompat (leftEmbedding D A B fA fB a) = pA a :=
  rfl

theorem fold_right
    (pA : V → Y) (pB : W → Y)
    (hcompat : ∀ d, pA (fA d) = pB (fB d))
    (b : W) :
    fold (D := D) (A := A) (B := B) (fA := fA) (fB := fB)
      pA pB hcompat (rightEmbedding D A B fA fB b) = pB b := by
  classical
  by_cases hb : b ∈ support D A B fA fB
  · have hb' : ∃ d : U, fB d = b := by
      simpa [support] using hb
    rcases hb' with ⟨d, rfl⟩
    calc
      fold (D := D) (A := A) (B := B) (fA := fA) (fB := fB)
          pA pB hcompat (rightEmbedding D A B fA fB (fB d)) =
        fold (D := D) (A := A) (B := B) (fA := fA) (fB := fB)
          pA pB hcompat (leftEmbedding D A B fA fB (fA d)) := by
            exact congrArg
              (fold (D := D) (A := A) (B := B) (fA := fA) (fB := fB)
                pA pB hcompat)
              (left_right_overlap D A B fA fB d).symm
      _ = pA (fA d) := fold_left pA pB hcompat (fA d)
      _ = pB (fB d) := hcompat d
  · change
      fold (D := D) (A := A) (B := B) (fA := fA) (fB := fB)
        pA pB hcompat
        (Attachment.copyMap B (support D A B fA fB) A
          (fun _ : Unit => overlapEmbedding D A B fA fB) () b) = pB b
    rw [Attachment.copyMap_not_mem () b hb]
    rfl

/-- Compatible homomorphism-embeddings on the two sides of a concrete free
amalgam fold to a homomorphism-embedding into the common target. -/
theorem fold_isHomomorphismEmbedding
    (pA : V → Y) (pB : W → Y)
    (hcompat : ∀ d, pA (fA d) = pB (fB d))
    (hpA : A.IsHomomorphismEmbedding Q pA)
    (hpB : B.IsHomomorphismEmbedding Q pB) :
    (amalgam D A B fA fB).IsHomomorphismEmbedding Q
      (fold (D := D) (A := A) (B := B) (fA := fA) (fB := fB)
        pA pB hcompat) := by
  classical
  let F :=
    fold (D := D) (A := A) (B := B) (fA := fA) (fB := fB)
      pA pB hcompat
  constructor
  · intro R x hx
    change
      (Attachment.attach B (support D A B fA fB) A
        (fun _ : Unit => overlapEmbedding D A B fA fB)).rel R x at hx
    rcases hx with ⟨y, hy, hxy⟩ | ⟨i, y, hy, hxy⟩
    · have hQ : Q.rel R (pA ∘ y) := hpA.1 R y hy
      convert hQ using 1
      funext k
      have hk := congrFun hxy k
      change F (x k) = pA (y k)
      rw [hk]
      rfl
    · have hi : i = () := Subsingleton.elim _ _
      subst i
      have hQ : Q.rel R (pB ∘ y) := hpB.1 R y hy
      convert hQ using 1
      funext k
      have hk := congrFun hxy k
      change F (x k) = pB (y k)
      rw [hk]
      exact fold_right pA pB hcompat (y k)
  · intro S hS
    let inc : Embedding ((amalgam D A B fA fB).induce S)
        (amalgam D A B fA fB) :=
      inclusion (amalgam D A B fA fB) S
    have hsplit :=
      Attachment.irreducible_core_or_copy
        (B := B) (S := support D A B fA fB) (D := A)
        (f := fun _ : Unit => overlapEmbedding D A B fA fB) S hS
    rcases hsplit with hcore | ⟨i, hcopy⟩
    · have hrange :
          ∀ z : S, ∃ a : V, inc z = leftEmbedding D A B fA fB a := by
        intro z
        rcases hcore z with ⟨a, ha⟩
        exact ⟨a, ha⟩
      let eA : Embedding ((amalgam D A B fA fB).induce S) A :=
        inc.factorThroughRange (leftEmbedding D A B fA fB) hrange
      obtain ⟨g, hg⟩ := hpA.after_irreducible_embedding hS eA
      refine ⟨g, ?_⟩
      intro z
      have hz := Classical.choose_spec (hrange z)
      calc
        g z = pA (eA z) := hg z
        _ = F (leftEmbedding D A B fA fB (eA z)) := by
          symm
          exact fold_left pA pB hcompat (eA z)
        _ = F z.1 := by
          apply congrArg F
          exact hz.symm
    · have hi : i = () := Subsingleton.elim _ _
      subst i
      have hrange :
          ∀ z : S, ∃ b : W, inc z = rightEmbedding D A B fA fB b := by
        intro z
        rcases hcopy z with ⟨b, hb⟩
        exact ⟨b, hb⟩
      let eB : Embedding ((amalgam D A B fA fB).induce S) B :=
        inc.factorThroughRange (rightEmbedding D A B fA fB) hrange
      obtain ⟨g, hg⟩ := hpB.after_irreducible_embedding hS eB
      refine ⟨g, ?_⟩
      intro z
      have hz := Classical.choose_spec (hrange z)
      calc
        g z = pB (eB z) := hg z
        _ = F (rightEmbedding D A B fA fB (eB z)) := by
          symm
          exact fold_right pA pB hcompat (eB z)
        _ = F z.1 := by
          apply congrArg F
          exact hz.symm

end StructuralRamsey.RelStructure.FreeAmalgam
