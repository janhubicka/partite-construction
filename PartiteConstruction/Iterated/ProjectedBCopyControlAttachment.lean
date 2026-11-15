import PartiteConstruction.Iterated.FinalCompletion
import PartiteConstruction.Iterated.ProjectedRoot

/-!
# Track E: one source-side B-copy attachment preserving a SAME control HE

The existing finite final-completion lemma freely attaches a B-copy
over an irreducible old test once that test embeds into B. To preserve
the selected global control map as well, its image must be contained
in a full B-copy of the CONTROL, and the attaching embedding must be
chosen compatibly with this particular image.

For a full irreducible Root embedding into Core and a common Control,
use the checked rootEmbeddingIntoBase theorem to lift the selected
projection along an actual Base embedding beta:Base↪Control. Freely
attach Base to Core over exactly Root. The checked fold theorem extends
the Core control projection and agrees with beta on the new copy.

This is a ONE-STEP interface, not an unconditional extension theorem
for the coordinated final 2019 witness: selected target B-cover
compatibility itself must be established for that witness.
-/

namespace StructuralRamsey.RelStructure.ProjectedBCopyControl

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.RelStructure.FreeAmalgam

universe u v
variable {L : RelLanguage.{u}}
variable {R C B Q : Type v}
variable {Root : RelStructure L R}
variable {Core : RelStructure L C}
variable {Base : RelStructure L B}
variable {Control : RelStructure L Q}

/-- A compatible Control-side full B-copy lets one attach a literal
fresh B-copy to the source over an irreducible Root, retaining the
EXACT original HE projection on the old source and the specified
full B embedding on the newly attached copy. -/
theorem attach_irreducible_preserves_controlHE
    (hRoot : Root.Irreducible)
    (i : Embedding Root Core)
    (p : C → Q)
    (hp : Core.IsHomomorphismEmbedding Control p)
    (beta : Embedding Base Control)
    (himage : ∀ r : R, ∃ b : B, p (i r) = beta b) :
    ∃ j : Embedding Root Base,
      ∃ newProjection :
        FreeAmalgam.Vertex Root Core Base i j → Q,
        (FreeAmalgam.amalgam Root Core Base i j).IsHomomorphismEmbedding
          Control newProjection ∧
        (∀ c : C, newProjection
          (FreeAmalgam.leftEmbedding Root Core Base i j c) = p c) ∧
        (∀ b : B, newProjection
          (FreeAmalgam.rightEmbedding Root Core Base i j b) = beta b) ∧
        (∀ r : R,
          FreeAmalgam.leftEmbedding Root Core Base i j (i r) =
          FreeAmalgam.rightEmbedding Root Core Base i j (j r)) := by
  classical
  obtain ⟨j, hj⟩ :=
    rootEmbeddingIntoBase hRoot i p hp beta himage
  let projected : FreeAmalgam.Vertex Root Core Base i j → Q :=
    FreeAmalgam.fold (D := Root) (A := Core) (B := Base)
      (fA := i) (fB := j) p beta hj
  have hProjected :
      (FreeAmalgam.amalgam Root Core Base i j).IsHomomorphismEmbedding
        Control projected :=
    FreeAmalgam.fold_isHomomorphismEmbedding
      (D := Root) (A := Core) (B := Base) (Q := Control)
      (fA := i) (fB := j)
      p beta hj hp beta.isHomomorphismEmbedding
  refine ⟨j, projected, hProjected, ?_, ?_, ?_⟩
  · intro c
    exact FreeAmalgam.fold_left
      (D := Root) (A := Core) (B := Base) (fA := i) (fB := j)
      p beta hj c
  · intro b
    exact FreeAmalgam.fold_right
      (D := Root) (A := Core) (B := Base) (fA := i) (fB := j)
      p beta hj b
  · intro r
    exact FreeAmalgam.left_right_overlap Root Core Base i j r

end StructuralRamsey.RelStructure.ProjectedBCopyControl
