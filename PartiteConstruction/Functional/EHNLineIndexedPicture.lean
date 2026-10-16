import PartiteConstruction.Functional.NativeHJLineWitness
import PartiteConstruction.Functional.EHNPicture

/-!
# A native FUNCTIONAL Picture need attach only Hales–Jewett LINES

The published functional Picture lemma's verified proof attaches one
copy of the old Picture for every full partite embedding R↪E of
the selected support R into the Hales–Jewett power E.

But the Hales–Jewett proof itself chooses a very particular FULL
embedding, namely `weak_lineEmbedding W`, for some Hales–Jewett
line W with a nonempty set of parameter coordinates. The larger
family of arbitrary full embeddings is not necessary for the
colour-extraction argument.

This module replays the SAME genuine function-language Picture step,
with the SAME power, selected closed whole-part support and genuine
free functional attachments, but indexes attachments ONLY by
Hales–Jewett lines. The line-index set is finite for finite
alphabet and word length. The proof uses
`weak_partiteLemma_withLineWitness` and the existing
`EHN.attachAll` with a line-indexed family.

Each attached map is now explicitly known to split at one of
its own parameter coordinates. No line shares a distinguished
parameter coordinate with every other line, so the full multi-line
strict functional B-tree-completion theorem remains open.

Output-fibre transversality is preserved at every stage by the
genuine `System` power and attachment operations, and no
U-closed/relational intermediate Picture is introduced. The
result is an ALTERNATIVE stronger-structured witness for the
original `EHN.PictureProperty`, not a change to the statement
of the functional Ramsey lemma.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure
open StructuralRamsey.HalesJewett

universe u v
variable {L : Language.{u}} {P U : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- The genuine finite Hales–Jewett LINE set, unlike the unrestricted
partite-embedding index family, carries an explicit parameter
coordinate at which its full support embedding is split. -/
theorem finite_HJLines
    {α : Type v} [Finite α] (N : ℕ) :
    Finite (Line α N) := by
  classical
  exact Finite.of_injective (fun W : Line α N => W.symbol)
    (by
      intro W₁ W₂ h
      cases W₁ with
      | mk symbols₁ hp₁ =>
        cases W₂ with
        | mk symbols₂ hp₂ =>
          cases h
          rfl)

/-- Direct genuinely SET-VALUED-FUNCTIONAL Picture lemma using
ATTACHMENTS ONLY ALONG FULL Hales–Jewett line embeddings.

This construction satisfies the same PictureProperty as the
published unrestricted-embedding version, because the HJ
canonicalization itself supplies a monochromatic line W.

There is no new Ramsey recursion and no temporary nonfunctional
stage. The weaker family of attached copies eliminates one
source of false coordinate-shadow generalizations, but not the
need to make distinct lines' relative B-tree witnesses coherent. -/
theorem pictureLemma_lineIndexed
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) [Finite U] (hA : K A)
    (B : Stage K D) (α : Structure.Embedding A D)
    (κ : Type*) [Fintype κ] :
    ∃ C : Stage K D, PictureProperty A B C α κ := by
  classical
  let R := B.system.weakRestrict D B.isPartite.1 A α
  have hR : R.WeaklyPartiteOver A :=
    B.system.weakRestrict_invariant
      D B.isPartite.1 A α B.isPartite
  obtain ⟨N, hN, hPower, hLineArrow⟩ :=
    Induced.weak_partiteLemma_withLineWitness hR κ
  let E := Induced.power R N
  have hmE : K E.toStructure :=
    mem_of_weaklyPartiteOver hK E hPower hA
  let ER := E.relabel α.toFunctionEmbedding
  have hER : ER.WeaklyPartiteOver D :=
    α.isEHNHomomorphismEmbedding.comp hPower
  let T : Stage K D := {
    Carrier := Induced.Vertex R N
    finiteCarrier := inferInstance
    system := ER
    isPartite := hER
    mem := hmE
  }
  let S := B.system.support α.toFunctionEmbedding
  have hS : B.system.toStructure.IsClosed S :=
    B.system.weak_support_closed D B.isPartite.1 A α
  letI : Finite (Line (Induced.Letter A R) N) :=
    finite_HJLines N
  let maps : Line (Induced.Letter A R) N →
      FunctionalPartite.Embedding (B.system.induce S hS) T.system :=
    fun W => {
      toEmbedding := (Induced.weak_lineEmbedding hR.1 W).toEmbedding
      map_part := by
        intro x
        exact (congrArg α
          ((Induced.weak_lineEmbedding hR.1 W).map_part x)).trans
          (B.system.restrictedPart_spec α.toFunctionEmbedding x)
    }
  obtain ⟨C, core, hcopies⟩ :=
    attachAll hK B.system B.isPartite B.mem S hS T maps
  refine ⟨C, ?_⟩
  intro χ
  obtain ⟨W, hW⟩ :=
    hLineArrow
      (fun e => χ (core.toEmbedding.comp e.toEmbedding))
  obtain ⟨f, hf⟩ := hcopies W
  refine ⟨f, ?_⟩
  intro e₁ e₂ he₁ he₂
  let r₁ := weakRestrictCopy
    B.system D B.isPartite.1 A α e₁ he₁
  let r₂ := weakRestrictCopy
    B.system D B.isPartite.1 A α e₂ he₂
  have hcomp (e : Structure.Embedding A B.system.toStructure)
      (he : ∀ x, B.system.part (e x) = α x) :
      f.toEmbedding.comp e =
        core.toEmbedding.comp
          ((Induced.weak_lineEmbedding hR.1 W).comp
            (weakRestrictCopy
              B.system D B.isPartite.1 A α e he)).toEmbedding := by
    apply Structure.Embedding.ext
    intro x
    exact hf ⟨e x, x, (he x).symm⟩
  rw [hcomp e₁ he₁, hcomp e₂ he₂]
  exact hW r₁ r₂

end StructuralRamsey.FunctionalPartite.EHN
