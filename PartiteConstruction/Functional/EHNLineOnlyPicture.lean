import PartiteConstruction.Functional.NativeHJLineWitness
import PartiteConstruction.Functional.EHNPictureInvariant

set_option autoImplicit false

/-!
# Native functional Picture Lemma indexed ONLY by Hales-Jewett lines

The previously verified EHN Picture attaches one OLD Picture copy for
EVERY full partite embedding of the selected closed support into the HJ
power. The Ramsey proof, however, extracts only one HJ LINE witness.
It is therefore sufficient to attach copies indexed by actual HJ
LINES. This reduces the attachment family while preserving the exact
PictureProperty needed by the induced Ramsey construction.

All stages remain genuine functional partite systems, including
transversal set-valued function images. Every attaching overlap is the
same ACTUAL function-closed selected support. All local tests stay
vertex-exact weak substructures; no extra closure budget is introduced.

This theorem does NOT claim that the reduced multi-line attachment
family preserves strict full-functional weak-tree locality: lines
have different parameter coordinates, and no global common
retraction or arbitrary-root extension is inferred.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open Structure HalesJewett

universe u v
variable {L : Language.{u}}
variable {P U : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- Hales-Jewett lines on a finite alphabet, of fixed finite length,
form a finite type. The parameter existence proof is proof-irrelevant,
so the symbol function determines the line. -/
noncomputable instance finiteLines
    (α : Type v) [Finite α] (N : ℕ) :
    Finite (Line α N) := by
  classical
  letI : Finite (SuccessorTree.LineSymbol α) :=
    Finite.of_injective
      (fun s : SuccessorTree.LineSymbol α =>
        match s with
        | .parameter => (none : Option α)
        | .const a => some a)
      (by
        intro x y h
        cases x <;> cases y <;> simp_all)
  exact Finite.of_injective (fun W : Line α N => W.symbol) (by
    intro ⟨sx, hx⟩ ⟨sy, hy⟩ h
    cases h
    rfl)

/-- Preserve an arbitrary genuine functional stage invariant while
performing one native Picture step, attaching OLD copies only along
the FINITE family of Hales-Jewett LINE embeddings in the power.

The sole geometric obligation remains stability under ONE
closed-support binary attachment. The colouring argument needs no
copies beyond these lines, since the Hales-Jewett lemma supplies
the actual line chosen after the colouring. -/
theorem pictureLemma_lines_preservingSupport
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) [Finite U] (hA : K A)
    (B : Stage K D) (α : Structure.Embedding A D)
    (κ : Type*) [Fintype κ]
    (Q : Stage K D → Prop)
    (hCore :
      ∀ (N : ℕ) (hN : 0 < N),
        let R := B.system.weakRestrict D B.isPartite.1 A α
        let hR : R.WeaklyPartiteOver A :=
          B.system.weakRestrict_invariant
            D B.isPartite.1 A α B.isPartite
        let E := Induced.power R N
        let hPower : E.WeaklyPartiteOver A :=
          Induced.power_weaklyPartiteOver hR hN
        let ER := E.relabel α.toFunctionEmbedding
        let hER : ER.WeaklyPartiteOver D :=
          α.isEHNHomomorphismEmbedding.comp hPower
        let T : Stage K D := {
          Carrier := Induced.Vertex R N
          finiteCarrier := inferInstance
          system := ER
          isPartite := hER
          mem := mem_of_weaklyPartiteOver hK E hPower hA
        }
        Q T)
    (hAttach :
      ∀ (T : Stage K D)
        (f : FunctionalPartite.Embedding
          (B.system.induce (B.system.support α.toFunctionEmbedding)
            (B.system.weak_support_closed D B.isPartite.1 A α))
          T.system),
        Q T →
        Q (T.attach hK B.system B.isPartite B.mem
          (B.system.support α.toFunctionEmbedding)
          (B.system.weak_support_closed D B.isPartite.1 A α) f)) :
    ∃ C : Stage K D,
      Q C ∧ PictureProperty A B C α κ := by
  classical
  let R := B.system.weakRestrict D B.isPartite.1 A α
  have hR : R.WeaklyPartiteOver A :=
    B.system.weakRestrict_invariant
      D B.isPartite.1 A α B.isPartite
  obtain ⟨N, hN, hPower, hLineArrow⟩ :=
    Induced.weak_partiteLemma_withLineWitness hR κ
  let E := Induced.power R N
  have hPower' : E.WeaklyPartiteOver A := by
    simpa [E] using hPower
  have hmE : K E.toStructure :=
    mem_of_weaklyPartiteOver hK E hPower' hA
  let ER := E.relabel α.toFunctionEmbedding
  have hER : ER.WeaklyPartiteOver D :=
    α.isEHNHomomorphismEmbedding.comp hPower'
  let T : Stage K D := {
    Carrier := Induced.Vertex R N
    finiteCarrier := inferInstance
    system := ER
    isPartite := hER
    mem := hmE
  }
  have hQT : Q T := by
    simpa [R, E, ER, T, hR, hPower', hER] using hCore N hN
  let S := B.system.support α.toFunctionEmbedding
  have hS : B.system.toStructure.IsClosed S :=
    B.system.weak_support_closed D B.isPartite.1 A α
  let maps : Line (Induced.Letter A R) N →
      FunctionalPartite.Embedding (B.system.induce S hS) T.system :=
    fun W => {
      toEmbedding := (Induced.weak_lineEmbedding hR.1 W).toEmbedding
      map_part := fun x =>
        (congrArg α ((Induced.weak_lineEmbedding hR.1 W).map_part x)).trans
          (B.system.restrictedPart_spec α.toFunctionEmbedding x)
    }
  have hAttach' :
      ∀ (T0 : Stage K D)
        (f0 : FunctionalPartite.Embedding
          (B.system.induce S hS) T0.system),
        Q T0 →
        Q (T0.attach hK B.system B.isPartite B.mem S hS f0) := by
    intro T0 f0 hQT0
    exact hAttach T0 f0 hQT0
  obtain ⟨C, hQC, core, hcopies⟩ :=
    attachAll_preserving hK B.system B.isPartite B.mem S hS
      Q hAttach' T hQT maps
  refine ⟨C, hQC, ?_⟩
  intro χ
  obtain ⟨W, hW⟩ := hLineArrow
    (fun e => χ (core.toEmbedding.comp e.toEmbedding))
  obtain ⟨f, hf⟩ := hcopies W
  refine ⟨f, ?_⟩
  intro e₁ e₂ he₁ he₂
  let r₁ := weakRestrictCopy B.system D B.isPartite.1 A α e₁ he₁
  let r₂ := weakRestrictCopy B.system D B.isPartite.1 A α e₂ he₂
  have hcomp (e : Structure.Embedding A B.system.toStructure)
      (he : ∀ x, B.system.part (e x) = α x) :
      f.toEmbedding.comp e =
        core.toEmbedding.comp
          ((Induced.weak_lineEmbedding hR.1 W).comp
            (weakRestrictCopy B.system D B.isPartite.1 A α e he)).toEmbedding := by
    apply Structure.Embedding.ext
    intro x
    exact hf ⟨e x, x, (he x).symm⟩
  rw [hcomp e₁ he₁, hcomp e₂ he₂]
  exact hW r₁ r₂

/-- The ordinary native functional PictureProperty remains true even if
OLD copies are attached only for Hales-Jewett lines. In particular
we can choose this construction as the Picture step in the verified
induced Ramsey iteration; no change to the Ramsey arrow is needed. -/
theorem pictureLemma_lines
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) [Finite U] (hA : K A)
    (B : Stage K D) (α : Structure.Embedding A D)
    (κ : Type*) [Fintype κ] :
    ∃ C : Stage K D, PictureProperty A B C α κ := by
  obtain ⟨C, _hTrue, hPicture⟩ :=
    pictureLemma_lines_preservingSupport hK A hA B α κ
      (fun _ => True) (fun _ _ => True.intro)
      (fun _ _ _ => True.intro)
  exact ⟨C, hPicture⟩

end StructuralRamsey.FunctionalPartite.EHN
