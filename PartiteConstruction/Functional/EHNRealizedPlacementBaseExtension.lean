import PartiteConstruction.Functional.EHNProjectedCover
import PartiteConstruction.Functional.WeakOperations
import PartiteConstruction.Functional.LabelledOneCopyWeakCore

/-!
# Actual functional Hales–Jewett letters force B-placements in the control

The native functional induced Picture has an existing, verified
`Stage.ProjectedCover Base` invariant. This is stronger than merely
knowing that the original control D contains one copy of Base:
**every irreducible full A-copy realised in the OLD Picture, with
part placement alpha:A↪D, projects inside some full Base-copy in D.**

By factoring alpha through that projected full Base-copy, we obtain
an actual full embedding A↪Base and a full Base↪D whose composition
is alpha. No stronger total-fibre projection or reflection of
undefined source inputs is assumed.

Moreover, the existence of an A-copy in Old over alpha is EQUIVALENT
to having an actual Hales–Jewett alphabet letter, namely a partite
embedding of the transversal A into Old restricted to the complete
selected alpha-parts. The equivalence uses the already verified
function-closed support restriction and genuine full embeddings.

Combining this with the marked labelled one-copy core theorem proves
that the stronger full-A-labelled core target is available for EVERY
nonempty actual native Hales–Jewett alphabet, with the factor
Base-placement derived automatically from projected coverage.

This discharges a genuine HJ-core hypothesis of the marked-A approach.
It does NOT construct the corresponding OLD-PICTURE side's compatible
marked strict B-tree witness. That remains the maximal-mixed gap.
All partite function images retain their transversal-image invariant.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {U VB P W : Type v}
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L P}

/-- An actually realised full irreducible A-copy of a native functional
Stage, with prescribed part placement alpha:A↪D, forces alpha to
factor through an actual FULL Base↪D placement.

This uses precisely the published projected irreducible B-coverage
invariant, not a false assertion that A must extend to a B-copy
INSIDE the old Picture. -/
theorem Stage.realizedACopy_extends_controlBase
    (Old : Stage K D)
    (A : Structure L U) (Base : Structure L VB)
    (hCover : Old.ProjectedCover Base)
    (hA : A.Irreducible)
    (alpha : Embedding A D)
    (eA : Embedding A Old.system.toStructure)
    (hAlpha : ∀ a, Old.system.part (eA a) = alpha a) :
    ∃ (beta : Embedding Base D)
      (eAB : Embedding A Base),
      ∀ a, beta (eAB a) = alpha a := by
  classical
  obtain ⟨beta, hb⟩ := hCover A hA eA
  choose f hf using hb
  have hFactor : ∀ a, alpha a = beta (f a) := by
    intro a
    exact (hAlpha a).symm.trans (hf a)
  let eAB : Embedding A Base :=
    alpha.factorWithMap beta f hFactor
  refine ⟨beta, eAB, ?_⟩
  intro a
  exact (hFactor a).symm

/-- The actual native HJ alphabet above alpha is nonempty exactly
when alpha labels a FULL ambient A-copy in the old Picture.

The selected support consists of WHOLE alpha-parts and is function
closed; its projection is the prescribed A-copy. We do not interpret
an arbitrary weak partial A-copy as a letter. -/
theorem Stage.nonempty_letters_iff_realizedACopy
    (Old : Stage K D)
    (A : Structure L U) (alpha : Embedding A D) :
    Nonempty (FunctionalPartite.Embedding
      (transversal A)
      (Old.system.weakRestrict D Old.isPartite.1 A alpha)) ↔
    ∃ eA : Embedding A Old.system.toStructure,
      ∀ a, Old.system.part (eA a) = alpha a := by
  classical
  constructor
  · rintro ⟨letter⟩
    let R := Old.system.weakRestrict D Old.isPartite.1 A alpha
    let inc : Embedding R.toStructure Old.system.toStructure :=
      Old.system.weakRestrictInclusion D Old.isPartite.1 A alpha
    let eA : Embedding A Old.system.toStructure :=
      inc.comp letter.toEmbedding
    refine ⟨eA, ?_⟩
    intro a
    calc
      Old.system.part (eA a) =
          alpha (R.part (letter a)) :=
        (Old.system.restrictedPart_spec alpha.toFunctionEmbedding
          (letter a)).symm
      _ = alpha a := congrArg alpha (letter.map_part a)
  · rintro ⟨eA, hAlpha⟩
    exact ⟨weakRestrictCopy Old.system D Old.isPartite.1
      A alpha eA hAlpha⟩

/-- Projected irreducible coverage forces every ACTUALLY ACTIVE
HJ alphabet to have a full extension alpha=A↪Base↪D.
This is true for the existing genuine functional EHN Picture, with
no singleton-valuedness or new recursive pass. -/
theorem Stage.nonempty_letters_extend_controlBase
    (Old : Stage K D)
    (A : Structure L U) (Base : Structure L VB)
    (hCover : Old.ProjectedCover Base)
    (hA : A.Irreducible)
    (alpha : Embedding A D)
    (hLetters : Nonempty (FunctionalPartite.Embedding
      (transversal A)
      (Old.system.weakRestrict D Old.isPartite.1 A alpha))) :
    ∃ (beta : Embedding Base D)
      (eAB : Embedding A Base),
      ∀ a, beta (eAB a) = alpha a := by
  obtain ⟨eA, hAlpha⟩ :=
    (Old.nonempty_letters_iff_realizedACopy A alpha).mp hLetters
  exact Old.realizedACopy_extends_controlBase
    A Base hCover hA alpha eA hAlpha

/-- The selected HJ core's marked A-placement can therefore be
constructed FROM projected coverage as soon as there is a genuine
alphabet letter; it need not be separately postulated.

The core is an arbitrary EHN source `C→A`, as instantiated by the
already verified coordinatewise functional Hales–Jewett power.
For EVERY exact weak source set, its one-copy strict Base target is
labelled by the derived full beta:Base↪D, preserving actual ambient
A-copy intersections and all projected histories; the function-image
part map is transversal. -/
theorem Stage.nonempty_letters_labelledOneCopyCore
    (Old : Stage K D)
    (A : Structure L U) (Base : Structure L VB)
    (hCover : Old.ProjectedCover Base)
    (hA : A.Irreducible)
    (hBase : Base.Irreducible)
    (alpha : Embedding A D)
    (hLetters : Nonempty (FunctionalPartite.Embedding
      (transversal A)
      (Old.system.weakRestrict D Old.isPartite.1 A alpha)))
    (C : Structure L W) (p : W → U)
    (hp : C.IsEHNHomomorphismEmbedding A p)
    (S : Set W) (history : List (Set P)) :
    ∃ (beta : Embedding Base D) (eAB : Embedding A Base),
      (∀ a, beta (eAB a) = alpha a) ∧
      ∃ f : S → VB,
        TreeAmalgam Base VB Base ∧
        IsAmbientRelativeWeakHE C S Base f ∧
        SetAmbientACopyIntersections A C Base S f ∧
        (∀ x : S, beta (f x) = alpha (p x.1)) ∧
        SetRespectsProjectedHistory (alpha ∘ p) S f history ∧
        eAB.ContainedInIrreducible ∧
        (∀ F (x : Fin (L.funcArity F) → VB),
          Set.InjOn beta (Base.func F x)) := by
  obtain ⟨beta, eAB, hAlpha⟩ :=
    Old.nonempty_letters_extend_controlBase
      A Base hCover hA alpha hLetters
  refine ⟨beta, eAB, hAlpha, ?_⟩
  exact hp.labelledOneCopyWeakHistory
    hA hBase eAB beta alpha hAlpha S history

end StructuralRamsey.FunctionalPartite.EHN
