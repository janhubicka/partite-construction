import PartiteConstruction.Functional.OriginalPartialRankZero
import PartiteConstruction.Functional.EHNOriginalPartialGeneratorPictureReduction
import PartiteConstruction.Functional.OriginalPartialRankFinalBCover

/-!
# The n-pass native original-partial strict-tree reduction

Only finite induction and composition of original 2019 partial-function
homomorphism-embeddings are added here. The verified genuine functional
Hales-Jewett and induced Ramsey passes are reused directly.

The uniform maximal-mixed relative extension assumption is explicitly
visible; it is unproved and must not be silently treated as an axiom.
All final local B-tree targets are strict FULL functional structures.
-/

namespace StructuralRamsey.FunctionalPartite.EHN.StrictRanked

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {U V P : Type v}

/-- The exact still-unproved hypothesis for genuine maximal mixed
closed tests across all finite control structures and all ranks. -/
def MaximalMixedSchema
    (K : Structure.StructureClass (L := L))
    (A : Structure L U) (Base : Structure L V) : Prop :=
  ∀ (Q : Type v) [Finite Q] [DecidableEq Q]
    (Control : Structure L Q) (n : ℕ)
    (Old T : EHN.Stage K Control)
    (alpha : Structure.Embedding A Control)
    (f : FunctionalPartite.Embedding
      (Old.system.induce (Old.system.support alpha.toFunctionEmbedding)
        (Old.system.weak_support_closed
          Control Old.isPartite.1 A alpha))
      T.system),
    LocallyGeneratedOriginalPartialTreeCompletable
      Base Old.system.toStructure n →
    LocallyGeneratedOriginalPartialTreeCompletable
      Base T.system.toStructure n →
    Attachment.NativeMaximalMixedOriginalPartialRelativeExtension
      Old.system (Old.system.support alpha.toFunctionEmbedding)
      (Old.system.weak_support_closed
        Control Old.isPartite.1 A alpha)
      T.system f Base n

/-- A stage after k genuine full-functional Ramsey passes. -/
structure Stage
    (K : Structure.StructureClass (L := L))
    (A : Structure L U) (Base : Structure L V)
    (D : Structure L P) (κ : Type*) (level : ℕ) where
  Carrier : Type v
  finiteCarrier : Finite Carrier
  C : Structure L Carrier
  mem : K C
  arrow : Structure.Arrow A Base C κ
  projection : Carrier → P
  projectionHE : IsOriginalPartialHomomorphismEmbedding C D projection
  localRank : LocallyGeneratedOriginalPartialTreeCompletable Base C level

attribute [instance] Stage.finiteCarrier

/-- Rank zero of the original Ramsey control plus one full native pass. -/
theorem first
    (K : Structure.StructureClass (L := L))
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) (Base : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hKA : K A) (hKB : K Base)
    (hBIrr : Base.Irreducible) (hPos : L.PositiveFuncArity)
    (eAB : Structure.Embedding A Base)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hArrow : Structure.Arrow A Base D κ)
    (hMixed : MaximalMixedSchema K A Base) :
    ∃ T : Stage K A Base D κ 1, True := by
  classical
  have hZero : LocallyGeneratedOriginalPartialTreeCompletable
      Base D 0 := by
    intro H hH hGen
    exact closed_rank_zero_originalPartial_completion_of_arrow
      A Base D hPos κ hArrow H hH hGen
  obtain ⟨T, hRank, hTArrow⟩ :=
    inducedConstruction_originalPartial_generatorRank_of_maximal_mixed
      hK A Base D hKA hKB hBIrr hPos eAB
      κ hArrow 1 hZero
      (fun Old Core alpha f hOld hCore =>
        hMixed P D 1 Old Core alpha f hOld hCore)
  let S : Stage K A Base D κ 1 := {
    Carrier := T.Carrier
    finiteCarrier := T.finiteCarrier
    C := T.system.toStructure
    mem := T.mem
    arrow := hTArrow
    projection := T.system.part
    projectionHE := T.isPartite.toOriginalPartial
    localRank := hRank
  }
  exact ⟨S, trivial⟩

/-- Inductive rank k to k+1 pass, composing the original-partial map. -/
theorem succ
    (K : Structure.StructureClass (L := L))
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) (Base : Structure L V) (D : Structure L P)
    [Finite U] [Finite V]
    (hKA : K A) (hKB : K Base)
    (hBIrr : Base.Irreducible) (hPos : L.PositiveFuncArity)
    (eAB : Structure.Embedding A Base)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hMixed : MaximalMixedSchema K A Base)
    (k : ℕ) (S : Stage K A Base D κ k) :
    ∃ T : Stage K A Base D κ (k+1), True := by
  classical
  letI : Finite S.Carrier := S.finiteCarrier
  have hPrev : LocallyGeneratedOriginalPartialTreeCompletable
      Base S.C ((k+1)-1) := by
    simpa using S.localRank
  obtain ⟨T, hRank, hArrow⟩ :=
    inducedConstruction_originalPartial_generatorRank_of_maximal_mixed
      hK A Base S.C hKA hKB hBIrr hPos eAB
      κ S.arrow (k+1) hPrev
      (fun Old Core alpha f hOld hCore =>
        hMixed S.Carrier S.C (k+1) Old Core alpha f hOld hCore)
  let p : T.Carrier → P := S.projection ∘ T.system.part
  have hp : IsOriginalPartialHomomorphismEmbedding
      T.system.toStructure D p :=
    S.projectionHE.comp T.isPartite.toOriginalPartial
  let R : Stage K A Base D κ (k+1) := {
    Carrier := T.Carrier
    finiteCarrier := T.finiteCarrier
    C := T.system.toStructure
    mem := T.mem
    arrow := hArrow
    projection := p
    projectionHE := hp
    localRank := hRank
  }
  exact ⟨R, trivial⟩

/-- Exactly n complete functional induced Ramsey passes under the one
stated maximal-mixed schema, without repeating a Ramsey proof. -/
theorem build
    (K : Structure.StructureClass (L := L))
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) (Base : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hKA : K A) (hKB : K Base)
    (hBIrr : Base.Irreducible) (hPos : L.PositiveFuncArity)
    (eAB : Structure.Embedding A Base)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hArrow : Structure.Arrow A Base D κ)
    (hMixed : MaximalMixedSchema K A Base)
    (n : ℕ) (hn : 0 < n) :
    ∃ T : Stage K A Base D κ n, True := by
  induction n with
  | zero =>
      omega
  | succ k ih =>
      by_cases hk : k = 0
      · subst k
        simpa using
          first K hK A Base D hKA hKB hBIrr hPos eAB
            κ hArrow hMixed
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
        obtain ⟨S, _⟩ := ih hkpos
        simpa [Nat.succ_eq_add_one] using
          succ K hK A Base D hKA hKB hBIrr hPos eAB
            κ hMixed k S

/-- Conditional full sparsening: strict full-functional B-tree local
completions, final genuine B-cover, original-partial map to initial D,
and full function-language Ramsey arrow. Only MaximalMixedSchema is open. -/
theorem sparsening_of_maximal_mixed_schema
    (K : Structure.StructureClass (L := L))
    (hK : Structure.FreeAmalgamationClass K)
    (A : Structure L U) (Base : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P]
    (hKA : K A) (hKB : K Base)
    (hBIrr : Base.Irreducible) (hPos : L.PositiveFuncArity)
    (eAB : Structure.Embedding A Base)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hArrow : Structure.Arrow A Base D κ)
    (hMixed : MaximalMixedSchema K A Base)
    (n : ℕ) (hn : 0 < n) :
    ∃ (W : Type v) (_ : Finite W) (C : Structure L W),
      K C ∧
      Structure.Arrow A Base C κ ∧
      (∃ p : W → P, IsOriginalPartialHomomorphismEmbedding C D p) ∧
      LocallyClosedOriginalPartialTreeCompletable Base C n ∧
      IrreduciblesExtendTo Base C ∧
      LooseTreeAmalgam Base W C := by
  classical
  obtain ⟨S, _⟩ :=
    build K hK A Base D hKA hKB hBIrr hPos eAB
      κ hArrow hMixed n hn
  letI : Finite S.Carrier := S.finiteCarrier
  obtain ⟨W, hW, C, hKC, hCArrow, ⟨q,hq⟩,
      hLocal, hCover, hLoose⟩ :=
    sparseningRamsey_originalPartial_strictClosed_from_generatorRank
      K hK A Base S.C hKA hKB κ S.arrow n S.localRank
  have hp : IsOriginalPartialHomomorphismEmbedding
      C D (S.projection ∘ q) :=
    S.projectionHE.comp hq
  exact ⟨W, hW, C, hKC, hCArrow,
    ⟨S.projection ∘ q, hp⟩, hLocal, hCover, hLoose⟩

end StructuralRamsey.FunctionalPartite.EHN.StrictRanked
