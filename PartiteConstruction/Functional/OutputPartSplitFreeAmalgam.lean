import PartiteConstruction.Functional.OutputPartSingletonization
import PartiteConstruction.Functional.WeakFunctionalFreeAmalgam

/-!
# Genuine native FULL functional free attachments preserve singleton output parts

A full part-preserving relation/function free amalgam of real
transversal native functional partite Systems remains a full
function-language free amalgam after the canonical (F,q) singleton
output-part split. Every output in the whole comes wholly from
one source side, with its exact part q preserved.

The TRUE native source geometry, including its arbitrary-arity
multivalued function incidences, is unchanged. Therefore the
verified weakInduce_withMaps theorem also gives, on ANY exact
weak subset S, a full free diagram of the split weak root and
side tests, on their literal inverse-image vertex sets.

This is SOURCE free-amalgam geometry, not a general
compatible strict B-tree TARGET root-completion theorem.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v w
variable {L : Language.{u}} {P : Type v}
variable {H E F C : Type w}

/-- The canonical per-output-part singleton presentation
preserves ALL axioms of a genuine full native functional
free-amalgam diagram, provided the attaching embeddings
are FULL and PART-PRESERVING.

The output split retains whole fibres by output part;
no singleton-valuedness is required of original F. -/
theorem splitOutputParts_of_partite
    {Root : FunctionalPartite.System L P H}
    {Left : FunctionalPartite.System L P E}
    {Right : FunctionalPartite.System L P F}
    {Whole : FunctionalPartite.System L P C}
    {sL : FunctionalPartite.Embedding Root Left}
    {sR : FunctionalPartite.Embedding Root Right}
    {iL : FunctionalPartite.Embedding Left Whole}
    {iR : FunctionalPartite.Embedding Right Whole}
    (hFree : IsFreeAmalgam sL.toEmbedding sR.toEmbedding
      iL.toEmbedding iR.toEmbedding) :
    IsFreeAmalgam
      sL.splitOutputParts.toEmbedding
      sR.splitOutputParts.toEmbedding
      iL.splitOutputParts.toEmbedding
      iR.splitOutputParts.toEmbedding := by
  refine {
    covers := hFree.covers
    overlap := hFree.overlap
    rel_iff := ?_
    func_iff := ?_
  }
  · intro R xs
    exact hFree.rel_iff R.down xs
  · intro Fq xs y
    rcases Fq with ⟨F0, q⟩
    change (y ∈ Whole.func F0.down xs ∧ Whole.part y = q) ↔
      ((∃ a : Fin (L.funcArity F0.down) → E, ∃ b : E,
          (b ∈ Left.func F0.down a ∧ Left.part b = q) ∧
          xs = iL ∘ a ∧ y = iL b) ∨
       (∃ a : Fin (L.funcArity F0.down) → F, ∃ b : F,
          (b ∈ Right.func F0.down a ∧ Right.part b = q) ∧
          xs = iR ∘ a ∧ y = iR b))
    constructor
    · rintro ⟨hFunc, hPart⟩
      rcases (hFree.func_iff F0.down xs y).mp hFunc with
        ⟨a, b, hb, hx, hy⟩ | ⟨a, b, hb, hx, hy⟩
      · have hq : Left.part b = q := by
          calc
            Left.part b = Whole.part (iL b) := (iL.map_part b).symm
            _ = Whole.part y := congrArg Whole.part hy.symm
            _ = q := hPart
        exact Or.inl ⟨a, b, ⟨hb, hq⟩, hx, hy⟩
      · have hq : Right.part b = q := by
          calc
            Right.part b = Whole.part (iR b) := (iR.map_part b).symm
            _ = Whole.part y := congrArg Whole.part hy.symm
            _ = q := hPart
        exact Or.inr ⟨a, b, ⟨hb, hq⟩, hx, hy⟩
    · rintro (⟨a, b, ⟨hb, hq⟩, hx, hy⟩ |
        ⟨a, b, ⟨hb, hq⟩, hx, hy⟩)
      · refine ⟨?_, ?_⟩
        · exact (hFree.func_iff F0.down xs y).mpr
            (Or.inl ⟨a, b, hb, hx, hy⟩)
        · calc
            Whole.part y = Whole.part (iL b) :=
              congrArg Whole.part hy
            _ = Left.part b := iL.map_part b
            _ = q := hq
      · refine ⟨?_, ?_⟩
        · exact (hFree.func_iff F0.down xs y).mpr
            (Or.inr ⟨a, b, hb, hx, hy⟩)
        · calc
            Whole.part y = Whole.part (iR b) :=
              congrArg Whole.part hy
            _ = Right.part b := iR.map_part b
            _ = q := hq

/-- On ANY vertex-exact weak test S of a TRUE full native
functional free attachment, the two split-language weak
side tests and their exact common weak root still form
a FULL functional free amalgam.

No subset is closed to a function-generated hull; all
four displayed weak vertex carriers are literal preimages
of the SAME original tested S. This is the direct
function-language equivalent of the original 2019 U-closed
weak-induction free-amalgam decomposition. -/
theorem splitOutputParts_exactWeak_withMaps
    {Root : FunctionalPartite.System L P H}
    {Left : FunctionalPartite.System L P E}
    {Right : FunctionalPartite.System L P F}
    {Whole : FunctionalPartite.System L P C}
    {sL : FunctionalPartite.Embedding Root Left}
    {sR : FunctionalPartite.Embedding Root Right}
    {iL : FunctionalPartite.Embedding Left Whole}
    {iR : FunctionalPartite.Embedding Right Whole}
    (hFree : IsFreeAmalgam sL.toEmbedding sR.toEmbedding
      iL.toEmbedding iR.toEmbedding)
    (S : Set C) :
    let Lset : Set E := iL.toEmbedding.toFun ⁻¹' S
    let Rset : Set F := iR.toEmbedding.toFun ⁻¹' S
    let Mset : Set H := (iL.toEmbedding.toFun ∘
      sL.toEmbedding.toFun) ⁻¹' S
    let Troot := (Root.splitOutputParts).toStructure
    let Tleft := (Left.splitOutputParts).toStructure
    let Tright := (Right.splitOutputParts).toStructure
    let Twhole := (Whole.splitOutputParts).toStructure
    ∃ (mL : Embedding (Troot.weakInduce Mset) (Tleft.weakInduce Lset))
      (mR : Embedding (Troot.weakInduce Mset) (Tright.weakInduce Rset))
      (jL : Embedding (Tleft.weakInduce Lset) (Twhole.weakInduce S))
      (jR : Embedding (Tright.weakInduce Rset) (Twhole.weakInduce S)),
      IsFreeAmalgam mL mR jL jR ∧
      (∀ a : Lset, (jL a).1 = iL a.1) ∧
      (∀ b : Rset, (jR b).1 = iR b.1) := by
  exact (hFree.splitOutputParts_of_partite).weakInduce_withMaps S

end StructuralRamsey.Structure.IsFreeAmalgam
