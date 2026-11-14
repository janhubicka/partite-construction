import PartiteConstruction.Functional.TrackCDomainEmptyLegalRoundtrip
import PartiteConstruction.Structure.FreeAmalgam

/-!
# Track C F2: legal rich partial Dom/Empty models survive FULL free amalgams

The legal native encoding carries two relation bits at each input:
Dom_F and Empty_F. Native whole-fibre values by themselves cannot
recognize a genuinely defined-empty partial application.

A genuine native full free amalgam of two LEGAL objects over an
arbitrary FULL common root is again legal. Proof is by direct
localization of the Dom, Empty and complete native value records
using the existing exact relational/function free-amalgam fields.

An active mixed input with some empty is forbidden by the
Empty_F relation, even though its native function fibre is empty.
The conclusion uses the same whole carrier; it does not add closure
vertices or replace a test by its function-closed hull.

This is the central F2 gluing lemma of the English-first
second native B-cover proof. The final induction along arbitrary
loose B-tree objects and original irreducibility-to-encoded-native
irreducibility (F4) remain separate formal gates.
-/

namespace StructuralRamsey.Structure

open StructuralRamsey
universe u v

variable {L : Language.{u}} {RV LV WV CV : Type v}
variable {Root : Structure L.withDomainEmptyFlags RV}
variable {Left : Structure L.withDomainEmptyFlags LV}
variable {Right : Structure L.withDomainEmptyFlags WV}
variable {Whole : Structure L.withDomainEmptyFlags CV}

/-- A FULL free amalgam of LEGAL Dom/Empty native models is LEGAL.
The empty fibre plus an active Empty_F mask is NOT silently treated
as undefined on a crossing input tuple. -/
theorem IsLegalDomainEmpty.ofFreeAmalgam
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hL : IsLegalDomainEmpty Left)
    (hR : IsLegalDomainEmpty Right) :
    IsLegalDomainEmpty Whole := by
  intro F xs
  have sideEmpty :
      ∀ {T : Type v} {Side : Structure L.withDomainEmptyFlags T}
        (i : Embedding Side Whole)
        (a : Fin (L.funcArity F) → T),
        Whole.func F (i.toFun ∘ a) = ∅ →
        Side.func F a = ∅ := by
    intro T Side i a hWholeEmpty
    ext y
    constructor
    · intro hy
      have hyWhole : i.toFun y ∈ Whole.func F (i.toFun ∘ a) := by
        rw [← i.map_func F a]
        exact ⟨y, hy, rfl⟩
      have hImpossible : False := by
        rw [hWholeEmpty] at hyWhole
        simpa only [Set.mem_empty_iff_false] using hyWhole
      exact hImpossible.elim
    · simp
  have hDom :
      Whole.rel (.inr (.inl F)) xs ↔
        (Whole.func F xs).Nonempty ∨
        Whole.rel (.inr (.inr F)) xs := by
    constructor
    · intro hd
      rcases (hFree.rel_iff (.inr (.inl F)) xs).mp hd with
        ⟨a, hDa, hx⟩ | ⟨a, hDa, hx⟩
      · rcases ((hL F a).1).mp hDa with hn | he
        · left
          obtain ⟨y, hy⟩ := hn
          refine ⟨iL.toFun y, ?_⟩
          have hVal : iL.toFun y ∈
              Whole.func F (iL.toFun ∘ a) := by
            rw [← iL.map_func F a]
            exact ⟨y, hy, rfl⟩
          simpa only [hx] using hVal
        · right
          exact (hFree.rel_iff (.inr (.inr F)) xs).mpr
            (Or.inl ⟨a, he, hx⟩)
      · rcases ((hR F a).1).mp hDa with hn | he
        · left
          obtain ⟨y, hy⟩ := hn
          refine ⟨iR.toFun y, ?_⟩
          have hVal : iR.toFun y ∈
              Whole.func F (iR.toFun ∘ a) := by
            rw [← iR.map_func F a]
            exact ⟨y, hy, rfl⟩
          simpa only [hx] using hVal
        · right
          exact (hFree.rel_iff (.inr (.inr F)) xs).mpr
            (Or.inr ⟨a, he, hx⟩)
    · rintro (⟨y, hy⟩ | he)
      · rcases (hFree.func_iff F xs y).mp hy with
          ⟨a, b, hb, hx, _⟩ | ⟨a, b, hb, hx, _⟩
        · have ha : Left.rel (.inr (.inl F)) a :=
            ((hL F a).1).mpr (Or.inl ⟨b, hb⟩)
          exact (hFree.rel_iff (.inr (.inl F)) xs).mpr
            (Or.inl ⟨a, ha, hx⟩)
        · have ha : Right.rel (.inr (.inl F)) a :=
            ((hR F a).1).mpr (Or.inl ⟨b, hb⟩)
          exact (hFree.rel_iff (.inr (.inl F)) xs).mpr
            (Or.inr ⟨a, ha, hx⟩)
      · rcases (hFree.rel_iff (.inr (.inr F)) xs).mp he with
          ⟨a, ha, hx⟩ | ⟨a, ha, hx⟩
        · have hDa : Left.rel (.inr (.inl F)) a :=
            (((hL F a).2).mp ha).1
          exact (hFree.rel_iff (.inr (.inl F)) xs).mpr
            (Or.inl ⟨a, hDa, hx⟩)
        · have hDa : Right.rel (.inr (.inl F)) a :=
            (((hR F a).2).mp ha).1
          exact (hFree.rel_iff (.inr (.inl F)) xs).mpr
            (Or.inr ⟨a, hDa, hx⟩)
  have hEmpty :
      Whole.rel (.inr (.inr F)) xs ↔
        Whole.rel (.inr (.inl F)) xs ∧
        Whole.func F xs = ∅ := by
    constructor
    · intro he
      have hd : Whole.rel (.inr (.inl F)) xs :=
        hDom.mpr (Or.inr he)
      refine ⟨hd, ?_⟩
      rcases (hFree.rel_iff (.inr (.inr F)) xs).mp he with
        ⟨a, ha, hx⟩ | ⟨a, ha, hx⟩
      · have hLa : Left.func F a = ∅ :=
          (((hL F a).2).mp ha).2
        calc
          Whole.func F xs =
              Whole.func F (iL.toFun ∘ a) := by rw [hx]
          _ = Structure.imageSet iL.toFun (Left.func F a) :=
            (iL.map_func F a).symm
          _ = ∅ := by rw [hLa]; simp [Structure.imageSet]
      · have hRa : Right.func F a = ∅ :=
          (((hR F a).2).mp ha).2
        calc
          Whole.func F xs =
              Whole.func F (iR.toFun ∘ a) := by rw [hx]
          _ = Structure.imageSet iR.toFun (Right.func F a) :=
            (iR.map_func F a).symm
          _ = ∅ := by rw [hRa]; simp [Structure.imageSet]
    · rintro ⟨hd, hVal⟩
      rcases (hFree.rel_iff (.inr (.inl F)) xs).mp hd with
        ⟨a, ha, hx⟩ | ⟨a, ha, hx⟩
      · have hLValue : Left.func F a = ∅ :=
          sideEmpty iL a (by simpa only [hx] using hVal)
        have he : Left.rel (.inr (.inr F)) a :=
          ((hL F a).2).mpr ⟨ha, hLValue⟩
        exact (hFree.rel_iff (.inr (.inr F)) xs).mpr
          (Or.inl ⟨a, he, hx⟩)
      · have hRValue : Right.func F a = ∅ :=
          sideEmpty iR a (by simpa only [hx] using hVal)
        have he : Right.rel (.inr (.inr F)) a :=
          ((hR F a).2).mpr ⟨ha, hRValue⟩
        exact (hFree.rel_iff (.inr (.inr F)) xs).mpr
          (Or.inr ⟨a, he, hx⟩)
  exact ⟨hDom, hEmpty⟩

end StructuralRamsey.Structure
