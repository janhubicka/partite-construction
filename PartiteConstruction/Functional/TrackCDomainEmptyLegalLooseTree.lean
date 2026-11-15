import PartiteConstruction.Functional.TrackCDomainEmptyFreeLegal
import PartiteConstruction.Functional.LooseTreeAmalgam

/-!
# Track C F2: legality survives full images and native loose B-trees

The first F2 lemma shows Dom/Empty/value coherence survives
arbitrary native free amalgams over FULL roots. Here we provide
the two remaining ingredients:
* legal native targets have legal induced/full-embedded subobjects;
* every loose native B-tree of a legal B is itself legal.

The copy case of LooseTreeAmalgam is a surjective full embedding,
so it has an inverse FULL embedding by the already verified
factorThroughRange construction. The recursive glue case uses
the exact legal free-amalgam lemma.

The domain/defined-empty correctness holds on the SAME exact
carrier. No strict tree assumption or reducible-root
target-completion oracle is introduced.
-/

namespace StructuralRamsey.Structure

open StructuralRamsey
universe u v

variable {L : Language.{u}} {V W : Type v}

/-- FULL native embeddings reflect the two legality equations.
No requirement that the source is irreducible or closed by a
separate U rule: its image is function-closed automatically. -/
theorem IsLegalDomainEmpty.ofEmbedding
    {A : Structure L.withDomainEmptyFlags V}
    {B : Structure L.withDomainEmptyFlags W}
    (hB : IsLegalDomainEmpty B)
    (e : Embedding A B) :
    IsLegalDomainEmpty A := by
  intro F xs
  have hDom := e.map_rel_iff (.inr (.inl F)) xs
  have hEmpty := e.map_rel_iff (.inr (.inr F)) xs
  have hNe :
      (B.func F (e.toFun ∘ xs)).Nonempty ↔
        (A.func F xs).Nonempty := by
    rw [← e.map_func F xs]
    constructor
    · rintro ⟨y, ⟨x, hx, _⟩⟩
      exact ⟨x, hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨e.toFun x, ⟨x, hx, rfl⟩⟩
  have hEmptyF :
      B.func F (e.toFun ∘ xs) = ∅ ↔ A.func F xs = ∅ := by
    rw [← e.map_func F xs]
    constructor
    · intro hImg
      ext x
      constructor
      · intro hx
        have hxImage : e.toFun x ∈
            Structure.imageSet e.toFun (A.func F xs) :=
          ⟨x, hx, rfl⟩
        rw [hImg] at hxImage
        have contra : False := by
          simpa only [Set.mem_empty_iff_false] using hxImage
        exact contra.elim
      · simp
    · intro hA
      rw [hA]
      simp [Structure.imageSet]
  constructor
  · calc
      A.rel (.inr (.inl F)) xs ↔
          B.rel (.inr (.inl F)) (e.toFun ∘ xs) := hDom.symm
      _ ↔ (B.func F (e.toFun ∘ xs)).Nonempty ∨
          B.rel (.inr (.inr F)) (e.toFun ∘ xs) :=
        (hB F (e.toFun ∘ xs)).1
      _ ↔ (A.func F xs).Nonempty ∨
          A.rel (.inr (.inr F)) xs :=
        or_congr hNe hEmpty
  · calc
      A.rel (.inr (.inr F)) xs ↔
          B.rel (.inr (.inr F)) (e.toFun ∘ xs) := hEmpty.symm
      _ ↔ B.rel (.inr (.inl F)) (e.toFun ∘ xs) ∧
          B.func F (e.toFun ∘ xs) = ∅ :=
        (hB F (e.toFun ∘ xs)).2
      _ ↔ A.rel (.inr (.inl F)) xs ∧
          A.func F xs = ∅ :=
        and_congr hDom hEmptyF

/-- Any finite native loose B-tree assembled from copies of a LEGAL
genuine-partial native base B is legal. Arbitrary full common roots
are allowed; the proof reuses the exact F2 free-amalgam lemma.

A true defined-empty input never disappears at a mixed root:
it remains a positive Empty_F relation, and every free attachment
must localize the entire tuple to one side. -/
theorem LooseTreeAmalgam.isLegalDomainEmpty
    {Base : Structure L.withDomainEmptyFlags V}
    {Target : Structure L.withDomainEmptyFlags W}
    (hTree : LooseTreeAmalgam Base W Target)
    (hBase : IsLegalDomainEmpty Base) :
    IsLegalDomainEmpty Target := by
  induction hTree with
  | copy e hSurj =>
      let j := (Embedding.id _).factorThroughRange e
        (fun x => by
          obtain ⟨b, hb⟩ := hSurj x
          exact ⟨b, hb.symm⟩)
      exact hBase.ofEmbedding j
  | glue hL hR fL fR iL iR hFree ihL ihR =>
      exact IsLegalDomainEmpty.ofFreeAmalgam hFree ihL ihR

end StructuralRamsey.Structure
