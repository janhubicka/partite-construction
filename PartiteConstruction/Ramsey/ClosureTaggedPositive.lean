import PartiteConstruction.Ramsey.ClosureTaggedIrreducibility

/-! # Positive maps and normalization of tagged test embeddings

Tagged part expansions add one unary part predicate per vertex and one
tagged copy of each closure relation per root-part profile. Positive
homomorphisms commute with this expansion EXACTLY when they preserve
part labels. Full embedded tests in an expanded source are themselves
canonical tagged expansions of their original relational reduct,
with the part map induced by their embedding. This normalization is
needed before transporting the protected CLOSED irreducible tests.

No claim is made about global injectivity of a positive map, or about
protection of nonclosed intrinsically U-irreducible tests.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {P U W E : Type v}

/-- The original relational reduct of an arbitrary tagged-language
structure. It keeps the untagged old relation symbols exactly. -/
def taggedOriginalReduct
    {rules : ClosureDescription L}
    (T : RelStructure (L.withTaggedClosureParts rules P) E) :
    RelStructure L E where
  rel R z := T.rel (.inl R) z

/-- Positive maps preserving parts lift to the correctly tagged
language, without any injectivity or reflection assumptions. -/
theorem IsHomomorphism.expandTaggedClosureParts
    {rules : ClosureDescription L}
    {A : RelStructure L U} {B : RelStructure L W}
    {f : U → W} {partA : U → P} {partB : W → P}
    (hf : A.IsHomomorphism B f)
    (hPart : ∀ x, partB (f x) = partA x) :
    (RelStructure.expandTaggedClosureParts rules A partA).IsHomomorphism
      (RelStructure.expandTaggedClosureParts rules B partB) f := by
  intro sym z hz
  cases sym with
  | inl R =>
      exact hf R z hz
  | inr sym =>
      cases sym with
      | inl tag =>
          refine ⟨hf tag.rule.symbol z hz.1, ?_⟩
          intro i
          exact (hPart (z (i.castLE tag.rule.rootLE))).trans (hz.2 i)
      | inr p =>
          change partB (f (z (RelLanguage.taggedParts_partIndex L rules P p))) = p
          exact (hPart _).trans hz

/-- Forgetting the added symbols preserves positivity. -/
theorem IsHomomorphism.forgetTaggedClosureParts
    {rules : ClosureDescription L}
    {A : RelStructure L U} {B : RelStructure L W}
    {partA : U → P} {partB : W → P} {f : U → W}
    (hf : (RelStructure.expandTaggedClosureParts rules A partA).IsHomomorphism
      (RelStructure.expandTaggedClosureParts rules B partB) f) :
    A.IsHomomorphism B f := by
  intro R z hz
  exact hf (.inl R) z hz

/-- Positivity on unary part predicates forces preservation of each
part. No positive map may change the part of an existing vertex. -/
theorem IsHomomorphism.tagged_preserves_part
    {rules : ClosureDescription L}
    {A : RelStructure L U} {B : RelStructure L W}
    {partA : U → P} {partB : W → P} {f : U → W}
    (hf : (RelStructure.expandTaggedClosureParts rules A partA).IsHomomorphism
      (RelStructure.expandTaggedClosureParts rules B partB) f)
    (x : U) : partB (f x) = partA x := by
  have hx := hf (.inr (.inr (partA x))) (fun _ : Fin 1 => x)
    (show (RelStructure.expandTaggedClosureParts rules A partA).rel
      (.inr (.inr (partA x))) (fun _ : Fin 1 => x) from rfl)
  exact hx

/-- Exact characterization of tagged positive maps by the underlying
positive relational map and commutation with the part labellings. -/
theorem isHomomorphism_tagged_iff
    (rules : ClosureDescription L)
    (A : RelStructure L U) (B : RelStructure L W)
    (partA : U → P) (partB : W → P) (f : U → W) :
    (RelStructure.expandTaggedClosureParts rules A partA).IsHomomorphism
        (RelStructure.expandTaggedClosureParts rules B partB) f ↔
      A.IsHomomorphism B f ∧ ∀ x, partB (f x) = partA x := by
  constructor
  · intro h
    exact ⟨h.forgetTaggedClosureParts, h.tagged_preserves_part⟩
  · rintro ⟨h, hp⟩
    exact h.expandTaggedClosureParts hp

/-- Any structure fully embedded into a tagged part expansion is
literally an expansion of its original-symbol reduct with the part
labels pulled back along that embedding.

This is an equality of FULL relational structures, not merely a
positive map. It also handles nullary symbols, duplicate symbols
and repeated-entry tuples, and has no closedness premise. -/
theorem tagged_embedded_test_eq_expansion
    {rules : ClosureDescription L}
    (A : RelStructure L U) (partA : U → P)
    (Test : RelStructure (L.withTaggedClosureParts rules P) E)
    (e : Embedding Test (RelStructure.expandTaggedClosureParts rules A partA)) :
    Test = RelStructure.expandTaggedClosureParts rules
      (taggedOriginalReduct Test) (partA ∘ e) := by
  let Normal := RelStructure.expandTaggedClosureParts rules
    (taggedOriginalReduct Test) (partA ∘ e)
  have hRel : Test.rel = Normal.rel := by
    funext sym z
    apply propext
    cases sym with
    | inl R =>
        rfl
    | inr sym =>
        cases sym with
        | inl tag =>
            calc
              Test.rel (.inr (.inl tag)) z ↔
                  (RelStructure.expandTaggedClosureParts rules A partA).rel
                    (.inr (.inl tag)) (e ∘ z) :=
                (e.map_rel_iff (.inr (.inl tag)) z).symm
              _ ↔
                  Test.rel (.inl tag.rule.symbol) z ∧
                    (∀ i : Fin tag.rule.rootSize,
                      partA (e (z (i.castLE tag.rule.rootLE))) = tag.rootParts i) := by
                change (A.rel tag.rule.symbol (e ∘ z) ∧
                    (∀ i : Fin tag.rule.rootSize,
                      partA (e (z (i.castLE tag.rule.rootLE))) = tag.rootParts i)) ↔
                  Test.rel (.inl tag.rule.symbol) z ∧
                    (∀ i : Fin tag.rule.rootSize,
                      partA (e (z (i.castLE tag.rule.rootLE))) = tag.rootParts i)
                exact and_congr (e.map_rel_iff (.inl tag.rule.symbol) z) Iff.rfl
              _ ↔ Normal.rel (.inr (.inl tag)) z := Iff.rfl
        | inr p =>
            exact (e.map_rel_iff (.inr (.inr p)) z).symm
  exact congrArg (fun rel =>
    (RelStructure.mk rel : RelStructure (L.withTaggedClosureParts rules P) E)) hRel

end StructuralRamsey.RelStructure
