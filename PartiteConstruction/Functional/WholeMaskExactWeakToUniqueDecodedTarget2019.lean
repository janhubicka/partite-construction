import PartiteConstruction.Functional.WholeMaskCoveredExactWeakLocalMap2019

/-!
# Exact weak OLD local maps into NONCANONICAL but whole-value-unique targets

The earlier exact weak local transfer theorem assumes the target is
literally the canonical complete-mask graph of a genuine partial
Option(Set)-structure. That requirement is stronger than necessary
for the source-defined partial *homomorphism* semantics.

For ANY OLD relational target D with UNIQUE entire complete-value
witnesses over each primitive function input, its independent
genuinely partial decoder chooses precisely the unique witnessed
whole set, preserving some-empty versus none. A positive OLD
homomorphism E.induce S → D therefore decodes to a genuine original
2019 partial homomorphism on the SAME weak source vertex set S.

No assumption about target domain-mask completeness, OLD canonical
tag normality, class K, or functional full embeddings is imposed.
The target D can retain arbitrary extra domain predicates; these
are irrelevant to positive defined-value transfer.

This does NOT prove K-members satisfy uniqueness or that such a
map is a full homomorphism-embedding on intrinsic weak functional
irreducible tests. The latter fails in general by persistent ambient
OLD domain masks (WholeMaskWeakDomainObstruction2019).
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Structure

universe u v w z
variable {L : Language.{u}} {P : Type v} [Fintype P]
variable {V : Type w} {W : Type z}

/-- A positive homomorphism of EXACT induced ambient OLD graphs into
an arbitrary entire-value-UNIQUE OLD target induces a source-defined
original partial-function homomorphism on the decoded weak function
sources and decoded target.  Unlike the canonical-target theorem,
no old output label compatibility or domain normalization is assumed
of the target; its decoder only uses complete output tuples. -/
theorem wholeMaskPartialDecode_weak_originalPartial_of_inducedOldHom_toDecoded
    (E : RelStructure (L.wholeMaskPatternLanguage P) V)
    (hUniqueSource : ∀ (F : L.FuncSymbol)
      (xs : Fin (L.funcArity F) → V)
      (U T : Set V),
      HasWholeMaskValue E F xs U →
      HasWholeMaskValue E F xs T → U = T)
    (S : Set V)
    (D : RelStructure (L.wholeMaskPatternLanguage P) W)
    (hUniqueTarget : ∀ (F : L.FuncSymbol)
      (xs : Fin (L.funcArity F) → W)
      (U T : Set W),
      HasWholeMaskValue D F xs U →
      HasWholeMaskValue D F xs T → U = T)
    (f : S → W)
    (hOld : (E.induce S).IsHomomorphism D f) :
    PartialSetStructure.IsOriginalPartialHomomorphism
      (PartialSetStructure.wholeWeakInduce E.wholeMaskPartialDecode S)
      D.wholeMaskPartialDecode f := by
  classical
  constructor
  · intro R xs hRel
    exact hOld (.inl R) xs hRel
  · intro F xs U hWeak
    have hWeakValue : PartialSetStructure.wholeWeakValue S
        (E.wholeMaskPartialDecode.func F (Subtype.val ∘ xs)) =
          some U := hWeak
    obtain ⟨T, hT, hTS, hUT⟩ :=
      (PartialSetStructure.wholeWeakValue_eq_some_iff S _ U).mp hWeakValue
    have hWitness : HasWholeMaskValue E F (Subtype.val ∘ xs) T :=
      (E.wholeMaskPartialDecode_func_some_iff
        F (Subtype.val ∘ xs)
        (hUniqueSource F (Subtype.val ∘ xs)) T).mp hT
    obtain ⟨m, r, hr, q, t, hRel, hArgs, hTSet⟩ := hWitness
    let pat : Language.FunctionInputPattern L := ⟨F, m, r, hr⟩
    have hRoot (i : Fin m) :
        t (Fin.castAdd q.size i) ∈ S := by
      obtain ⟨j, hj⟩ := hr i
      have hx : (Subtype.val ∘ xs) j ∈ S := (xs j).2
      rw [hArgs j] at hx
      simpa only [hj] using hx
    have hOut (j : Fin q.size) :
        t (Fin.natAdd m j) ∈ S := by
      apply hTS
      rw [hTSet]
      exact ⟨j, rfl⟩
    have hAll (k : Fin (m + q.size)) : t k ∈ S :=
      Fin.addCases hRoot hOut k
    let tS : Fin (m + q.size) → S :=
      fun k => ⟨t k, hAll k⟩
    have hRelS : (E.induce S).rel (.inr (.inr (pat,q))) tS :=
      hRel
    have hMapped : D.rel (.inr (.inr (pat,q))) (f ∘ tS) :=
      hOld (.inr (.inr (pat,q))) tS hRelS
    have hInput :
        ((fun i : Fin m => f (tS (Fin.castAdd q.size i))) ∘ r) =
          f ∘ xs := by
      funext i
      apply congrArg f
      apply Subtype.ext
      exact (hArgs i).symm
    have hOutput :
        Set.range (fun j : Fin q.size =>
          f (tS (Fin.natAdd m j))) =
        Structure.imageSet f U := by
      rw [hUT]
      ext y
      constructor
      · rintro ⟨j, rfl⟩
        have hIn : (tS (Fin.natAdd m j)).1 ∈ T := by
          change t (Fin.natAdd m j) ∈ T
          rw [hTSet]
          exact ⟨j, rfl⟩
        exact ⟨tS (Fin.natAdd m j), hIn, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        have hIn : x.1 ∈ T := hx
        rw [hTSet] at hIn
        obtain ⟨j, hj⟩ := hIn
        have hEq : x = tS (Fin.natAdd m j) :=
          Subtype.ext hj.symm
        exact ⟨j, congrArg f hEq.symm⟩
    have hWitnessTarget : HasWholeMaskValue D F (f ∘ xs)
        (Structure.imageSet f U) := by
      refine ⟨m, r, hr, q, f ∘ tS, hMapped, ?_, ?_⟩
      · intro i
        exact (congrFun hInput i).symm
      · exact hOutput.symm
    exact (D.wholeMaskPartialDecode_func_some_iff
      F (f ∘ xs) (hUniqueTarget F (f ∘ xs))
      (Structure.imageSet f U)).mpr hWitnessTarget

end StructuralRamsey.RelStructure
