import PartiteConstruction.Ramsey.ClosureTaggedPartsClosedness
import PartiteConstruction.Ramsey.ClosureClosedCover
import PartiteConstruction.Ramsey.ClosureEmbeddingRange

/-! # Closed U-irreducible tests and tagged part predicates

On a U-closed structure, U-irreducibility is equivalent to the absence
of a proper two-sided free cover by relative U-substructures. This
avoids translating arbitrary *abstract* free-amalgamation diagrams when
the language is expanded by unary part predicates and root-tagged
closure relations.

The exact same relative closed covers exist in the original and
properly tagged structures. The new tagged symbols contain only
subrelations of old ones; the unary part predicates have one coordinate
and cannot span a free-cover cut. Hence U-irreducibility of every CLOSED
test is equivalent in both languages, with no finiteness hypothesis.
This does not equate the UNRESTRICTED literal nonclosed test semantics.
-/

namespace StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {V : Type w} {P : Type v}

/-- Converse to the existing closed-cover lemma. The ambient source
must be U-closed, but its tested two-sided covers need only be RELATIVE
U-substructures (not intrinsically closed supports supplied by callers).
This is a characterization of intrinsic U-irreducibility on closed
sources, including nullary tuples and empty source carriers. -/
theorem IsUClosed.uIrreducible_of_closed_cover
    {rules : ClosureDescription L} {A : RelStructure L V}
    (hA : IsUClosed rules A)
    (hCover : ∀ (S T : Set V),
      IsUSubstructure rules A S →
      IsUSubstructure rules A T →
      (∀ x, x ∈ S ∨ x ∈ T) →
      (∀ R (z : Fin (L.arity R) → V), A.rel R z →
        (∀ k, z k ∈ S) ∨ (∀ k, z k ∈ T)) →
      (∀ x, x ∈ S) ∨ (∀ x, x ∈ T)) :
    IsUIrreducible rules A := by
  intro H E F Root Left Right sL sR iL iR hLeft hRight hFree
  let S : Set V := Set.range iL
  let T : Set V := Set.range iR
  have hS : IsUSubstructure rules A S :=
    iL.range_isUSubstructure hLeft hA
  have hT : IsUSubstructure rules A T :=
    iR.range_isUSubstructure hRight hA
  have hAll : ∀ x : V, x ∈ S ∨ x ∈ T := by
    intro x
    rcases hFree.covers x with ⟨a, ha⟩ | ⟨b, hb⟩
    · exact Or.inl ⟨a, ha.symm⟩
    · exact Or.inr ⟨b, hb.symm⟩
  have hTuples : ∀ R (z : Fin (L.arity R) → V), A.rel R z →
      (∀ k, z k ∈ S) ∨ (∀ k, z k ∈ T) := by
    intro R z hz
    rcases (hFree.rel_iff R z).mp hz with ⟨a, _, ha⟩ | ⟨b, _, hb⟩
    · exact Or.inl (fun k => ⟨a k, (congrFun ha k).symm⟩)
    · exact Or.inr (fun k => ⟨b k, (congrFun hb k).symm⟩)
  rcases hCover S T hS hT hAll hTuples with hLS | hRS
  · exact Or.inl (fun x => hLS x)
  · exact Or.inr (fun x => hRS x)

/-- The proper root-tagged expansion preserves intrinsic U-irreducibility
of CLOSED structures in both directions. In particular, tagged
irreducibility may now be used for the protected closed tests in the
repaired Theorem 2.18, without asserting anything about nonclosed
intrinsically U-irreducible weak tests. -/
theorem isUIrreducible_iff_taggedParts_of_closed
    (rules : ClosureDescription L)
    (A : RelStructure L V) (part : V → P)
    (hA : IsUClosed rules A) :
    IsUIrreducible rules A ↔
      IsUIrreducible (rules.withTaggedClosureParts P)
        (RelStructure.expandTaggedClosureParts rules A part) := by
  let T := RelStructure.expandTaggedClosureParts rules A part
  have hT : IsUClosed (rules.withTaggedClosureParts P) T :=
    (isUClosed_iff_taggedParts rules A part).mp hA
  constructor
  · intro hIrred
    apply hT.uIrreducible_of_closed_cover
    intro S R hS hR hCoverage hTuples
    apply hIrred.closed_cover hA S R
      ((isUSubstructure_iff_taggedParts rules A part S).mpr hS)
      ((isUSubstructure_iff_taggedParts rules A part R).mpr hR)
      hCoverage
    intro sym z hz
    exact hTuples (.inl sym) z hz
  · intro hIrred
    apply hA.uIrreducible_of_closed_cover
    intro S R hS hR hCoverage hTuples
    apply hIrred.closed_cover hT S R
      ((isUSubstructure_iff_taggedParts rules A part S).mp hS)
      ((isUSubstructure_iff_taggedParts rules A part R).mp hR)
      hCoverage
    intro sym z hz
    cases sym with
    | inl sym =>
        exact hTuples sym z hz
    | inr sym =>
        cases sym with
        | inl tag =>
            exact hTuples tag.rule.symbol z hz.1
        | inr p =>
            let k0 := RelLanguage.taggedParts_partIndex L rules P p
            have hOne : Subsingleton
                (Fin ((L.withTaggedClosureParts rules P).arity (.inr (.inr p)))) := by
              change Subsingleton (Fin 1)
              infer_instance
            letI := hOne
            rcases hCoverage (z k0) with hLS | hRS
            · exact Or.inl (fun k => by
                have hk : k = k0 := Subsingleton.elim k k0
                simpa only [hk] using hLS)
            · exact Or.inr (fun k => by
                have hk : k = k0 := Subsingleton.elim k k0
                simpa only [hk] using hRS)

end StructuralRamsey.RelStructure
