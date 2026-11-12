import PartiteConstruction.Functional.WholeMaskCoveredPartialDecoding2019
import PartiteConstruction.Functional.WholeMaskCoveredTargetTagNormality2019
import PartiteConstruction.Functional.WholeMaskClosednessDictionary2019
import PartiteConstruction.Structure.PartialSetFunctionsClosure

/-!
# Track E: a closed decoded final vertex set is an actual U-substructure

The final 2019 U-closed, protected canonical-B-covered tagged witness
may have a noncanonical OLD reduct. Do NOT assert equality with the
canonical tagging of its decoded partial-function structure.

There is nevertheless a one-way exact closedness transfer on any
literal vertex set S. Normality identifies every actual fresh closure
tag with an OLD complete-output-value tuple. Covered cross-pattern
uniqueness identifies that tuple with the entire decoded function
value at precisely the primitive input tuple. If the decoded genuine
partial-function structure is closed on S, the outputs all stay in S.

Thus the SAME S is a relative U-substructure of the ACTUAL tagged C.
Since C is globally U-closed, its induced structure on S is intrinsically
U-closed. No generated hull, canonicality of C, or change of cutoff.
This is the closedness half of the outstanding native irreducible
exact-test geometry in Appendix A Track E; U-irreducibility is separate.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V W : Type v}

/-- In the verified FINAL U-closed B-covered tagged 2019 Picture,
function-closedness of S in the genuine whole-value decoder implies
relative U-closedness of the EXACT same set of original tagged vertices.

The converse is not needed for this result, and no synthetic canonical
tagged witness replaces C. -/
theorem wholeMaskCovered_decodedClosed_to_USubstructure
    (C : RelStructure (L.wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L W) (part : W → P)
    (hC : IsUClosed (L.wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure (L.wholeMaskTagLanguage P) X),
      IsUClosed (L.wholeMaskClosureRules P) Test →
      IsUIrreducible (L.wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion (Base.wholeMaskPatternGraph part))))
    (S : Set V)
    (hDecodedClosed :
      ((wholeMaskTagReduct C).wholeMaskPartialDecode).IsClosed S) :
    IsUSubstructure (L.wholeMaskClosureRules P) C S := by
  classical
  let E : RelStructure (L.wholeMaskPatternLanguage P) V :=
    wholeMaskTagReduct C
  have hNormal : WholeMaskTagNormal C :=
    wholeMaskTagNormal_of_closed_coverage C Base part hC hCover
  intro rule hrule t ht hRoot k
  obtain ⟨p, rfl⟩ := hrule
  let F : L.FuncSymbol := p.input.symbol
  let xs : Fin (L.funcArity F) → V :=
    (fun i : Fin p.input.rootSize =>
      t (Fin.castAdd p.mask.size i)) ∘ p.input.argMap
  let outputs : Set V :=
    Set.range (fun j : Fin p.mask.size =>
      t (Fin.natAdd p.input.rootSize j))
  have hGraph : E.rel (.inr (.inr (p.input, p.mask))) t :=
    ((hNormal p t).mp ht).1
  have hWitness : HasWholeMaskValue E F xs outputs := by
    refine ⟨p.input.rootSize, p.input.argMap, p.input.onto,
      p.mask, t, hGraph, ?_, ?_⟩
    · intro i
      rfl
    · rfl
  have hUnique (U T : Set V)
      (hU : HasWholeMaskValue E F xs U)
      (hT : HasWholeMaskValue E F xs T) : U = T :=
    wholeMaskValue_unique_of_closed_coverage
      C Base part hC hPos hCover F xs U T hU hT
  have hValue :
      E.wholeMaskPartialDecode.func F xs = some outputs :=
    (E.wholeMaskPartialDecode_func_some_iff
      F xs hUnique outputs).mpr hWitness
  have hRootS :
      ∀ i : Fin p.input.rootSize,
        t (Fin.castAdd p.mask.size i) ∈ S := by
    intro i
    have hIdx : i.castLE p.closureRule.rootLE =
        Fin.castAdd p.mask.size i := by
      apply Fin.ext
      rfl
    rw [← hIdx]
    exact hRoot i
  have hInputs : ∀ i : Fin (L.funcArity F), xs i ∈ S := by
    intro i
    exact hRootS (p.input.argMap i)
  have hOutputs :
      ∀ j : Fin p.mask.size,
        t (Fin.natAdd p.input.rootSize j) ∈ S := by
    intro j
    exact hDecodedClosed F xs outputs hInputs hValue ⟨j, rfl⟩
  exact Fin.addCases hRootS hOutputs k

/-- Same original vertices, with no closure hull: the exact induced
tagged test is U-closed whenever the final decoded genuine partial
operation is closed on that set. -/
theorem wholeMaskCovered_decodedClosed_to_inducedUClosed
    (C : RelStructure (L.wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L W) (part : W → P)
    (hC : IsUClosed (L.wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure (L.wholeMaskTagLanguage P) X),
      IsUClosed (L.wholeMaskClosureRules P) Test →
      IsUIrreducible (L.wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion (Base.wholeMaskPatternGraph part))))
    (S : Set V)
    (hDecodedClosed :
      ((wholeMaskTagReduct C).wholeMaskPartialDecode).IsClosed S) :
    IsUClosed (L.wholeMaskClosureRules P) (C.induce S) := by
  apply (hC.induce_iff_USubstructure S).mpr
  exact wholeMaskCovered_decodedClosed_to_USubstructure
    C Base part hC hPos hCover S hDecodedClosed

end StructuralRamsey.RelStructure
