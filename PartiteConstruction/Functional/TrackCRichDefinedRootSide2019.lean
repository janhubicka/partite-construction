import PartiteConstruction.Functional.TrackEFinalInducedTestLocalization2019
import PartiteConstruction.Structure.PartialSetFunctionsWholeWeak

/-!
# Track C: complete OLD source inputs localize even when their value is empty

The existing Track E actual induced-test localization only handled
NONEMPTY FUNCTION OUTPUT INCIDENCES. A genuinely partial function
may have a defined input with EMPTY output. Such an active input
is an obstruction to a free cut but is invisible to collapseDomain.

At an actual U-closed, canonical-B-covered, noncanonical tagged OLD
witness C, a defined input in the genuine partial decoder has a
COMPLETE old value relation tuple (mask size may be ZERO). Since
all primitive input positions occur in the complete relation's
root, localization of induced OLD relation tuples implies
localization of ALL primitive source input coordinates.

For a closed exact S the complete output tuple is wholly inside S,
including the zero-output tuple. This yields the missing rich
definedness-sensitive free-cut premise without a generated hull.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V W : Type v}

/-- On an ACTUAL B-covered U-closed OLD test, every source-defined
genuine Option(Set) input localizes to ONE side whenever ALL tagged
relation tuples of the exact induced test localize. The mask may be
empty: we use the complete OLD input-root relation, not a nonempty
output incidence. No collapseDomain or change of vertex carrier. -/
theorem wholeMaskCovered_inducedDefinedInput_side
    (C : RelStructure (L.wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L W) (part : W → P)
    (hC : IsUClosed (L.wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {Z : Type v}
      (Test : RelStructure (L.wholeMaskTagLanguage P) Z),
      IsUClosed (L.wholeMaskClosureRules P) Test →
      IsUIrreducible (L.wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion (Base.wholeMaskPatternGraph part))))
    (S : Set V)
    (hS : ((wholeMaskTagReduct C).wholeMaskPartialDecode).IsClosed S)
    (X Y : Set S)
    (hLoc : ∀ (R : (L.wholeMaskTagLanguage P).Symbol)
        (t : Fin ((L.wholeMaskTagLanguage P).arity R) → S),
      (C.induce S).rel R t →
        (∀ k, t k ∈ X) ∨ (∀ k, t k ∈ Y))
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → S)
    (U : Set V)
    (hVal :
      ((wholeMaskTagReduct C).wholeMaskPartialDecode).func F
        (Subtype.val ∘ xs) = some U) :
    (∀ i, xs i ∈ X) ∨ (∀ i, xs i ∈ Y) := by
  classical
  let E : RelStructure (L.wholeMaskPatternLanguage P) V :=
    wholeMaskTagReduct C
  let A : PartialSetStructure L V := E.wholeMaskPartialDecode
  have hUnique (T T' : Set V)
      (hT : HasWholeMaskValue E F (Subtype.val ∘ xs) T)
      (hT' : HasWholeMaskValue E F (Subtype.val ∘ xs) T') : T = T' :=
    wholeMaskValue_unique_of_closed_coverage
      C Base part hC hPos hCover F (Subtype.val ∘ xs) T T' hT hT'
  obtain ⟨m,r,hr,q,t,hGraph,hArgs,hOutputs⟩ :=
    (E.wholeMaskPartialDecode_func_some_iff
      F (Subtype.val ∘ xs) hUnique U).mp hVal
  let pat : Language.FunctionInputPattern L := ⟨F, m, r, hr⟩
  have hRoots (j : Fin m) :
      t (Fin.castAdd q.size j) ∈ S := by
    obtain ⟨i,hi⟩ := hr j
    have hArg : ((Subtype.val ∘ xs) i) ∈ S := (xs i).2
    rw [hArgs i] at hArg
    simpa only [hi] using hArg
  have hOutputsS (j : Fin q.size) :
      t (Fin.natAdd m j) ∈ S := by
    have hT : U ⊆ S :=
      hS F (Subtype.val ∘ xs) U (fun i => (xs i).2) hVal
    apply hT
    rw [hOutputs]
    exact ⟨j, rfl⟩
  have hAll (k : Fin (m + q.size)) : t k ∈ S :=
    Fin.addCases hRoots hOutputsS k
  let tS : Fin (m + q.size) → S :=
    fun k => ⟨t k, hAll k⟩
  have hRel : (C.induce S).rel
      (.inl (.inr (.inr (pat,q)))) tS := hGraph
  have hOneSide (Side : Set S)
      (hSide : ∀ k : Fin (m + q.size), tS k ∈ Side) :
      ∀ i, xs i ∈ Side := by
    intro i
    have heq : xs i = tS (Fin.castAdd q.size (r i)) :=
      Subtype.ext (hArgs i)
    rw [heq]
    exact hSide _
  rcases hLoc (.inl (.inr (.inr (pat,q)))) tS hRel with
    hLeft | hRight
  · exact Or.inl (hOneSide X hLeft)
  · exact Or.inr (hOneSide Y hRight)

/-- The same ROOT-localization conclusion for the exact WHOLE-FIBRE
weak restriction of the actually decoded partial source. For closed
S this is literally its genuinely induced partial structure. In
particular a weakly retained source-defined-empty input still
forces all its arguments into one OLD free-amalgam side. -/
theorem wholeMaskCovered_inducedWholeWeakDefinedInput_side
    (C : RelStructure (L.wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L W) (part : W → P)
    (hC : IsUClosed (L.wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {Z : Type v}
      (Test : RelStructure (L.wholeMaskTagLanguage P) Z),
      IsUClosed (L.wholeMaskClosureRules P) Test →
      IsUIrreducible (L.wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion (Base.wholeMaskPatternGraph part))))
    (S : Set V)
    (hS : ((wholeMaskTagReduct C).wholeMaskPartialDecode).IsClosed S)
    (X Y : Set S)
    (hLoc : ∀ (R : (L.wholeMaskTagLanguage P).Symbol)
        (t : Fin ((L.wholeMaskTagLanguage P).arity R) → S),
      (C.induce S).rel R t →
        (∀ k, t k ∈ X) ∨ (∀ k, t k ∈ Y))
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → S)
    (U : Set S)
    (hSome : (PartialSetStructure.wholeWeakInduce
        (wholeMaskTagReduct C).wholeMaskPartialDecode S).func F xs =
        some U) :
    (∀ i, xs i ∈ X) ∨ (∀ i, xs i ∈ Y) := by
  obtain ⟨T, hT, _hTS, _hUT⟩ :=
    (PartialSetStructure.wholeWeakValue_eq_some_iff
      S _ U).mp hSome
  exact wholeMaskCovered_inducedDefinedInput_side
    C Base part hC hPos hCover S hS X Y hLoc F xs T hT

end StructuralRamsey.RelStructure
