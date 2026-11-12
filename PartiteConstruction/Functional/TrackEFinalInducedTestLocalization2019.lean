import PartiteConstruction.Functional.TrackEFinalCoveredClosureDictionary2019
import PartiteConstruction.Functional.TrackEFinalCoveredCompleteValueSideLocalization2019
import PartiteConstruction.Structure.FreeAmalgamationClass
import PartiteConstruction.Structure.PartialSetFunctionsClosure

/-!
# Track E: exact induced tagged tests transfer native closure and free-cover incidences

This is preparation for the actual final global-control homomorphism-embedding.
Take an ACTUAL final covered U-closed whole-mask tagged 2019 witness C and
an exact S closed under its decoded genuine partial functions. Do not
replace C by a canonical tagged decoder, nor replace S by its hull.

1. A relatively U-closed side X of C.induce S becomes a function-closed
   side of the actual full native restriction to S.
2. If the tuples of C.induce S localize to X/Y, then every native
   function incidence in that full restricted structure localizes to
   X/Y, by a single OLD COMPLETE-VALUE tuple for the entire decoded
   output set. The relation-side localization is immediate separately.

The next theorem can combine these with native irreducibility in
lean-all-those-ramsey-classes; it does NOT assert U-irreducibility here.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V W : Type v}

/-- Relative U-closedness INSIDE an exact tagged test implies intrinsic
native function-closedness in the actual full native induced test.
Both side sets remain on the original S-carrier. -/
theorem wholeMaskCovered_inducedUSubstructure_to_nativeClosed
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
    (hS : ((wholeMaskTagReduct C).wholeMaskPartialDecode).IsClosed S)
    (X : Set S)
    (hX : IsUSubstructure (L.wholeMaskClosureRules P)
      (C.induce S) X) :
    (((wholeMaskTagReduct C).wholeMaskPartialDecode.collapseDomain).induce
      S ((PartialSetStructure.isClosed_iff_collapseDomain_isClosed
          (wholeMaskTagReduct C).wholeMaskPartialDecode S).mp hS)).IsClosed X := by
  let A : PartialSetStructure L V :=
    (wholeMaskTagReduct C).wholeMaskPartialDecode
  let N : Structure L V := A.collapseDomain
  have hSU : IsUSubstructure (L.wholeMaskClosureRules P) C S :=
    wholeMaskCovered_decodedClosed_to_USubstructure
      C Base part hC hPos hCover S hS
  have hXU : IsUSubstructure (L.wholeMaskClosureRules P) C
      (Subtype.val '' X) := hSU.image_inclusion hX
  have hAX : A.IsClosed (Subtype.val '' X) :=
    (wholeMaskCovered_USubstructure_iff_decodedClosed
      C Base part hC hPos hCover (Subtype.val '' X)).mp hXU
  have hNX : N.IsClosed (Subtype.val '' X) :=
    (A.isClosed_iff_collapseDomain_isClosed (Subtype.val '' X)).mp hAX
  intro F xs hXs y hy
  have hyN : y.1 ∈ N.func F (Subtype.val ∘ xs) := hy
  have hArgs : ∀ i, (xs i).1 ∈ Subtype.val '' X :=
    fun i => ⟨xs i, hXs i, rfl⟩
  obtain ⟨z, hz, hzeq⟩ := hNX F (Subtype.val ∘ xs) hArgs hyN
  have hyEq : y = z := Subtype.ext hzeq.symm
  exact hyEq.symm ▸ hz

/-- Every genuine native function incidence INSIDE the exact full
function-closed S-restriction is localized to a single side of any
two-set free cover of the ACTUAL induced tagged test C.induce S.

Uses the ORIGINAL full decoded value and its complete OLD output
tuple. The root may repeat primitive inputs; the output may have
several distinct parts. No closure-hull or alternate target. -/
theorem wholeMaskCovered_inducedNativeFunctionIncident_side
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
    (hS : ((wholeMaskTagReduct C).wholeMaskPartialDecode).IsClosed S)
    (X Y : Set S)
    (hLoc : ∀ (R : (L.wholeMaskTagLanguage P).Symbol)
        (t : Fin ((L.wholeMaskTagLanguage P).arity R) → S),
      (C.induce S).rel R t →
        (∀ k, t k ∈ X) ∨ (∀ k, t k ∈ Y))
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → S) (y : S)
    (hy : y ∈
      (((wholeMaskTagReduct C).wholeMaskPartialDecode.collapseDomain).induce
        S ((PartialSetStructure.isClosed_iff_collapseDomain_isClosed
          (wholeMaskTagReduct C).wholeMaskPartialDecode S).mp hS)).func F xs) :
    ((∀ i, xs i ∈ X) ∧ y ∈ X) ∨
      ((∀ i, xs i ∈ Y) ∧ y ∈ Y) := by
  classical
  let E : RelStructure (L.wholeMaskPatternLanguage P) V :=
    wholeMaskTagReduct C
  let A : PartialSetStructure L V := E.wholeMaskPartialDecode
  have hyNative :
      y.1 ∈ A.collapseDomain.func F (Subtype.val ∘ xs) := hy
  cases hVal : A.func F (Subtype.val ∘ xs) with
  | none =>
      have hFalse : False := by
        change y.1 ∈ (A.func F (Subtype.val ∘ xs)).getD ∅ at hyNative
        simp [hVal] at hyNative
      exact hFalse.elim
  | some U =>
      have hyU : y.1 ∈ U := by
        change y.1 ∈ (A.func F (Subtype.val ∘ xs)).getD ∅ at hyNative
        simpa [hVal] using hyNative
      have hUnique (T T' : Set V)
          (hT : HasWholeMaskValue E F (Subtype.val ∘ xs) T)
          (hT' : HasWholeMaskValue E F (Subtype.val ∘ xs) T') : T = T' :=
        wholeMaskValue_unique_of_closed_coverage
          C Base part hC hPos hCover F (Subtype.val ∘ xs) T T' hT hT'
      obtain ⟨m,r,hr,q,t,hGraph,hArgs,hOutputs⟩ :=
        (E.wholeMaskPartialDecode_func_some_iff
          F (Subtype.val ∘ xs) hUnique U).mp hVal
      let pat : Language.FunctionInputPattern L := ⟨F,m,r,hr⟩
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
          (.inl (.inr (.inr (pat, q)))) tS := hGraph
      have hOneSide (T : Set S)
          (hT : ∀ k : Fin (m + q.size), tS k ∈ T) :
          (∀ i, xs i ∈ T) ∧ y ∈ T := by
        constructor
        · intro i
          have heq : xs i = tS (Fin.castAdd q.size (r i)) :=
            Subtype.ext (hArgs i)
          rw [heq]
          exact hT _
        · have hyRange : y.1 ∈ Set.range
              (fun j : Fin q.size => t (Fin.natAdd m j)) := by
            rw [← hOutputs]
            exact hyU
          obtain ⟨j,hj⟩ := hyRange
          have heq : y = tS (Fin.natAdd m j) :=
            Subtype.ext hj.symm
          rw [heq]
          exact hT _
      rcases hLoc (.inl (.inr (.inr (pat,q)))) tS hRel with
        hLeft | hRight
      · exact Or.inl (hOneSide X hLeft)
      · exact Or.inr (hOneSide Y hRight)

end StructuralRamsey.RelStructure
