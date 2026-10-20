import PartiteConstruction.Functional.NativeUClosedExactDictionary
import PartiteConstruction.Structure.WeakSubstructure
import PartiteConstruction.Ramsey.ClosureGeneratedHullRank
import PartiteConstruction.Functional.ClosedGeneratorRank

/-!
# Exact weak functional closure = relative 2019 U-closure on AMBIENT tags

For ANY literal vertex subset S of a finite real multivalued
functional structure A with positive function arities, the weak
native substructure A.weakInduce S keeps precisely those output
values whose vertices survive in S.

The induced AMBIENT complete-root tagged relational structure
(patternTagExpansion A.patternGraph).induce S retains exactly
the original output closure tuples whose vertices survive in S,
while retaining old ambient ACTIVE INPUT-DOMAIN relations even
when every corresponding output was removed.

For EVERY further subset T of the exact subtype carrier S:

  (A.weakInduce S).IsClosed T
    iff
  IsUSubstructure L.patternClosureRules
    ((patternTagExpansion A.patternGraph).induce S) T.

No S or T is functionally closed by fiat. The proof uses exact
surjective equality-pattern factorization for repeated native
arguments and captures ALL genuine multivalued outputs.
The root description uses positive primitive arities; nullaries
require the separately checked nullary reduction.

This is the missing literal WEAK-substructure closure dictionary.
It is a source-side statement, not arbitrary strict B-tree target
history/root compatibility or global EHN domain reflection.
-/

namespace StructuralRamsey.Structure

open StructuralRamsey.RelStructure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Every exact native WEAK substructure's relative function-closed
subsets are precisely relative U-substructures of the induced
AMBIENT canonical tagged full input-pattern relations.

Unlike canonical tags recomputed from truncated weak function
fibres, the displayed right-hand structure RETAINS the original
active input/domain relations; only tuples with vertices
outside S disappear. No closure hull or new vertices. -/
theorem weakIsClosed_iff_ambientTagged_isUSubstructure
    (A : Structure L V) [Finite V]
    (hPos : L.PositiveFuncArity) (S : Set V) (T : Set S) :
    (A.weakInduce S).IsClosed T ↔
      IsUSubstructure L.patternClosureRules
        ((patternTagExpansion A.patternGraph).induce S) T := by
  classical
  constructor
  · intro hClosed rule hRule t hTag hRoot j
    obtain ⟨q, rfl⟩ := hRule
    have hPrefix :
        ∀ i : Fin q.input.rootSize,
          t (Fin.castSucc i) ∈ T := by
      intro i
      have hidx :
          i.castLE q.closureRule.rootLE = Fin.castSucc i := by
        apply Fin.ext
        rfl
      rw [← hidx]
      exact hRoot i
    have hValue :
        t (Fin.last q.input.rootSize) ∈
          (A.weakInduce S).func q.input.symbol
            ((fun i : Fin q.input.rootSize => t (Fin.castSucc i)) ∘
              q.input.argMap) := by
      exact hTag.1.2
    have hOutput :
        t (Fin.last q.input.rootSize) ∈ T :=
      hClosed q.input.symbol
        ((fun i : Fin q.input.rootSize => t (Fin.castSucc i)) ∘
          q.input.argMap)
        (fun k => hPrefix (q.input.argMap k)) hValue
    refine Fin.lastCases ?_ (fun i => ?_) j
    · exact hOutput
    · exact hPrefix i
  · intro hU F x hx y hy
    let input : Fin (L.funcArity F) → V := Subtype.val ∘ x
    obtain ⟨m, r, e, hSurj, hInj, hFact, _hExact⟩ :=
      exists_tuple_equality_pattern_exact input
    have hmPos : 0 < m := by
      by_contra h
      have hmZero : m = 0 := Nat.eq_zero_of_not_pos h
      subst m
      exact Fin.elim0 (r ⟨0, hPos F⟩)
    let pat : Language.FunctionInputPattern L := {
      symbol := F
      rootSize := m
      argMap := r
      onto := hSurj
    }
    let Old := A.patternGraph
    have hargs : e ∘ r = input := by
      funext i
      exact (hFact i).symm
    have hDom : Old.rel (.inr (.inl pat)) e := by
      change Function.Injective e ∧
        (A.func F (e ∘ r)).Nonempty
      refine ⟨hInj, ⟨y.1, ?_⟩⟩
      rw [hargs]
      exact hy
    let root : Language.FunctionRootPattern L :=
      Language.FunctionRootPattern.ofActiveDomain
        Old pat hmPos e hDom
    let t : Fin (m + 1) → V := Structure.funcTuple e y.1
    have hGraph : Old.rel (.inr (.inr pat)) t := by
      change Function.Injective
          (fun i : Fin m => t (Fin.castSucc i)) ∧
        t (Fin.last m) ∈
          A.func F
            ((fun i : Fin m => t (Fin.castSucc i)) ∘ r)
      simpa only [t, Structure.funcTuple_castSucc,
        Structure.funcTuple_last, hargs] using
        (show Function.Injective e ∧ y.1 ∈ A.func F (e ∘ r)
          from ⟨hInj, by rw [hargs]; exact hy⟩)
    have hTag : (patternTagExpansion Old).rel (.inr root) t := by
      refine ⟨hGraph, ?_⟩
      refine ⟨Language.FunctionRootPattern.ofActiveDomain_embedding
        Old pat hmPos e hInj hDom, ?_⟩
      intro i
      change Structure.funcTuple e y.1 (Fin.castSucc i) = e i
      exact Structure.funcTuple_castSucc e y.1 i
    have heS : ∀ i : Fin m, e i ∈ S := by
      intro i
      obtain ⟨k, hk⟩ := hSurj i
      rw [← hk, ← hFact k]
      exact (x k).2
    have heT : ∀ i : Fin m, (⟨e i, heS i⟩ : S) ∈ T := by
      intro i
      obtain ⟨k, hk⟩ := hSurj i
      have heq : (⟨e i, heS i⟩ : S) = x k := by
        apply Subtype.ext
        calc
          e i = e (r k) := by rw [hk]
          _ = input k := (hFact k).symm
          _ = (x k).1 := rfl
      rw [heq]
      exact hx k
    let tS : Fin (m + 1) → S :=
      fun j => ⟨t j, by
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simpa only [t, Structure.funcTuple_last] using y.2
        · simpa only [t, Structure.funcTuple_castSucc] using heS i⟩
    have hTagS :
        ((patternTagExpansion Old).induce S).rel (.inr root) tS := by
      change (patternTagExpansion Old).rel (.inr root)
        (Subtype.val ∘ tS)
      exact hTag
    have hRootIn :
        ∀ i : Fin root.closureRule.rootSize,
          tS (i.castLE root.closureRule.rootLE) ∈ T := by
      change ∀ i : Fin m, tS (Fin.castSucc i) ∈ T
      intro i
      have heq : tS (Fin.castSucc i) = (⟨e i, heS i⟩ : S) := by
        apply Subtype.ext
        exact Structure.funcTuple_castSucc e y.1 i
      rw [heq]
      exact heT i
    have hLast :=
      hU root.closureRule ⟨root, rfl⟩ tS hTagS
        hRootIn (Fin.last m)
    have hLastEq : tS (Fin.last m) = y := by
      apply Subtype.ext
      exact Structure.funcTuple_last e y.1
    rw [hLastEq] at hLast
    exact hLast

/-- The full relative weak U-closure hull inside an EXACT
native weak vertex test S is literally the same vertex set
as the weak native function-closure hull of any T⊆S.

This compares closure WITHIN S, NOT the potentially larger
closure of T in the full ambient A. -/
theorem weakFunctionClosure_eq_ambientTaggedUClosureHull
    (A : Structure L V) [Finite V]
    (hPos : L.PositiveFuncArity) (S : Set V) (T : Set S) :
    (A.weakInduce S).functionClosure T =
      UClosureHull L.patternClosureRules
        ((patternTagExpansion A.patternGraph).induce S) T := by
  have hEquiv (Q : Set S) :
      (A.weakInduce S).IsClosed Q ↔
        IsUSubstructure L.patternClosureRules
          ((patternTagExpansion A.patternGraph).induce S) Q :=
    weakIsClosed_iff_ambientTagged_isUSubstructure A hPos S Q
  ext x
  change
    (∀ Q : Set S, (A.weakInduce S).IsClosed Q →
      T ⊆ Q → x ∈ Q) ↔
    (∀ Q : Set S,
      IsUSubstructure L.patternClosureRules
        ((patternTagExpansion A.patternGraph).induce S) Q →
      T ⊆ Q → x ∈ Q)
  constructor
  · intro hx Q hQ hTQ
    exact hx Q ((hEquiv Q).mpr hQ) hTQ
  · intro hx Q hQ hTQ
    exact hx Q ((hEquiv Q).mp hQ) hTQ


/-- In every EXACT weak source vertex test S, the SAME generators
in its native weak function structure also generate its AMBIENT
induced canonical U-tag structure relative to S.

The comparison is WITHIN the weak carrier S, not the often much
larger closure of S inside the full original ambient A. -/
theorem weakGeneratedBy_iff_ambientTaggedUGenerating
    (A : Structure L V) [Finite V]
    (hPos : L.PositiveFuncArity) (S : Set V) (T : Set S) :
    (A.weakInduce S).GeneratedBy T ↔
      IsUGenerating L.patternClosureRules
        ((patternTagExpansion A.patternGraph).induce S) T := by
  change (A.weakInduce S).functionClosure T = Set.univ ↔
    UClosureHull L.patternClosureRules
      ((patternTagExpansion A.patternGraph).induce S) T = Set.univ
  rw [weakFunctionClosure_eq_ambientTaggedUClosureHull A hPos S T]

/-- Minimum exact WEAK source generator size is precisely the
published 2019 USize of its induced AMBIENT tagged pattern structure.

This directly identifies the two weak-substructure induction
parameters on the SAME carrier S and does not equate
cardinality of a potentially larger closure hull with rank. -/
theorem weakGeneratedByAtMost_iff_ambientTaggedUSize_le
    (A : Structure L V) [Finite V]
    (hPos : L.PositiveFuncArity) (S : Set V)
    [Fintype S] (n : ℕ) :
    (A.weakInduce S).GeneratedByAtMost n ↔
      USize L.patternClosureRules
        ((patternTagExpansion A.patternGraph).induce S) ≤ n := by
  let Weak := A.weakInduce S
  let Tagged := (patternTagExpansion A.patternGraph).induce S
  constructor
  · rintro ⟨G, hG, hGen⟩
    have hU : IsUGenerating L.patternClosureRules Tagged (↑G : Set S) :=
      (weakGeneratedBy_iff_ambientTaggedUGenerating
        A hPos S (↑G : Set S)).mp hGen
    exact (USize_le_of_generating L.patternClosureRules Tagged G hU).trans hG
  · intro h
    obtain ⟨G, hCard, hGen⟩ :=
      USize_spec L.patternClosureRules Tagged
    have hBound : G.card ≤ n := by
      rw [hCard]
      exact h
    exact ⟨G, hBound,
      (weakGeneratedBy_iff_ambientTaggedUGenerating
        A hPos S (↑G : Set S)).mpr hGen⟩

end StructuralRamsey.Structure
