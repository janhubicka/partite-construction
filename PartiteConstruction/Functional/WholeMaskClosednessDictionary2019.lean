import PartiteConstruction.Functional.WholeMaskActiveRootExtraction
import PartiteConstruction.Functional.WholeMaskClosureCanonical2019
import PartiteConstruction.Functional.TupleEqualityPattern2019
import PartiteConstruction.Functional.Closed
import PartiteConstruction.Structure.PartialSetFunctionsWholePartRepresent

/-!
# Exact canonical full-mask 2019 closure dictionary

For finite genuinely partial set-valued functions with transversal
outputs and positive function arities, a vertex subset S is function
closed iff it is a relative U-substructure in the ambient canonical
full-mask tagged source. The second equivalence uses canonical
U-closedness and Lemma 2.23(1) to characterize the SAME induced
vertex carrier. This is a source theorem, not arbitrary target decoding.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey.RelStructure
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {P : Type v} {V : Type w}
variable [Fintype P]

theorem isClosed_iff_wholeMaskTagged_isUSubstructure
    (A : PartialSetStructure L V) [Finite V]
    (part : V → P) (hPos : L.PositiveFuncArity)
    (hTrans : FibreTransversal A part) (S : Set V) :
    A.IsClosed S ↔
      IsUSubstructure (L.wholeMaskClosureRules P)
        (wholeMaskTagExpansion (A.wholeMaskPatternGraph part)) S := by
  classical
  constructor
  · intro hClosed rule hrule t ht hRoot k
    obtain ⟨p, rfl⟩ := hrule
    have hPrefix : ∀ i : Fin p.input.rootSize,
        t (Fin.castAdd p.mask.size i) ∈ S := by
      intro i
      have hIdx : i.castLE p.closureRule.rootLE =
          Fin.castAdd p.mask.size i := by
        apply Fin.ext
        rfl
      rw [← hIdx]
      exact hRoot i
    have hArgs : ∀ i : Fin (L.funcArity p.input.symbol),
        t (Fin.castAdd p.mask.size (p.input.argMap i)) ∈ S :=
      fun i => hPrefix (p.input.argMap i)
    have hValue :
        A.func p.input.symbol
          ((fun i : Fin p.input.rootSize =>
            t (Fin.castAdd p.mask.size i)) ∘ p.input.argMap) =
        some (Set.range (fun j : Fin p.mask.size =>
          t (Fin.natAdd p.input.rootSize j))) := ht.1.2.1
    have hOutput : ∀ j : Fin p.mask.size,
        t (Fin.natAdd p.input.rootSize j) ∈ S := by
      intro j
      exact hClosed p.input.symbol
        ((fun i : Fin p.input.rootSize =>
          t (Fin.castAdd p.mask.size i)) ∘ p.input.argMap)
        (Set.range (fun i : Fin p.mask.size =>
          t (Fin.natAdd p.input.rootSize i)))
        hArgs hValue ⟨j, rfl⟩
    exact Fin.addCases hPrefix hOutput k
  · intro hU F xs U hXs hF y hy
    obtain ⟨q, ys, hRange, hLabels⟩ :=
      A.completeOutputPartGraph_represents_value part hTrans F xs U hF
    have hyRange : y ∈ Set.range ys := by
      rw [hRange]
      exact hy
    obtain ⟨j, hj⟩ := hyRange
    have hQPos : 0 < q.size :=
      Nat.lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
    obtain ⟨m, r, e, hSurj, hInj, hFact, _⟩ :=
      exists_tuple_equality_pattern_exact xs
    have hmPos : 0 < m := by
      by_contra hn
      have hmZero : m = 0 := Nat.eq_zero_of_not_pos hn
      subst m
      exact Fin.elim0 (r ⟨0, hPos F⟩)
    let pat : Language.FunctionInputPattern L :=
      ⟨F, m, r, hSurj⟩
    let Old := A.wholeMaskPatternGraph part
    have hArgEq : e ∘ r = xs := by
      funext i
      exact (hFact i).symm
    have hMask : part '' U = Set.range q.label := by
      rw [← hRange]
      ext a
      constructor
      · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, (hLabels i).symm⟩
      · rintro ⟨i, rfl⟩
        exact ⟨ys i, ⟨i, rfl⟩, hLabels i⟩
    have hDomain : Old.rel (.inr (.inl (pat,q))) e := by
      change Function.Injective e ∧
        ∃ T : Set V, A.func F (e ∘ r) = some T ∧
          part '' T = Set.range q.label
      refine ⟨hInj, U, ?_, hMask⟩
      rw [hArgEq]
      exact hF
    let root : Language.WholeMaskRootPattern L P :=
      Language.WholeMaskRootPattern.ofActiveDomain
        Old pat q hmPos hQPos e hDomain
    let t : Fin (m + q.size) → V := Fin.append e ys
    have hGraph : Old.rel (.inr (.inr (pat,q))) t := by
      change Function.Injective (fun i : Fin m =>
        t (Fin.castAdd q.size i)) ∧
        A.func F ((fun i : Fin m =>
          t (Fin.castAdd q.size i)) ∘ r) =
          some (Set.range (fun i : Fin q.size =>
            t (Fin.natAdd m i))) ∧
        (∀ i : Fin q.size,
          part (t (Fin.natAdd m i)) = q.label i)
      simp only [t, Fin.append_left, Fin.append_right]
      refine ⟨hInj, ?_, hLabels⟩
      rw [hArgEq, hRange]
      exact hF
    have hTag : (wholeMaskTagExpansion Old).rel (.inr root) t := by
      change Old.rel (.inr (.inr (pat,q))) t ∧
        ∃ f : RelStructure.Embedding root.root Old,
          ∀ i : Fin m, t (Fin.castAdd q.size i) = f i
      refine ⟨hGraph,
        Language.WholeMaskRootPattern.ofActiveDomain_embedding
          Old pat q hmPos hQPos e hInj hDomain, ?_⟩
      intro i
      exact Fin.append_left e ys i
    have hPrefix : ∀ i : Fin m,
        t (Fin.castAdd q.size i) ∈ S := by
      intro i
      obtain ⟨k, hk⟩ := hSurj i
      have hei : e i ∈ S := by
        rw [← hk, ← hFact k]
        exact hXs k
      simpa only [t, Fin.append_left] using hei
    have hRoot : ∀ i : Fin root.closureRule.rootSize,
        t (i.castLE root.closureRule.rootLE) ∈ S := by
      change ∀ i : Fin m, t (Fin.castAdd q.size i) ∈ S
      exact hPrefix
    have hWhole : ∀ i : Fin (m + q.size), t i ∈ S :=
      hU root.closureRule ⟨root, rfl⟩ t hTag hRoot
    have hOut : ys j ∈ S := by
      simpa only [t, Fin.append_right] using
        hWhole (Fin.natAdd m j)
    rw [hj] at hOut
    exact hOut

theorem isClosed_iff_wholeMaskTaggedInduce_isUClosed
    (A : PartialSetStructure L V) [Finite V]
    (part : V → P) (hPos : L.PositiveFuncArity)
    (hTrans : FibreTransversal A part) (S : Set V) :
    A.IsClosed S ↔
      IsUClosed (L.wholeMaskClosureRules P)
        ((wholeMaskTagExpansion (A.wholeMaskPatternGraph part)).induce S) := by
  have hAmbient : IsUClosed (L.wholeMaskClosureRules P)
      (wholeMaskTagExpansion (A.wholeMaskPatternGraph part)) :=
    A.wholeMaskTagExpansion_isUClosed part hTrans
  exact (A.isClosed_iff_wholeMaskTagged_isUSubstructure
    part hPos hTrans S).trans
      (hAmbient.induce_iff_USubstructure S).symm

end StructuralRamsey.PartialSetStructure
