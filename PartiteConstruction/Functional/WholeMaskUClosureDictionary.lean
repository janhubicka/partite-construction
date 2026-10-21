import PartiteConstruction.Functional.WholeMaskActiveRootExtraction
import PartiteConstruction.Structure.PartialSetFunctionsWholePartRepresent
import PartiteConstruction.Structure.PartialSetFunctionsClosure
import PartiteConstruction.Ramsey.ClosureGeneratedHullRank
import PartiteConstruction.Functional.Closed

/-!
# Exact partial-function vertex closure as 2019 U-closure of whole-mask tags

The old complete-mask source remembers the full function-value mask, while
each fresh closure tag names a full induced irreducible equality-pattern
input root and ALL positive outputs of that complete value.

For positive-arity functions, a finite transversal partial-function
structure has an EXACT vertex-closed set S iff S is a 2019 relative
U-substructure of the canonically tagged full-root structure.
Consequently the vertex-closure hull and finite generator rank coincide
with UClosureHull and USize. No extra vertices replace S.

The SOURCE is canonical; this does not normalize arbitrary U-closed
target Pictures, synchronize target mask permutations, or prove mixed
strict functional B-tree completions.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey.RelStructure
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {P : Type v} {V : Type w}
variable [Fintype P]

/-- For a finite genuinely partial transverse structure and positive
function arities, ordinary vertex closedness of EXACT S is equivalent
to the 2019 relative U-substructure condition on its canonical FULL
complete-mask input-root tagged source. -/
theorem isClosed_iff_wholeMaskTag_isUSubstructure
    (A : PartialSetStructure L V) [Finite V]
    (part : V → P) (hTrans : FibreTransversal A part)
    (hPos : L.PositiveFuncArity) (S : Set V) :
    A.IsClosed S ↔
      IsUSubstructure (L.wholeMaskClosureRules P)
        (wholeMaskTagExpansion (A.wholeMaskPatternGraph part)) S := by
  classical
  constructor
  · intro hClosed rule hRule t hTag hRoot j
    obtain ⟨p, rfl⟩ := hRule
    have hPrefix : ∀ i : Fin p.input.rootSize,
        t (Fin.castAdd p.mask.size i) ∈ S := by
      intro i
      have hIdx :
          i.castLE p.closureRule.rootLE =
            Fin.castAdd p.mask.size i := by
        apply Fin.ext
        rfl
      rw [← hIdx]
      exact hRoot i
    have hValue : A.func p.input.symbol
        ((fun i : Fin p.input.rootSize =>
          t (Fin.castAdd p.mask.size i)) ∘ p.input.argMap) =
        some (Set.range (fun k : Fin p.mask.size =>
          t (Fin.natAdd p.input.rootSize k))) := hTag.1.2.1
    have hOutput (k : Fin p.mask.size) :
        t (Fin.natAdd p.input.rootSize k) ∈ S :=
      hClosed p.input.symbol
        ((fun i : Fin p.input.rootSize =>
          t (Fin.castAdd p.mask.size i)) ∘ p.input.argMap)
        (Set.range (fun k : Fin p.mask.size =>
          t (Fin.natAdd p.input.rootSize k)))
        (fun i => hPrefix (p.input.argMap i)) hValue
        ⟨k, rfl⟩
    exact Fin.addCases (fun i => hPrefix i) (fun k => hOutput k) j
  · intro hU F xs U hx hValue y hy
    obtain ⟨m,r,e,hSurj,hInj,hFact,_⟩ :=
      exists_tuple_equality_pattern_exact xs
    have hmPos : 0 < m := by
      by_contra h
      have hZero : m = 0 := Nat.eq_zero_of_not_pos h
      subst m
      exact Fin.elim0 (r ⟨0,hPos F⟩)
    obtain ⟨q,ys,hRange,hParts⟩ :=
      A.completeOutputPartGraph_represents_value
        part hTrans F xs U hValue
    have hyRange : y ∈ Set.range ys := by
      rw [hRange]
      exact hy
    obtain ⟨j,hjy⟩ := hyRange
    have hqPos : 0 < q.size := by
      have hj := j.isLt
      omega
    let pat : Language.FunctionInputPattern L := {
      symbol := F
      rootSize := m
      argMap := r
      onto := hSurj
    }
    let Old := A.wholeMaskPatternGraph part
    let t : Fin (m + q.size) → V := Fin.append e ys
    have hArgs : e ∘ r = xs := by
      funext i
      exact (hFact i).symm
    have hGraph : Old.rel (.inr (.inr (pat,q))) t := by
      change
        Function.Injective
          (fun i : Fin m => t (Fin.castAdd q.size i)) ∧
        A.func F
          ((fun i : Fin m => t (Fin.castAdd q.size i)) ∘ r) =
          some (Set.range (fun k : Fin q.size =>
            t (Fin.natAdd m k))) ∧
        (∀ k : Fin q.size,
          part (t (Fin.natAdd m k)) = q.label k)
      simp only [t, Fin.append_left, Fin.append_right]
      refine ⟨hInj, ?_, hParts⟩
      rw [hArgs, hRange]
      exact hValue
    have hDomain : Old.rel (.inr (.inl (pat,q))) e := by
      have h := A.wholeMaskPatternGraph_output_has_domain
        part pat q t hGraph
      simpa only [t, Fin.append_left] using h
    let root : Language.WholeMaskRootPattern L P :=
      Language.WholeMaskRootPattern.ofActiveDomain
        Old pat q hmPos hqPos e hDomain
    let emb : RelStructure.Embedding root.root Old :=
      Language.WholeMaskRootPattern.ofActiveDomain_embedding
        Old pat q hmPos hqPos e hInj hDomain
    have hTag : (wholeMaskTagExpansion Old).rel (.inr root) t := by
      change
        Old.rel (.inr (.inr (pat,q))) t ∧
          ∃ g : RelStructure.Embedding root.root Old,
            ∀ i : Fin m,
              t (Fin.castAdd q.size i) = g i
      refine ⟨hGraph, emb, ?_⟩
      intro i
      exact Fin.append_left e ys i
    have hPrefix : ∀ i : Fin m,
        t (Fin.castAdd q.size i) ∈ S := by
      intro i
      obtain ⟨k,hk⟩ := hSurj i
      have heS : e i ∈ S := by
        rw [← hk, ← hFact k]
        exact hx k
      simpa only [t, Fin.append_left] using heS
    have hRoot : ∀ i : Fin root.closureRule.rootSize,
        t (i.castLE root.closureRule.rootLE) ∈ S := by
      intro i
      have hIdx :
          i.castLE root.closureRule.rootLE =
            Fin.castAdd q.size i := by
        apply Fin.ext
        rfl
      rw [hIdx]
      exact hPrefix i
    have hSelected : t (Fin.natAdd m j) ∈ S :=
      hU root.closureRule ⟨root, rfl⟩ t hTag
        hRoot (Fin.natAdd m j)
    have hY : ys j ∈ S := by
      simpa only [t, Fin.append_right] using hSelected
    rw [hjy] at hY
    exact hY

/-- Exact equality of the two ambient vertex closure operators: closure
under partial function values and 2019 U-closure of the canonical
full-root complete-mask tagged relational source. -/
theorem functionClosure_eq_wholeMaskUClosureHull
    (A : PartialSetStructure L V) [Finite V]
    (part : V → P) (hTrans : FibreTransversal A part)
    (hPos : L.PositiveFuncArity) (S : Set V) :
    A.functionClosure S =
      UClosureHull (L.wholeMaskClosureRules P)
        (wholeMaskTagExpansion (A.wholeMaskPatternGraph part)) S := by
  ext y
  rw [A.mem_functionClosure_iff S y]
  change
    (∀ T : Set V, A.IsClosed T → S ⊆ T → y ∈ T) ↔
    (∀ T : Set V,
      IsUSubstructure (L.wholeMaskClosureRules P)
        (wholeMaskTagExpansion (A.wholeMaskPatternGraph part)) T →
      S ⊆ T → y ∈ T)
  constructor
  · intro h T hT hST
    exact h T
      ((A.isClosed_iff_wholeMaskTag_isUSubstructure
        part hTrans hPos T).mpr hT) hST
  · intro h T hT hST
    exact h T
      ((A.isClosed_iff_wholeMaskTag_isUSubstructure
        part hTrans hPos T).mp hT) hST

/-- The exact minimum number of vertex generators of the original
finite genuinely partial source equals the 2019 USize of its canonical
full-root complete-mask tagged source. Not the number of hull vertices. -/
theorem generatedByAtMost_iff_wholeMaskUSize_le
    (A : PartialSetStructure L V) [Fintype V]
    (part : V → P) (hTrans : FibreTransversal A part)
    (hPos : L.PositiveFuncArity) (n : ℕ) :
    A.GeneratedByAtMost n ↔
      USize (L.wholeMaskClosureRules P)
        (wholeMaskTagExpansion (A.wholeMaskPatternGraph part)) ≤ n := by
  let Tags := wholeMaskTagExpansion (A.wholeMaskPatternGraph part)
  let Rules := L.wholeMaskClosureRules P
  have hGenerating (T : Set V) :
      A.GeneratedBy T ↔ IsUGenerating Rules Tags T := by
    change A.functionClosure T = Set.univ ↔
      UClosureHull Rules Tags T = Set.univ
    rw [A.functionClosure_eq_wholeMaskUClosureHull part hTrans hPos T]
  constructor
  · rintro ⟨G,hCard,hGen⟩
    have hUGen : IsUGenerating Rules Tags (↑G : Set V) :=
      (hGenerating (↑G : Set V)).mp hGen
    exact (USize_le_of_generating Rules Tags G hUGen).trans hCard
  · intro h
    obtain ⟨G,hCard,hUGen⟩ := USize_spec Rules Tags
    have hBound : G.card ≤ n := by
      rw [hCard]
      exact h
    exact ⟨G,hBound,(hGenerating (↑G : Set V)).mpr hUGen⟩

end StructuralRamsey.PartialSetStructure
