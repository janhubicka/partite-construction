import PartiteConstruction.Functional.PatternCompleteRootExtraction2019
import PartiteConstruction.Functional.PatternClosureCanonical2019
import PartiteConstruction.Functional.WeakPatternDomainBridge2019
import PartiteConstruction.Functional.Closed

/-!
# Exact native function closure equals the 2019 U-substructure condition

The canonical relation/function-to-U-closure encoding has a
FRESH closure relation for each FULL equality-pattern ROOT of
an actual defined function tuple. Its active tagged closure tuples
are exactly the native output graph tuples with that FULL root.

For any finite genuine relation/set-valued-function structure A
in a POSITIVE-function-arity language, and ANY EXACT vertex set S:

  A.IsClosed S  iff
    IsUSubstructure L.patternClosureRules
      (patternTagExpansion A.patternGraph) S.

No singleton-valuedness is needed: every possible output has its
OWN tagged tuple and the U-substructure condition requires every
one of them to stay inside S. Repeated inputs are handled by
the verified surjective equality-pattern factorization.

For singleton-valued A, the canonical tagged ambient structure
is itself U-CLOSED (previously verified), so the 2019
induce_iff_USubstructure lemma also identifies native closed S
with U-CLOSEDNESS of the tagged INDUCED structure on EXACTLY S.

For arbitrary weak S the induced AMBIENT tagged relations must
be retained: recomputing a domain bit from the weakly restricted
native function would forget active closure roots with missing
outputs. That difference is proved in WeakPatternDomainBridge2019.

This is a proof of the faithful SOURCE closure dictionary, NOT
a full native HJ mixed-rank or strict target-tree completion theorem.
-/

namespace StructuralRamsey.Structure

open StructuralRamsey.RelStructure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Native function-closedness of an EXACT S is precisely the
relative 2019 U-substructure property in the canonical tagged
equality-pattern function-graph language.

This equivalence holds for genuinely MULTIVALUED fibres without
output-part transversality. Every native output yields a closure
tuple, so the U-substructure condition prevents losing ANY output.
Nullaries are excluded exactly as required by the published 2019
positive-root closure description; a separate nullary reduction
is necessary for arity-zero function symbols. -/
theorem isClosed_iff_taggedPattern_isUSubstructure
    (A : Structure L V) [Finite V]
    (hPos : L.PositiveFuncArity) (S : Set V) :
    A.IsClosed S ↔
      IsUSubstructure L.patternClosureRules
        (patternTagExpansion A.patternGraph) S := by
  classical
  constructor
  · intro hClosed rule hRule t hTag hRoot j
    obtain ⟨q, rfl⟩ := hRule
    have hPrefix :
        ∀ i : Fin q.input.rootSize,
          t (Fin.castSucc i) ∈ S := by
      intro i
      have hidx :
          i.castLE q.closureRule.rootLE = Fin.castSucc i := by
        apply Fin.ext
        rfl
      rw [← hidx]
      exact hRoot i
    have hValue :
        t (Fin.last q.input.rootSize) ∈
          A.func q.input.symbol
            ((fun i : Fin q.input.rootSize => t (Fin.castSucc i)) ∘
              q.input.argMap) := by
      exact hTag.1.2
    have hOutput :
        t (Fin.last q.input.rootSize) ∈ S :=
      hClosed q.input.symbol
        ((fun i : Fin q.input.rootSize => t (Fin.castSucc i)) ∘
          q.input.argMap)
        (fun k => hPrefix (q.input.argMap k)) hValue
    refine Fin.lastCases ?_ (fun i => ?_) j
    · exact hOutput
    · exact hPrefix i
  · intro hU F x hx y hy
    obtain ⟨m, r, e, hSurj, hInj, hFact, _hExact⟩ :=
      exists_tuple_equality_pattern_exact x
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
    have hargs : e ∘ r = x := by
      funext i
      exact (hFact i).symm
    have hDom : Old.rel (.inr (.inl pat)) e := by
      change Function.Injective e ∧
        (A.func F (e ∘ r)).Nonempty
      refine ⟨hInj, ⟨y, ?_⟩⟩
      rw [hargs]
      exact hy
    let root : Language.FunctionRootPattern L :=
      Language.FunctionRootPattern.ofActiveDomain
        Old pat hmPos e hDom
    let t : Fin (m + 1) → V := Structure.funcTuple e y
    have hGraph : Old.rel (.inr (.inr pat)) t := by
      change Function.Injective
          (fun i : Fin m => t (Fin.castSucc i)) ∧
        t (Fin.last m) ∈
          A.func F
            ((fun i : Fin m => t (Fin.castSucc i)) ∘ r)
      simpa only [t, Structure.funcTuple_castSucc,
        Structure.funcTuple_last, hargs] using
        (show Function.Injective e ∧ y ∈ A.func F (e ∘ r)
          from ⟨hInj, by rw [hargs]; exact hy⟩)
    have hTag : (patternTagExpansion Old).rel (.inr root) t := by
      refine ⟨hGraph, ?_⟩
      refine ⟨Language.FunctionRootPattern.ofActiveDomain_embedding
        Old pat hmPos e hInj hDom, ?_⟩
      intro i
      change Structure.funcTuple e y (Fin.castSucc i) = e i
      exact Structure.funcTuple_castSucc e y i
    have hPrefixIn : ∀ i : Fin m, t (Fin.castSucc i) ∈ S := by
      intro i
      obtain ⟨k, hk⟩ := hSurj i
      have hmem : e i ∈ S := by
        rw [← hk, ← hFact k]
        exact hx k
      have heq : t (Fin.castSucc i) = e i := by
        change Structure.funcTuple e y (Fin.castSucc i) = e i
        exact Structure.funcTuple_castSucc e y i
      rw [heq]
      exact hmem
    have hRootIn :
        ∀ i : Fin root.closureRule.rootSize,
          t (i.castLE root.closureRule.rootLE) ∈ S := by
      change ∀ i : Fin m, t (Fin.castSucc i) ∈ S
      exact hPrefixIn
    have hLast :=
      hU root.closureRule ⟨root, rfl⟩ t hTag
        hRootIn (Fin.last m)
    simpa only [t, Structure.funcTuple_last] using hLast

/-- On genuine finite SINGLETON-valued partial functions, the
canonical tagged relation structure is U-closed. Hence the
published 2019 exact induced U-closedness predicate is EQUIVALENT
to ordinary native function-closedness of the SAME vertex set S.

No weak test is replaced by its generated function closure.
The induced AMBIENT tagged domain relations stay present, even
when the recomputed native weak restriction would lose outputs. -/
theorem isClosed_iff_taggedPatternInduce_isUClosed
    (A : Structure L V) [Finite V]
    (hPos : L.PositiveFuncArity)
    (hSingle : A.SingletonValued)
    (S : Set V) :
    A.IsClosed S ↔
      IsUClosed L.patternClosureRules
        ((patternTagExpansion A.patternGraph).induce S) := by
  have hAmbient : IsUClosed L.patternClosureRules
      (patternTagExpansion A.patternGraph) :=
    patternTagExpansion_isUClosed A hSingle
  exact
    (isClosed_iff_taggedPattern_isUSubstructure A hPos S).trans
      (hAmbient.induce_iff_USubstructure S).symm

end StructuralRamsey.Structure
