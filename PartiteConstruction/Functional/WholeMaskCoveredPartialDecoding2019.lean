import PartiteConstruction.Functional.WholeMaskDomainValueCompletion2019
import PartiteConstruction.Functional.WholeMaskCoveredActiveDomainInjective2019
import PartiteConstruction.Functional.WholeMaskCoveredOutputCrossPattern2019

/-!
# Final covered U-closed targets decode to coherent partial function domains

The genuine OLD complete-mask Option(Set) decoder was defined without
assuming consistency of arbitrary relational data. Its source round
trip and final target correctness require two independent properties:

* VALUE uniqueness: all complete-value witnesses of the same literal
  primitive input have the same ENTIRE vertex output set, even across
  distinct input equality patterns and output-part masks.
* DOMAIN completeness: every active OLD domain record has at least
  one complete-value witness; conversely every complete output tuple
  carries an active OLD domain root.

Both properties now follow for POSITIVE-ARITY functions on the FINAL
U-closed tagged C under its protected canonical B-copy coverage:
fresh tags are normal and the OLD graph roots valid, arbitrary active
domain roots injective, positive masks admit a closure completion,
and defined-empty masks retain complete zero-output graph tuples.

Thus decoding the OLD reduct returns a genuine Option(Set)-valued
partial structure whose operation is defined EXACTLY at the OLD
active domain inputs. All complete graph tuples describe precisely
that one decoded value, including some empty, multivalued outputs,
and repeated arguments. This is a final target-semantic theorem,
NOT a mixed-stage strict functional B-tree completion.
Nullary positive outputs still require their separate root reduction.
-/

namespace StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V W : Type v}

/-- In a final canonical-B-covered target, any two OLD complete
function value witnesses on the SAME actual primitive input must
have the same full output set; the witnesses may have unrelated
surjective distinct-input root patterns and mask enumerations. -/
theorem wholeMaskValue_unique_of_closed_coverage
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
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → V)
    (U T : Set V)
    (hU : HasWholeMaskValue (wholeMaskTagReduct C) F x U)
    (hT : HasWholeMaskValue (wholeMaskTagReduct C) F x T) :
    U = T := by
  classical
  have hNormal : WholeMaskTagNormal C :=
    wholeMaskTagNormal_of_closed_coverage C Base part hC hCover
  have hValid : HasValidCompleteMaskDomains (wholeMaskTagReduct C) :=
    wholeMask_validCompleteDomains_of_closed_coverage
      C Base part hC hCover
  obtain ⟨m₁, r₁, hr₁, q₁, t₁, hGraph₁, hArgs₁, hUset⟩ := hU
  obtain ⟨m₂, r₂, hr₂, q₂, t₂, hGraph₂, hArgs₂, hTset⟩ := hT
  have hSets :
      Set.range (fun j : Fin q₁.size => t₁ (Fin.natAdd m₁ j)) =
      Set.range (fun j : Fin q₂.size => t₂ (Fin.natAdd m₂ j)) :=
    hNormal.completeValue_unique_crossPattern_of_covered
      C Base part hC hValid hPos hCover
      F m₁ m₂ r₁ r₂ hr₁ hr₂ q₁ q₂ t₁ t₂ x
      hArgs₁ hArgs₂ hGraph₁ hGraph₂
  exact hUset.trans (hSets.trans hTset.symm)

/-- In the final covered U-closed tagged Picture, for each POSITIVE
primitive function input x, the genuinely partial decoded operation
is defined iff an OLD active domain-mask relation records x. In the
defined case, EVERY complete OLD graph tuple gives the exact same
decoded output set, not just a positive inclusion of incidences. -/
theorem wholeMaskPartialDecode_defined_iff_OLD_domain_of_closed_coverage
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
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → V) :
    (wholeMaskTagReduct C).wholeMaskPartialDecode.Defined F x ↔
      HasWholeMaskDomain (wholeMaskTagReduct C) F x := by
  classical
  let E := wholeMaskTagReduct C
  have hNormal : WholeMaskTagNormal C :=
    wholeMaskTagNormal_of_closed_coverage C Base part hC hCover
  have hValid : HasValidCompleteMaskDomains E :=
    wholeMask_validCompleteDomains_of_closed_coverage
      C Base part hC hCover
  have hRootInj (p : Language.FunctionInputPattern L)
      (q : Language.CompleteOutputParts P)
      (root : Fin p.rootSize → V)
      (hDomain : E.rel (.inr (.inl (p,q))) root) :
      Function.Injective root :=
    wholeMask_activeDomain_injective_of_closed_coverage
      C Base part hC hCover p q root hDomain
  have hUnique (U T : Set V)
      (hU : HasWholeMaskValue E F x U)
      (hT : HasWholeMaskValue E F x T) : U = T :=
    wholeMaskValue_unique_of_closed_coverage
      C Base part hC hPos hCover F x U T hU hT
  constructor
  · rintro ⟨U, hSome⟩
    have hU : HasWholeMaskValue E F x U :=
      (E.wholeMaskPartialDecode_func_some_iff
        F x hUnique U).mp hSome
    exact hValid.domain_of_value E F x U hU
  · intro hDomain
    obtain ⟨U, hU⟩ :=
      hNormal.domain_has_wholeMaskValue_of_injective
        C Base part hC hPos hRootInj hCover F x hDomain
    exact ⟨U, (E.wholeMaskPartialDecode_func_some_iff
      F x hUnique U).mpr hU⟩

end StructuralRamsey.RelStructure
