import PartiteConstruction.Functional.WholeMaskClosureTags2019
import PartiteConstruction.Functional.PatternLanguageFinite

/-!
# Finiteness of the canonical complete-mask 2019 tag language

With finitely many original symbols and finitely many output parts,
input equality patterns and complete output masks are finite.
For every one of these patterns there are finitely many FULL old
relational structures on its finite root. Active/full-root axioms
are mere propositions on this data and cannot create more elements.

Thus the 2019 fresh tag language has FINITELY many relation symbols,
despite indexing symbols by complete induced old root patterns.
This is source-language finiteness, not a general target completion.
-/

namespace StructuralRamsey.Language

universe u v
variable {L : Language.{u}} {P : Type v}
variable [Fintype P]

/-- The proof-free finite data specifying a complete-mask root. -/
def WholeMaskRootRaw (L : Language.{u}) (P : Type v)
    [Fintype P] :=
  Σ input : FunctionInputPattern L,
    Σ mask : CompleteOutputParts P,
      RelStructure (L.wholeMaskPatternLanguage P) (Fin input.rootSize)

/-- Forget positivity and domain proofs but retain the complete old
root structure. These omitted fields are propositions. -/
def WholeMaskRootPattern.toRaw
    (p : WholeMaskRootPattern L P) : WholeMaskRootRaw L P :=
  ⟨p.input, p.mask, p.root⟩

instance wholeMaskRootRaw_finite
    [Finite L.RelSymbol] [Finite L.FuncSymbol] :
    Finite (WholeMaskRootRaw L P) := by
  classical
  unfold WholeMaskRootRaw
  infer_instance

theorem WholeMaskRootPattern.toRaw_injective :
    Function.Injective
      (WholeMaskRootPattern.toRaw :
        WholeMaskRootPattern L P → WholeMaskRootRaw L P) := by
  intro a b h
  cases a
  cases b
  cases h
  rfl

/-- There are finitely many positive active full old input-root
patterns, without placing any a priori cutoff on root-pattern names. -/
instance wholeMaskRootPattern_finite
    [Finite L.RelSymbol] [Finite L.FuncSymbol] :
    Finite (WholeMaskRootPattern L P) :=
  Finite.of_injective WholeMaskRootPattern.toRaw
    WholeMaskRootPattern.toRaw_injective

/-- Consequently the complete-mask full-root 2019 closure language is
finite, as required for the finite Ramsey expansion machinery. -/
instance wholeMaskTagLanguage_symbol_finite
    [Finite L.RelSymbol] [Finite L.FuncSymbol] :
    Finite (L.wholeMaskTagLanguage P).Symbol := by
  change Finite ((L.wholeMaskPatternLanguage P).Symbol ⊕
    WholeMaskRootPattern L P)
  infer_instance

end StructuralRamsey.Language
