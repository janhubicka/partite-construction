import PartiteConstruction.Functional.PatternLanguageFinite

#print axioms StructuralRamsey.RelStructure.rel_injective
#print axioms StructuralRamsey.Language.FunctionInputPattern.rootSize_le_arity
#print axioms StructuralRamsey.Language.FunctionInputPattern.ofBounded_toBounded
#print axioms StructuralRamsey.Language.FunctionInputPattern.toBounded_injective

example (R : StructuralRamsey.RelLanguage) (V : Type)
    [Finite R.Symbol] [Finite V] :
    Finite (StructuralRamsey.RelStructure R V) := inferInstance

example (L : StructuralRamsey.Language) [Finite L.FuncSymbol] :
    Finite (StructuralRamsey.Language.FunctionInputPattern L) := inferInstance
