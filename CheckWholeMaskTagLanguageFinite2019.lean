import PartiteConstruction.Functional.WholeMaskTagLanguageFinite2019

#print axioms StructuralRamsey.Language.WholeMaskRootPattern.toRaw_injective

example (L : StructuralRamsey.Language) (P : Type)
    [Fintype P] [Finite L.RelSymbol] [Finite L.FuncSymbol] :
    Finite (L.wholeMaskTagLanguage P).Symbol := inferInstance
