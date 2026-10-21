import PartiteConstruction.Structure.PartialSetFunctionsWholeMaskPatterns

#print axioms StructuralRamsey.PartialSetStructure.wholeMaskPatternGraph_output_has_domain
#print axioms StructuralRamsey.PartialSetStructure.wholeWeakInduce_wholeMaskPatternGraph_output_iff

example (L : StructuralRamsey.Language) (P : Type)
    [Fintype P] [Finite L.RelSymbol] [Finite L.FuncSymbol] :
    Finite (L.wholeMaskPatternLanguage P).Symbol := inferInstance
