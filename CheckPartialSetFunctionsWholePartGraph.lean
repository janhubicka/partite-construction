import PartiteConstruction.Structure.PartialSetFunctionsWholePartGraph

#print axioms StructuralRamsey.Language.CompleteOutputParts.label_injective
#print axioms StructuralRamsey.PartialSetStructure.wholeWeakInduce_completeOutputPartGraph_rel_iff
#print axioms StructuralRamsey.PartialSetStructure.wholeWeakCompletePartGraphToInduce
#print axioms StructuralRamsey.PartialSetStructure.completeOutputPartGraph_unique_outputs

example (L : StructuralRamsey.Language) (P : Type)
    [Fintype P] [Finite L.RelSymbol] [Finite L.FuncSymbol] :
    Finite (StructuralRamsey.Language.completeOutputPartLanguage L P).Symbol :=
  inferInstance
