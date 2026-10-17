import PartiteConstruction.Functional.PartialFunctionPatternGraph2019
import PartiteConstruction.Structure.WeakSubstructure
import PartiteConstruction.Functional.WeakTransversalTests
import PartiteConstruction.Structure.GeneratedWeakHomImage

/-!
# Weak functional tests versus induced closure-root domain records

For the existing 2019 equality-pattern OLD relational encoding of
genuine set-valued functions, weak restriction on a vertex set S
commutes EXACTLY with output graph incidences. But it does NOT in
general commute with the DOMAIN predicate: the ambient input may
have a nonempty function value entirely OUTSIDE S, which becomes
undefined in the weak functional restriction while its induced
ambient domain tuple remains present.

This is precisely the difference between a WEAK induced U-structure
with an active but unfulfilled closure root and a U-CLOSED structure.
On a genuinely function-closed S, both domain records agree again.
The quotient/test vertex carrier stays EXACTLY S throughout.

A single global domain bit does not encode all missing values of a
multivalued function. For each output part, the genuine functional
partite transversality law supplies at most one value, hence a
part-indexed active-output bit identifies an individual closure slot.

These are syntactic bridge lemmas only. They do NOT infer compatible
strict B-tree root completions for arbitrary mixed HJ line families
or replay the relational U-closed recursive construction.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Every actual OLD equality-pattern OUTPUT graph relation commutes
with exact weak restriction, just as the unpatterned graph encoding
does. This works with arbitrary repeated input arguments and
genuinely multivalued set-valued output fibres. -/
theorem weakInduce_patternGraph_output_iff
    (A : Structure L V) (S : Set V)
    (p : Language.FunctionInputPattern L)
    (xs : Fin (p.rootSize + 1) → S) :
    (A.weakInduce S).patternGraph.rel (.inr (.inr p)) xs ↔
      (A.patternGraph.induce S).rel (.inr (.inr p)) xs := by
  change
    (Function.Injective
      (fun i : Fin p.rootSize => xs i.castSucc) ∧
      (xs (Fin.last p.rootSize)).1 ∈
        A.func p.symbol
          ((fun i : Fin p.rootSize => (xs i.castSucc).1) ∘ p.argMap)) ↔
    (Function.Injective
      (fun i : Fin p.rootSize => (xs i.castSucc).1) ∧
      (xs (Fin.last p.rootSize)).1 ∈
        A.func p.symbol
          ((fun i : Fin p.rootSize => (xs i.castSucc).1) ∘ p.argMap))
  constructor
  · rintro ⟨hInj, hGraph⟩
    refine ⟨?_, hGraph⟩
    intro i j heq
    apply hInj
    exact Subtype.ext heq
  · rintro ⟨hInj, hGraph⟩
    refine ⟨?_, hGraph⟩
    intro i j heq
    exact hInj (congrArg Subtype.val heq)

/-- The domain bit RECOMPUTED from a weak functional restriction
holds exactly when SOME original output of the input tuple
remains inside S, besides injectivity of the equality-pattern
root enumeration. -/
theorem weakInduce_patternGraph_domain_iff
    (A : Structure L V) (S : Set V)
    (p : Language.FunctionInputPattern L)
    (xs : Fin p.rootSize → S) :
    (A.weakInduce S).patternGraph.rel (.inr (.inl p)) xs ↔
      Function.Injective xs ∧
      ∃ y : V, y ∈ S ∧
        y ∈ A.func p.symbol
          ((Subtype.val ∘ xs) ∘ p.argMap) := by
  change
    (Function.Injective xs ∧
      (∃ y : S, y.1 ∈
        A.func p.symbol
          ((Subtype.val ∘ xs) ∘ p.argMap))) ↔ _
  constructor
  · rintro ⟨hInj, y, hy⟩
    exact ⟨hInj, y.1, y.2, hy⟩
  · rintro ⟨hInj, y, hyS, hyF⟩
    exact ⟨hInj, ⟨y, hyS⟩, hyF⟩

/-- The AMBIENT domain predicate restricted to S can remain true
even when all its function outputs lie outside S. The input-root
enumeration in the OLD pattern language is injective on the same
original vertices. -/
theorem induced_patternGraph_domain_iff
    (A : Structure L V) (S : Set V)
    (p : Language.FunctionInputPattern L)
    (xs : Fin p.rootSize → S) :
    (A.patternGraph.induce S).rel (.inr (.inl p)) xs ↔
      Function.Injective xs ∧
      (A.func p.symbol
        ((Subtype.val ∘ xs) ∘ p.argMap)).Nonempty := by
  change
    (Function.Injective (Subtype.val ∘ xs) ∧
      (A.func p.symbol
        ((Subtype.val ∘ xs) ∘ p.argMap)).Nonempty) ↔ _
  constructor
  · rintro ⟨hInj, hDom⟩
    refine ⟨?_, hDom⟩
    intro i j hij
    exact hInj (congrArg Subtype.val hij)
  · rintro ⟨hInj, hDom⟩
    refine ⟨?_, hDom⟩
    intro i j hij
    exact hInj (Subtype.ext hij)

/-- Recomputed WEAK domains can only lose active roots. They
never invent new ambient function roots. -/
theorem weakPatternDomain_implies_ambient
    (A : Structure L V) (S : Set V)
    (p : Language.FunctionInputPattern L)
    (xs : Fin p.rootSize → S) :
    (A.weakInduce S).patternGraph.rel (.inr (.inl p)) xs →
      (A.patternGraph.induce S).rel (.inr (.inl p)) xs := by
  intro hWeak
  obtain ⟨hInj, y, _hyS, hyF⟩ :=
    (weakInduce_patternGraph_domain_iff A S p xs).mp hWeak
  exact (induced_patternGraph_domain_iff A S p xs).mpr
    ⟨hInj, ⟨y, hyF⟩⟩

/-- A genuinely FUNCTION-CLOSED source set has no missing
function-output roots. Thus the OLD pattern domain predicate of
its weak functional restriction agrees with the induced AMBIENT
pattern-domain relation on the identical vertex set. -/
theorem weakInduce_patternGraph_domain_iff_of_closed
    (A : Structure L V) (S : Set V)
    (hS : A.IsClosed S)
    (p : Language.FunctionInputPattern L)
    (xs : Fin p.rootSize → S) :
    (A.weakInduce S).patternGraph.rel (.inr (.inl p)) xs ↔
      (A.patternGraph.induce S).rel (.inr (.inl p)) xs := by
  constructor
  · exact weakPatternDomain_implies_ambient A S p xs
  · intro hAmb
    obtain ⟨hInj, y, hyF⟩ :=
      (induced_patternGraph_domain_iff A S p xs).mp hAmb
    have hyS : y ∈ S := by
      apply hS p.symbol ((Subtype.val ∘ xs) ∘ p.argMap)
      · intro i
        exact (xs (p.argMap i)).2
      · exact hyF
    apply (weakInduce_patternGraph_domain_iff A S p xs).mpr
    exact ⟨hInj, y, hyS, hyF⟩

/-- For genuinely closed weak subsets, the ENTIRE canonical
pattern OLD relational encoding is identical to its induced
ambient counterpart. Arbitrary weak sets need not satisfy this:
the domain case explicitly uses closedness. -/
theorem weakInduce_patternGraph_rel_iff_of_closed
    (A : Structure L V) (S : Set V)
    (hS : A.IsClosed S)
    (R : (L.patternGraph).Symbol)
    (xs : Fin ((L.patternGraph).arity R) → S) :
    (A.weakInduce S).patternGraph.rel R xs ↔
      (A.patternGraph.induce S).rel R xs := by
  rcases R with R | R
  · rfl
  rcases R with p | p
  · exact weakInduce_patternGraph_domain_iff_of_closed A S hS p xs
  · exact weakInduce_patternGraph_output_iff A S p xs

/-- A fully function-closed weak substructure therefore admits a
FULL induced relational embedding of its canonical equality-pattern
record into the ambient canonical pattern graph. No new vertices
are introduced. -/
def weakPatternGraphInclusion_of_closed
    (A : Structure L V) (S : Set V)
    (hS : A.IsClosed S) :
    RelStructure.Embedding (A.weakInduce S).patternGraph A.patternGraph :=
  (RelStructure.inclusion A.patternGraph S).comp {
    toFun := id
    injective := Function.injective_id
    map_rel_iff := by
      intro R xs
      exact (weakInduce_patternGraph_rel_iff_of_closed A S hS R xs).symm
  }

/-- An ambient ACTIVE closure-root whose entire output fibre is
forgotten remains present in the induced ambient pattern graph,
but disappears from the recomputed weak function-domain record.
This is the reusable obstruction to the FALSE blanket weak/U-closed
identification. -/
theorem patternGraph_domain_lost_of_missing_outputs
    (A : Structure L V) (S : Set V)
    (p : Language.FunctionInputPattern L)
    (xs : Fin p.rootSize → S)
    (hInj : Function.Injective xs)
    (hAmbient :
      (A.func p.symbol
        ((Subtype.val ∘ xs) ∘ p.argMap)).Nonempty)
    (hOutside : ∀ y, y ∈
      A.func p.symbol ((Subtype.val ∘ xs) ∘ p.argMap) →
      y ∉ S) :
    (A.patternGraph.induce S).rel (.inr (.inl p)) xs ∧
      ¬ (A.weakInduce S).patternGraph.rel (.inr (.inl p)) xs := by
  constructor
  · exact (induced_patternGraph_domain_iff A S p xs).mpr
      ⟨hInj, hAmbient⟩
  · intro hWeak
    obtain ⟨_hinj, y, hyS, hyF⟩ :=
      (weakInduce_patternGraph_domain_iff A S p xs).mp hWeak
    exact hOutside y hyF hyS

end StructuralRamsey.Structure


namespace StructuralRamsey.FunctionalPartite

universe u v
variable {L : Language.{u}} {P V : Type v}

/-- Every ACTIVE output-part root of a genuine partite function has
exactly ONE output vertex of that part. This is precisely the
per-output-part singleton closure slot missing from the naive
global-domain encoding for genuinely MULTIVALUED fibres. -/
theorem System.existsUnique_output_at_part
    (B : System L P V)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → V) (q : P)
    (hActive : ∃ y : V, y ∈ B.func F xs ∧ B.part y = q) :
    ∃! y : V, y ∈ B.func F xs ∧ B.part y = q := by
  obtain ⟨y, hy, hqy⟩ := hActive
  refine ⟨y, ⟨hy, hqy⟩, ?_⟩
  intro z ⟨hz, hqz⟩
  exact B.funcTransversal F xs z y hz hy (hqz.trans hqy.symm)

/-- An ambient part-indexed active root retains its *source*
definedness on a weak test even when the associated output is lost.
An output of that part survives precisely if its unique witness
lies inside the EXACT tested vertex set S. -/
theorem System.active_output_survives_iff
    (B : System L P V) (S : Set V)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → S)
    (q : P) :
    (∃ y : S, y ∈ (B.toStructure.weakInduce S).func F xs ∧
        B.part y.1 = q) ↔
      (∃ y : V, y ∈ B.func F (Subtype.val ∘ xs) ∧
        B.part y = q ∧ y ∈ S) := by
  constructor
  · rintro ⟨y, hy, hq⟩
    exact ⟨y.1, hy, hq, y.2⟩
  · rintro ⟨y, hy, hq, hyS⟩
    exact ⟨⟨y, hyS⟩, hy, hq⟩

end StructuralRamsey.FunctionalPartite
