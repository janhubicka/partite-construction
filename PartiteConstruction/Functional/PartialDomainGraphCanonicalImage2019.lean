import PartiteConstruction.Functional.PartialDomainGraphFaithful2019
import PartiteConstruction.Structure.Relationalize

/-!
# Track A: exact image of the domain-and-output relational encoding

The previously verified `domainGraph` map is injective on genuine
`Option (Set V)` structures, but not every arbitrary structure in its
relational language is in its image. The exact necessary and sufficient
condition is that every positive function-output tuple has its corresponding
function-domain tuple. There is NO converse requirement: defined-empty
applications are legal and must be retained.

This file supplies a canonical decoder and both round trips, with literally
the same vertex carrier. It handles nullary operations and repeated argument
tuples without closure, irreducibility, transversality or finiteness assumptions.

This is a source representation theorem only. It does not assert that an
arbitrary tagged OLD/U-closed structure admits the required tree completion,
nor does it convert ordinary relational homomorphism-embeddings to exact
source-defined functional homomorphism-embeddings.
-/

namespace StructuralRamsey.PartialSetStructure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- The only coherence law required of a domain/output relational structure:
each output incidence must originate at a defined input tuple. -/
def IsCanonicalDomainGraph
    (R : RelStructure (domainGraphLanguage L) V) : Prop :=
  ∀ (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → V) (y : V),
    R.rel (.inr (.inr F)) (Structure.funcTuple xs y) →
      R.rel (.inr (.inl F)) xs

/-- Decode each defined input to the SET of its positive output incidences.
A defined input with no outputs becomes `some ∅`, not `none`. -/
noncomputable def decodeDomainGraph
    (R : RelStructure (domainGraphLanguage L) V) :
    PartialSetStructure L V := by
  classical
  exact {
    rel := fun S xs => R.rel (.inl S) xs
    func := fun F xs =>
      if R.rel (.inr (.inl F)) xs then
        some {y : V | R.rel (.inr (.inr F)) (Structure.funcTuple xs y)}
      else none
  }

/-- The decoder has precisely the relationally prescribed domain. -/
theorem decodeDomainGraph_defined_iff
    (R : RelStructure (domainGraphLanguage L) V)
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → V) :
    (decodeDomainGraph R).Defined F xs ↔
      R.rel (.inr (.inl F)) xs := by
  classical
  constructor
  · rintro ⟨U, hU⟩
    by_cases hd : R.rel (.inr (.inl F)) xs
    · exact hd
    · simp [decodeDomainGraph, hd] at hU
  · intro hd
    refine ⟨{y : V | R.rel (.inr (.inr F))
        (Structure.funcTuple xs y)}, ?_⟩
    simp [decodeDomainGraph, hd]

/-- Under output-implies-domain coherence, the decoder recovers exactly
all positive output incidences (including the zero-arity case). -/
theorem decodeDomainGraph_hasOutput_iff
    (R : RelStructure (domainGraphLanguage L) V)
    (hCan : IsCanonicalDomainGraph R)
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → V) (y : V) :
    (decodeDomainGraph R).HasOutput F xs y ↔
      R.rel (.inr (.inr F)) (Structure.funcTuple xs y) := by
  classical
  constructor
  · rintro ⟨U, hU, hy⟩
    by_cases hd : R.rel (.inr (.inl F)) xs
    · have hSet :
          U = {z : V | R.rel (.inr (.inr F))
            (Structure.funcTuple xs z)} := by
        have hEq : some {z : V | R.rel (.inr (.inr F))
            (Structure.funcTuple xs z)} = some U := by
          simpa only [decodeDomainGraph, if_pos hd] using hU
        exact (Option.some.inj hEq).symm
      simpa only [hSet, Set.mem_setOf_eq] using hy
    · simp [decodeDomainGraph, hd] at hU
  · intro hOut
    have hd := hCan F xs y hOut
    refine ⟨{z : V | R.rel (.inr (.inr F))
        (Structure.funcTuple xs z)}, ?_, hOut⟩
    simp [decodeDomainGraph, hd]

/-- Every genuine partial-function structure satisfies the relational
output-to-domain coherence requirement. -/
theorem domainGraph_isCanonical (A : PartialSetStructure L V) :
    IsCanonicalDomainGraph (domainGraph A) := by
  intro F xs y h
  have hOut : A.HasOutput F xs y := by
    simpa only [domainGraph, Structure.funcTuple_castSucc,
      Structure.funcTuple_last] using h
  obtain ⟨U, hU, _⟩ := hOut
  exact ⟨U, hU⟩

/-- Pointwise exactness of the reconstructed relational structure.
No assumption is made on any other closure, ordering or local class axiom. -/
theorem domainGraph_decode_rel_iff
    (R : RelStructure (domainGraphLanguage L) V)
    (hCan : IsCanonicalDomainGraph R)
    (symbol : (domainGraphLanguage L).Symbol)
    (xs : Fin ((domainGraphLanguage L).arity symbol) → V) :
    (domainGraph (decodeDomainGraph R)).rel symbol xs ↔
      R.rel symbol xs := by
  rcases symbol with S | symbol
  · rfl
  rcases symbol with F | F
  · exact decodeDomainGraph_defined_iff R F xs
  · simpa only [Structure.funcTuple_eta] using
      (decodeDomainGraph_hasOutput_iff R hCan F
        (fun i => xs i.castSucc) (xs (Fin.last (L.funcArity F))))

/-- Every coherent domain/output graph is representable as a genuine
partial set-valued structure, on the very same underlying vertex type. -/
theorem domainGraph_decode
    (R : RelStructure (domainGraphLanguage L) V)
    (hCan : IsCanonicalDomainGraph R) :
    domainGraph (decodeDomainGraph R) = R := by
  cases R with
  | mk rel =>
    change RelStructure.mk
      (fun symbol xs =>
        (domainGraph (decodeDomainGraph (RelStructure.mk rel))).rel symbol xs) =
      RelStructure.mk rel
    congr 1
    funext symbol xs
    exact propext
      (domainGraph_decode_rel_iff (RelStructure.mk rel) hCan symbol xs)

/-- Decoding the domain graph of a genuine partial structure recovers
the original structure, including originally defined-empty function values. -/
theorem decode_domainGraph (A : PartialSetStructure L V) :
    decodeDomainGraph (domainGraph A) = A := by
  exact eq_of_domainGraph_eq (decodeDomainGraph (domainGraph A)) A
    (domainGraph_decode (domainGraph A) (domainGraph_isCanonical A))

/-- Exact image characterization: an arbitrary relational domain/output
structure comes from some genuine partial set-valued structure if and only
if every output tuple implies its corresponding domain tuple. -/
theorem canonical_iff_exists_domainGraph
    (R : RelStructure (domainGraphLanguage L) V) :
    IsCanonicalDomainGraph R ↔
      ∃ A : PartialSetStructure L V, domainGraph A = R := by
  constructor
  · intro hCan
    exact ⟨decodeDomainGraph R, domainGraph_decode R hCan⟩
  · rintro ⟨A, hA⟩
    rw [← hA]
    exact domainGraph_isCanonical A

end StructuralRamsey.PartialSetStructure
