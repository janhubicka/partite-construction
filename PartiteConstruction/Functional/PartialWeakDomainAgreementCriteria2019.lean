import PartiteConstruction.Functional.PartialWeakExactDomain2019
import PartiteConstruction.Functional.PartSaturatedWholeWeakCounterexample2019

/-!
# Track A: exact iff criteria for domain-mask agreement on weak carriers

The 2019 construction stores persistent ambient OLD domain masks on a weak
test. These masks may differ from the intrinsic partial operation domain.

The clipped weak domain agrees with the ambient domain precisely when
every ambient defined application on the exact input carrier S has EITHER
a genuinely empty value OR at least one output surviving in S.
This "no lost application" property is weaker than function-closedness:
some outputs of a multivalued fibre may escape while others survive.

For whole-fibre deletion, agreement of the domain predicates for ALL
function symbols and argument tuples is equivalent to function-closedness.
These theorems hold for nullaries, repeated inputs, defined-empty values and
arbitrary multivalued fibres, with no enlargement of S.
-/

namespace StructuralRamsey.PartialSetStructure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- No ambient defined function application on inputs in S becomes
undefined after CLIPPING: originally defined-empty is allowed, and every
other ambient defined fibre must have some surviving output in S. -/
def NoLostDefinedApplications (A : PartialSetStructure L V) (S : Set V) :
    Prop :=
  ∀ (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → S)
    (U : Set V), A.func F (Subtype.val ∘ xs) = some U →
      U = ∅ ∨ (U ∩ S).Nonempty

/-- Sharp exact-carrier criterion for equality of intrinsic clipped and
induced AMBIENT definedness masks. The output graph itself already has
the expected induced behaviour. -/
theorem weakDomain_agrees_iff_noLost
    (A : PartialSetStructure L V) (S : Set V) :
    (∀ (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → S),
       (A.weakInduce S).Defined F xs ↔
         A.Defined F (Subtype.val ∘ xs)) ↔
      NoLostDefinedApplications A S := by
  constructor
  · intro h F xs U hValue
    have hAmb : A.Defined F (Subtype.val ∘ xs) := ⟨U, hValue⟩
    have hWeak : (A.weakInduce S).Defined F xs :=
      (h F xs).mpr hAmb
    obtain ⟨T, hT, hRet⟩ :=
      (weakInduce_defined_iff_exact A S F xs).mp hWeak
    have hTU : T = U :=
      Option.some.inj (hT.symm.trans hValue)
    simpa [hTU] using hRet
  · intro hNo F xs
    constructor
    · exact weakInduce_defined_implies_ambient A S F xs
    · rintro ⟨U, hValue⟩
      exact (weakInduce_defined_iff_exact A S F xs).mpr
        ⟨U, hValue, hNo F xs U hValue⟩

/-- For WHOLE-FIBRE deletion, equality of the intrinsic domain mask
with the induced ambient mask at EVERY primitive function application
is equivalent to genuine closure under all defined function outputs. -/
theorem wholeDomain_agrees_iff_closed
    (A : PartialSetStructure L V) (S : Set V) :
    (∀ (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → S),
       (A.wholeWeakInduce S).Defined F xs ↔
         A.Defined F (Subtype.val ∘ xs)) ↔
      A.IsClosed S := by
  constructor
  · intro h F xs U hx hValue
    let ys : Fin (L.funcArity F) → S := fun i => ⟨xs i, hx i⟩
    have hVal : A.func F (Subtype.val ∘ ys) = some U := by
      simpa [ys] using hValue
    have hDefined : (A.wholeWeakInduce S).Defined F ys :=
      (h F ys).mpr ⟨U, hVal⟩
    obtain ⟨T, hT, hTS⟩ :=
      (wholeWeakInduce_defined_iff_exact A S F ys).mp hDefined
    have hUT : U = T :=
      Option.some.inj (hVal.symm.trans hT)
    exact hUT ▸ hTS
  · intro hClosed F xs
    constructor
    · intro hWeak
      obtain ⟨U, hValue, _⟩ :=
        (wholeWeakInduce_defined_iff_exact A S F xs).mp hWeak
      exact ⟨U, hValue⟩
    · rintro ⟨U, hValue⟩
      apply (wholeWeakInduce_defined_iff_exact A S F xs).mpr
      exact ⟨U, hValue,
        hClosed F (Subtype.val ∘ xs) U (fun i => (xs i).2) hValue⟩

end StructuralRamsey.PartialSetStructure

namespace StructuralRamsey.FunctionalPartite.TrackASaturation

open StructuralRamsey
open StructuralRamsey.PartialSetStructure

/-- The concrete transversal, part-saturated weak cut in Track A loses
NO entire defined clipped operation, despite not being function-closed.
All values have two outputs in distinct parts; only one survives. -/
theorem noLost_even_though_not_closed :
    NoLostDefinedApplications examplePartial S ∧
      ¬ examplePartial.IsClosed S := by
  constructor
  · intro F xs U hValue
    have hU : U = (Set.univ : Set (Fin 2)) := by
      have heq : some (Set.univ : Set (Fin 2)) = some U := by
        simpa [examplePartial] using hValue
      exact (Option.some.inj heq).symm
    subst U
    right
    exact ⟨0, Set.mem_univ _, by simp [S]⟩
  · intro hClosed
    have hSub : (Set.univ : Set (Fin 2)) ⊆ S :=
      hClosed () (fun _ : Fin 2 => (0 : Fin 2)) Set.univ
        (fun _ => by simp [S]) rfl
    have h1 : (1 : Fin 2) ∈ S := hSub (Set.mem_univ _)
    have hne : (1 : Fin 2) ≠ 0 := by decide
    exact hne (by simpa [S] using h1)

end StructuralRamsey.FunctionalPartite.TrackASaturation
