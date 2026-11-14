import PartiteConstruction.Functional.FibreExactness
import PartiteConstruction.Structure.PartialSetFunctionsClosed

/-!
# Track C: faithful native encoding of genuine Option(Set) functions

A genuinely partial Option(Set)-valued operation has three distinct
states at an input: undefined, defined empty, and defined nonempty.
The existing native Structure encoding by an empty set fibre loses
the first distinction.

Adjoin independent Dom_F and Empty_F relation symbols of exactly
the SAME input arity as F, retaining all original relations and
native set-valued function symbols. The entire source value is
encoded as follows:
* none: native fibre empty, Dom false, Empty false;
* some empty: native fibre empty, Dom true, Empty true;
* some U nonempty: native fibre U, Dom true, Empty false.

Full embeddings preserve and reflect this entire record.
A native EHN map preserves original source-defined Option(Set)
values on the same vertex map: nonempty fibre equality follows
from verified EHN exact-fibre transport; some-empty follows from
positive Empty_F (the EHN map is never assumed domain reflecting).

This is the representation/semantic part of the English
cover-and-pullback proof for Appendix A Track C. It does NOT yet
prove closure of the legal class under arbitrary free amalgams,
the second native B-cover construction, or the original
intrinsic class-local Ramsey theorem.
-/

namespace StructuralRamsey

universe u v w

namespace Language

/-- Dom and defined-empty input relations in addition to the native
function-graph fibres. The first right summand names Dom_F, the second
names Empty_F. No additional vertices or function symbols. -/
def withDomainEmptyFlags (L : Language.{u}) : Language.{u} where
  RelSymbol := L.RelSymbol ⊕ (L.FuncSymbol ⊕ L.FuncSymbol)
  FuncSymbol := L.FuncSymbol
  relArity
    | .inl R => L.relArity R
    | .inr (.inl F) => L.funcArity F
    | .inr (.inr F) => L.funcArity F
  funcArity := L.funcArity

end Language

namespace PartialSetStructure

variable {L : Language.{u}} {V : Type v} {W : Type w}

/-- Faithfully encode the entire Option(Set) input record in the
native function language with independent domain and empty flags. -/
def domainEmptyEncode (A : PartialSetStructure L V) :
    Structure L.withDomainEmptyFlags V where
  rel
    | .inl R, xs => A.rel R xs
    | .inr (.inl F), xs => A.Defined F xs
    | .inr (.inr F), xs => A.func F xs = some ∅
  func F xs := (A.func F xs).getD ∅

/-- A full genuine partial embedding lifts to a full embedding in the
native Dom/Empty language. In particular, some-empty cannot become
undefined, and undefined cannot become some-empty. -/
def Embedding.domainEmptyEncode
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    (e : Embedding A B) :
    Structure.Embedding A.domainEmptyEncode B.domainEmptyEncode where
  toFun := e.toFun
  injective := e.injective
  map_rel_iff := by
    intro R xs
    rcases R with R | R
    · exact e.map_rel_iff R xs
    rcases R with F | F
    · change (∃ U : Set W, B.func F (e.toFun ∘ xs) = some U) ↔
          (∃ U : Set V, A.func F xs = some U)
      rw [← e.map_func F xs]
      cases hA : A.func F xs with
      | none =>
          simp [Defined, hA]
      | some U =>
          simp [Defined, hA]
    · change B.func F (e.toFun ∘ xs) = some ∅ ↔
          A.func F xs = some ∅
      rw [← e.map_func F xs]
      cases hA : A.func F xs with
      | none =>
          simp [hA]
      | some U =>
          simp only [hA, Option.map_some, Option.some.injEq]
          constructor
          · intro hImage
            ext x
            constructor
            · intro hx
              have hfx : e.toFun x ∈
                  Structure.imageSet e.toFun U := ⟨x, hx, rfl⟩
              rw [hImage] at hfx
              have hImpossible : False := by
                simpa only [Set.mem_empty_iff_false] using hfx
              exact hImpossible.elim
            · simp
          · intro hEmpty
            subst U
            simp [Structure.imageSet]
  map_func := by
    intro F xs
    change Structure.imageSet e.toFun ((A.func F xs).getD ∅) =
      (B.func F (e.toFun ∘ xs)).getD ∅
    cases hA : A.func F xs with
    | none =>
        have hB : B.func F (e.toFun ∘ xs) = none := by
          simpa only [hA, Option.map_none] using
            (e.map_func F xs).symm
        simp [hA, hB, Structure.imageSet]
    | some U =>
        have hB : B.func F (e.toFun ∘ xs) =
            some (Structure.imageSet e.toFun U) := by
          simpa only [hA, Option.map_some] using
            (e.map_func F xs).symm
        simp only [hA, hB, Option.getD_some]

/-- Conversely, the FULL native Dom/Empty embedding induces the SAME
full genuine Option(Set) embedding on its original vertex map.
Domain reflection comes from Dom_F and the complete value comes
from the native function fibre. -/
def Embedding.ofDomainEmptyEncode
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    (e : Structure.Embedding
      A.domainEmptyEncode B.domainEmptyEncode) :
    Embedding A B where
  toFun := e.toFun
  injective := e.injective
  map_rel_iff R xs := e.map_rel_iff (.inl R) xs
  map_func := by
    intro F xs
    have hDomain : B.Defined F (e.toFun ∘ xs) ↔ A.Defined F xs :=
      e.map_rel_iff (.inr (.inl F)) xs
    have hValues : Structure.imageSet e.toFun
        ((A.func F xs).getD ∅) =
        (B.func F (e.toFun ∘ xs)).getD ∅ :=
      e.map_func F xs
    cases hA : A.func F xs with
    | none =>
        have hNot : ¬ B.Defined F (e.toFun ∘ xs) := by
          intro hB
          obtain ⟨U, hU⟩ := hDomain.mp hB
          rw [hA] at hU
          cases hU
        cases hB : B.func F (e.toFun ∘ xs) with
        | none =>
            simp [hA, hB]
        | some U =>
            exact (hNot ⟨U, hB⟩).elim
    | some U =>
        have hDefined : B.Defined F (e.toFun ∘ xs) :=
          hDomain.mpr ⟨U, hA⟩
        obtain ⟨T, hB⟩ := hDefined
        have hImage : Structure.imageSet e.toFun U = T := by
          simpa only [hA, hB, Option.getD_some] using hValues
        simpa only [hA, hB, Option.map_some, Option.some.injEq]
          using hImage

end PartialSetStructure

namespace Structure

-- The existing EHN API is universe-homogeneous in both vertex carriers.
variable {L : Language.{u}} {V W : Type v}

/-- An original native EHN projection between these FAITHFULLY
encoded genuine partial structures preserves each source-defined
entire Option(Set) value, including some empty. It does NOT reflect
undefined source inputs. -/
theorem IsEHNHomomorphismEmbedding.ofDomainEmptyEncode_originalPartial
    {A : PartialSetStructure L V} {B : PartialSetStructure L W}
    {f : V → W}
    (hf : A.domainEmptyEncode.IsEHNHomomorphismEmbedding
      B.domainEmptyEncode f) :
    PartialSetStructure.IsOriginalPartialHomomorphism A B f := by
  constructor
  · intro R xs hRel
    exact hf.1.1 (.inl R) xs hRel
  · intro F xs U hA
    by_cases hNonempty : U.Nonempty
    · have hSourceNonempty :
          (A.domainEmptyEncode.func F xs).Nonempty := by
        change ((A.func F xs).getD ∅).Nonempty
        simpa [hA] using hNonempty
      have hFull := hf.map_func_of_nonempty F xs hSourceNonempty
      have hEq : Structure.imageSet f U =
          (B.func F (f ∘ xs)).getD ∅ := by
        change Structure.imageSet f ((A.func F xs).getD ∅) =
          (B.func F (f ∘ xs)).getD ∅ at hFull
        simpa only [hA, Option.getD_some] using hFull
      have hDom : B.Defined F (f ∘ xs) :=
        hf.1.1 (.inr (.inl F)) xs ⟨U, hA⟩
      obtain ⟨T, hB⟩ := hDom
      have hImage : Structure.imageSet f U = T := by
        simpa only [hB, Option.getD_some] using hEq
      exact hB.trans (congrArg some hImage.symm)
    · have hEmpty : U = ∅ := by
        ext y
        constructor
        · intro hy
          exact (hNonempty ⟨y, hy⟩).elim
        · simp
      have hSourceEmptyRel :
          A.domainEmptyEncode.rel (.inr (.inr F)) xs := by
        change A.func F xs = some ∅
        rw [hA, hEmpty]
      have hTargetEmptyRel :=
        hf.1.1 (.inr (.inr F)) xs hSourceEmptyRel
      change B.func F (f ∘ xs) = some ∅ at hTargetEmptyRel
      simpa only [hEmpty, Structure.imageSet, Set.image_empty]
        using hTargetEmptyRel

end Structure
end StructuralRamsey
