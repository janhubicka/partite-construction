import PartiteConstruction.Functional.TrackEClosedExactTaggedTestEmbedding2019
import PartiteConstruction.Functional.TrackENativePartialFullFaithfulness
import PartiteConstruction.Functional.WholeMaskCoveredFunctionalTarget2019
import PartiteConstruction.Functional.PartialSetFunctionsPartPredicates2019

/-!
# Track E: forget genuine unary labels on ACTUAL tagged-test decoders

The final two-pass whole-mask tagged witness need not be canonically tagged.
Its complete-function decoder lives in the language with unary part predicates.
The original native HE endpoint, however, is in the original language.

A full embedding of an ACTUAL exact induced tagged test into a canonical
control can first be decoded to a full PART-LABELLED partial-function
embedding by the existing closed-exact-test theorem. The present adapter
forgets only the unary labels on arbitrary decoded structures (not merely
structures already of the form A.withParts), retaining all original
functions and their independent definedness bits.

We also prove the general closed-vertex dictionary from whole-fibre weak
partial restrictions to the usual native induced structure, and full
faithfulness after collapsing domains. These are the precise primitive
steps needed to close the same-selected-map native HE on original full
irreducible tests. No canonicality or membership of the final tagged
picture in the original native class is assumed.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.RelStructure
open StructuralRamsey.Structure.TrackENativePartialFullFaithfulness

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V W : Type w}

/-- Forget unary part predicates from an arbitrary genuine partial
structure in the expanded language. This is also defined for a
noncanonical final decoded tagged witness. -/
def originalLanguageReduct
    (A : PartialSetStructure (L.withParts Parts) V) :
    PartialSetStructure L V where
  rel R xs := A.rel (.inl (ULift.up R)) xs
  func F xs := A.func (ULift.up F) xs

/-- Full embeddings of arbitrary part-labelled partial structures
forget only the part symbols, preserving and reflecting the entire
primitive function Option(Set) value on precisely the same map. -/
def Embedding.originalLanguageReduct
    {A : PartialSetStructure (L.withParts Parts) V}
    {B : PartialSetStructure (L.withParts Parts) W}
    (e : Embedding A B) :
    Embedding A.originalLanguageReduct B.originalLanguageReduct where
  toFun := e.toFun
  injective := e.injective
  map_rel_iff R xs := e.map_rel_iff (.inl (ULift.up R)) xs
  map_func F xs := e.map_func (ULift.up F) xs

/-- The new reduct agrees exactly with the usual forget-parts
operation on canonical unary-part expansions. -/
theorem originalLanguageReduct_withParts
    (A : PartialSetStructure L V) (part : V → Parts) :
    (A.withParts part).originalLanguageReduct = A := rfl

/-- No function value is recomputed when forgetting the part labels
on a literal weak carrier. -/
theorem originalLanguageReduct_wholeWeakInduce
    (A : PartialSetStructure (L.withParts Parts) V)
    (S : Set V) :
    (A.wholeWeakInduce S).originalLanguageReduct =
      (A.originalLanguageReduct).wholeWeakInduce S := rfl

/-- Forgetting arbitrary part-labelled structures commutes with
collapsing the independent domain bit at every original input. -/
def Embedding.originalNativeCollapse
    {A : PartialSetStructure (L.withParts Parts) V}
    {B : PartialSetStructure (L.withParts Parts) W}
    (e : Embedding A B) :
    Structure.Embedding
      A.originalLanguageReduct.collapseDomain
      B.originalLanguageReduct.collapseDomain where
  toFun := e.toFun
  injective := e.injective
  map_rel_iff R xs := e.map_rel_iff (.inl (ULift.up R)) xs
  map_func := by
    intro F xs
    have heq := e.map_func (ULift.up F) xs
    have hget := congrArg (fun x : Option (Set W) => x.getD ∅) heq
    change Structure.imageSet e.toFun
      ((A.func (ULift.up F) xs).getD ∅) =
      (B.func (ULift.up F) (e.toFun ∘ xs)).getD ∅
    simpa only [option_getD_image] using hget

/-- A genuinely function-closed exact set loses no whole-value outputs,
so the collapsed whole-fibre weak restriction is exactly the native
full induced structure on that set. This is NOT true on arbitrary
nonclosed weak sets. -/
theorem wholeWeakInduce_collapse_eq_nativeInduce
    (A : PartialSetStructure L V) (S : Set V)
    (hS : A.IsClosed S) :
    (A.wholeWeakInduce S).collapseDomain =
      A.collapseDomain.induce S
        ((A.isClosed_iff_collapseDomain_isClosed S).mp hS) := by
  classical
  change
    Structure.mk
      (fun R xs => A.rel R (Subtype.val ∘ xs))
      (fun F xs =>
        (wholeWeakValue S (A.func F (Subtype.val ∘ xs))).getD ∅) =
    Structure.mk
      (fun R xs => A.rel R (Subtype.val ∘ xs))
      (fun F xs =>
        {y : S | y.1 ∈ (A.func F (Subtype.val ∘ xs)).getD ∅})
  congr 1
  funext F xs
  cases h : A.func F (Subtype.val ∘ xs) with
  | none =>
      simp only [h, wholeWeakValue_none, Option.getD_none, Set.mem_empty_iff_false]
      rfl
  | some U =>
      have hU : U ⊆ S :=
        hS F (Subtype.val ∘ xs) U (fun i => (xs i).2) h
      simp only [wholeWeakValue_of_subset S U hU, Option.getD_some]

/-- The original-language reduct of the actual final tagged decoder
is IDENTICALLY the previously verified original 2019 decoder. -/
theorem originalLanguageReduct_actualWholeMaskDecoder
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V) :
    (((wholeMaskTagReduct C).wholeMaskPartialDecode).originalLanguageReduct) =
      wholeMaskOriginalDecode C := rfl

end StructuralRamsey.PartialSetStructure
