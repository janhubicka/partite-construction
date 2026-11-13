import PartiteConstruction.Functional.WholeMaskProjectionOldHom2019
import PartiteConstruction.Functional.TrackBRealEHNExactImageUSize2019
import PartiteConstruction.Functional.FibreExactness

/-!
# Track C: native EHN maps preserve the OLD complete masks, no defined-empty

The English two-pass/cover proof requires the NATIVE EHN map from
the second cover pass to preserve the complete OLD relation symbols
of the first pass on SOURCE-DEFINED applications.

For genuine Option(Set) partial structures with defined-empty inputs,
the separate domain and empty masks require a faithful legal encoding.
Here we prove the nonempty-valued native subcase with no additional
axiom and on the same original vertex map.

A native EHN map is full on every irreducible closed test. For a
realized primitive function input, the generated closure of that
input root is irreducible, even if the whole source is reducible.
Thus the EHN map cannot identify distinct input-root vertices.
With this root-injectivity, the already verified
IsOriginalPartialHomomorphism.wholeMaskPatternGraph_hom transports
the full OLD complete-value and active-domain relations.

This is a positive OLD homomorphism, not a full embedding globally:
source-undefined tuples are not required to remain undefined.
The U-tagged lift and full-test protection are separate obligations.
-/

namespace StructuralRamsey.Structure

open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {U V : Type v}
variable {P : Type w} [Fintype P]

/-- Any native EHN map is injective on distinct vertices among the
inputs of one genuinely defined (nonempty-fibre) operation. This is
not global injectivity or domain reflection. -/
theorem IsEHNHomomorphismEmbedding.input_eq_of_defined
    {A : Structure L U} {B : Structure L V} {f : U → V}
    (hf : A.IsEHNHomomorphismEmbedding B f)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → U)
    (hDefined : (A.func F xs).Nonempty)
    (i j : Fin (L.funcArity F))
    (hImages : f (xs i) = f (xs j)) :
    xs i = xs j := by
  classical
  let Hset : Set U := A.functionClosure (Set.range xs)
  have hClosed : A.IsClosed Hset :=
    A.functionClosure_isClosed (Set.range xs)
  let H : Structure L Hset := A.induce Hset hClosed
  obtain ⟨y, hy⟩ := hDefined
  have hIrred : H.Irreducible := by
    change (A.induce
      (A.functionClosure (Set.range xs))
      (A.functionClosure_isClosed (Set.range xs))).Irreducible
    exact functionClosure_inputs_irreducible_of_value A F xs hy
  let inc : Embedding H A := inclusion A Hset hClosed
  obtain ⟨g, hg⟩ := hf.2 H hIrred inc
  have hi : xs i ∈ Hset :=
    A.subset_functionClosure (Set.range xs) ⟨i, rfl⟩
  have hj : xs j ∈ Hset :=
    A.subset_functionClosure (Set.range xs) ⟨j, rfl⟩
  have hEq : g (⟨xs i, hi⟩ : Hset) =
      g (⟨xs j, hj⟩ : Hset) := by
    calc
      g (⟨xs i, hi⟩ : Hset) = f (xs i) := hg _
      _ = f (xs j) := hImages
      _ = g (⟨xs j, hj⟩ : Hset) := by
        have h := hg (⟨xs j, hj⟩ : Hset)
        change g (⟨xs j, hj⟩ : Hset) = f (xs j) at h
        exact h.symm
  exact congrArg Subtype.val (g.injective hEq)

/-- The same genuinely native EHN/2019 homomorphism-embedding,
if it preserves the literal vertex parts, preserves all active OLD
complete-mask domain and value tuples after the faithful
nonempty-valued genuine-partial encoding. Nothing is asserted for
undefined source applications and the map need not be globally
injective or globally full. -/
theorem IsEHNHomomorphismEmbedding.toNonemptyPartial_oldMaskHom
    {A : Structure L U} {B : Structure L V} {f : U → V}
    (hf : A.IsEHNHomomorphismEmbedding B f)
    (partA : U → P) (partB : V → P)
    (hParts : ∀ x : U, partB (f x) = partA x) :
    (A.toNonemptyPartial.wholeMaskPatternGraph partA).IsHomomorphism
      (B.toNonemptyPartial.wholeMaskPatternGraph partB) f := by
  classical
  apply PartialSetStructure.IsOriginalPartialHomomorphism.wholeMaskPatternGraph_hom
    (hf.toOriginalPartial.1.toNonemptyPartial) partA partB hParts
  intro pat mask root hRel
  change Function.Injective root ∧
    ∃ T : Set U,
      A.toNonemptyPartial.func pat.symbol (root ∘ pat.argMap) =
        some T ∧ partA '' T = Set.range mask.label at hRel
  obtain ⟨hRootInj, T, hValue, _⟩ := hRel
  have hDefined : (A.func pat.symbol (root ∘ pat.argMap)).Nonempty := by
    by_contra hNone
    have hNoneValue :
        A.toNonemptyPartial.func pat.symbol (root ∘ pat.argMap) =
          none := by
      change (if (A.func pat.symbol (root ∘ pat.argMap)).Nonempty
        then some (A.func pat.symbol (root ∘ pat.argMap))
        else none) = none
      simp [hNone]
    rw [hNoneValue] at hValue
    cases hValue
  intro i j hij
  obtain ⟨ii, hii⟩ := pat.onto i
  obtain ⟨jj, hjj⟩ := pat.onto j
  have hInputs :
      f ((root ∘ pat.argMap) ii) =
        f ((root ∘ pat.argMap) jj) := by
    simpa only [Function.comp_apply, hii, hjj] using hij
  have hEq := hf.input_eq_of_defined
    pat.symbol (root ∘ pat.argMap) hDefined ii jj hInputs
  have hRootEq : root i = root j := by
    simpa only [Function.comp_apply, hii, hjj] using hEq
  exact hRootInj hRootEq

end StructuralRamsey.Structure
