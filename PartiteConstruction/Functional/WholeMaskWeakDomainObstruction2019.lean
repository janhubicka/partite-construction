import PartiteConstruction.Functional.WholeMaskOldEmbeddingTransport2019
import PartiteConstruction.Structure.PartialSetFunctionsWholeWeak

/-!
# Persistent ambient mask domains obstruct FULL weak functional embeddings

For a genuine partial Option(Set) source A and an exact vertex subset S,
suppose F(xs) is defined in A with an entire output U not contained in S.
Then the *whole-fibre weak restriction* on S deletes F(xs) and makes it
undefined.  But the induced ambient complete-mask OLD relation retains
the active domain predicate on the original input vertices in S.

Consequently ANY positive OLD homomorphism of that induced ambient
graph into a canonical genuine partial target forces F(f xs) to be
DEFINED in the target.  Therefore that SAME vertex map cannot underlie
a full genuine functional embedding of the weak restriction into the
target: a full embedding must reflect undefined source applications.

This obstruction has no assumption about K-membership or mixed
B-trees. It shows why the existing 2019 relational exact weak
K-completion map cannot be upgraded BLANKETLY to a full functional
homomorphism-embedding simply by making its K-target canonical.
It does not obstruct the already proved SOURCE-DEFINED partial
homomorphism on surviving complete output fibres.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V W : Type v}

/-- Any OLD positive map from an EXACT induced ambient mask source
preserves source active domain predicates, even when the entire
original function value has been deleted from the weak subset.
This theorem works for all arities, repetitions and some-empty. -/
theorem oldInducedHom_target_defined_of_ambient_defined
    (A : PartialSetStructure L V) [Finite V]
    (partA : V → P) (hTransA : FibreTransversal A partA)
    (S : Set V)
    (Target : PartialSetStructure L W) [Finite W]
    (partTarget : W → P)
    (hTransTarget : FibreTransversal Target partTarget)
    (f : S → W)
    (hOld : ((A.wholeMaskPatternGraph partA).induce S).IsHomomorphism
      (Target.wholeMaskPatternGraph partTarget) f)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → S)
    (hDefined : A.Defined F (Subtype.val ∘ xs)) :
    Target.Defined F (f ∘ xs) := by
  classical
  have hDom : HasWholeMaskDomain (A.wholeMaskPatternGraph partA)
      F (Subtype.val ∘ xs) :=
    (A.hasWholeMaskDomain_iff_sourceDefined partA hTransA
      F (Subtype.val ∘ xs)).mpr hDefined
  obtain ⟨m, r, hr, q, root, hRel, hArgs⟩ := hDom
  let pat : Language.FunctionInputPattern L := ⟨F, m, r, hr⟩
  have hRootS (i : Fin m) : root i ∈ S := by
    obtain ⟨j, hj⟩ := hr i
    have hxs : (Subtype.val ∘ xs) j ∈ S := (xs j).2
    rw [hArgs j] at hxs
    simpa only [hj] using hxs
  let rootS : Fin m → S := fun i => ⟨root i, hRootS i⟩
  have hRelS : ((A.wholeMaskPatternGraph partA).induce S).rel
      (.inr (.inl (pat,q))) rootS := hRel
  have hTargetRel : (Target.wholeMaskPatternGraph partTarget).rel
      (.inr (.inl (pat,q))) (f ∘ rootS) :=
    hOld (.inr (.inl (pat,q))) rootS hRelS
  have hTargetDom : HasWholeMaskDomain
      (Target.wholeMaskPatternGraph partTarget) F (f ∘ xs) := by
    refine ⟨m, r, hr, q, f ∘ rootS, hTargetRel, ?_⟩
    intro j
    apply congrArg f
    apply Subtype.ext
    exact hArgs j
  exact (Target.hasWholeMaskDomain_iff_sourceDefined
    partTarget hTransTarget F (f ∘ xs)).mp hTargetDom

/-- Losing even ONE output of a defined whole-valued application
forces failure of EVERY full genuine functional embedding using the
vertex map of an induced ambient OLD completion map.
The obstruction is domain reflection, not output transversality. -/
theorem oldInducedHom_not_fullWholeWeakEmbedding_of_lost_output
    (A : PartialSetStructure L V) [Finite V]
    (partA : V → P) (hTransA : FibreTransversal A partA)
    (S : Set V)
    (Target : PartialSetStructure L W) [Finite W]
    (partTarget : W → P)
    (hTransTarget : FibreTransversal Target partTarget)
    (f : S → W)
    (hOld : ((A.wholeMaskPatternGraph partA).induce S).IsHomomorphism
      (Target.wholeMaskPatternGraph partTarget) f)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → S)
    (U : Set V)
    (hValue : A.func F (Subtype.val ∘ xs) = some U)
    (hLost : ¬ U ⊆ S) :
    ¬ ∃ e : Embedding (wholeWeakInduce A S) Target,
        ∀ x : S, e.toFun x = f x := by
  intro ⟨e, he⟩
  have hTargetDefined : Target.Defined F (f ∘ xs) :=
    oldInducedHom_target_defined_of_ambient_defined
      A partA hTransA S Target partTarget hTransTarget
      f hOld F xs ⟨U, hValue⟩
  have hWeakNone : (wholeWeakInduce A S).func F xs = none := by
    change wholeWeakValue S (A.func F (Subtype.val ∘ xs)) = none
    rw [hValue]
    exact wholeWeakValue_of_not_subset S U hLost
  have hTargetNone : Target.func F (e.toFun ∘ xs) = none := by
    have hMap := e.map_func F xs
    rw [hWeakNone] at hMap
    simpa only [Option.map_none] using hMap.symm
  have hMapEq : (e.toFun ∘ xs) = f ∘ xs := by
    funext i
    exact he (xs i)
  rw [hMapEq] at hTargetNone
  obtain ⟨T,hT⟩ := hTargetDefined
  rw [hT] at hTargetNone
  cases hTargetNone

end StructuralRamsey.PartialSetStructure
