import PartiteConstruction.Functional.WholeMaskCanonicalPartialRoundTrip2019
import PartiteConstruction.Functional.WholeMaskPartialDecode2019
import PartiteConstruction.Functional.WholeMaskRelativeClosure2019

/-!
# FULL old complete-mask embeddings transport genuine partial domains

An old complete-mask relational embedding carries every active
domain mask and every COMPLETE output-value tuple. Unlike a weak
projection, a full embedding also REFLECTS active domain records
whose entire distinct input root lies in the embedded source.

For the reflection: any target equality-pattern root of the image
of a primitive input tuple has no mysterious extra vertices.
Surjectivity of the primitive-argument map implies each root vertex
is one of the embedded arguments; the root therefore factors back
through the source embedding, including repeated primitive inputs
and nullary roots. Full relation reflection then applies.

These exact root and whole-value transport lemmas are reusable for
interpreting closed B-copies in a final covered tagged target as
genuine full partial-function embeddings. No weak test is replaced
by a closure hull, and undefined source inputs are not confused
with defined-empty ones.
-/

namespace StructuralRamsey.RelStructure.Embedding

universe u v w z
variable {L : Language.{u}} {P : Type z} [Fintype P]
variable {V : Type v} {W : Type w}
variable {E : RelStructure (L.wholeMaskPatternLanguage P) V}
variable {D : RelStructure (L.wholeMaskPatternLanguage P) W}

/-- A complete OLD function-value witness maps to another COMPLETE
value witness, with its ENTIRE output set replaced by its exact image
under the embedding. Includes empty outputs and nullary inputs. -/
theorem map_hasWholeMaskValue
    (f : Embedding E D)
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → V)
    (U : Set V)
    (h : HasWholeMaskValue E F x U) :
    HasWholeMaskValue D F (f ∘ x) (StructuralRamsey.Structure.imageSet f U) := by
  classical
  obtain ⟨m,r,hr,q,t,hRel,hArgs,hU⟩ := h
  let p : Language.FunctionInputPattern L := ⟨F,m,r,hr⟩
  have hTarget : D.rel (.inr (.inr (p,q))) (f ∘ t) :=
    (f.map_rel_iff (.inr (.inr (p,q))) t).mpr hRel
  refine ⟨m,r,hr,q,f ∘ t,hTarget,?_,?_⟩
  · intro i
    exact congrArg f (hArgs i)
  · change StructuralRamsey.Structure.imageSet f U =
      Set.range (fun j : Fin q.size => f (t (Fin.natAdd m j)))
    rw [hU]
    ext y
    constructor
    · rintro ⟨x, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨t (Fin.natAdd m j), ⟨j, rfl⟩, rfl⟩

/-- A full OLD relational embedding preserves and REFLECTS
activation of partial function domains for a fixed literal
primitive argument tuple. Reflection requires no root closure,
because the surjective argument pattern places every root vertex
inside the embedded original arguments. -/
theorem hasWholeMaskDomain_map_iff
    (f : Embedding E D)
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → V) :
    HasWholeMaskDomain E F x ↔
      HasWholeMaskDomain D F (f ∘ x) := by
  classical
  constructor
  · rintro ⟨m,r,hr,q,root,hDom,hArgs⟩
    let p : Language.FunctionInputPattern L := ⟨F,m,r,hr⟩
    have hMapped : D.rel (.inr (.inl (p,q))) (f ∘ root) :=
      (f.map_rel_iff (.inr (.inl (p,q))) root).mpr hDom
    refine ⟨m,r,hr,q,f ∘ root,hMapped,?_⟩
    intro i
    exact congrArg f (hArgs i)
  · rintro ⟨m,r,hr,q,root,hDom,hArgs⟩
    let p : Language.FunctionInputPattern L := ⟨F,m,r,hr⟩
    let rootSource : Fin m → V :=
      fun i => x (Classical.choose (hr i))
    have hRootMap : f ∘ rootSource = root := by
      funext i
      change f (x (Classical.choose (hr i))) = root i
      calc
        f (x (Classical.choose (hr i))) =
            (f ∘ x) (Classical.choose (hr i)) := rfl
        _ = root (r (Classical.choose (hr i))) :=
          hArgs (Classical.choose (hr i))
        _ = root i :=
          congrArg root (Classical.choose_spec (hr i))
    have hSourceDomain : E.rel (.inr (.inl (p,q))) rootSource := by
      apply (f.map_rel_iff (.inr (.inl (p,q))) rootSource).mp
      change D.rel (.inr (.inl (p,q))) (f ∘ rootSource)
      rw [hRootMap]
      exact hDom
    have hSourceArgs : ∀ i : Fin (L.funcArity F),
        x i = rootSource (r i) := by
      intro i
      apply f.injective
      calc
        f (x i) = (f ∘ x) i := rfl
        _ = root (r i) := hArgs i
        _ = (f ∘ rootSource) (r i) :=
          (congrFun hRootMap (r i)).symm
        _ = f (rootSource (r i)) := rfl
    exact ⟨m,r,hr,q,rootSource,hSourceDomain,hSourceArgs⟩

end StructuralRamsey.RelStructure.Embedding

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type v} [Fintype P]
variable {V : Type w}

/-- Active OLD complete-mask domain records in a CANONICAL source
are exactly the original primitive Option(Set) operation's domain.
Defined-empty values contribute true OLD domain tuples, and nullary
inputs require no special convention here. -/
theorem hasWholeMaskDomain_iff_sourceDefined
    (A : PartialSetStructure L V) [Finite V]
    (part : V → P) (hTrans : FibreTransversal A part)
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → V) :
    HasWholeMaskDomain (A.wholeMaskPatternGraph part) F x ↔
      A.Defined F x := by
  classical
  constructor
  · rintro ⟨m,r,hr,q,root,hDomain,hArgs⟩
    change Function.Injective root ∧
      ∃ U : Set V, A.func F (root ∘ r) = some U ∧
        part '' U = Set.range q.label at hDomain
    obtain ⟨_,U,hValue,_⟩ := hDomain
    have hEq : root ∘ r = x := by
      funext i
      exact (hArgs i).symm
    rw [hEq] at hValue
    exact ⟨U,hValue⟩
  · rintro ⟨U,hValue⟩
    have hGraph : HasWholeMaskValue
        (A.wholeMaskPatternGraph part) F x U :=
      (A.hasWholeMaskValue_iff_source_func_some
        part hTrans F x U).mpr hValue
    exact (A.wholeMaskPatternGraph_validDomains part).domain_of_value
      (A.wholeMaskPatternGraph part) F x U hGraph

end StructuralRamsey.PartialSetStructure
