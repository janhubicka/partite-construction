import PartiteConstruction.Functional.WholeMaskCanonicalPartialRoundTrip2019
import PartiteConstruction.Functional.WholeMaskFullEmbeddingFromCovered2019
import PartiteConstruction.Functional.WholeMaskOldEmbeddingTransport2019

/-!
# Canonical complete-mask graphs fully remember genuine partial structures

The verified pointwise source round trip now gives literal equality of
genuine partial Option(Set) structures, not just separate equivalences
of their operation relations. This makes it possible to turn ANY full
OLD complete-mask relational embedding of two canonical transversal
partial-function sources into a FULL genuine partial-function embedding.

The source functions may be defined with empty values; the OLD graph
also reflects undefined inputs via its separate domain relation.
All maps retain their original vertices and require no closure hull.

The part maps are used to construct the graph presentations and to
ensure their output values are transversal. A full OLD embedding need
not preserve part labels on otherwise isolated vertices, so no
unwarranted part-preservation conclusion is asserted here.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey.RelStructure

universe u v w z
variable {L : Language.{u}} {P : Type z} [Fintype P]
variable {V : Type v} {W : Type w}

/-- Equality of genuine partial structures is determined pointwise
by their ordinary relations and entire Option(Set) fibres. -/
private theorem eq_of_rel_func_eq
    (A B : PartialSetStructure L V)
    (hRel : ∀ R xs, A.rel R xs = B.rel R xs)
    (hFunc : ∀ F xs, A.func F xs = B.func F xs) : A = B := by
  cases A with
  | mk ar af =>
    cases B with
    | mk br bf =>
      have hr : ar = br := by
        funext R xs
        exact hRel R xs
      have hf : af = bf := by
        funext F xs
        exact hFunc F xs
      cases hr
      cases hf
      rfl

/-- Canonical genuine partial-function decoding is literally the
IDENTITY on the source structure, including both the undefined none
and the defined-empty some(empty) states. -/
theorem wholeMaskPartialDecode_canonical_eq
    (A : PartialSetStructure L V) [Finite V]
    (part : V → P) (hTrans : FibreTransversal A part) :
    (A.wholeMaskPatternGraph part).wholeMaskPartialDecode = A := by
  apply eq_of_rel_func_eq
    ((A.wholeMaskPatternGraph part).wholeMaskPartialDecode) A
  · intro R xs
    exact A.wholeMaskPartialDecode_canonical_rel part R xs
  · intro F xs
    exact A.wholeMaskPartialDecode_canonical_func part hTrans F xs

namespace Embedding

/-- Full OLD complete-mask relational embeddings of canonical
transversal genuine partial-function sources reflect ALL original
relations, ENTIRE output values and the domain bit. This is the
inverse of the full-mask forward encoding on its underlying map.

The target's part map is not automatically preserved by the old
graph embedding for vertices that never occur as outputs. -/
noncomputable def ofCanonicalWholeMaskPatternGraph
    (A : PartialSetStructure L V) [Finite V]
    (B : PartialSetStructure L W) [Finite W]
    (partA : V → P) (partB : W → P)
    (hTransA : FibreTransversal A partA)
    (hTransB : FibreTransversal B partB)
    (e : RelStructure.Embedding
      (A.wholeMaskPatternGraph partA)
      (B.wholeMaskPatternGraph partB)) :
    Embedding A B := by
  classical
  let E := B.wholeMaskPatternGraph partB
  have hEq : E.wholeMaskPartialDecode = B :=
    B.wholeMaskPartialDecode_canonical_eq partB hTransB
  have hUnique (F : L.FuncSymbol)
      (xs : Fin (L.funcArity F) → W) (U T : Set W)
      (hU : HasWholeMaskValue E F xs U)
      (hT : HasWholeMaskValue E F xs T) : U = T := by
    have hu : B.func F xs = some U :=
      (B.hasWholeMaskValue_iff_source_func_some partB hTransB F xs U).mp hU
    have ht : B.func F xs = some T :=
      (B.hasWholeMaskValue_iff_source_func_some partB hTransB F xs T).mp hT
    exact Option.some.inj (hu.symm.trans ht)
  have hDomain (F : L.FuncSymbol)
      (xs : Fin (L.funcArity F) → W) :
      E.wholeMaskPartialDecode.Defined F xs ↔
        HasWholeMaskDomain E F xs := by
    have hSource : HasWholeMaskDomain E F xs ↔ B.Defined F xs :=
      B.hasWholeMaskDomain_iff_sourceDefined partB hTransB F xs
    have hDecoded : E.wholeMaskPartialDecode.Defined F xs ↔
        B.Defined F xs := by
      rw [hEq]
    exact hDecoded.trans hSource.symm
  let eDecoded : Embedding A E.wholeMaskPartialDecode :=
    Embedding.ofWholeMaskPatternGraph A partA hTransA E
      hUnique hDomain e
  simpa only [hEq] using eDecoded

end Embedding

end StructuralRamsey.PartialSetStructure
