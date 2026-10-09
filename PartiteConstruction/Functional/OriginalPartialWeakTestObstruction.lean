import PartiteConstruction.Functional.OriginalPartialWeakRank
import PartiteConstruction.Functional.NativePowerOrderedTarget

/-! # A weak source test need not have a strict partial tree completion

The original 2019 partial-function semantics allow undefined source
inputs to map to defined target inputs. But a homomorphism-EMBEDDING
must still be a full embedding on every irreducible source
substructure. Weakly restricting a closed functional copy can produce
an irreducible piece with a missing function output.

The ordered three-vertex base contains input vertices 0<1 and one
binary function value F(0,1)={2}. On the weak subset {0,1}, the
order edge survives but the function output disappears. This
two-vertex weak test is irreducible and cannot fully embed into
any strict full-functional tree of the base copies.

This rules out the tempting all-weak-tests predecessor hypothesis
even at rank two, *already when the predecessor is a single B-copy*.
It does not affect the verified closed-source weak-image transfer,
whose source really is function-closed.
-/

namespace StructuralRamsey.Structure.NativePowerObstruction

open StructuralRamsey
open StructuralRamsey.Structure

def weakOrderedXYSet : Set (Fin 3) := {x | x = 0 ∨ x = 1}

def weakOrderedXY : Structure toyLanguage.withLinearOrder weakOrderedXYSet :=
  toyBaseOrdered.weakInduce weakOrderedXYSet

def weakX : weakOrderedXYSet := ⟨0, Or.inl rfl⟩
def weakY : weakOrderedXYSet := ⟨1, Or.inr rfl⟩

theorem weakOrderedXY_graph_irreducible :
    weakOrderedXY.graph.Irreducible := by
  intro x y hxy
  obtain ⟨R,z,i,j,hz,hxi,hyj⟩ :=
    (toyBaseOrdered_graph_hereditarilyIrreducible weakOrderedXYSet) x y hxy
  refine ⟨R,z,i,j,?_,hxi,hyj⟩
  exact (weakInduce_graph_rel_iff toyBaseOrdered weakOrderedXYSet R z).mpr hz

theorem weakOrderedXY_irreducible : weakOrderedXY.Irreducible :=
  irreducible_of_graph_irreducible weakOrderedXY
    weakOrderedXY_graph_irreducible

theorem weakOrderedXY_missingOutput :
    ¬ InOriginalPartialDomain weakOrderedXY () ![weakX,weakY] := by
  rintro ⟨z,hz⟩
  have hz2 : z.1 = (2 : Fin 3) := by
    change (0 : Fin 3) = 0 ∧ (1 : Fin 3) = 1 ∧ z.1 = 2 at hz
    exact hz.2.2
  rcases z.2 with h0 | h1
  · have hbad : (2 : Fin 3) = 0 := hz2.symm.trans h0
    exact (by decide : (2 : Fin 3) ≠ 0) hbad
  · have hbad : (2 : Fin 3) = 1 := hz2.symm.trans h1
    exact (by decide : (2 : Fin 3) ≠ 1) hbad

/-- Any full embedding of the weak ordered pair into B preserves the
unary roles 0 and 1 and must therefore send its input pair to (0,1).
That target pair has an output, contradicting domain reflection. -/
theorem weakOrderedXY_no_fullEmbedding
    (e : Embedding weakOrderedXY toyBaseOrdered) : False := by
  have hxRole : weakOrderedXY.rel (.inl (0 : Fin 3))
      (fun _ : Fin 1 => weakX) := by
    change (0 : Fin 3) = 0
    rfl
  have hyRole : weakOrderedXY.rel (.inl (1 : Fin 3))
      (fun _ : Fin 1 => weakY) := by
    change (1 : Fin 3) = 1
    rfl
  have heX : e weakX = (0 : Fin 3) := by
    have h := (e.map_rel_iff (.inl (0 : Fin 3))
      (fun _ : Fin 1 => weakX)).mpr hxRole
    change e weakX = (0 : Fin 3) at h
    exact h
  have heY : e weakY = (1 : Fin 3) := by
    have h := (e.map_rel_iff (.inl (1 : Fin 3))
      (fun _ : Fin 1 => weakY)).mpr hyRole
    change e weakY = (1 : Fin 3) at h
    exact h
  have hDefined :
      InOriginalPartialDomain toyBaseOrdered ()
        (e ∘ ![weakX,weakY]) := by
    refine ⟨(2 : Fin 3), ?_⟩
    change e weakX = 0 ∧ e weakY = 1 ∧ (2 : Fin 3) = 2
    exact ⟨heX,heY,rfl⟩
  have hSourceDefined :=
    (e.originalPartialDomain_iff () ![weakX,weakY]).mp hDefined
  exact weakOrderedXY_missingOutput hSourceDefined

/-- The irreducible weak pair has no 2019 partial-homomorphism
strict-tree completion: a partial HE would restrict to a full
embedding of this whole irreducible source into a strict tree,
and irreducible localization forces it into one B-copy. -/
theorem weakOrderedXY_no_originalPartialTreeCompletion :
    ¬ HasOriginalPartialTreeCompletion toyBaseOrdered weakOrderedXY := by
  rintro ⟨W,T,hTree,f,hf⟩
  obtain ⟨g,hg⟩ :=
    hf.2 weakOrderedXY weakOrderedXY_irreducible
      (Embedding.id weakOrderedXY)
  obtain ⟨j,hj⟩ :=
    hTree.irreducible_contained_in_copy
      weakOrderedXY_irreducible g
  let e : Embedding weakOrderedXY toyBaseOrdered :=
    g.factorThroughRange j hj
  exact weakOrderedXY_no_fullEmbedding e

end StructuralRamsey.Structure.NativePowerObstruction
