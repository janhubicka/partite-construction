import PartiteConstruction.Functional.WeakTransversalTests
import PartiteConstruction.Functional.WeakInduced

/-!
# Agreement roots of full partite embeddings are FUNCTION-CLOSED

For genuinely set-valued functions, agreement of two ordinary full
functional embeddings need NOT be closed if a target function can have
different outputs of the same part.

A TRUE functional partite system excludes exactly this pathology:
individual output fibres are TRANSVERSAL under the part map.
Consequently, if two full PARTITE embeddings f,g:A↪B agree on the
arguments of a function application, they must also agree on EVERY
output, since each mapped output belongs to the same target function
fibre AND occupies the same part.

Therefore the exact agreement set
  {x ∈ A | f(x)=g(x)}
is function-closed in the ORIGINAL A, even for genuinely multivalued
operations of arbitrary arity. The proof does not require global
injectivity of the part map, or any singleton-valuedness hypothesis.

Applied to two native Hales–Jewett LINE embeddings of the selected
support into its genuine coordinate power, their pointwise agreement
set is closed. The overlap of their full ranges is also closed,
because both line ranges are genuine full embedded substructures.

This is a useful geometric restriction on possible mixed roots of
the line-indexed functional Picture. It does NOT, on its own, assert
that a collection of several line copies forms a strict B-tree or
that arbitrary mixed weak-test completions are compatible.
-/

namespace StructuralRamsey.FunctionalPartite

open Structure
open StructuralRamsey.HalesJewett

universe u v
variable {L : Language.{u}} {P : Type v} {V W : Type v}

/-- The exact pointwise EQUALIZER of two full PARTITE embeddings
between genuine set-valued-function systems is function-closed.

The only nontrivial step uses the target's OUTPUT TRANSVERSALITY
to force equality of two function values in the same part.
Ordinary functional embeddings alone do not suffice. -/
theorem Embedding.agreement_isClosed
    {A : System L P V} {B : System L P W}
    (f g : Embedding A B) :
    A.toStructure.IsClosed {x : V | f x = g x} := by
  intro F x hArgs y hy
  have heF : f y ∈ B.func F (f ∘ x) := by
    rw [← f.toEmbedding.map_func F x]
    exact ⟨y, hy, rfl⟩
  have heG : g y ∈ B.func F (g ∘ x) := by
    rw [← g.toEmbedding.map_func F x]
    exact ⟨y, hy, rfl⟩
  have hTuple : (f ∘ x) = (g ∘ x) := by
    funext i
    exact hArgs i
  rw [← hTuple] at heG
  have hPart : B.part (f y) = B.part (g y) :=
    (f.map_part y).trans (g.map_part y).symm
  exact B.funcTransversal F (f ∘ x) (f y) (g y)
    heF heG hPart

end StructuralRamsey.FunctionalPartite

namespace StructuralRamsey.FunctionalPartite.Induced

open StructuralRamsey.Structure
open StructuralRamsey.HalesJewett

universe u v
variable {L : Language.{u}} {P V : Type v}
variable {A : Structure L P} {B : System L P V} {N : ℕ}

/-- Exact pointwise agreement of two actual FULL Hales–Jewett LINE
embeddings is a FUNCTION-CLOSED root in the old selected support,
including for all genuinely multivalued operation fibres.

The closing argument is exactly the per-fibre transversal-image
axiom of the Hales–Jewett coordinate power. -/
theorem line_agreement_isClosed
    (hB : B.toStructure.IsWeakHomomorphism A B.part)
    (W₁ W₂ : Line (Letter A B) N) :
    B.toStructure.IsClosed
      {x : V | lineMap W₁ x = lineMap W₂ x} :=
  (weak_lineEmbedding hB W₁).agreement_isClosed
    (weak_lineEmbedding hB W₂)

/-- Intersections of two actual FULL line ranges are function-closed
inside the Hales–Jewett coordinate power. This holds even when the
pairwise intersection is reducible or nontransversal as a vertex set;
its full function fibres are nonetheless well-defined. -/
theorem line_range_inter_isClosed
    (hB : B.toStructure.IsWeakHomomorphism A B.part)
    (W₁ W₂ : Line (Letter A B) N) :
    (power B N).toStructure.IsClosed
      (Set.range (lineMap W₁) ∩ Set.range (lineMap W₂)) := by
  have hL :
      (power B N).toStructure.IsClosed (Set.range (lineMap W₁)) :=
    (weak_lineEmbedding hB W₁).toEmbedding.range_isClosed
  have hR :
      (power B N).toStructure.IsClosed (Set.range (lineMap W₂)) :=
    (weak_lineEmbedding hB W₂).toEmbedding.range_isClosed
  intro F x hx y hy
  exact ⟨hL F x (fun i => (hx i).1) hy,
    hR F x (fun i => (hx i).2) hy⟩

end StructuralRamsey.FunctionalPartite.Induced
