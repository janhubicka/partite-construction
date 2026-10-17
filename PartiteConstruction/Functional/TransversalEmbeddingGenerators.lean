import PartiteConstruction.Functional.TransversalEmbeddingEqualizer
import PartiteConstruction.Structure.GeneratedWeakHomImage

/-!
# Function generators determine full transversal partite embeddings

For set-valued operations, two embeddings need not agree on all
function outputs merely because their images agree on the argument
tuple. In a genuine functional partite system this *does* follow
from per-fibre output transversality: the exact agreement equalizer
is function-closed (already verified).

Consequently, if two FULL partite embeddings agree on a vertex set G
whose function closure is the entire source, the embeddings coincide
globally, including genuinely multivalued output fibres.

This is a reusable rigidity principle for Hales--Jewett constant
letters: a small set of generating A-parts, rather than necessarily
every A-part, can determine the whole letter. No rank or closure
inflation of a weak test is asserted.
-/

namespace StructuralRamsey.FunctionalPartite

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {P V W : Type v}

/-- Agreement on a function-generating set forces equality of full
partite embeddings, because output-fibre transversality closes the
exact agreement equalizer. -/
theorem Embedding.eq_of_agree_on_generators
    {A : System L P V} {B : System L P W}
    (f g : Embedding A B) (G : Set V)
    (hGen : A.toStructure.functionClosure G = Set.univ)
    (hAgree : ∀ x, x ∈ G → f x = g x) :
    f = g := by
  have hClosed :
      A.toStructure.IsClosed {x : V | f x = g x} :=
    f.agreement_isClosed g
  have hSub : G ⊆ {x : V | f x = g x} :=
    fun x hx => hAgree x hx
  apply Embedding.ext
  intro x
  have hx : x ∈ A.toStructure.functionClosure G := by
    rw [hGen]
    exact Set.mem_univ x
  exact hx _ hClosed hSub

end StructuralRamsey.FunctionalPartite
