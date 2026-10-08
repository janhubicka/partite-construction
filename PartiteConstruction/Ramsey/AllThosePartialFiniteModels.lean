import PartiteConstruction.Ramsey.AllThoseFiniteModels
import PartiteConstruction.Functional.SingletonExpansion
import PartiteConstruction.Ramsey.FreeAmalgamationFunctionsAllArity

/-! # Exact 2019 Ramsey theorem for finite models with partial functions

Theorem 2.19 of Hubička--Nešetřil, *All those Ramsey classes*,
concerns structures whose functions are genuinely PARTIAL and
SINGLE-VALUED. Its target Ramsey witness must also have this property.

The earlier all-set-valued all-arity theorem gives a Ramsey witness
in the larger class of set-valued-function structures, but by itself
does not guarantee the witness is singleton-valued.

Here we show the class of singleton-or-empty fibres is hereditary and
closed under full functional free amalgamation. The existing all-arity
class-preserving EHN Ramsey theorem then yields the exact 2019 result
with genuine partial-function output syntax (encoded as at most one
element per fibre). The domain of a partial function is the set of
tuples with a nonempty fibre; a *full embedding* reflects that domain.

This is a class-level theorem. It does not conflate the 2019 partial
homomorphism notion (which does not reflect undefined input domains)
with the stronger 2026 total-set-valued notion.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {U V : Type v}

/-- Class of genuinely partially defined single-valued functions:
every fibre is either empty (undefined) or a singleton (defined). -/
def originalPartialModelClass :
    StructureClass.{u,v} (L := L) :=
  fun {_} C => C.SingletonValued

/-- The defining partial-function condition is hereditary for full
substructure embeddings, which reflect function input domains. -/
theorem singletonValued_of_embedding
    {A : Structure L U} {B : Structure L V}
    (hB : B.SingletonValued) (e : Embedding A B) :
    A.SingletonValued := by
  intro F x y z hy hz
  have hyB : e y ∈ B.func F (e ∘ x) := by
    rw [← e.map_func F x]
    exact ⟨y, hy, rfl⟩
  have hzB : e z ∈ B.func F (e ∘ x) := by
    rw [← e.map_func F x]
    exact ⟨z, hz, rfl⟩
  exact e.injective (hB F (e ∘ x) (e y) (e z) hyB hzB)

/-- Genuine partial single-valued functions remain single-valued under
a full free amalgam, including nullary symbols.

Although functions may have mixed undefined input tuples in the
amalgam, a defined input cannot acquire two outputs: each side
embedding is full on its entire function fibre. -/
theorem singletonValued_of_freeAmalgam
    {H E F C : Type v}
    {D : Structure L H} {A : Structure L E}
    {B : Structure L F} {Cstr : Structure L C}
    {sA : Embedding D A} {sB : Embedding D B}
    {iA : Embedding A Cstr} {iB : Embedding B Cstr}
    (hA : A.SingletonValued) (hB : B.SingletonValued)
    (hFree : IsFreeAmalgam sA sB iA iB) :
    Cstr.SingletonValued := by
  intro G x y z hy hz
  rcases (hFree.func_iff G x y).mp hy with
    ⟨args, out, hval, hx, hyval⟩ |
    ⟨args, out, hval, hx, hyval⟩
  · have hzA : z ∈ Cstr.func G (iA ∘ args) := by
      rw [← hx]
      exact hz
    have hImage : z ∈ imageSet iA (A.func G args) := by
      rw [iA.map_func G args]
      exact hzA
    obtain ⟨out', hout', houtEq⟩ := hImage
    calc
      y = iA out := hyval
      _ = iA out' := congrArg iA (hA G args out out' hval hout')
      _ = z := houtEq
  · have hzB : z ∈ Cstr.func G (iB ∘ args) := by
      rw [← hx]
      exact hz
    have hImage : z ∈ imageSet iB (B.func G args) := by
      rw [iB.map_func G args]
      exact hzB
    obtain ⟨out', hout', houtEq⟩ := hImage
    calc
      y = iB out := hyval
      _ = iB out' := congrArg iB (hB G args out out' hval hout')
      _ = z := houtEq

/-- The partially defined single-valued models form a hereditary
full-functional free-amalgamation class. -/
theorem originalPartialModelClass_free :
    FreeAmalgamationClass (originalPartialModelClass (L := L)) := by
  refine { hereditary := ?_, free := ?_ }
  · intro X Y A B hB e
    exact singletonValued_of_embedding hB e
  · intro H E F C D A B Cstr sA sB iA iB hA hB hFree
    exact singletonValued_of_freeAmalgam hA hB hFree

/-- **Exact Theorem 2.19 of All those Ramsey classes (2019):**
finite linearly ordered models with arbitrary relations and genuine
partial single-valued operations (including constants) form a Ramsey
class for full embeddings.

Unlike the all-set-valued generalization, the witness is explicitly
also a single-valued partial-function structure. -/
theorem allThoseRamseyClasses_theorem_2_19_partialFunctions
    (A : Structure L U) (B : Structure L V)
    [LinearOrder U] [LinearOrder V] [Finite U] [Finite V]
    (hA : A.SingletonValued) (hB : B.SingletonValued)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W)
      (C : Structure L W),
      C.SingletonValued ∧
      Arrow A.withLinearOrder B.withLinearOrder
        (@Structure.withLinearOrder L W C o.toLT) κ := by
  obtain ⟨W, hW, oW, C, hC, hRamsey⟩ :=
    StructuralRamsey.Rooted.Structure.FreeAmalgamationClass.orderedRamsey_allArity
      (originalPartialModelClass_free (L := L))
      A B hA hB κ
  exact ⟨W, hW, oW, C, hC, hRamsey⟩

end StructuralRamsey.Structure
