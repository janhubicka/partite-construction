import PartiteConstruction.Ramsey.ForbiddenFunctionsAllArity

/-! # All those Ramsey classes: the finite-model theorem

Theorem 2.19 of Hubička--Nešetřil, *All those Ramsey classes*
(Advances in Mathematics 356, 2019), says that finite linearly ordered
models in an arbitrary relation/function language form a Ramsey class.

Here the named order is represented by `Structure.withLinearOrder`;
all embeddings preserve it and **all** original function fibres.
The result includes arbitrary set-valued functions, including constants.
It follows immediately from the fully checked fixed-root, all-arity
functional EHN Ramsey theorem for the unrestricted hereditary
free-amalgamation class.

Theorem 2.18 has a different logical scope: an (R,U)-multiamalgamation
class is not necessarily closed under *free* amalgamation. It must not
be inferred from this unrestricted result or from the free-amalgamation
corollaries alone.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V : Type v}

/-- All those Ramsey classes, Theorem 2.19 (Ramsey theorem for finite
models): every finite pair of ordered models in an arbitrary language of
relations and set-valued functions has a finite ordered Ramsey witness.

No function-arity restriction and no local-tree or full-projection
assumption are involved. All embeddings in this arrow are genuine full
function-language embeddings. -/
theorem allThoseRamseyClasses_theorem_2_19
    (A : Structure L U) (B : Structure L V)
    [LinearOrder U] [LinearOrder V] [Finite U] [Finite V]
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W)
      (C : Structure L W),
      Arrow A.withLinearOrder B.withLinearOrder
        (@Structure.withLinearOrder L W C o.toLT) κ := by
  let K : StructureClass.{u,v} (L := L) := allStructures
  have hK : FreeAmalgamationClass K := allStructures_free
  obtain ⟨W, hW, oW, C, _hKC, hArrow⟩ :=
    StructuralRamsey.Rooted.Structure.FreeAmalgamationClass.orderedRamsey_allArity
      hK A B (by trivial) (by trivial) κ
  exact ⟨W, hW, oW, C, hArrow⟩

end StructuralRamsey.Structure
