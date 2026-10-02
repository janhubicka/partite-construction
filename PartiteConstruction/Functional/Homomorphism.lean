import PartiteConstruction.Functional.Basic
import PartiteConstruction.Structure.FreeAmalgam

/-! # Functional partite homomorphism-embedding invariant -/
namespace StructuralRamsey.FunctionalPartite

open Structure

universe u v w
variable {L : Language.{u}} {P : Type v} {V : Type w}

/-- The full survey notion of an A-partite system: the partition projection is
a homomorphism-embedding for both relations and set-valued functions. -/
def System.IsPartiteOver (B : System L P V) (A : Structure L P) : Prop :=
  B.toStructure.IsHomomorphismEmbedding A B.part

theorem System.projectionHom
    {B : System L P V} {A : Structure L P}
    (hB : B.IsPartiteOver A) :
    B.ProjectionHom A :=
  hB.1

end StructuralRamsey.FunctionalPartite
