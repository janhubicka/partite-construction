import PartiteConstruction.Functional.TrackBNativePowerOutputMasks2019
import PartiteConstruction.Functional.NativeTaggedWeakPreimage
import PartiteConstruction.Functional.OutputPartSplitFreeAmalgam

/-!
# Track B: native Hales--Jewett line maps preserve ambient U-root tests

No new source picture is created. The concrete native coordinate power and
its full native Hales--Jewett line embeddings are taken from Induced.lean.
Split each transversal multi-output fibre by OUTPUT PART, and tag the
complete input-root patterns on the same vertex sets.

A genuine full line embedding gives a full relational embedding from
the ambient tagged data induced on its exact weak inverse-image set
into the tagged data of the genuine native power, for EVERY test set.
This does not turn a nonclosed weak inclusion into a full functional
embedding, nor claim that canonical tagging commutes with arbitrary
relational coordinate powers.
-/

namespace StructuralRamsey.FunctionalPartite.Induced

open StructuralRamsey.Structure
open StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {P : Type v} {V : Type w}

/-- The complete active output-part mask of the genuine power is
exactly the active output-part mask in the common control A, provided
the native partite source B has its genuine full projection to A and
the Hales--Jewett coordinate count is POSITIVE.

This bridges the source output-part masks at the ACTUAL power step.
In particular the old full function-domain bit is not identified with
a merely coordinatewise conjunction of unqualified domain bits. -/
theorem power_active_outputPart_iff_control
    (A : Structure L P) (B : System L P V)
    (hB : B.ProjectionHom A)
    (N : ℕ) (hN : 0 < N)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → Vertex B N)
    (p : P) :
    (∃ y : Vertex B N, y ∈ (power B N).func F xs ∧ y.part = p) ↔
      p ∈ A.func F ((power B N).part ∘ xs) := by
  have hImage := (power_projectionHom hB hN).2 F xs
  constructor
  · rintro ⟨y, hy, hp⟩
    rw [← hImage]
    exact ⟨y, hy, hp⟩
  · intro hp
    rw [← hImage] at hp
    exact hp

/-- With positive power length, existence of any genuine power output
is equivalent to existence of a value at the COMMON control tuple.
The output part is witnessed globally, not chosen independently in
each coordinate. -/
theorem power_nonempty_iff_control
    (A : Structure L P) (B : System L P V)
    (hB : B.ProjectionHom A)
    (N : ℕ) (hN : 0 < N)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → Vertex B N) :
    ((power B N).func F xs).Nonempty ↔
      (A.func F ((power B N).part ∘ xs)).Nonempty := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y.part, (power_active_outputPart_iff_control A B hB N hN
      F xs y.part).mp ⟨y, hy, rfl⟩⟩
  · rintro ⟨p, hp⟩
    obtain ⟨y, hy, _⟩ :=
      (power_active_outputPart_iff_control A B hB N hN F xs p).mpr hp
    exact ⟨y, hy⟩

/-- A FULL genuine Hales--Jewett line embedding into the real native
power restricts to a FULL canonical TAGGED 2019 relational embedding on
EVERY exact preimage weak test, including arbitrary nonclosed tests.

All old input-domain root masks, relations, output tuples and new
complete-root U-closure tags are transported using the same underlying
lineMap vertex function; no weak carrier is replaced by its hull. -/
theorem lineEmbedding_taggedWeakPreimage
    (A : Structure L P) (B : System L P V)
    (hB : B.ProjectionHom A)
    {N : ℕ} (W : Line (Letter A B) N)
    (Test : Set (Vertex B N)) :
    let e := (lineEmbedding hB W).splitOutputParts.toEmbedding
    Nonempty (RelStructure.Embedding
      ((patternTagExpansion
        (B.splitOutputParts).toStructure.patternGraph).induce
          (e.toFun ⁻¹' Test))
      ((patternTagExpansion
        ((power B N).splitOutputParts).toStructure.patternGraph).induce
          Test)) := by
  exact ⟨((lineEmbedding hB W).splitOutputParts.toEmbedding)
    .taggedPatternWeakPreimage Test⟩

end StructuralRamsey.FunctionalPartite.Induced
