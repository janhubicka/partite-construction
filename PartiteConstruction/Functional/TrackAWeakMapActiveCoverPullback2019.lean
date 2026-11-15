import PartiteConstruction.Functional.TrackANativeActiveWeakOutputPartCover2019

/-!
# Track A — active output-part cover pulls back along POSITIVE weak maps

The existing Track A source correspondence says that a native functional
partite weak support S carries an original source-defined partial part
projection exactly when S satisfies ActiveWeakOutputPartCover.

The old stability theorem proved pullback under FULL part-preserving
embeddings. Its complete-fibre reflection assumption is unnecessary.

Indeed suppose f:B→C preserves parts and every positive function output
incidence: y∈F_B(x) implies f(y)∈F_C(f(x)). Let T be any EXACT weak
support of C satisfying active output-part cover. If a source function
fibre over arguments in f⁻¹(T) meets f⁻¹(T), then its image yields a
genuinely active target fibre over arguments in T. Any source output
whose part label is occupied in f⁻¹(T) maps to a target output whose
part is occupied in T. Target active-cover brings this particular
target output back into T, so the source output belongs to f⁻¹(T).

This proof needs neither injectivity, relation reflection, source
undefinedness reflection, nor equality of complete output fibres.
It holds for arbitrarily multivalued and nullary operations.

Consequently the same property pulls back along the REAL native
EHN/WeaklyPartiteOver-compatible maps whenever they preserve parts.
It is NOT asserted for part-preserving maps that fail even positive
function-incidence preservation.

Only a source-side weak carrier invariant is proved; no target-side
strict full-functional B-tree completion or ambient K-local transfer.
-/

namespace StructuralRamsey.FunctionalPartite

open StructuralRamsey

universe u v
variable {L : Language.{u}} {P V W : Type v}

/-- Pullback of the minimal active-output-part criterion under a map
preserving PART LABELS and POSITIVE function-output incidences.
The original weak homomorphism's relation-preservation component is
available but unused; no full/total-fibre equality is required. -/
theorem System.ActiveWeakOutputPartCover.preimage_weakHom
    (B : System L P V) (C : System L P W) (f : V → W)
    (hPart : ∀ x, C.part (f x) = B.part x)
    (hf : B.toStructure.IsWeakHomomorphism C.toStructure f)
    (S : Set W)
    (hS : C.ActiveWeakOutputPartCover S) :
    B.ActiveWeakOutputPartCover (f ⁻¹' S) := by
  intro F xs hMeet y hy hPartSource
  let xsC : Fin (L.funcArity F) → S :=
    fun i => ⟨f (xs i).1, (xs i).2⟩
  have hMeetC :
      ((C.toStructure.func F (Subtype.val ∘ xsC)) ∩ S).Nonempty := by
    obtain ⟨z, hzQ, hzS⟩ := hMeet
    refine ⟨f z, ?_, hzS⟩
    change f z ∈ C.toStructure.func F (f ∘ (Subtype.val ∘ xs))
    exact hf.2 F (Subtype.val ∘ xs) z hzQ
  have hyC :
      f y ∈ C.toStructure.func F (Subtype.val ∘ xsC) := by
    change f y ∈ C.toStructure.func F (f ∘ (Subtype.val ∘ xs))
    exact hf.2 F (Subtype.val ∘ xs) y hy
  have hPartC : C.part (f y) ∈ C.part '' S := by
    obtain ⟨z, hzS, hzPart⟩ := hPartSource
    refine ⟨f z, hzS, ?_⟩
    calc
      C.part (f z) = B.part z := hPart z
      _ = B.part y := hzPart
      _ = C.part (f y) := (hPart y).symm
  exact hS F xsC hMeetC (f y) hyC hPartC

/-- The same pullback holds along genuine EHN homomorphism-embeddings
that preserve part labels, using ONLY their globally positive weak
functional component. Their full-on-irreducibles clause plays no role
and no reflection of undefined source function inputs is required. -/
theorem System.ActiveWeakOutputPartCover.preimage_ehn
    (B : System L P V) (C : System L P W) (f : V → W)
    (hPart : ∀ x, C.part (f x) = B.part x)
    (hf : B.toStructure.IsEHNHomomorphismEmbedding C.toStructure f)
    (S : Set W)
    (hS : C.ActiveWeakOutputPartCover S) :
    B.ActiveWeakOutputPartCover (f ⁻¹' S) :=
  System.ActiveWeakOutputPartCover.preimage_weakHom
    B C f hPart hf.1 S hS

end StructuralRamsey.FunctionalPartite
