import PartiteConstruction.Functional.PureSideAmbientFullTraceTransfer

/-!
# Track D: A-copywise source root retraction for exact pure old tests

English proof committed first:
docs/track-d-english-copywise-root-map-pure-A-traces-20261114.md

A FULL functional source free amalgam admits a pure-right ambient
A-copy trace transfer when the LEFT source has merely an A-COPYWISE
FULL vertex map to Right that fixes the genuine FULL common root.
This does NOT require a globally EHN map nor any function-fibre law
outside the chosen full A-copies.

This is a sufficient SOURCE geometric input for the already verified
pure-right A-copy target certificate transfer. The hard existence
question for arbitrary multiple genuine HJ lines is still open;
single-parameter coordinates give a positive special case.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {UA E F : Type v}

/-- A vertex map preserves each full source A-copy as an actual FULL
A-copy, rather than being assumed EHN on all irreducible sources,
or weak/function preserving on the entire source.

This is exactly the piece of EHN data needed for ambient A-copy
certificates, and can be required only for the particular A. -/
def IsFullOnACopies
    {A : Structure L UA} {Left : Structure L E}
    {Right : Structure L F} (r : E → F) : Prop :=
  ∀ γ : Embedding A Left,
    ∃ δ : Embedding A Right,
      ∀ a : UA, δ a = r (γ a)

/-- Every genuine EHN map is full on all irreducible A-copies,
so it satisfies the strictly weaker A-copywise condition.
No separate global injectivity or domain-reflection premise. -/
theorem IsEHNHomomorphismEmbedding.isFullOnACopies
    {A : Structure L UA} (hA : A.Irreducible)
    {Left : Structure L E} {Right : Structure L F}
    {r : E → F}
    (hr : Left.IsEHNHomomorphismEmbedding Right r) :
    IsFullOnACopies (A := A) (Left := Left) (Right := Right) r := by
  intro γ
  exact hr.2 A hA γ

end StructuralRamsey.Structure

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}} {UA H E F C Z : Type v}

/-- Exact pure copied-RIGHT weak-test cross-side FULL A-trace lifting
from only an A-copywise source map Left→Right fixing Root.

The vertex map r need not preserve primitive relations, functions,
undefined domains, labels, or ANY irreducibles other than the
particular chosen full ambient A-copies. The full *source*
free-amalgam overlap, plus purity of the LITERAL tested S,
forces exact agreement of the lifted full A-copy on its
actual tested intersection. -/
theorem crossSideFullATraces_of_copywise_root_map
    {A : Structure L UA}
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (S : Set C)
    (hPure : ∀ z : C, z ∈ S → ∃ b : F, z = iR b)
    (r : E → F)
    (hRoot : ∀ d : H, r (sL d) = sR d)
    (hCopywise : IsFullOnACopies
      (A := A) (Left := Left) (Right := Right) r) :
    ∀ γL : Embedding A Left,
      ∃ γR : Embedding A Right,
        ∀ (a : UA) (ha : iL (γL a) ∈ S),
          iR (γR a) = iL (γL a) := by
  intro γL
  obtain ⟨γR, hγ⟩ := hCopywise γL
  refine ⟨γR, ?_⟩
  intro a ha
  obtain ⟨b, hb⟩ := hPure (iL (γL a)) ha
  obtain ⟨d, hdL, hdR⟩ :=
    (hSrc.overlap (γL a) b).mp hb
  calc
    iR (γR a) = iR (r (γL a)) := congrArg iR (hγ a)
    _ = iR (r (sL d)) := by rw [hdL]
    _ = iR (sR d) := by rw [hRoot d]
    _ = iR b := by rw [hdR]
    _ = iL (γL a) := hb.symm

/-- SOURCE-root A-copywise retraction is sufficient to transfer
a pre-existing old-side strict target's full ambient A-copy
certificates to the whole source at every exact pure-right test.

The target map f itself and its ambient-relative weak functional
homomorphism law are separate; no arbitrary projected history is
claimed. This isolates the pure maximal-image HJ obstruction
without inventing a full global EHN retraction. -/
theorem pureRight_ambientACopies_of_copywise_root_map
    {A : Structure L UA} (hA : A.Irreducible)
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C} {Target : Structure L Z}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (S : Set C)
    (hPure : ∀ z : C, z ∈ S → ∃ b : F, z = iR b)
    (f : S → Z)
    (fR : (iR ⁻¹' S) → Z)
    (hMap : ∀ x : (iR ⁻¹' S),
      f ⟨iR x.1, x.2⟩ = fR x)
    (hCopiesR : SetAmbientACopyIntersections
      A Right Target (iR ⁻¹' S) fR)
    (r : E → F)
    (hRoot : ∀ d : H, r (sL d) = sR d)
    (hCopywise : IsFullOnACopies
      (A := A) (Left := Left) (Right := Right) r) :
    SetAmbientACopyIntersections A Whole Target S f := by
  exact hSrc.pureRight_ambientACopies_of_crossSideTraces hA
    S f fR hMap hCopiesR
    (hSrc.crossSideFullATraces_of_copywise_root_map
      S hPure r hRoot hCopywise)

end StructuralRamsey.Structure.IsFreeAmalgam
