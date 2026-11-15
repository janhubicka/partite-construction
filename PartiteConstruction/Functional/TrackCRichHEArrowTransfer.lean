import PartiteConstruction.Functional.TrackCRichOptionEHN
import PartiteConstruction.Functional.TrackCRichDomainEmptyArrow

/-!
# Track C: genuine rich Ramsey arrows transfer through original partial HE

The intrinsic locally finite subclass construction will eventually
give a source-defined original genuine Option(Set) HE f:D→H, not
necessarily a full embedding on the entire reducible D. The
Ramsey arrow of D must transfer to H without changing colors
or assuming any global reflection on missing function domains.

If A and B are genuinely closed-free irreducible, the HE f is
FULL on every actual A/B copy in D, on the SAME f-composite
vertex maps. Pull a coloring of full A-copies of H back along
these full embedded images. A monochromatic full B-copy in D
lifts to a full B-copy in H, and all its A-copies agree because
full embeddings are determined by their literal vertex maps.

This works for arbitrary color types, including finite k,
nonempty or empty domain masks, and arbitrary arities.
No global injectivity of f, NoDefinedEmptyValues, free root
or added closure vertices. This is an exact ENDGAME lemma;
it does not claim that the locally finite subclass axiom has
already produced the H-completion of D.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.Structure.TrackECanonicalArrowEquivalence

universe u v
variable {L : Language.{u}} {U V X Y : Type v}

/-- If D has a genuine partial Ramsey arrow and there is an ORIGINAL
source-defined partial homomorphism-embedding f:D→H which is FULL
on every intrinsically rich irreducible copy, then H inherits
the same arrow whenever A and B are rich irreducible.

The proof does not assert that f is a global full embedding:
all selected lifted A/B maps agree only on their own sources. -/
theorem GenuinePartialArrow.of_irreducible_originalPartialHE
    (A : PartialSetStructure L U)
    (B : PartialSetStructure L V)
    (D : PartialSetStructure L X)
    (H : PartialSetStructure L Y)
    (κ : Type*)
    (hA : A.IsOptionClosedFreeIrreducible)
    (hB : B.IsOptionClosedFreeIrreducible)
    (hArrow : GenuinePartialArrow A B D κ)
    (f : X → Y)
    (hf : D.IsOptionClosedFreeHomomorphismEmbedding H f) :
    GenuinePartialArrow A B H κ := by
  classical
  let liftA : Embedding A D → Embedding A H :=
    fun a => Classical.choose (hf.2 A hA a)
  have hLiftA (a : Embedding A D) (x : U) :
      (liftA a).toFun x = f (a.toFun x) :=
    Classical.choose_spec (hf.2 A hA a) x
  intro χ
  obtain ⟨b, hb⟩ :=
    hArrow (fun a : Embedding A D => χ (liftA a))
  obtain ⟨bH, hbH⟩ := hf.2 B hB b
  refine ⟨bH, ?_⟩
  intro a₁ a₂
  have hLiftComposition (a : Embedding A B) :
      bH.comp a = liftA (b.comp a) := by
    apply Embedding.ext
    intro x
    calc
      (bH.comp a).toFun x = bH.toFun (a.toFun x) := rfl
      _ = f (b.toFun (a.toFun x)) := hbH (a.toFun x)
      _ = (liftA (b.comp a)).toFun x :=
        (hLiftA (b.comp a) x).symm
  rw [hLiftComposition a₁, hLiftComposition a₂]
  exact hb a₁ a₂

end StructuralRamsey.PartialSetStructure
