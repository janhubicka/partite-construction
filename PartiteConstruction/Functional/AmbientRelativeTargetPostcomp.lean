import PartiteConstruction.Functional.AmbientRelativeWeakPullback

/-!
# Target-side full-embedding transfer for relative weak function maps

A strict functional B-tree completion may be extended by gluing further
B-trees over full closed roots. The existing witness map need not be a
FULL homomorphism on arbitrary weak subsets, but it must remain an
AMBIENT-RELATIVE weak HE into the enlarged tree.

This lemma proves exactly that: composing a relative weak HE with
ANY full functional target embedding preserves (1) positive relation
and all witnessed function incidences, (2) complete function fibres
whenever all ambient source outputs survive in the test, and
(3) genuine full ambient irreducible pieces.

The proof does not use singleton-valued functions, add closure vertices,
reflect undefined domains or claim that arbitrary weak boundary roots
can be glued. It supplies the target-extension interface needed by
the genuine native Hales-Jewett mixed-case relative-root induction.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {U V W : Type v}

/-- Ambient-relative weak functional maps are stable under
postcomposition with a FULL functional embedding of the target.
This preserves complete fibres for each input whose original
outputs lie entirely in the weak tested vertex set. -/
theorem IsAmbientRelativeWeakHomomorphism.postcomp_full
    {C : Structure L U} {S : Set U}
    {Target : Structure L V} {Target' : Structure L W}
    {f : S → V}
    (h : IsAmbientRelativeWeakHomomorphism C S Target f)
    (e : Embedding Target Target') :
    IsAmbientRelativeWeakHomomorphism C S Target' (e ∘ f) := by
  constructor
  · exact e.isWeakHomomorphism.comp h.1
  · intro F x hDefined hAll
    have hF := h.2 F x hDefined hAll
    have hE := e.map_func F (f ∘ x)
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      have haT : f a ∈ Target.func F (f ∘ x) := by
        rw [← hF]
        exact ⟨a, ha, rfl⟩
      have heT : e (f a) ∈ Target'.func F (e ∘ (f ∘ x)) := by
        rw [← hE]
        exact ⟨f a, haT, rfl⟩
      simpa only [Function.comp_assoc, Function.comp_apply] using heT
    · intro hz
      have hz' : z ∈ Target'.func F (e ∘ (f ∘ x)) := by
        simpa only [Function.comp_assoc] using hz
      rw [← hE] at hz'
      obtain ⟨b, hb, rfl⟩ := hz'
      rw [← hF] at hb
      obtain ⟨a, ha, rfl⟩ := hb
      exact ⟨a, ha, rfl⟩

/-- Target extensions preserve not only the relative fibre law but
also the FULL embeddings of every genuine ambient irreducible source
piece lying in the tested set. Thus the strict B-tree witness
can be freely extended without sacrificing the weak induction
projection interface. -/
theorem IsAmbientRelativeWeakHE.postcomp_full
    {C : Structure L U} {S : Set U}
    {Target : Structure L V} {Target' : Structure L W}
    {f : S → V}
    (h : IsAmbientRelativeWeakHE C S Target f)
    (e : Embedding Target Target') :
    IsAmbientRelativeWeakHE C S Target' (e ∘ f) := by
  refine ⟨h.1.postcomp_full e, ?_⟩
  intro X E hE j hj
  obtain ⟨g, hg⟩ := h.2 E hE j hj
  refine ⟨e.comp g, ?_⟩
  intro x
  exact congrArg e (hg x)

end StructuralRamsey.Structure
