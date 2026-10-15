import PartiteConstruction.Functional.AmbientRelativeWeakFunctions

/-!
# Composition of ambient-relative weak function maps along an EHN projection

For arbitrary SET-VALUED partial functions, relative weak maps are
the right substitute for the false claim that an EHN part projection
is a genuine partial homomorphism on every truncated weak fibre.

Suppose p:C→D is EHN and g is an ambient-relative weak HE from
the EXACT image p[S] into a functional target T. A nonempty C-function
fibre wholly contained in S is sent ONTO the complete D-function
fibre, which is therefore wholly contained in p[S]. Hence both
relative weak homomorphism laws apply in sequence, yielding a
relative HE C|ᵂS→T. Full ambient irreducibles remain protected by
composing the two protected-copy certificates.

There is NO singleton-valuedness, no reflection of undefined
function domains, and no generated closure hull. When S is
function-closed, the result upgrades to an original-2019
homomorphism-embedding into the same target. Target strictness/tree
data, when available, is unaffected by this pullback.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V W : Type v}

/-- An EHN map followed by an ambient-relative weak HE on its
EXACT weak vertex image is again an ambient-relative weak HE.
This is the general set-valued function-language small-image
transfer, without requiring a singleton-valued source. -/
theorem IsAmbientRelativeWeakHE.pullback_ehn_exact
    {C : Structure L U} {D : Structure L V}
    {Target : Structure L W}
    {p : U → V}
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (S : Set U) (g : (p '' S) → W)
    (hg : IsAmbientRelativeWeakHE D (p '' S) Target g) :
    IsAmbientRelativeWeakHE C S Target
      (g ∘ (fun x : S =>
        (⟨p x.1, ⟨x.1, x.2, rfl⟩⟩ : p '' S))) := by
  let pS : S → p '' S := fun x => ⟨p x.1, ⟨x.1, x.2, rfl⟩⟩
  have hpS : IsAmbientRelativeWeakHE C S
      (D.weakInduce (p '' S)) pS :=
    hp.ambientRelativeWeakImage S
  change IsAmbientRelativeWeakHE C S Target (g ∘ pS)
  constructor
  · constructor
    · constructor
      · intro R x hx
        exact hg.1.1.1 R (pS ∘ x) (hpS.1.1.1 R x hx)
      · intro F x y hy
        have hyD :
            pS y ∈ (D.weakInduce (p '' S)).func F (pS ∘ x) :=
          hpS.1.1.2 F x y hy
        have hyT :
            g (pS y) ∈ Target.func F (g ∘ (pS ∘ x)) :=
          hg.1.1.2 F (pS ∘ x) (pS y) hyD
        simpa only [Function.comp_assoc] using hyT
    · intro F x hDef hAll
      have hFirst := hpS.1.2 F x hDef hAll
      have hFull :
          imageSet p (C.func F (Subtype.val ∘ x)) =
            D.func F (p ∘ (Subtype.val ∘ x)) :=
        hp.toOriginalPartial.1.2 F (Subtype.val ∘ x) hDef
      have hDdef :
          (D.func F (Subtype.val ∘ (pS ∘ x))).Nonempty := by
        obtain ⟨y, hy⟩ := hDef
        refine ⟨p y, ?_⟩
        change p y ∈ D.func F (p ∘ (Subtype.val ∘ x))
        rw [← hFull]
        exact ⟨y, hy, rfl⟩
      have hDall :
          ∀ y, y ∈ D.func F (Subtype.val ∘ (pS ∘ x)) →
            y ∈ p '' S := by
        intro y hy
        have hyD : y ∈ D.func F (p ∘ (Subtype.val ∘ x)) := hy
        rw [← hFull] at hyD
        obtain ⟨z, hz, hzy⟩ := hyD
        exact ⟨z, hAll z hz, hzy⟩
      have hSecond := hg.1.2 F (pS ∘ x) hDdef hDall
      ext z
      constructor
      · rintro ⟨a, ha, rfl⟩
        have hb :
            pS a ∈ (D.weakInduce (p '' S)).func F (pS ∘ x) := by
          rw [← hFirst]
          exact ⟨a, ha, rfl⟩
        have hc : g (pS a) ∈
            imageSet g ((D.weakInduce (p '' S)).func F (pS ∘ x)) :=
          ⟨pS a, hb, rfl⟩
        rw [hSecond] at hc
        simpa only [Function.comp_assoc] using hc
      · intro hz
        have hzT :
            z ∈ Target.func F (g ∘ (pS ∘ x)) := by
          simpa only [Function.comp_assoc] using hz
        rw [← hSecond] at hzT
        obtain ⟨b, hb, hgb⟩ := hzT
        rw [← hFirst] at hb
        obtain ⟨a, ha, hpa⟩ := hb
        exact ⟨a, ha, (congrArg g hpa).trans hgb⟩
  · intro X E hE e he
    obtain ⟨eD, heD⟩ := hp.2 E hE e
    have heImage : ∀ x : X, eD x ∈ p '' S := by
      intro x
      rw [heD x]
      exact ⟨e x, he x, rfl⟩
    obtain ⟨eT, heT⟩ := hg.2 E hE eD heImage
    refine ⟨eT, ?_⟩
    intro x
    calc
      eT x = g ⟨eD x, heImage x⟩ := heT x
      _ = (g ∘ pS) ⟨e x, he x⟩ := by
        change g (⟨eD x, heImage x⟩ : p '' S) =
          g (pS ⟨e x, he x⟩)
        congr 1
        apply Subtype.ext
        exact heD x

/-- Closed test consequence: if the predecessor gives an
ambient-relative weak functional tree witness on the exact
projected vertex set, then the original closed source test has
an ordinary original-partial homomorphism-embedding into that
same target. This is the small-image induction implication,
not an assertion that every predecessor weak test has a witness. -/
theorem IsAmbientRelativeWeakHE.pullback_ehn_closed
    {C : Structure L U} {D : Structure L V}
    {Target : Structure L W}
    {p : U → V}
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (S : Set U) (hClosed : C.IsClosed S)
    (g : (p '' S) → W)
    (hg : IsAmbientRelativeWeakHE D (p '' S) Target g) :
    IsOriginalPartialHomomorphismEmbedding
      (C.induce S hClosed) Target
      (g ∘ (fun x : S =>
        (⟨p x.1, ⟨x.1, x.2, rfl⟩⟩ : p '' S))) :=
  (hg.pullback_ehn_exact hp S g).toOriginalPartialHE_of_closed hClosed

end StructuralRamsey.Structure
