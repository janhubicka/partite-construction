import PartiteConstruction.Functional.RelativeHistoryTreeCompletion
import PartiteConstruction.Functional.LabelledIntersectionControl
import PartiteConstruction.Functional.ClosedGeneratorRank

/-! # Injective relative pullback from the outer EHN target

In the hard branch of the functional Picture-step proof, the projection of the
whole tested closed substructure is injective.  A mixed overlap is only
labelled by A; it need not embed into A as a structure.  Nevertheless its
label map is a full homomorphism, because its composite with a fixed copy of A
in D is the restriction of the ambient functional projection.

The label image is therefore a closed substructure of A.  Query the
relative-history invariant of D on the closed projected image of the side and
on this closed label image.  Injectivity of the side projection then pulls the
relative witness back and upgrades the target A-copy isolation to the original
source overlap.

This is the functional replacement for the relative-labelled side witnesses in
the relational mixed Picture step.
-/

namespace StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {U P W V H : Type v}
variable {A : Structure L U}
variable {D : Structure L P}
variable {C : Structure L W}
variable {Base : Structure L V}
variable {Root : Structure L H}

/-- Pull a relative labelled witness back from D along an injective full
homomorphism-embedding. -/
theorem FunctionalProjectedHistoryTreeLike.relativeWitness_of_injective_projection
    [Fintype W]
    (hA : A.Irreducible)
    (eAB : Embedding A Base)
    {p : W → P}
    {n : ℕ}
    (hD : FunctionalProjectedHistoryTreeLike
      (A := A) (D := D) (C := D) (Base := Base) id n)
    (hp : C.IsHomomorphismEmbedding D p)
    (hinj : Function.Injective p)
    (hgen : C.GeneratedByAtMost n)
    (history : List (Set P))
    (s : Embedding Root C)
    (β : Embedding A D)
    (q : H → U)
    (hproj : ∀ d, p (s d) = β (q d)) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : W → Z,
        C.IsHomomorphismEmbedding Target f ∧
        (∀ K ∈ history, ∀ x y : W,
          f x = f y → (p x ∈ K ↔ p y ∈ K)) ∧
        ∃ targetCopy : Embedding A Target,
          (∀ d : H, f (s d) = targetCopy (q d)) ∧
          IsFreeAmalgam.RootIsolated s targetCopy q f := by
  classical
  have hqHom : Root.IsHomomorphism A q := by
    have hs : Root.IsHomomorphism D (p ∘ s) :=
      hp.1.comp s.isHomomorphism
    have heq : p ∘ s = β ∘ q := by
      funext d
      exact hproj d
    have hβq : Root.IsHomomorphism D (β ∘ q) := by
      rw [← heq]
      exact hs
    exact β.cancelHomomorphism hβq

  let I : Finset P := Finset.univ.image p
  have hrange : Set.range p = (↑I : Set P) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
    · intro hy
      rcases Finset.mem_image.mp hy with ⟨x, _, hxy⟩
      exact ⟨x, hxy⟩
  have hIclosed : D.IsClosed (↑I : Set P) := by
    rw [← hrange]
    exact hp.1.range_isClosed
  let R := D.induce (↑I : Set P) hIclosed
  let incR : Embedding R D :=
    inclusion D (↑I : Set P) hIclosed
  let pR : W → ↥(↑I : Set P) :=
    fun x => ⟨p x, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩

  have hpRHom : C.IsHomomorphism R pR :=
    hp.1.codRestrict (↑I : Set P) hIclosed
      (fun x => Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
  have hpRIHE : C.IsHomomorphismEmbedding R pR := by
    refine ⟨hpRHom, ?_⟩
    intro X E hE e
    obtain ⟨g, hg⟩ := hp.2 E hE e
    have hgrange :
        ∀ z : X, ∃ r : ↥(↑I : Set P), g z = incR r := by
      intro z
      let r : ↥(↑I : Set P) :=
        ⟨p (e z), Finset.mem_image.mpr
          ⟨e z, Finset.mem_univ _, rfl⟩⟩
      exact ⟨r, hg z⟩
    let gr : Embedding E R :=
      g.factorThroughClosedRange incR hgrange
    refine ⟨gr, ?_⟩
    intro z
    apply Subtype.ext
    have hfactor :
        incR (gr z) = g z :=
      Embedding.factorThroughClosedRange_spec g incR hgrange z
    calc
      (gr z).1 = g z := hfactor
      _ = p (e z) := hg z
      _ = (pR (e z)).1 := rfl

  have hIgen : R.GeneratedByAtMost n := by
    have hgenRange :=
      homRange_generatedByAtMost hp.1 hgen
    let Range :=
      D.induce (Set.range p) hp.1.range_isClosed
    let incRange : Embedding Range D :=
      inclusion D (Set.range p) hp.1.range_isClosed
    have hinto :
        ∀ x : ↥(Set.range p),
          ∃ y : ↥(↑I : Set P), incRange x = incR y := by
      intro x
      have hxI : x.1 ∈ (↑I : Set P) := by
        rw [← hrange]
        exact x.2
      exact ⟨⟨x.1, hxI⟩, rfl⟩
    let eRange : Embedding Range R :=
      incRange.factorThroughClosedRange incR hinto
    have heSurj : Function.Surjective eRange := by
      intro y
      have hyRange : y.1 ∈ Set.range p := by
        rw [hrange]
        exact y.2
      let x : ↥(Set.range p) := ⟨y.1, hyRange⟩
      refine ⟨x, ?_⟩
      apply Subtype.ext
      have hs :=
        Embedding.factorThroughClosedRange_spec
          incRange incR hinto x
      change (eRange x).1 = x.1 at hs
      exact hs
    have hgenRange' : Range.GeneratedByAtMost n := by
      simpa [Range] using hgenRange
    exact hgenRange'.of_surjective_embedding eRange heSurj

  let Hset : Set U := Set.range q
  have hHclosed : A.IsClosed Hset := hqHom.range_isClosed
  let Hstr := A.induce Hset hHclosed
  let incH : Embedding Hstr A :=
    inclusion A Hset hHclosed
  let eD : Embedding Hstr D := β.comp incH
  have hRangeD : ∀ x : Hstr, eD x ∈ I := by
    intro x
    rcases x.2 with ⟨d, hd⟩
    apply Finset.mem_image.mpr
    refine ⟨s d, Finset.mem_univ _, ?_⟩
    change p (s d) = β x.1
    calc
      p (s d) = β (q d) := hproj d
      _ = β x.1 := congrArg β hd
  have hprojD :
      ∀ x : Hstr, (id : P → P) (eD x) = β x.1 :=
    fun _ => rfl

  have hRel :
      FunctionalRelativeHistoryTreeLike
        (A := A) (D := D) (C := D) (Base := Base) id n :=
    FunctionalRelativeHistoryTreeLike.ofProjectedHistory_identity
      hA eAB hD

  obtain ⟨Z, Target, hTree, g, hg, _hPart, hHist, _hSrc,
      targetCopy, hcompat0, hiso0⟩ :=
    hRel.2 I hIclosed hIgen history []
      β Hset hHclosed eD hprojD hRangeD incH

  let f : W → Z := g ∘ pR
  have hf : C.IsHomomorphismEmbedding Target f :=
    hg.comp hpRIHE
  have hHist :
      ∀ K ∈ history, ∀ x y : W,
        f x = f y → (p x ∈ K ↔ p y ∈ K) := by
    intro K hK x y hxy
    have hh := hHist K hK (pR x) (pR y) hxy
    exact hh

  have hcompat :
      ∀ d : H, f (s d) = targetCopy (q d) := by
    intro d
    let xH : Hstr := ⟨q d, ⟨d, rfl⟩⟩
    have hxI : eD xH ∈ I := hRangeD xH
    have hx :
        pR (s d) = (⟨eD xH, hxI⟩ : ↥(↑I : Set P)) := by
      apply Subtype.ext
      change p (s d) = β (q d)
      exact hproj d
    change g (pR (s d)) = targetCopy (q d)
    rw [hx]
    exact hcompat0 xH

  have hroot :
      IsFreeAmalgam.RootIsolated s targetCopy q f := by
    intro y a hya
    obtain ⟨xH, hyD, hxa⟩ :=
      hiso0 (pR y) a hya
    rcases xH.2 with ⟨d, hd⟩
    have hpy :
        p y = p (s d) := by
      calc
        p y = (pR y).1 := rfl
        _ = eD xH := congrArg Subtype.val hyD
        _ = β xH.1 := rfl
        _ = β (q d) := congrArg β hd.symm
        _ = p (s d) := (hproj d).symm
    have hy : y = s d := hinj hpy
    refine ⟨d, hy, ?_⟩
    calc
      q d = xH.1 := hd
      _ = a := hxa

  exact ⟨Z, Target, hTree, f, hf, hHist,
    targetCopy, hcompat, hroot⟩

end StructuralRamsey.Structure
