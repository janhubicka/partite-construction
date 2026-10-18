import PartiteConstruction.Functional.ProtectedAMarkWeakTreeGlue
import PartiteConstruction.Functional.ProtectedAMarkWeakPullback

/-!
# Strict native functional mixed gluing from two protected CONTROL side witnesses

The actual full-functional source free amalgam Whole=Left *Root Right
has an EHN/original-2019 source-defined projection p:Whole→D, and
the projected genuine common attaching root lies in a selected FULL
alpha:A↪D. Fix ANY exact weak source vertex set S, not assumed
closed under function images.

If the two exact projected side images
  (p∘iL) '' (iL ⁻¹' S) and (p∘iR) '' (iR ⁻¹' S)
have STRICT full-functional Base-tree protected A-mark witnesses
for the SAME alpha and finite history, EHN-pullback produces
protected witnesses of the corresponding ACTUAL source weak sides.
The verified target FULL A-mark amalgamation then gives a strict
functional Base-tree weak witness for the entire ORIGINAL S.

No rank/cardinality assumptions, no source closure hull,
no total-fibre reflection at undefined source inputs, and no
guaranteed existence of protected marks are asserted here.
This extraction allows different sound predecessor constructions
(weak rank-m or closed-control-only rank-m) to reuse one checked
target gluing proof.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v
variable {L : Language.{u}}
variable {UA VB H E F C P : Type v}

/-- Protected strict functional witnesses for BOTH exact projected
side weak tests imply a strict full-functional witness of the
ORIGINAL exact weak source S, including ambient full A-copy
intersections and every requested projected history.

The protected CONTROL witnesses are explicit premises. Their
existence is not automatic for nonclosed occupied A-boundaries. -/
theorem weakTree_of_protected_projected_side_witnesses
    {A : Structure L UA} (hA : A.Irreducible)
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (D : Structure L P) (alpha : Embedding A D)
    (p : C → P)
    (hp : Whole.IsEHNHomomorphismEmbedding D p)
    (hRootAlpha : ∀ d : H,
      ∃ a : UA, p (iL (sL d)) = alpha a)
    (Base : Structure L VB)
    (S : Set C) (history : List (Set P))
    (hControlL : SetAmbientProtectedWeakTreeWitness
      A Base alpha D (id : P → P)
      ((p ∘ iL) '' (iL ⁻¹' S)) history)
    (hControlR : SetAmbientProtectedWeakTreeWitness
      A Base alpha D (id : P → P)
      ((p ∘ iR) '' (iR ⁻¹' S)) history) :
    SetAmbientRelativeWeakTreeWitness
      A Base Whole p S history := by
  classical
  let pL : E → P := p ∘ iL
  let pR : F → P := p ∘ iR
  have hpL : Left.IsEHNHomomorphismEmbedding D pL :=
    hp.comp iL.isEHNHomomorphismEmbedding
  have hpR : Right.IsEHNHomomorphismEmbedding D pR :=
    hp.comp iR.isEHNHomomorphismEmbedding
  have hLeft : SetAmbientProtectedWeakTreeWitness A Base alpha
      Left pL (iL ⁻¹' S) history :=
    SetAmbientProtectedWeakTreeWitness.pullback_ehn_commutingParts
      alpha pL (id : P → P) pL hpL
      (fun _ => rfl) hA
      (iL ⁻¹' S) history hControlL
  have hRight : SetAmbientProtectedWeakTreeWitness A Base alpha
      Right pR (iR ⁻¹' S) history :=
    SetAmbientProtectedWeakTreeWitness.pullback_ehn_commutingParts
      alpha pR (id : P → P) pR hpR
      (fun _ => rfl) hA
      (iR ⁻¹' S) history hControlR
  obtain ⟨ZL, TL, hTreeL, fL, hWeakL, hCopiesL, hHistL,
    markL, hcL, hTraceL⟩ := hLeft
  obtain ⟨ZR, TR, hTreeR, fR, hWeakR, hCopiesR, hHistR,
    markR, hcR, hTraceR⟩ := hRight
  exact hSrc.protectedAMarkWeakTree_glue hA
    S alpha p pL pR
    (fun _ => rfl) (fun _ => rfl)
    hRootAlpha Base TL TR hTreeL hTreeR markL markR hcL hcR
    fL fR hWeakL hWeakR hTraceL hTraceR
    hCopiesL hCopiesR history hHistL hHistR

end StructuralRamsey.Structure.IsFreeAmalgam
