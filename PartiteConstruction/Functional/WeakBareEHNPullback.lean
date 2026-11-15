import PartiteConstruction.Functional.WeakAmbientACopyTraceRestorationBudget
import PartiteConstruction.Functional.AmbientRelativeWeakPullback

/-!
# Track D: bare strict B-tree rank pulls back along every genuine EHN map

English proof committed FIRST:
docs/track-d-english-bare-ehn-pullback-onecopy-20261115.md

AtMostBare is a deliberately weaker STRICT full-functional
tree locality invariant: for each LITERAL weak finite vertex
test it requires only a strict Base-tree and an ambient-relative
weak HE, not target marks for partially tested A-copies.

This property is EHN-pullback invariant at the SAME cardinal
bound, since each literal target image has at most as many
vertices as the source weak test. Genuine multivalued output
fibres are handled by the checked ambient-relative EHN
pullback theorem; source-undefined function inputs are
not reflected and no weak tested set is enlarged.
-/

namespace StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness

universe u v
variable {L : Language.{u}} {VB U V UA : Type v}

/-- BARE strict full-functional local B-trees pull back along
arbitrary EHN projections, with no ambient irreducible A-copy
hypothesis, protected root, projected history, or labels.

Only the exact finite weak image of the actual tested source
set is requested from the predecessor. -/
theorem AtMostBare.pullback_ehn
    {Base : Structure L VB}
    {C : Structure L U} {D : Structure L V}
    {q : U → V}
    (hq : C.IsEHNHomomorphismEmbedding D q)
    (n : ℕ)
    (hD : AtMostBare Base D n) :
    AtMostBare Base C n := by
  classical
  intro S hS
  let I : Finset V := S.image q
  have hCard : I.card ≤ n :=
    Finset.card_image_le.trans hS
  have hImage : (↑I : Set V) = q '' (↑S : Set U) := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx, hxz⟩ := Finset.mem_image.mp hz
      exact ⟨x, hx, hxz⟩
    · rintro ⟨x, hx, rfl⟩
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hOld :
      ∃ (Y : Type v) (Target : Structure L Y),
        TreeAmalgam Base Y Target ∧
        ∃ g : (q '' (↑S : Set U)) → Y,
          IsAmbientRelativeWeakHE D
            (q '' (↑S : Set U)) Target g := by
    rw [← hImage]
    exact hD I hCard
  obtain ⟨Y, Target, hTree, g, hg⟩ := hOld
  let f : (↑S : Set U) → Y :=
    g ∘ (fun x : (↑S : Set U) =>
      (⟨q x.1, ⟨x.1, x.2, rfl⟩⟩ : q '' (↑S : Set U)))
  exact ⟨Y, Target, hTree, f,
    hg.pullback_ehn_exact hq (↑S : Set U) g⟩

/-- The FULL identity source map into its own strict
Base-tree gives a BARE ambient-relative weak HE on
every exact weak test at every finite vertex bound.

No irreducibility assumption on the auxiliary A and
no source part map is required. -/
theorem AtMostBare.of_strictTree
    {Base : Structure L VB} {C : Structure L U}
    (hTree : TreeAmalgam Base U C) (n : ℕ) :
    AtMostBare Base C n := by
  intro S _hS
  let f : (↑S : Set U) → U := fun x => x.1
  have hf : IsAmbientRelativeWeakHE C (↑S : Set U) C f :=
    (Embedding.id C).ambientRelativeWeakRestriction (↑S : Set U)
  exact ⟨U, C, hTree, f, hf⟩

/-- A genuine EHN source projection C→A followed by a
FULL embedding A↪Base supplies one-copy strict Base-tree
BARE weak witnesses at EVERY rank. Unlike the stronger
history-free A-marked theorem, this needs no
irreducibility of A and works with arbitrary
set-valued function fibres. -/
theorem AtMostBare.of_ehn_oneCopy
    {Base : Structure L VB} {A : Structure L UA}
    {C : Structure L U} {q : U → UA}
    (hq : C.IsEHNHomomorphismEmbedding A q)
    (eAB : Embedding A Base) (n : ℕ) :
    AtMostBare Base C n := by
  have hBaseTree : TreeAmalgam Base VB Base :=
    TreeAmalgam.copy (Embedding.id Base) (fun b => ⟨b, rfl⟩)
  have hSelf : AtMostBare Base Base n :=
    AtMostBare.of_strictTree hBaseTree n
  have hComp : C.IsEHNHomomorphismEmbedding Base (eAB ∘ q) :=
    eAB.isEHNHomomorphismEmbedding.comp hq
  exact AtMostBare.pullback_ehn hComp n hSelf

end StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness
