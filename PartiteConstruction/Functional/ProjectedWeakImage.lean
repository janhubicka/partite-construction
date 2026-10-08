import PartiteConstruction.Structure.WeakSubstructure
import PartiteConstruction.Iterated.WeakFunctionalTreeCompletion

/-! # Weak images of weak substructures

For the vertex-size induction, the image of a weak test is again taken
weakly, on precisely the projected vertices. It is NOT the function-closed
hull of the projected vertices. This is the function-graph version of the
usual relational induced-image restriction of a homomorphism-embedding.
-/

namespace StructuralRamsey.Structure

universe u v

variable {L : Language.{u}} {V W : Type v}

/-- Restrict a weak homomorphism-embedding to an arbitrary weak source test,
with its target the weak substructure on the *set-theoretic image*. No
function closure is taken on either side. -/
theorem IsWeakHomomorphismEmbedding.weakImage
    {C : Structure L V} {D : Structure L W} {p : V → W}
    (hp : C.IsWeakHomomorphismEmbedding D p)
    (S : Set V) :
    (C.weakInduce S).IsWeakHomomorphismEmbedding
      (D.weakInduce (p '' S))
      (fun x : S => (⟨p x.1, ⟨x.1, x.2, rfl⟩⟩ : p '' S)) := by
  have hSource :
      (C.weakInduce S).graph.IsHomomorphismEmbedding D.graph
        (p ∘ Subtype.val) :=
    hp.comp (weakInclusion C S).isHomomorphismEmbedding
  have hImage :
      (C.weakInduce S).graph.IsHomomorphismEmbedding
        (D.graph.induce (p '' S))
        (fun x : S => (⟨p x.1, ⟨x.1, x.2, rfl⟩⟩ : p '' S)) :=
    hSource.codRestrict (p '' S) (fun x => ⟨x.1, x.2, rfl⟩)
  exact (weakGraphFromInduce D (p '' S)).isHomomorphismEmbedding.comp hImage

/-- The small-image branch of the functional vertex-size induction. BOTH the
tested source and its projected image are weakly induced. The previous-stage
bound is evaluated on the image's actual vertex set, and no function-closed
hull or extra vertex enters the proof. The completion target is a relational
tree of function graphs, not automatically a strict full-function tree. -/
theorem WeakLocallyTreeCompletable.completion_of_small_weakImage
    {Base : Structure L V} {C : Structure L V}
    {D : Structure L W} {p : V → W}
    [DecidableEq W] {m : ℕ}
    (hD : WeakLocallyTreeCompletable Base D m)
    (hp : C.IsWeakHomomorphismEmbedding D p)
    (S : Finset V) (hSize : (S.image p).card ≤ m) :
    RelStructure.HasTreeCompletion Base.graph
      (C.weakInduce (↑S : Set V)).graph := by
  classical
  let I : Finset W := S.image p
  have hImageSet : p '' (↑S : Set V) = (↑I : Set W) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨x, hx, rfl⟩
  let pS : ↥(↑S : Set V) → ↥(↑I : Set W) :=
    fun x => ⟨p x.1, Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩⟩
  have hProjection :
      (C.weakInduce (↑S : Set V)).graph.IsHomomorphismEmbedding
        (D.weakInduce (↑I : Set W)).graph pS := by
    simpa only [hImageSet] using hp.weakImage (↑S : Set V)
  obtain ⟨Z, T, hTree, f, hf⟩ :=
    hD I (by simpa [I] using hSize)
  have hfWeak :
      (D.weakInduce (↑I : Set W)).graph.IsHomomorphismEmbedding T f :=
    hf.comp (weakGraphToInduce D (↑I : Set W)).isHomomorphismEmbedding
  exact ⟨Z, T, hTree, f ∘ pS, hfWeak.comp hProjection⟩

end StructuralRamsey.Structure
