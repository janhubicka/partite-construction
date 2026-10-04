import PartiteConstruction.Functional.WeakInduced
import PartiteConstruction.Structure.GeneratedWeakHomImage

set_option autoImplicit false

/-! # Weak projections that are full embeddings on irreducibles

The coordinate range of a closed irreducible in a power need not be closed.
Its closed hull is irreducible, and the previous-stage invariant applies to
that hull. This supplies the coordinate embeddings needed for injectivity,
relation reflection, and exact function-fibre preservation on the source.
-/
namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V W : Type v}

def IsWeakHomomorphismEmbedding (A : Structure L U) (B : Structure L V)
    (f : U → V) : Prop :=
  A.IsWeakHomomorphism B f ∧
  ∀ {X : Type v} (E : Structure L X), E.Irreducible →
    ∀ e : Embedding E A,
      ∃ g : Embedding E B, ∀ x, g x = f (e x)

theorem IsWeakHomomorphismEmbedding.comp
    {A : Structure L U} {B : Structure L V} {C : Structure L W}
    {f : U → V} {g : V → W}
    (hg : B.IsWeakHomomorphismEmbedding C g)
    (hf : A.IsWeakHomomorphismEmbedding B f) :
    A.IsWeakHomomorphismEmbedding C (g ∘ f) := by
  constructor
  · exact hg.1.comp hf.1
  · intro X E hE e
    obtain ⟨eB, heB⟩ := hf.2 E hE e
    obtain ⟨eC, heC⟩ := hg.2 E hE eB
    exact ⟨eC, fun x => (heC x).trans (congrArg g (heB x))⟩

theorem Embedding.isWeakHomomorphismEmbedding
    {A : Structure L U} {B : Structure L V} (e : Embedding A B) :
    A.IsWeakHomomorphismEmbedding B e := by
  refine ⟨e.isWeakHomomorphism, ?_⟩
  intro X E _ f
  exact ⟨e.comp f, fun _ => rfl⟩

end StructuralRamsey.Structure

namespace StructuralRamsey.FunctionalPartite

open Structure

universe u v
variable {L : Language.{u}} {P V : Type v}

def System.WeaklyPartiteOver (B : System L P V) (A : Structure L P) : Prop :=
  B.toStructure.IsWeakHomomorphismEmbedding A B.part

namespace Induced

variable {A : Structure L P} {B : System L P V} {N : ℕ}

theorem coordinateWeak (i : Fin N) :
    (power B N).toStructure.IsWeakHomomorphism B.toStructure
      (fun z => z.coord i) := by
  constructor
  · intro R z hz
    exact hz i
  · intro F x y hy
    exact hy i

theorem power_projectionWeak
    (hB : B.toStructure.IsWeakHomomorphism A B.part) (hN : 0 < N) :
    (power B N).toStructure.IsWeakHomomorphism A (power B N).part := by
  let i : Fin N := ⟨0, hN⟩
  constructor
  · intro R z hz
    have h := hB.1 R (fun k => (z k).coord i) (hz i)
    have hp : B.part ∘ (fun k => (z k).coord i) = (power B N).part ∘ z :=
      funext (fun k => (z k).belongs i)
    rw [hp] at h
    exact h
  · intro F x y hy
    have h := hB.2 F (fun k => (x k).coord i) (y.coord i) (hy i)
    have hp : B.part ∘ (fun k => (x k).coord i) = (power B N).part ∘ x :=
      funext (fun k => (x k).belongs i)
    rw [hp, y.belongs i] at h
    exact h

/-- The full functional irreducible invariant survives the same coordinate
power used in the Hales--Jewett lemma, with only weak global projections. -/
theorem power_weaklyPartiteOver
    (hB : B.WeaklyPartiteOver A) (hN : 0 < N) :
    (power B N).WeaklyPartiteOver A := by
  classical
  let C := power B N
  have hp : C.toStructure.IsWeakHomomorphism A C.part :=
    power_projectionWeak hB.1 hN
  refine ⟨hp, ?_⟩
  intro X E hE e
  let q (i : Fin N) : X → V := fun x => (e x).coord i
  have hq (i : Fin N) : E.IsWeakHomomorphism B.toStructure (q i) :=
    (coordinateWeak i).comp e.isWeakHomomorphism
  let S (i : Fin N) : Set V := B.toStructure.functionClosure (Set.range (q i))
  have hS (i : Fin N) : B.toStructure.IsClosed (S i) :=
    B.toStructure.functionClosure_isClosed (Set.range (q i))
  let H (i : Fin N) := B.toStructure.induce (S i) (hS i)
  have hH (i : Fin N) : (H i).Irreducible :=
    hE.functionClosure_weakImage (hq i)
  have hex (i : Fin N) :
      ∃ g : Structure.Embedding (H i) A,
        ∀ z : S i, g z = B.part z.1 :=
    hB.2 (H i) (hH i) (Structure.inclusion B.toStructure (S i) (hS i))
  choose g hg using hex
  let qs (i : Fin N) : X → S i := closureLift B.toStructure (q i)
  let target : X → P := fun x => C.part (e x)
  have htarget (i : Fin N) (x : X) : g i (qs i x) = target x :=
    (hg i (qs i x)).trans ((e x).belongs i)
  have htWeak : E.IsWeakHomomorphism A target := hp.comp e.isWeakHomomorphism
  have hinj : Function.Injective target := by
    intro x y hxy
    apply e.injective
    apply Vertex.ext B hxy
    intro i
    have hgi : g i (qs i x) = g i (qs i y) :=
      (htarget i x).trans (hxy.trans (htarget i y).symm)
    exact congrArg Subtype.val ((g i).injective hgi)
  let ge : Structure.Embedding E A := {
    toFun := target
    injective := hinj
    map_rel_iff := by
      intro R z
      constructor
      · intro hArel
        have hPower : C.rel R (e ∘ z) := by
          intro i
          have hargs : g i ∘ (qs i ∘ z) = target ∘ z :=
            funext (fun k => htarget i (z k))
          have hAt : A.rel R (g i ∘ (qs i ∘ z)) := by
            rw [hargs]
            exact hArel
          exact ((g i).map_rel_iff R (qs i ∘ z)).mp hAt
        exact (e.map_rel_iff R z).mp hPower
      · exact htWeak.1 R z
    map_func := by
      intro F x
      ext a
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact htWeak.2 F x z hz
      · intro ha
        have hout : ∀ i : Fin N, ∃ b : V,
            b ∈ B.func F (q i ∘ x) ∧ B.part b = a := by
          intro i
          have hargs : g i ∘ (qs i ∘ x) = target ∘ x :=
            funext (fun k => htarget i (x k))
          have hat : a ∈ A.func F (g i ∘ (qs i ∘ x)) := by
            rw [hargs]
            exact ha
          rw [← (g i).map_func F (qs i ∘ x)] at hat
          obtain ⟨b, hb, hba⟩ := hat
          exact ⟨b.1, hb, (hg i b).symm.trans hba⟩
        choose b hb hba using hout
        let y : Vertex B N := {part := a, coord := b, belongs := hba}
        have hy : y ∈ C.func F (e ∘ x) := hb
        rw [← e.map_func F x] at hy
        obtain ⟨z, hz, hzy⟩ := hy
        exact ⟨z, hz, congrArg C.part hzy⟩
  }
  exact ⟨ge, fun _ => rfl⟩

/-- The full functional Partite Lemma together with the invariant used by the
single EHN refinement pass. -/
theorem weak_partiteLemma_withInvariant
    (hB : B.WeaklyPartiteOver A) [Finite P] [Finite V]
    (κ : Type*) [Fintype κ] :
    ∃ N : ℕ, 0 < N ∧ (power B N).WeaklyPartiteOver A ∧
      FunctionalPartite.Arrow (transversal A) B (power B N) κ := by
  obtain ⟨N, hN, hArrow⟩ := weak_partiteLemma hB.1 κ
  exact ⟨N, hN, power_weaklyPartiteOver hB hN, hArrow⟩

end Induced
end StructuralRamsey.FunctionalPartite
