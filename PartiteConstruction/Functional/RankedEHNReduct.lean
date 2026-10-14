import PartiteConstruction.Functional.RankedIrreducibleBridge
import PartiteConstruction.Structure.IrreducibleHomImage

/-!
# Full EHN protected-test descent through singleton-rank reduction

Given an irreducible FULL substructure E of the rank reduct of A,
its embedded image S in A is closed in the rank reduct and therefore
closed for EACH rank.  The induced ranked structure H = A|S has
irreducible rank reduct (isomorphic to E), and thus H is itself
irreducible.  Apply the EHN ranked projection to this actual closed
ranked H.  Its full embedding into the ranked target can then be
rank-reduced and composed with the original E -> H embedding.

This gives the *complete* EHN homomorphism-embedding on the rank
reduct, not merely the already proved defined-fibre preservation.
No irreducible source carrier is enlarged: the ranked H uses exactly
the range of the originally protected full embedding.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V : Type v}

/-- An EHN weak homomorphism-embedding of singleton-ranked functional
structures descends to the EHN weak homomorphism-embedding of their
genuinely set-valued rank reducts. All irreducible FULL source tests
remain protected even though the resulting fibres may contain
multiple outputs. -/
theorem IsEHNHomomorphismEmbedding.rankReduct
    {n : ℕ}
    {A : Structure (L.rankFunctions n) U}
    {B : Structure (L.rankFunctions n) V}
    {p : U → V}
    (hp : A.IsEHNHomomorphismEmbedding B p) :
    (Structure.rankReduct A).IsEHNHomomorphismEmbedding
      (Structure.rankReduct B) p := by
  classical
  refine ⟨hp.1.rankReduct, ?_⟩
  intro X E hE e
  let S : Set U := Set.range e
  have hSRed : (Structure.rankReduct A).IsClosed S :=
    e.range_isClosed
  have hSRank : A.IsClosed S := IsClosed.of_rankReduct hSRed
  let H : Structure (L.rankFunctions n) S := A.induce S hSRank
  have hHRedIrred : (Structure.rankReduct H).Irreducible := by
    change ((Structure.rankReduct A).induce S hSRed).Irreducible
    exact hE.range_homomorphism e.isHomomorphism
  have hHIrred : H.Irreducible :=
    Irreducible.of_rankReduct hHRedIrred
  let inc : Embedding H A := inclusion A S hSRank
  obtain ⟨g, hg⟩ := hp.2 H hHIrred inc
  let eH : Embedding E (Structure.rankReduct H) := {
    toFun := fun x => ⟨e x, ⟨x, rfl⟩⟩
    injective := by
      intro x y hxy
      apply e.injective
      exact congrArg Subtype.val hxy
    map_rel_iff := by
      intro R x
      change A.rel R (e ∘ x) ↔ E.rel R x
      exact e.map_rel_iff R x
    map_func := by
      intro F x
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        change e y ∈ (Structure.rankReduct A).func F (e ∘ x)
        have h : e y ∈ imageSet e (E.func F x) :=
          ⟨y, hy, rfl⟩
        rw [e.map_func F x] at h
        exact h
      · intro hz
        have h : z.1 ∈ (Structure.rankReduct A).func F (e ∘ x) :=
          hz
        rw [← e.map_func F x] at h
        obtain ⟨y, hy, hey⟩ := h
        refine ⟨y, hy, ?_⟩
        exact Subtype.ext hey
  }
  let out : Embedding E (Structure.rankReduct B) :=
    g.rankReduct.comp eH
  refine ⟨out, ?_⟩
  intro x
  exact hg (eH x)

end StructuralRamsey.Structure
