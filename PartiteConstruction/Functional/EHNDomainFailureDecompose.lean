import PartiteConstruction.Functional.EHNTestDecompose
import PartiteConstruction.Functional.FibreExactness

/-! # Domain failures give the strict induction split

For the closure-aware functional sparsening proof, the difficult maximal test
has an injective EHN projection but may still fail reflection of a function
domain.  Such a failure rules out irreducibility of the whole closed test.
Hence the test has a proper full free decomposition, and all three pieces are
strictly smaller.

This packages the exact strong-induction split used by the remaining
reducible-separator argument.
-/

namespace StructuralRamsey.Structure.IsEHNHomomorphismEmbedding

universe u v

variable {L : Language.{u}}
variable {P W : Type v}
variable {D : Structure L P}
variable {C : Structure L W}
variable {p : W → P}

/-- A genuine domain-reflection failure on a finite closed test supplies a
proper free decomposition with strict cardinal drops on both sides and the
common separator. -/
theorem closedTest_decompose_of_domainFailure
    [Finite W]
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (S : Finset W) (hS : C.IsClosed (↑S : Set W))
    (F : L.FuncSymbol)
    (x : Fin (L.funcArity F) → ↥(↑S : Set W))
    (htgt :
      (D.func F ((p ∘ Subtype.val) ∘ x)).Nonempty)
    (hsrc :
      ¬ ((C.induce (↑S : Set W) hS).func F x).Nonempty) :
    let Small := C.induce (↑S : Set W) hS
    ∃ d : ProperFreeDecomposition Small,
      Nat.card d.Left < Nat.card ↥(↑S : Set W) ∧
      Nat.card d.Right < Nat.card ↥(↑S : Set W) ∧
      Nat.card d.Common < Nat.card ↥(↑S : Set W) := by
  classical
  let Small := C.induce (↑S : Set W) hS
  let inc : Embedding Small C :=
    inclusion C (↑S : Set W) hS
  rcases hp.closedTest_embedding_or_decompose S hS with
    hEmbed | hDecomp
  · rcases hEmbed with ⟨g, hg⟩
    have hargs :
        g ∘ x = (p ∘ Subtype.val) ∘ x := by
      funext i
      exact hg (x i)
    obtain ⟨y, hy⟩ := htgt
    have hy' : y ∈ D.func F (g ∘ x) := by
      rw [hargs]
      exact hy
    have himg : y ∈ imageSet g (Small.func F x) := by
      rw [g.map_func F x]
      exact hy'
    rcases himg with ⟨z, hz, _⟩
    exact (hsrc ⟨z, hz⟩).elim
  · rcases hDecomp with ⟨d⟩
    letI : Finite ↥(↑S : Set W) := Finite.of_fintype _
    exact ⟨d, d.left_card_lt, d.right_card_lt, d.common_card_lt⟩

end StructuralRamsey.Structure.IsEHNHomomorphismEmbedding
