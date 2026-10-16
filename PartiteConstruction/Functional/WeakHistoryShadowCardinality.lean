import PartiteConstruction.Functional.WeakHistoryCommutingPartsPullback

/-!
# A finite EHN shadow does not increase the rank of any exact weak test

The native functional partite sparsening induction is on the cardinality
of the ACTUAL weak vertex set, not on its generated function closure.

If a functional EHN map q:C→Old commutes with original-control
part projections, then every exact finite tested subset S of C
projects onto q[S] with |q[S]|≤|S|. The strict FULL-functional weak-tree
witness of Old for q[S] pulls back to S with:
  * positive relations and retained multivalued function incidences,
  * complete ambient fibres when every output survives in S,
  * protection of genuine full ambient A-copy intersections,
  * arbitrary finite projected histories of the ORIGINAL control.

No singleton-valued functions, domain reflection, or function-generated
closure hull is needed. A closed S has the same original-partial HE
upgrade as the general exact weak shadow theorem.

A genuine ONE-LINE native HJ attachment retracts to its copied Old
Picture by a parameter coordinate (see EHNLineAttachmentRetraction).
The same finite bound therefore survives one attachment unchanged,
but this lemma does not claim one global shadow for different HJ lines.
-/

namespace StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness

universe u v
variable {L : Language.{u}}
variable {UA VB W V P : Type v}

/-- Uniform strict functional weak-tree witnesses for all exact finite
sets of size at most n. Projected history predicates are arbitrary
and refer to the fixed control part carrier P. -/
def AtMost
    (A : Structure L UA) (Base : Structure L VB)
    (C : Structure L W) (part : W → P) (n : ℕ) : Prop :=
  ∀ S : Finset W, S.card ≤ n →
    ∀ history : List (Set P),
      SetAmbientRelativeWeakTreeWitness
        A Base C part (↑S : Set W) history

/-- Any EHN shadow commuting with the ORIGINAL control labels preserves
the exact n-VERTEX strict functional weak-tree locality invariant.

The cardinal calculation is performed on the literal Finset image
S.image q. No generated closure hull is introduced anywhere. -/
theorem AtMost.pullback_ehn_commutingParts
    {A : Structure L UA} {Base : Structure L VB}
    {C : Structure L W} {D : Structure L V}
    [DecidableEq V]
    (pC : W → P) (pD : V → P)
    (q : W → V)
    (hq : C.IsEHNHomomorphismEmbedding D q)
    (hParts : ∀ x, pC x = pD (q x))
    (hA : A.Irreducible)
    (n : ℕ)
    (hD : AtMost A Base D pD n) :
    AtMost A Base C pC n := by
  intro S hS history
  let I : Finset V := S.image q
  have hImage : (↑I : Set V) = q '' (↑S : Set W) := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
      exact ⟨x, hx, hxy⟩
    · rintro ⟨x, hx, rfl⟩
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hICard : I.card ≤ n :=
    (Finset.card_image_le).trans hS
  have hOld : SetAmbientRelativeWeakTreeWitness
      A Base D pD (q '' (↑S : Set W)) history := by
    have hTmp := hD I hICard history
    rw [hImage] at hTmp
    exact hTmp
  exact StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness.pullback_ehn_commutingParts
    pC pD q hq hParts hA (↑S : Set W) history hOld

/-- On any genuinely function-closed finite test, the same n-bound
yields an ORIGINAL-2019 partial homomorphism-embedding into a strict
full-functional Base-tree target. The cardinal budget stays at
|S|, not at the size of the function-closure of S. -/
theorem AtMost.closed_test
    {A : Structure L UA} {Base : Structure L VB}
    {C : Structure L W} {p : W → P}
    {n : ℕ}
    (h : AtMost A Base C p n)
    (S : Finset W) (hCard : S.card ≤ n)
    (hClosed : C.IsClosed (↑S : Set W))
    (history : List (Set P)) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : (↑S : Set W) → Z,
        IsOriginalPartialHomomorphismEmbedding
          (C.induce (↑S : Set W) hClosed) Target f ∧
        SetAmbientACopyIntersections A C Target
          (↑S : Set W) f ∧
        SetRespectsProjectedHistory p
          (↑S : Set W) f history :=
  (h S hCard history).closed_test hClosed

end StructuralRamsey.Structure.SetAmbientRelativeWeakTreeWitness
