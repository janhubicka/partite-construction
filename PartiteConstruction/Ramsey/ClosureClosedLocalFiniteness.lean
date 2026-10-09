import PartiteConstruction.Ramsey.ClosureClosedCompletionRank
import PartiteConstruction.Ramsey.CopywiseRamseyTransfer
import PartiteConstruction.Ramsey.CompatibleClassCompletion

/-! # The proposed closed-substructure local completion axiom

This is an EXPLICIT corrected convention, not a theorem identifying it
with literal Definition 2.17. Maps protect closed U-irreducible tests.
The class-membership premise tests only closed U-irreducibles, whereas
the n-vertex completion premise still tests EVERY exact induced subset,
including nonclosed ones. A weak test has its own positive completion map
which protects its closed irreducible substructures.

The original witness C0 need not be U-closed. The cutoff n is fixed for
B,C0 before constructing C and is never recomputed from a later picture.
The rank endpoint below proves all local-axiom premises from explicit
construction data and transfers the arrow. It does NOT construct that
rank-controlled picture or prove the missing rank increment.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V W P : Type v}

/-- Only closed substructures are required to inherit membership. -/
def ClosedUHereditary
    (K : StructureClass.{u,v} (L := L)) (rules : ClosureDescription L) : Prop :=
  ∀ {X Y : Type v} (A : RelStructure L X) (B : RelStructure L Y),
    K B → IsUClosed rules A → Embedding A B → K A

/-- Corrected (4b): membership for closed U-irreducible induced tests.
Embeddings retain the original test carrier, including empty tests. -/
def ClosedUIrreduciblesIn
    (K : StructureClass.{u,v} (L := L)) (rules : ClosureDescription L)
    (C : RelStructure L V) : Prop :=
  ∀ {X : Type v} (Test : RelStructure L X),
    IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test C → K Test

/-- Closed-copy coverage implies the corrected membership condition
using ONLY closed hereditariness, not full relational hereditariness. -/
theorem ClosedUIrreduciblesIn.of_copy_coverage
    {K : StructureClass.{u,v} (L := L)} {rules : ClosureDescription L}
    (hHer : ClosedUHereditary K rules)
    (B : RelStructure L W) (hB : K B) (C : RelStructure L V)
    (hCover : ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test C → Nonempty (Embedding Test B)) :
    ClosedUIrreduciblesIn K rules C := by
  intro X Test hClosed hIrred e
  obtain ⟨d⟩ := hCover Test hClosed hIrred e
  exact hHer Test B hB hClosed d

/-- A genuine K-member satisfies corrected (4b). In particular, the
lack of singleton K-members does not force the candidate to be empty. -/
theorem ClosedUIrreduciblesIn.of_mem
    {K : StructureClass.{u,v} (L := L)} {rules : ClosureDescription L}
    (hHer : ClosedUHereditary K rules)
    (C : RelStructure L V) (hC : K C) :
    ClosedUIrreduciblesIn K rules C := by
  intro X Test hClosed _ e
  exact hHer Test C hC hClosed e

/-- Corrected test membership restricts to arbitrary weak sources. -/
theorem ClosedUIrreduciblesIn.pullback_embedding
    {K : StructureClass.{u,v} (L := L)} {rules : ClosureDescription L}
    {C : RelStructure L V} {D : RelStructure L W}
    (hC : ClosedUIrreduciblesIn K rules C) (e : Embedding D C) :
    ClosedUIrreduciblesIn K rules D := by
  intro X Test hClosed hIrred d
  exact hC Test hClosed hIrred (e.comp d)

/-- Corrected Definition 2.17(4), at ONE fixed B,C0,n. The candidate C
is closed; its n-vertex tests need not be. No closedness of C0 is assumed.
The conclusion is the original B-copywise completion condition. -/
def ClosedULocalCompletionAt
    (K : StructureClass.{u,v} (L := L)) (rules : ClosureDescription L)
    (B : RelStructure L W) (C0 : RelStructure L P) (n : ℕ) : Prop :=
  ∀ {X : Type v} [Finite X] (C : RelStructure L X),
    IsUClosed rules C →
    (C0.Irreducible ∧ ∃ p : X → P,
      IsClosedUHomomorphismEmbedding rules C C0 p) →
    ClosedUIrreduciblesIn K rules C →
    (∀ S : Finset X, S.card ≤ n →
      HasClosedUKCompletion K rules (C.induce (↑S : Set X))) →
    HasCopywiseCompletion K B C

/-- Increasing the tested cutoff strengthens the antecedent, hence
preserves a fixed local-completion implication. Includes cutoff zero. -/
theorem ClosedULocalCompletionAt.mono
    {K : StructureClass.{u,v} (L := L)} {rules : ClosureDescription L}
    {B : RelStructure L W} {C0 : RelStructure L P} {n m : ℕ}
    (h : ClosedULocalCompletionAt K rules B C0 n) (hnm : n ≤ m) :
    ClosedULocalCompletionAt K rules B C0 m := by
  intro X hX C hC hProj hTests hSmall
  exact h C hC hProj hTests (fun S hS => hSmall S (hS.trans hnm))

/-- The proposed multiamalgamation hypotheses with the closed-test
repair coordinated in (4a), (4b), and (4c). R's Ramsey and irreducibility
properties are supplied separately when stating a main theorem.
This definition asserts no construction or Ramsey implication. -/
structure ClosedUMultiamalgamationClass
    (R K : StructureClass.{u,v} (L := L)) (rules : ClosureDescription L) : Prop where
  subset : ∀ {X : Type v} (C : RelStructure L X), K C → R C
  finite : ∀ {X : Type v} (C : RelStructure L X), K C → Finite X
  closed : ∀ {X : Type v} (C : RelStructure L X), K C → IsUClosed rules C
  hereditary : ClosedUHereditary K rules
  strong : HasFiniteStrongAmalgamation K
  localCompletion : ∀ {X Y : Type v} [Finite X] [Finite Y]
    (B : RelStructure L X) (C0 : RelStructure L Y),
    K B → R C0 → ∃ n : ℕ, ClosedULocalCompletionAt K rules B C0 n

/-- Discharge the corrected local axiom from closed generating-rank
control and actual closed-test coverage. The exact weak S, not its hull,
is tested in (4c); its completion is obtained by restricting the hull map. -/
theorem ClosedULocalCompletionAt.of_rank_and_coverage
    {K : StructureClass.{u,v} (L := L)} {rules : ClosureDescription L}
    (B : RelStructure L W) (C0 : RelStructure L P) (C : RelStructure L V)
    [Finite V] (n : ℕ)
    (hLocal : ClosedULocalCompletionAt K rules B C0 n)
    (hHer : ClosedUHereditary K rules) (hB : K B)
    (hC : IsUClosed rules C) (hC0 : C0.Irreducible)
    (p : V → P) (hp : IsClosedUHomomorphismEmbedding rules C C0 p)
    (hCover : ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test C → Nonempty (Embedding Test B))
    (hRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (C.induce T) → USize rules (C.induce T) ≤ n →
      HasClosedUKCompletion K rules (C.induce T)) :
    HasCopywiseCompletion K B C := by
  apply hLocal C hC ⟨hC0, p, hp⟩
  · exact ClosedUIrreduciblesIn.of_copy_coverage hHer B hB C hCover
  · intro S hS
    exact HasClosedUKCompletion.of_closed_USize rules C hC n hRank S hS

/-- Final Ramsey transfer for the corrected closed-test local axiom.
All construction data remain explicit: no missing rank step is assumed
under a theorem name or hidden in an unproved instance. -/
theorem ramsey_of_closedLocalCompletionAt_rank_and_coverage
    {K : StructureClass.{u,v} (L := L)} {rules : ClosureDescription L}
    (A : RelStructure L U) (B : RelStructure L W)
    (C0 : RelStructure L P) (C : RelStructure L V)
    [Finite V] (n : ℕ) (κ : Type*) [Nonempty κ]
    (hLocal : ClosedULocalCompletionAt K rules B C0 n)
    (hHer : ClosedUHereditary K rules) (hB : K B)
    (hC : IsUClosed rules C) (hC0 : C0.Irreducible)
    (p : V → P) (hp : IsClosedUHomomorphismEmbedding rules C C0 p)
    (hCover : ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test C → Nonempty (Embedding Test B))
    (hRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (C.induce T) → USize rules (C.induce T) ≤ n →
      HasClosedUKCompletion K rules (C.induce T))
    (hArrow : StructuralRamsey.Arrow A B C κ) :
    ∃ (X : Type v) (_ : Finite X) (D : RelStructure L X),
      K D ∧ StructuralRamsey.Arrow A B D κ := by
  exact arrow_of_BCopywiseCompletion_inClass hArrow
    (ClosedULocalCompletionAt.of_rank_and_coverage B C0 C n
      hLocal hHer hB hC hC0 p hp hCover hRank)

end StructuralRamsey.RelStructure
