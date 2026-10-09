import PartiteConstruction.Ramsey.ClosureTwoCopyIntrinsicObstruction
import PartiteConstruction.Ramsey.ClosureWeakTestIntrinsicObstruction
import PartiteConstruction.Ramsey.ClosureUSize2019
import PartiteConstruction.Ramsey.Basic

/-! # Four-vertex obstruction to the literal 2019 U-irreducible coverage

We use the unary root predicate P and binary closure relation R from the
fully checked two-copy regression.  A is a singleton with no relations.
B has the P-root 0, its R-output 1 and two further free non-P vertices,
2 and 3.  All three non-root vertices form distinct copies of A.

The universal no-C statement is proved WITHOUT choosing a finite
C0: for any U-closed C whose every intrinsic U-irreducible induced test
embeds in B, a B-copy creates a missing-output test C \\ {output}. The
coverage embeds this test into B. Together with the one P-root, this
gives an injection from all A-copies into the four vertices of B.

Colour the four possible labels in two groups of size two. Every
B-copy contains three distinct A-copies, so no B-copy is monochromatic.

A complete refutation of the existential Lemma 2.29 also requires an
explicit C0 satisfying the Ramsey and U-substructure premises; that
is a separate small finite construction and will not be assumed here.
-/

namespace StructuralRamsey.RelStructure.FourPointIntrinsicObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.RelStructure.TwoCopyIntrinsicObstruction

universe v

private abbrev One : RelStructure Lang (Fin 1) where
  rel _ _ := False

private abbrev Four : RelStructure Lang (Fin 4) where
  rel
    | false, t => t ⟨0, by decide⟩ = 0
    | true, t => t ⟨0, by decide⟩ = 0 ∧ t ⟨1, by decide⟩ = 1

private abbrev rootInFour : Embedding Root Four where
  toFun := fun _ => 0
  injective := by
    intro x y _
    exact Subsingleton.elim x y
  map_rel_iff := by
    intro R x
    cases R with
    | false =>
      change ((0 : Fin 4) = 0) ↔ (false = false)
      simp
    | true =>
      change (((0 : Fin 4) = 0) ∧ ((0 : Fin 4) = 1)) ↔ (true = false)
      simp

/-- A has no embedded P-roots and is U-closed. -/
theorem one_isUClosed : IsUClosed rules One := by
  intro r hr
  have hrule : r = rule := by
    simpa [rules] using hr
  subst r
  constructor
  · intro t ht
    exact False.elim ht
  · intro e
    have hP : Root.rel false (fun _ : Fin 1 => (0 : Fin 1)) := by
      decide
    have hA : One.rel false (e ∘ (fun _ : Fin 1 => (0 : Fin 1))) :=
      (e.map_rel_iff false (fun _ : Fin 1 => (0 : Fin 1))).mpr hP
    exact False.elim hA

/-- B is U-closed, with the unique closure output of root 0 being 1. -/
theorem four_isUClosed : IsUClosed rules Four := by
  intro r hr
  have hrule : r = rule := by
    simpa [rules] using hr
  subst r
  constructor
  · intro t ht
    refine ⟨rootInFour, ?_⟩
    intro k
    fin_cases k
    exact ht.1
  · intro e
    have he : e = rootInFour := by
      apply Embedding.ext
      intro k
      fin_cases k
      have hp : Four.rel false
          (e ∘ (fun _ : Fin 1 => (0 : Fin 1))) :=
        (e.map_rel_iff false (fun _ : Fin 1 => 0)).mpr (by decide)
      change e 0 = (0 : Fin 4) at hp
      exact hp
    rw [he]
    refine ⟨![0, 1], ⟨?_, ?_⟩, ?_⟩
    · decide
    · intro k
      fin_cases k
      rfl
    · intro t ht
      funext j
      fin_cases j
      · exact ht.1.1
      · exact ht.1.2

/-- Each non-root vertex of B carries a full copy of A. -/
private def oneAt (i : Fin 4) (hi : i ≠ 0) : Embedding One Four where
  toFun := fun _ => i
  injective := by
    intro x y _
    exact Subsingleton.elim x y
  map_rel_iff := by
    intro R x
    cases R with
    | false =>
      change (i = (0 : Fin 4)) ↔ False
      simp [hi]
    | true =>
      change (i = (0 : Fin 4) ∧ i = (1 : Fin 4)) ↔ False
      simp [hi]

private def bit (i : Fin 4) : Bool := decide (i.val < 2)

/-- Among three distinct values in Fin 4, at least two have different
bits under the 2+2 partition. -/
private theorem bit_noThree (i j k : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ (bit i = bit j ∧ bit i = bit k) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all [bit]

variable {W : Type} {C : RelStructure Lang W}

/-- A copied root in a U-closed C has a unique existing R-output.
Removing that output yields an intrinsically U-irreducible weak test,
regardless of all other vertices of C. -/
private theorem removedOutput_irreducible
    (hC : IsUClosed rules C)
    (b : Embedding Four C) :
    IsUIrreducible rules (C.induce {w : W | w ≠ b 1}) := by
  classical
  let e : Embedding Root C := b.comp rootInFour
  let S : Set W := {w | w ≠ b 1}
  have hro : b 0 ≠ b 1 := by
    intro h
    exact (by decide : (0 : Fin 4) ≠ 1) (b.injective h)
  have hr : ∀ k : Fin rule.rootSize, e k ∈ S := by
    intro k
    fin_cases k
    exact hro
  obtain ⟨tC, hCtuple, hUnique⟩ :=
    (hC rule (by simp [rules])).2 e
  let tB : Fin 2 → Fin 4 := ![0, 1]
  have htB : C.rel true (b ∘ tB) :=
    (b.map_rel_iff true tB).mpr (by decide)
  have hRootB :
      ∀ k : Fin rule.rootSize,
        (b ∘ tB) (k.castLE rule.rootLE) = e k := by
    intro k
    fin_cases k
    rfl
  have htBC : b ∘ tB = tC :=
    hUnique (b ∘ tB) ⟨htB, hRootB⟩
  have hMissing :
      ∀ t : Fin (Lang.arity rule.symbol) → W,
        C.rel rule.symbol t →
        (∀ k : Fin rule.rootSize,
          t (k.castLE rule.rootLE) = e k) →
        ∃ j : Fin (Lang.arity rule.symbol), t j ∉ S := by
    intro t ht htRoot
    have htEq : t = tC :=
      hUnique t ⟨ht, htRoot⟩
    have hto : t (1 : Fin 2) = b 1 := by
      calc
        t 1 = tC 1 := congrFun htEq 1
        _ = (b ∘ tB) 1 := congrFun htBC.symm 1
        _ = b 1 := rfl
    refine ⟨1, ?_⟩
    simpa [S, hto]
  have hRule : rule ∈ rules := by simp [rules]
  exact IsUIrreducible.of_missing_tuple_in_weak_test
    rule hRule e S hr hMissing

/-- No A-copy can meet the unique P-root of an embedded B-copy:
full embeddings reflect the P predicate. -/
private theorem oneCopy_ne_root
    (b : Embedding Four C) (a : Embedding One C) :
    a 0 ≠ b 0 := by
  intro heq
  have hpB : Four.rel false (fun _ : Fin 1 => (0 : Fin 4)) := by
    decide
  have hpC : C.rel false (b ∘ (fun _ : Fin 1 => (0 : Fin 4))) :=
    (b.map_rel_iff false (fun _ : Fin 1 => 0)).mpr hpB
  have hpA : C.rel false (a ∘ (fun _ : Fin 1 => (0 : Fin 1))) := by
    convert hpC using 1
    funext i
    exact heq
  have hp : One.rel false (fun _ : Fin 1 => (0 : Fin 1)) :=
    (a.map_rel_iff false (fun _ : Fin 1 => 0)).mp hpA
  exact hp

/-- Encode an A-copy by a vertex away from the removed R-output.
The only adjustment is to send the removed output to the P-root,
which is never itself the image of an A-copy. -/
private noncomputable def key
    (b : Embedding Four C) (a : Embedding One C) :
    {w : W | w ≠ b 1} := by
  classical
  have hro : b 0 ≠ b 1 := by
    intro h
    exact (by decide : (0 : Fin 4) ≠ 1) (b.injective h)
  by_cases ha : a 0 = b 1
  · exact ⟨b 0, hro⟩
  · exact ⟨a 0, ha⟩

private theorem key_injective
    (b : Embedding Four C) :
    Function.Injective (key b) := by
  intro a a' h
  have hv : a 0 = a' 0 := by
    by_cases ha : a 0 = b 1
    · by_cases ha' : a' 0 = b 1
      · exact ha.trans ha'.symm
      · have he : b 0 = a' 0 := by
          simpa [key, ha, ha'] using congrArg Subtype.val h
        exact False.elim ((oneCopy_ne_root b a') he.symm)
    · by_cases ha' : a' 0 = b 1
      · have he : a 0 = b 0 := by
          simpa [key, ha, ha'] using congrArg Subtype.val h
        exact False.elim ((oneCopy_ne_root b a) he)
      · simpa [key, ha, ha'] using congrArg Subtype.val h
  apply Embedding.ext
  intro i
  fin_cases i
  exact hv

/-- Fundamental nonexistence: no U-closed C can simultaneously have
the two-colour Ramsey arrow for A,B and cover EVERY intrinsically
U-irreducible induced weak test by an embedding into B. -/
theorem no_UClosed_Ramsey_and_intrinsic_coverage
    (hC : IsUClosed rules C)
    (hArrow : StructuralRamsey.Arrow One Four C Bool)
    (hCover : AllIntrinsicUIrreducibleTestsEmbed rules C Four) :
    False := by
  classical
  obtain ⟨b, _⟩ := hArrow (fun _ => false)
  let S : Set W := {w | w ≠ b 1}
  have hUI : IsUIrreducible rules (C.induce S) :=
    removedOutput_irreducible hC b
  obtain ⟨g⟩ := hCover S hUI
  let code : Embedding One C → Fin 4 :=
    fun a => g (key b a)
  have hCodeInjective : Function.Injective code := by
    intro a a' h
    exact key_injective b (g.injective h)
  let χ : Embedding One C → Bool :=
    fun a => bit (code a)
  obtain ⟨b', hMono⟩ := hArrow χ
  let a1 : Embedding One Four :=
    oneAt 1 (by decide)
  let a2 : Embedding One Four :=
    oneAt 2 (by decide)
  let a3 : Embedding One Four :=
    oneAt 3 (by decide)
  have h12 : b'.comp a1 ≠ b'.comp a2 := by
    intro h
    have he : b' 1 = b' 2 :=
      congrArg (fun e : Embedding One C => e (0 : Fin 1)) h
    exact (by decide : (1 : Fin 4) ≠ 2) (b'.injective he)
  have h13 : b'.comp a1 ≠ b'.comp a3 := by
    intro h
    have he : b' 1 = b' 3 :=
      congrArg (fun e : Embedding One C => e (0 : Fin 1)) h
    exact (by decide : (1 : Fin 4) ≠ 3) (b'.injective he)
  have h23 : b'.comp a2 ≠ b'.comp a3 := by
    intro h
    have he : b' 2 = b' 3 :=
      congrArg (fun e : Embedding One C => e (0 : Fin 1)) h
    exact (by decide : (2 : Fin 4) ≠ 3) (b'.injective he)
  exact bit_noThree (code (b'.comp a1))
      (code (b'.comp a2)) (code (b'.comp a3))
      (fun he => h12 (hCodeInjective he))
      (fun he => h13 (hCodeInjective he))
      (fun he => h23 (hCodeInjective he))
      ⟨hMono a1 a2, hMono a1 a3⟩

end StructuralRamsey.RelStructure.FourPointIntrinsicObstruction
