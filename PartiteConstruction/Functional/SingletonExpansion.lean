import PartiteConstruction.Structure.Basic
import Mathlib.Data.Finset.Sort

/-! # Canonical singleton expansion of finite ordered function fibres

For a finite ordered structure, replace every set-valued function symbol F by
finitely many symbols (F,i).  The i-th symbol contains exactly the i-th
smallest value of the original fibre, when that value exists.

This is the reduction needed in the recursive partite construction: once the
number of ranks is at least the size of the target structure, every original
fibre is recovered as the union of its ranked singleton fibres.  A full
order-preserving embedding maps each fibre bijectively and hence preserves
rank, so it lifts canonically to the ranked expansion.
-/
namespace StructuralRamsey

universe u v w

namespace Language

/-- Replace each set-valued function symbol by `n` ranked copies. -/
def rankFunctions (L : Language.{u}) (n : ℕ) : Language.{u} where
  RelSymbol := L.RelSymbol
  FuncSymbol := L.FuncSymbol × Fin n
  relArity := L.relArity
  funcArity F := L.funcArity F.1

@[simp] theorem rankFunctions_relArity
    (L : Language.{u}) (n : ℕ) (R : L.RelSymbol) :
    (L.rankFunctions n).relArity R = L.relArity R := rfl

@[simp] theorem rankFunctions_funcArity
    (L : Language.{u}) (n : ℕ) (F : L.FuncSymbol) (i : Fin n) :
    (L.rankFunctions n).funcArity (F, i) = L.funcArity F := rfl

end Language

namespace Structure

variable {L : Language.{u}} {V : Type v} {W : Type w}

/-- Every function fibre has at most one value. -/
def SingletonValued (A : Structure L V) : Prop :=
  ∀ F x y z, y ∈ A.func F x → z ∈ A.func F x → y = z

/-- The finite set underlying one function fibre. -/
noncomputable def fiberFinset
    (A : Structure L V) [Finite V]
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → V) : Finset V := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  exact Finset.univ.filter (fun y => y ∈ A.func F x)

@[simp] theorem mem_fiberFinset
    (A : Structure L V) [Finite V]
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → V) (y : V) :
    y ∈ fiberFinset A F x ↔ y ∈ A.func F x := by
  classical
  simp [fiberFinset]

/-- The i-th ordered value of a fibre, represented as an empty set or a
singleton.  The existential proof merely records that rank i exists. -/
noncomputable def rankedValue
    (A : Structure L V) [LinearOrder V] [Finite V]
    (n : ℕ) (F : L.FuncSymbol) (i : Fin n)
    (x : Fin (L.funcArity F) → V) : Set V := by
  classical
  let s := fiberFinset A F x
  exact {y | ∃ h : i.val < s.card,
    y = s.orderEmbOfFin rfl ⟨i.val, h⟩}

/-- Canonical finite ranked expansion of a finite ordered structure. -/
noncomputable def rankExpand
    (A : Structure L V) [LinearOrder V] [Finite V]
    (n : ℕ) : Structure (L.rankFunctions n) V where
  rel R x := A.rel R x
  func Fi x := rankedValue A n Fi.1 Fi.2 x

/-- Every newly introduced function symbol is singleton-valued. -/
theorem rankExpand_singletonValued
    (A : Structure L V) [LinearOrder V] [Finite V] (n : ℕ) :
    SingletonValued (rankExpand A n) := by
  classical
  intro Fi x y z hy hz
  rcases Fi with ⟨F, i⟩
  change y ∈ rankedValue A n F i x at hy
  change z ∈ rankedValue A n F i x at hz
  unfold rankedValue at hy hz
  rcases hy with ⟨hylt, hy⟩
  rcases hz with ⟨hzlt, hz⟩
  let s := fiberFinset A F x
  have hij :
      (⟨i.val, hylt⟩ : Fin s.card) =
        ⟨i.val, hzlt⟩ := by
    apply Fin.ext
    rfl
  calc
    y = s.orderEmbOfFin rfl ⟨i.val, hylt⟩ := hy
    _ = s.orderEmbOfFin rfl ⟨i.val, hzlt⟩ := by rw [hij]
    _ = z := hz.symm

/-- A ranked singleton is always a value of the original set-valued
function. -/
theorem rankedValue_subset
    (A : Structure L V) [LinearOrder V] [Finite V]
    (n : ℕ) (F : L.FuncSymbol) (i : Fin n)
    (x : Fin (L.funcArity F) → V) :
    rankedValue A n F i x ⊆ A.func F x := by
  classical
  intro y hy
  unfold rankedValue at hy
  rcases hy with ⟨hi, rfl⟩
  exact (mem_fiberFinset A F x
    (fiberFinset A F x |>.orderEmbOfFin rfl ⟨i.val, hi⟩)).mp
      (Finset.orderEmbOfFin_mem (fiberFinset A F x) rfl
        ⟨i.val, hi⟩)

/-- If `n` bounds a fibre, every original value occurs in one ranked
singleton. -/
theorem mem_rankedValue_of_mem
    (A : Structure L V) [LinearOrder V] [Finite V]
    (n : ℕ) (F : L.FuncSymbol)
    (x : Fin (L.funcArity F) → V)
    (hcard : (fiberFinset A F x).card ≤ n)
    {y : V} (hy : y ∈ A.func F x) :
    ∃ i : Fin n, y ∈ rankedValue A n F i x := by
  classical
  let s := fiberFinset A F x
  have hys : y ∈ s := (mem_fiberFinset A F x y).mpr hy
  let q : s := ⟨y, hys⟩
  let j : Fin s.card := (s.orderIsoOfFin rfl).symm q
  let i : Fin n := ⟨j.val, lt_of_lt_of_le j.isLt hcard⟩
  refine ⟨i, ?_⟩
  change ∃ h : i.val < s.card,
    y = s.orderEmbOfFin rfl ⟨i.val, h⟩
  refine ⟨j.isLt, ?_⟩
  have happ : (s.orderIsoOfFin rfl) j = q :=
    (s.orderIsoOfFin rfl).apply_symm_apply q
  have hval : ((s.orderIsoOfFin rfl) j).1 = y :=
    congrArg Subtype.val happ
  change y = s.orderEmbOfFin rfl j
  exact hval.symm.trans (Finset.coe_orderIsoOfFin_apply s rfl j)

/-- A full embedding maps the finite source fibre exactly onto the target
fibre. -/
theorem fiberFinset_image
    {A : Structure L V} {B : Structure L W}
    [Finite V] [Finite W]
    (e : Embedding A B)
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → V) :
    Finset.map e.toFunctionEmbedding (fiberFinset A F x) =
      fiberFinset B F (e ∘ x) := by
  classical
  ext y
  constructor
  · intro hy
    rcases Finset.mem_map.mp hy with ⟨a, ha, rfl⟩
    have ha' : a ∈ A.func F x :=
      (mem_fiberFinset A F x a).mp ha
    have himg : e a ∈ imageSet e (A.func F x) :=
      ⟨a, ha', rfl⟩
    rw [e.map_func F x] at himg
    exact (mem_fiberFinset B F (e ∘ x) (e a)).mpr himg
  · intro hy
    have hy' : y ∈ B.func F (e ∘ x) :=
      (mem_fiberFinset B F (e ∘ x) y).mp hy
    have himg : y ∈ imageSet e (A.func F x) := by
      rw [e.map_func F x]
      exact hy'
    rcases himg with ⟨a, ha, rfl⟩
    exact Finset.mem_map.mpr
      ⟨a, (mem_fiberFinset A F x a).mpr ha, rfl⟩

theorem fiberFinset_card_eq
    {A : Structure L V} {B : Structure L W}
    [Finite V] [Finite W]
    (e : Embedding A B)
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → V) :
    (fiberFinset B F (e ∘ x)).card =
      (fiberFinset A F x).card := by
  classical
  rw [← fiberFinset_image e F x]
  simpa using
    (Finset.card_map e.toFunctionEmbedding
      (s := fiberFinset A F x))

/-- An order-preserving full embedding sends the i-th value of a fibre to the
i-th value of the target fibre. -/
theorem map_orderedFiber
    {A : Structure L V} {B : Structure L W}
    [LinearOrder V] [LinearOrder W] [Finite V] [Finite W]
    (e : Embedding A B) (hmono : StrictMono e)
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → V)
    (i : Fin (fiberFinset A F x).card) :
    e ((fiberFinset A F x).orderEmbOfFin rfl i) =
      (fiberFinset B F (e ∘ x)).orderEmbOfFin
        (fiberFinset_card_eq e F x) i := by
  classical
  let sA := fiberFinset A F x
  let sB := fiberFinset B F (e ∘ x)
  have himage : Finset.map e.toFunctionEmbedding sA = sB := by
    simpa [sA, sB] using fiberFinset_image e F x
  have hcard : sB.card = sA.card := by
    simpa [sA, sB] using fiberFinset_card_eq e F x
  have hmem :
      ∀ j : Fin sA.card,
        e (sA.orderEmbOfFin rfl j) ∈ sB := by
    intro j
    rw [← himage]
    exact Finset.mem_map.mpr
      ⟨sA.orderEmbOfFin rfl j,
        Finset.orderEmbOfFin_mem sA rfl j, rfl⟩
  have hinc :
      StrictMono (fun j : Fin sA.card =>
        e (sA.orderEmbOfFin rfl j)) :=
    hmono.comp (sA.orderEmbOfFin rfl).strictMono
  have hu :
      (fun j : Fin sA.card => e (sA.orderEmbOfFin rfl j)) =
        fun j => sB.orderEmbOfFin hcard j :=
    Finset.orderEmbOfFin_unique hcard hmem hinc
  simpa [sA, sB, hcard] using congrFun hu i

/-- Ranked singleton fibres are preserved exactly by an order-preserving full
embedding. -/
theorem image_rankedValue
    {A : Structure L V} {B : Structure L W}
    [LinearOrder V] [LinearOrder W] [Finite V] [Finite W]
    (e : Embedding A B) (hmono : StrictMono e)
    (n : ℕ) (F : L.FuncSymbol) (i : Fin n)
    (x : Fin (L.funcArity F) → V) :
    imageSet e (rankedValue A n F i x) =
      rankedValue B n F i (e ∘ x) := by
  classical
  let sA := fiberFinset A F x
  let sB := fiberFinset B F (e ∘ x)
  have hcard : sB.card = sA.card := by
    simpa [sA, sB] using fiberFinset_card_eq e F x
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    change z ∈ {q | ∃ h : i.val < sA.card,
      q = sA.orderEmbOfFin rfl ⟨i.val, h⟩} at hz
    rcases hz with ⟨hiA, hz⟩
    have hiB : i.val < sB.card := by
      simpa [hcard] using hiA
    change e z ∈ {q | ∃ h : i.val < sB.card,
      q = sB.orderEmbOfFin rfl ⟨i.val, h⟩}
    refine ⟨hiB, ?_⟩
    have hmap := map_orderedFiber e hmono F x
      (⟨i.val, hiA⟩ : Fin sA.card)
    have htarget :
        sB.orderEmbOfFin hcard (⟨i.val, hiA⟩ : Fin sA.card) =
          sB.orderEmbOfFin rfl (⟨i.val, hiB⟩ : Fin sB.card) := by
      exact (Finset.orderEmbOfFin_eq_orderEmbOfFin_iff).2 rfl
    calc
      e z = e (sA.orderEmbOfFin rfl
        (⟨i.val, hiA⟩ : Fin sA.card)) := congrArg e hz
      _ = sB.orderEmbOfFin hcard
        (⟨i.val, hiA⟩ : Fin sA.card) := by
          simpa [sA, sB] using hmap
      _ = sB.orderEmbOfFin rfl
        (⟨i.val, hiB⟩ : Fin sB.card) := htarget
  · intro hy
    change y ∈ {q | ∃ h : i.val < sB.card,
      q = sB.orderEmbOfFin rfl ⟨i.val, h⟩} at hy
    rcases hy with ⟨hiB, hy⟩
    have hiA : i.val < sA.card := by
      simpa [hcard] using hiB
    let z := sA.orderEmbOfFin rfl (⟨i.val, hiA⟩ : Fin sA.card)
    refine ⟨z, ?_, ?_⟩
    · change z ∈ {q | ∃ h : i.val < sA.card,
        q = sA.orderEmbOfFin rfl ⟨i.val, h⟩}
      exact ⟨hiA, rfl⟩
    · have hmap := map_orderedFiber e hmono F x
        (⟨i.val, hiA⟩ : Fin sA.card)
      have htarget :
          sB.orderEmbOfFin hcard (⟨i.val, hiA⟩ : Fin sA.card) =
            sB.orderEmbOfFin rfl (⟨i.val, hiB⟩ : Fin sB.card) := by
        exact (Finset.orderEmbOfFin_eq_orderEmbOfFin_iff).2 rfl
      calc
        e z = sB.orderEmbOfFin hcard
            (⟨i.val, hiA⟩ : Fin sA.card) := by
          simpa [z, sA, sB] using hmap
        _ = sB.orderEmbOfFin rfl
            (⟨i.val, hiB⟩ : Fin sB.card) := htarget
        _ = y := hy.symm

/-- Every order-preserving full embedding lifts canonically to the ranked
singleton expansion. -/
noncomputable def Embedding.rankExpand
    {A : Structure L V} {B : Structure L W}
    [LinearOrder V] [LinearOrder W] [Finite V] [Finite W]
    (e : Embedding A B) (hmono : StrictMono e) (n : ℕ) :
    Embedding (rankExpand A n) (rankExpand B n) where
  toFun := e
  injective := e.injective
  map_rel_iff := e.map_rel_iff
  map_func := by
    rintro ⟨F, i⟩ x
    exact image_rankedValue e hmono n F i x

@[simp] theorem Embedding.rankExpand_apply
    {A : Structure L V} {B : Structure L W}
    [LinearOrder V] [LinearOrder W] [Finite V] [Finite W]
    (e : Embedding A B) (hmono : StrictMono e) (n : ℕ) (x : V) :
    e.rankExpand hmono n x = e x := rfl

/-- The lift with a prescribed underlying map is unique. -/
theorem Embedding.rankExpand_unique
    {A : Structure L V} {B : Structure L W}
    [LinearOrder V] [LinearOrder W] [Finite V] [Finite W]
    (e : Embedding A B) (hmono : StrictMono e) (n : ℕ)
    (g : Embedding (Structure.rankExpand A n) (Structure.rankExpand B n))
    (hg : ∀ x, g x = e x) :
    g = e.rankExpand hmono n := by
  apply Embedding.ext
  intro x
  exact hg x

/-- Every fibre of a finite structure has size at most its carrier. -/
theorem fiberFinset_card_le
    (A : Structure L V) [Fintype V]
    (F : L.FuncSymbol) (x : Fin (L.funcArity F) → V) :
    (fiberFinset A F x).card ≤ Fintype.card V := by
  classical
  apply Finset.card_le_card
  intro y hy
  simp

end Structure
end StructuralRamsey
