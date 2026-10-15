import PartiteConstruction.Structure.WeakSubstructure
import PartiteConstruction.Structure.FreeAmalgam

/-!
# Vertex-exact weak restriction of genuine FULL functional free amalgams

The iterated partite induction must work with weak substructures, not
function-generated closures. This theorem is the direct full-language
analogue of the already-verified relational weak-induced free-amalgam
lemma. All operation fibres are still genuine (possibly multivalued)
sets; a weak subset keeps exactly the outputs inside it.

If C is a FULL free amalgam of Left and Right over Root, then the weak
restriction C|ᵂS to ANY vertex set S is itself the FULL functional free
amalgam of the weak restrictions to the inverse-image side/root sets,
with their canonical full embeddings. No closure hull, assumption of
singleton-valuedness or artificial domain predicates are involved.

The root S∩Root may itself be nonclosed in the ambient C. It is an
honest *weak* substructure, and the exact functional free-amalgam
identities are checked for the weak structures. This is the correct
combinatorial decomposition for the mixed Hales–Jewett Picture step;
it does not by itself supply compatible strict B-tree completions.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {U V W X : Type v}

/-- A full functional embedding restricted to any exact source subset
S and target subset T, provided S is the precise preimage of T.
Neither subset is required to be function-closed. -/
def Embedding.weakRestrictExact
    {A : Structure L U} {B : Structure L V}
    (e : Embedding A B)
    (S : Set U) (T : Set V)
    (hS : ∀ x, x ∈ S ↔ e x ∈ T) :
    Embedding (A.weakInduce S) (B.weakInduce T) where
  toFun := fun x => ⟨e x.1, (hS x.1).mp x.2⟩
  injective := by
    intro x y heq
    apply Subtype.ext
    apply e.injective
    exact congrArg Subtype.val heq
  map_rel_iff := by
    intro R x
    change B.rel R (e ∘ (Subtype.val ∘ x)) ↔
      A.rel R (Subtype.val ∘ x)
    exact e.map_rel_iff R (Subtype.val ∘ x)
  map_func := by
    intro F x
    ext y
    constructor
    · rintro ⟨z, hz, heq⟩
      have heF : e z.1 ∈ B.func F (e ∘ (Subtype.val ∘ x)) := by
        rw [← e.map_func F (Subtype.val ∘ x)]
        exact ⟨z.1, hz, rfl⟩
      have hval : y.1 = e z.1 := (congrArg Subtype.val heq).symm
      change y.1 ∈ B.func F (e ∘ (Subtype.val ∘ x))
      rw [hval]
      exact heF
    · intro hy
      have hyB : y.1 ∈ B.func F (e ∘ (Subtype.val ∘ x)) := hy
      rw [← e.map_func F (Subtype.val ∘ x)] at hyB
      obtain ⟨z, hz, heq⟩ := hyB
      have hzS : z ∈ S := (hS z).mpr (by
        change e z ∈ T
        rw [heq]
        exact y.2)
      refine ⟨(⟨z, hzS⟩ : S), hz, ?_⟩
      apply Subtype.ext
      exact heq


/-- Every arbitrary vertex-exact WEAK restriction of a full functional
free amalgam is again a free amalgam IN THE FUNCTION LANGUAGE of the
weak side and common-root restrictions.

Crucially:
* all four restricted maps are full functional embeddings of WEAK
  structures (not necessarily embeddings of ambient closed structures);
* the root is the exact inverse image of the chosen vertex set, not
  its function-generated closure;
* function output incidences are present iff one of the weak
  sides supplies them, even for set-valued operations.

These are precisely the side/root components of the mixed native
Hales-Jewett Picture induction. The theorem does not assert a strict
tree-completion witness for an arbitrary mixed test. -/
theorem IsFreeAmalgam.weakInduce_withMaps
    {H E F C : Type v}
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR) (S : Set C) :
    let Lset : Set E := iL ⁻¹' S
    let Rset : Set F := iR ⁻¹' S
    let Mset : Set H := (iL.comp sL) ⁻¹' S
    ∃ (mL : Embedding (Root.weakInduce Mset) (Left.weakInduce Lset))
      (mR : Embedding (Root.weakInduce Mset) (Right.weakInduce Rset))
      (jL : Embedding (Left.weakInduce Lset) (Whole.weakInduce S))
      (jR : Embedding (Right.weakInduce Rset) (Whole.weakInduce S)),
      IsFreeAmalgam mL mR jL jR ∧
      (∀ a : Lset, (jL a).1 = iL a.1) ∧
      (∀ b : Rset, (jR b).1 = iR b.1) := by
  classical
  dsimp only
  let Lset : Set E := iL ⁻¹' S
  let Rset : Set F := iR ⁻¹' S
  let Mset : Set H := (iL.comp sL) ⁻¹' S
  have hOverlap (d : H) : iL (sL d) = iR (sR d) :=
    (hFree.overlap (sL d) (sR d)).mpr ⟨d, rfl, rfl⟩
  let mL : Embedding (Root.weakInduce Mset) (Left.weakInduce Lset) :=
    sL.weakRestrictExact Mset Lset (by intro x; rfl)
  let mR : Embedding (Root.weakInduce Mset) (Right.weakInduce Rset) :=
    sR.weakRestrictExact Mset Rset (by
      intro x
      change iL (sL x) ∈ S ↔ iR (sR x) ∈ S
      rw [hOverlap x])
  let jL : Embedding (Left.weakInduce Lset) (Whole.weakInduce S) :=
    iL.weakRestrictExact Lset S (by intro x; rfl)
  let jR : Embedding (Right.weakInduce Rset) (Whole.weakInduce S) :=
    iR.weakRestrictExact Rset S (by intro x; rfl)
  refine ⟨mL, mR, jL, jR, ?_, ?_, ?_⟩
  · constructor
    · intro z
      rcases hFree.covers z.1 with ⟨a, ha⟩ | ⟨b, hb⟩
      · have haS : a ∈ Lset := by
          change iL a ∈ S
          rw [← ha]
          exact z.2
        exact Or.inl ⟨⟨a, haS⟩, by
          apply Subtype.ext
          exact ha⟩
      · have hbS : b ∈ Rset := by
          change iR b ∈ S
          rw [← hb]
          exact z.2
        exact Or.inr ⟨⟨b, hbS⟩, by
          apply Subtype.ext
          exact hb⟩
    · intro a b
      constructor
      · intro hab
        have hraw : iL a.1 = iR b.1 := congrArg Subtype.val hab
        obtain ⟨d, had, hbd⟩ := (hFree.overlap a.1 b.1).mp hraw
        have hdS : d ∈ Mset := by
          change iL (sL d) ∈ S
          rw [← had]
          exact a.2
        refine ⟨(⟨d, hdS⟩ : Mset), ?_, ?_⟩
        · apply Subtype.ext
          exact had
        · apply Subtype.ext
          exact hbd
      · rintro ⟨d, had, hbd⟩
        have hleft : a.1 = sL d.1 := congrArg Subtype.val had
        have hright : b.1 = sR d.1 := congrArg Subtype.val hbd
        apply Subtype.ext
        change iL a.1 = iR b.1
        rw [hleft, hright]
        exact hOverlap d.1
    · intro R z
      constructor
      · intro hz
        have hzWhole : Whole.rel R (Subtype.val ∘ z) := hz
        rcases (hFree.rel_iff R (Subtype.val ∘ z)).mp hzWhole with
          ⟨x, hx, hzx⟩ | ⟨x, hx, hzx⟩
        · have hxS : ∀ i, x i ∈ Lset := by
            intro i
            change iL (x i) ∈ S
            have hi := congrFun hzx i
            rw [← hi]
            exact (z i).2
          let xs : Fin (L.relArity R) → Lset :=
            fun i => ⟨x i, hxS i⟩
          refine Or.inl ⟨xs, hx, ?_⟩
          funext i
          apply Subtype.ext
          exact congrFun hzx i
        · have hxS : ∀ i, x i ∈ Rset := by
            intro i
            change iR (x i) ∈ S
            have hi := congrFun hzx i
            rw [← hi]
            exact (z i).2
          let xs : Fin (L.relArity R) → Rset :=
            fun i => ⟨x i, hxS i⟩
          refine Or.inr ⟨xs, hx, ?_⟩
          funext i
          apply Subtype.ext
          exact congrFun hzx i
      · rintro (⟨xs, hx, hzx⟩ | ⟨xs, hx, hzx⟩)
        · change Whole.rel R (Subtype.val ∘ z)
          apply (hFree.rel_iff R (Subtype.val ∘ z)).mpr
          refine Or.inl ⟨Subtype.val ∘ xs, hx, ?_⟩
          funext i
          exact congrArg Subtype.val (congrFun hzx i)
        · change Whole.rel R (Subtype.val ∘ z)
          apply (hFree.rel_iff R (Subtype.val ∘ z)).mpr
          refine Or.inr ⟨Subtype.val ∘ xs, hx, ?_⟩
          funext i
          exact congrArg Subtype.val (congrFun hzx i)
    · intro Func x y
      constructor
      · intro hy
        have hyWhole :
            y.1 ∈ Whole.func Func (Subtype.val ∘ x) := hy
        rcases (hFree.func_iff Func (Subtype.val ∘ x) y.1).mp hyWhole with
          ⟨args, out, hout, hargs, htarget⟩ |
          ⟨args, out, hout, hargs, htarget⟩
        · have hargsS : ∀ i, args i ∈ Lset := by
            intro i
            change iL (args i) ∈ S
            have hi := congrFun hargs i
            rw [← hi]
            exact (x i).2
          have houtS : out ∈ Lset := by
            change iL out ∈ S
            rw [← htarget]
            exact y.2
          let as : Fin (L.funcArity Func) → Lset :=
            fun i => ⟨args i, hargsS i⟩
          let bs : Lset := ⟨out, houtS⟩
          refine Or.inl ⟨as, bs, hout, ?_, ?_⟩
          · funext i
            apply Subtype.ext
            exact congrFun hargs i
          · apply Subtype.ext
            exact htarget
        · have hargsS : ∀ i, args i ∈ Rset := by
            intro i
            change iR (args i) ∈ S
            have hi := congrFun hargs i
            rw [← hi]
            exact (x i).2
          have houtS : out ∈ Rset := by
            change iR out ∈ S
            rw [← htarget]
            exact y.2
          let as : Fin (L.funcArity Func) → Rset :=
            fun i => ⟨args i, hargsS i⟩
          let bs : Rset := ⟨out, houtS⟩
          refine Or.inr ⟨as, bs, hout, ?_, ?_⟩
          · funext i
            apply Subtype.ext
            exact congrFun hargs i
          · apply Subtype.ext
            exact htarget
      · rintro (⟨args, out, hout, hargs, htarget⟩ |
          ⟨args, out, hout, hargs, htarget⟩)
        · have hx : Subtype.val ∘ x =
              iL ∘ (Subtype.val ∘ args) := by
            funext i
            exact congrArg Subtype.val (congrFun hargs i)
          have hy : y.1 = iL out.1 :=
            congrArg Subtype.val htarget
          change y.1 ∈ Whole.func Func (Subtype.val ∘ x)
          rw [hx, hy]
          apply (hFree.func_iff Func
            (iL ∘ (Subtype.val ∘ args)) (iL out.1)).mpr
          exact Or.inl ⟨Subtype.val ∘ args, out.1, hout, rfl, rfl⟩
        · have hx : Subtype.val ∘ x =
              iR ∘ (Subtype.val ∘ args) := by
            funext i
            exact congrArg Subtype.val (congrFun hargs i)
          have hy : y.1 = iR out.1 :=
            congrArg Subtype.val htarget
          change y.1 ∈ Whole.func Func (Subtype.val ∘ x)
          rw [hx, hy]
          apply (hFree.func_iff Func
            (iR ∘ (Subtype.val ∘ args)) (iR out.1)).mpr
          exact Or.inr ⟨Subtype.val ∘ args, out.1, hout, rfl, rfl⟩
  · intro a
    rfl
  · intro b
    rfl

/-- The same exact weak functional free-amalgam decomposition, dropping
only the coordinate equations for the canonical side maps. -/
theorem IsFreeAmalgam.weakInduce
    {H E F C : Type v}
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR) (S : Set C) :
    let Lset : Set E := iL ⁻¹' S
    let Rset : Set F := iR ⁻¹' S
    let Mset : Set H := (iL.comp sL) ⁻¹' S
    ∃ (mL : Embedding (Root.weakInduce Mset) (Left.weakInduce Lset))
      (mR : Embedding (Root.weakInduce Mset) (Right.weakInduce Rset))
      (jL : Embedding (Left.weakInduce Lset) (Whole.weakInduce S))
      (jR : Embedding (Right.weakInduce Rset) (Whole.weakInduce S)),
      IsFreeAmalgam mL mR jL jR := by
  obtain ⟨mL, mR, jL, jR, hRestricted, _, _⟩ :=
    hFree.weakInduce_withMaps S
  exact ⟨mL, mR, jL, jR, hRestricted⟩

end StructuralRamsey.Structure
