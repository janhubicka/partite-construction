import PartiteConstruction.Functional.WeakOperations
import PartiteConstruction.Structure.WeakSubstructure
import PartiteConstruction.Structure.GeneratedWeakHomImage

/-! # Direct function-language iteration: closed supports, weak vertex tests

In the iterated partite construction all intermediate stages are genuine
set-valued-function structures.  The projection is weak globally, but
preimages of genuine closed substructures are closed.  Hence the selected
support in each Picture step is a genuine closed substructure.  The
function-valued Hales--Jewett partite lemma and full free attachment operate
directly in the function language.

There is no need for the U-closed *graph-embedding* apparatus of the recursive
partite construction: its job is to control relational stages that need not
represent structures with functions until the final repair.

The *local induction* nevertheless tests arbitrary weak substructures,
represented exactly by induced substructures of function graphs.  No closure
hull of such a test is taken when measuring its number of vertices.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U : Type v}

/-- Relational graph irreducibility of an actual function structure implies
irreducibility for the full function-language free-amalgamation definition.
Every relation or function-output tuple localizes entirely to one side of
a full functional free amalgam. -/
theorem irreducible_of_graph_irreducible
    (A : Structure L U) (hgraph : A.graph.Irreducible) :
    A.Irreducible := by
  intro H E F C Dsrc Esrc Fsrc Csrc sE sF iE iF hfree e
  classical
  by_cases hleft : ∀ a : U, ∃ t : E, e a = iE t
  · exact Or.inl hleft
  · right
    push_neg at hleft
    obtain ⟨x, hx⟩ := hleft
    intro y
    by_contra hright
    have hxy : x ≠ y := by
      intro hEq
      subst y
      rcases hfree.covers (e x) with ⟨a, ha⟩ | ⟨b, hb⟩
      · exact hx a ha
      · exact hright ⟨b, hb⟩
    obtain ⟨R, z, i, j, hz, hzi, hzj⟩ := hgraph hxy
    cases R with
    | inl R =>
      have ht : Csrc.rel R (e ∘ z) :=
        (e.map_rel_iff R z).mpr hz
      rcases (hfree.rel_iff R (e ∘ z)).mp ht with
        ⟨a, ha, heq⟩ | ⟨b, hb, heq⟩
      · apply hx (a i)
        calc
          e x = e (z i) := congrArg e hzi.symm
          _ = iE (a i) := congrFun heq i
      · apply hright
        refine ⟨b j, ?_⟩
        calc
          e y = e (z j) := congrArg e hzj.symm
          _ = iF (b j) := congrFun heq j
    | inr F0 =>
      let args : Fin (L.funcArity F0) → U := fun k => z k.castSucc
      let out : U := z (Fin.last (L.funcArity F0))
      have hs : out ∈ A.func F0 args := hz
      have ht : e out ∈ Csrc.func F0 (e ∘ args) := by
        rw [← e.map_func F0 args]
        exact ⟨out, hs, rfl⟩
      rcases (hfree.func_iff F0 (e ∘ args) (e out)).mp ht with
        ⟨a, b, hb, hargs, hout⟩ | ⟨a, b, hb, hargs, hout⟩
      · have hall : ∀ k : Fin (L.funcArity F0 + 1),
            ∃ t : E, e (z k) = iE t := by
          intro k
          refine Fin.lastCases ?_ (fun l => ?_) k
          · exact ⟨b, hout⟩
          · exact ⟨a l, congrFun hargs l⟩
        exact hx (hall i).choose
          ((congrArg e hzi).symm.trans (hall i).choose_spec)
      · have hall : ∀ k : Fin (L.funcArity F0 + 1),
            ∃ t : F, e (z k) = iF t := by
          intro k
          refine Fin.lastCases ?_ (fun l => ?_) k
          · exact ⟨b, hout⟩
          · exact ⟨a l, congrFun hargs l⟩
        exact hright ⟨(hall j).choose,
          (congrArg e hzj).symm.trans (hall j).choose_spec⟩

end StructuralRamsey.Structure

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure
universe u v
variable {L : Language.{u}} {P U V : Type v}

/-- Direct functional Picture supports are actual closed substructures.
Their induced partite restriction retains the weak irreducible projection
invariant.  No U-closed relational embedding hypothesis is present. -/
theorem directSupport_and_restriction
    (B : System L P V)
    (D : Structure L P)
    (hB : B.WeaklyPartiteOver D)
    (A : Structure L U)
    (α : Structure.Embedding A D) :
    let S := B.support α.toFunctionEmbedding
    B.toStructure.IsClosed S ∧
      (B.weakRestrict D hB.1 A α).WeaklyPartiteOver A := by
  exact ⟨B.weak_support_closed D hB.1 A α,
    B.weakRestrict_invariant D hB.1 A α hB⟩

/-- Since the selected support is closed under real function values, the
direct full restriction agrees with the weak restriction of the same
carrier, for all relation and function symbols. -/
def directSupportInduceToWeak
    (B : System L P V)
    (D : Structure L P)
    (hB : B.WeaklyPartiteOver D)
    (A : Structure L U)
    (α : Structure.Embedding A D) :
    Structure.Embedding
      (B.toStructure.induce (B.support α.toFunctionEmbedding)
        (B.weak_support_closed D hB.1 A α))
      (B.toStructure.weakInduce (B.support α.toFunctionEmbedding)) :=
  B.toStructure.induceToWeak _
    (B.weak_support_closed D hB.1 A α)

end StructuralRamsey.FunctionalPartite.EHN
