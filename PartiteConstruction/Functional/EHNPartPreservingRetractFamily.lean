import PartiteConstruction.Functional.EHNPartPreservingRetractAppend

/-!
# Track D: finite actual-support attachment histories with a common EHN shadow

The strict weak-tree preservation lemma for one native FULL functional
attachment can be iterated over any prescribed finite family of genuine
FULL support maps, provided all those maps are split by ONE initial
part-preserving EHN shadow q0: Core -> Old.

Each attachment extends that shadow, fixes the newly copied Old stage,
and preserves the original core map and control part projection.
This is an actual, inductively constructed list of full native
UnitAttachD systems, not merely a predicate asserted of an unknown
stage. Source function outputs remain part-transversal.

The necessary splitting premise is explicit on EACH member of the list.
When the list consists of Hales--Jewett lines sharing one parameter
coordinate it follows by coordinate evaluation. Without this premise
the three-line C7 gives a counterexample to the naive strict-tree
invariant. No maximal mixed-root existence is claimed here.
-/

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {P V W I UA VB : Type v}

/-- Iterate genuine native full support attachments through a finite
family, retaining one compatible EHN shadow of the ORIGINAL old stage.

The list is attached recursively, in reverse order, which has no
effect on the existence conclusion. Every step uses the SAME
function-closed selected support S and its original full embedding.

Neither the full source Test nor any tested weak vertex set is replaced
by a closure hull; the q-splitting hypothesis is required on the exact
support, not merely on its part image. -/
theorem attachFamily_splitRoot_EHN_retraction
    (B : System L P V)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (Core : System L P W)
    (q0 : W → V)
    (hq0 : Core.toStructure.IsEHNHomomorphismEmbedding B.toStructure q0)
    (hPart0 : ∀ x : W, B.part (q0 x) = Core.part x)
    (maps : I → FunctionalPartite.Embedding (B.induce S hS) Core)
    (xs : List I)
    (hSplit : ∀ i ∈ xs, ∀ x : S, q0 (maps i x) = x.1) :
    ∃ (X : Type v) (T : System L P X)
      (j : FunctionalPartite.Embedding Core T)
      (q : X → V),
      T.toStructure.IsEHNHomomorphismEmbedding B.toStructure q ∧
      (∀ x : X, B.part (q x) = T.part x) ∧
      (∀ x : W, q (j x) = q0 x) := by
  induction xs with
  | nil =>
      exact ⟨W, Core, FunctionalPartite.Embedding.id Core,
        q0, hq0, hPart0, fun _ => rfl⟩
  | cons i xs ih =>
      have hTail : ∀ k ∈ xs, ∀ x : S, q0 (maps k x) = x.1 := by
        intro k hk x
        exact hSplit k (List.mem_cons_of_mem i hk) x
      obtain ⟨X, T, j, q, hq, hPart, hCore⟩ := ih hTail
      let f : FunctionalPartite.Embedding (B.induce S hS) T :=
        j.comp (maps i)
      have hFix : ∀ x : S, q (f x) = x.1 := by
        intro x
        calc
          q (f x) = q (j (maps i x)) := rfl
          _ = q0 (maps i x) := hCore (maps i x)
          _ = x.1 := hSplit i (by simp) x
      obtain ⟨r, hr, hrCore, _hrCopy, hrPart⟩ :=
        unitAttach_extend_partPreserving_EHN_retraction
          B S hS T f q hq hFix hPart
      let C := Attachment.UnitAttachD B S hS T f
      let step : FunctionalPartite.Embedding T C :=
        Attachment.coreEmbedding B S hS T (fun _ : PUnit.{v+1} => f)
      refine ⟨_, C, step.comp j, r, hr, hrPart, ?_⟩
      intro x
      calc
        r ((step.comp j) x) =
            r (Attachment.unitCoreEmbedding B S hS T f (j x)) := rfl
        _ = q (j x) := hrCore (j x)
        _ = q0 x := hCore x

/-- Every finite history whose full support attachments share a
compatible EHN shadow preserves the SAME rank bound n on all exact
weak tests, all actual ambient A-copy intersections and all finite
projected histories.

The witnesses are full functional strict Base-trees. No additional
compatibility assumption is hidden in the final conclusion: the exact
support-splitting premise remains visible in the theorem hypotheses. -/
theorem attachFamily_splitRoot_strictWeakHistory
    [DecidableEq V]
    (B : System L P V)
    (S : Set V) (hS : B.toStructure.IsClosed S)
    (Core : System L P W)
    (q0 : W → V)
    (hq0 : Core.toStructure.IsEHNHomomorphismEmbedding B.toStructure q0)
    (hPart0 : ∀ x : W, B.part (q0 x) = Core.part x)
    (maps : I → FunctionalPartite.Embedding (B.induce S hS) Core)
    (xs : List I)
    (hSplit : ∀ i ∈ xs, ∀ x : S, q0 (maps i x) = x.1)
    (TestA : Structure L UA) (Base : Structure L VB)
    (hTestA : TestA.Irreducible)
    (n : ℕ)
    (hOld : SetAmbientRelativeWeakTreeWitness.AtMost
      TestA Base B.toStructure B.part n) :
    ∃ (X : Type v) (T : System L P X)
      (j : FunctionalPartite.Embedding Core T),
      SetAmbientRelativeWeakTreeWitness.AtMost
        TestA Base T.toStructure T.part n := by
  obtain ⟨X, T, j, q, hq, hPart, _hj⟩ :=
    attachFamily_splitRoot_EHN_retraction
      B S hS Core q0 hq0 hPart0 maps xs hSplit
  refine ⟨X, T, j, ?_⟩
  exact SetAmbientRelativeWeakTreeWitness.AtMost.pullback_ehn_commutingParts
    T.part B.part q hq (fun x => (hPart x).symm)
    hTestA n hOld

end StructuralRamsey.FunctionalPartite.EHN
