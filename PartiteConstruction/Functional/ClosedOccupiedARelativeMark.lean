import PartiteConstruction.Functional.ProtectedAMarkWeakPullback
import PartiteConstruction.Functional.OccupiedAlphaMark
import PartiteConstruction.Functional.AmbientRelativeWeakTreeHistoryGlue
import PartiteConstruction.Functional.FullFreeAmalgam

/-!
# Genuine functional relative labelled extension over a CLOSED partial A-boundary

This proves the native function-language analogue of the RELATIONAL
relative-labelled predecessor step whenever the occupied selected
A-boundary H is truly function-closed in A.

Given an ordinary strict FULL-functional Base-tree weak witness for
the EXACT projected control test I, use the actual ambient A-copy
intersection certificate to obtain an old target mark A↪T.
On H={a | alpha(a)∈I} that mark agrees with the test map.
Because H is function-closed, A.induce H is a FULL functional
substructure of A; freely attach ONE fresh Base-copy along the
two FULL embeddings of A.induce H into T and Base.

This is a STRICT genuine full-functional Base-tree, not a loose or
relational tree. The new full marked A copy agrees with I on
the occupied H, while all its unoccupied vertices are FRESH.
Singleton projected histories rule out accidental target hits
inside H, yielding an EXACT full protected A mark on I.

No additional source vertices or generated closure are introduced,
and no singleton-function, global domain reflection, or false
uniform protected-mark predecessor is assumed. The missing
nonclosed-H case remains the true weak U-root completion problem.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {UA VB P : Type v}

/-- Strict functional relative completion with a safe full A-mark
for the exact weak control test I, PROVIDED the occupied
alpha(A)-boundary is function-closed in A.

A fresh Base-copy is attached over the COMPLETE occupied A-root,
which is a legitimate FULL functional gluing root precisely because
of hClosed. The target mark's unoccupied vertices are fresh and
therefore cannot identify different projected weak-test parts. -/
theorem SetAmbientRelativeWeakTreeWitness.protected_of_closedOccupiedA
    {A : Structure L UA} {Base : Structure L VB}
    {D : Structure L P}
    (eAB : Embedding A Base)
    (hBase : Base.Irreducible)
    (alpha : Embedding A D)
    (I : Set P)
    (hClosed : A.IsClosed {a : UA | alpha a ∈ I})
    (history : List (Set P))
    (hSingletons : ∀ q : P, Set.singleton q ∈ history)
    (h : SetAmbientRelativeWeakTreeWitness
      A Base D (id : P → P) I history) :
    SetAmbientProtectedWeakTreeWitness
      A Base alpha D (id : P → P) I history := by
  classical
  obtain ⟨Z, T, hTree, f, hWeak, hCopies, hHist⟩ := h
  obtain ⟨mark, hMarkContained, hAgree⟩ := hCopies alpha
  let H : Set UA := {a : UA | alpha a ∈ I}
  let Root : Structure L H := A.induce H hClosed
  let inc : Embedding Root A := Structure.inclusion A H hClosed
  let rL : Embedding Root T := mark.comp inc
  let rR : Embedding Root Base := eAB.comp inc
  let Tplus : Structure L
      (FreeAmalgam.Vertex Root T Base rL rR) :=
    FreeAmalgam.amalgam Root T Base rL rR
  let jL : Embedding T Tplus :=
    FreeAmalgam.leftEmbedding Root T Base rL rR
  let jR : Embedding Base Tplus :=
    FreeAmalgam.rightEmbedding Root T Base rL rR
  have hFree : IsFreeAmalgam rL rR jL jR :=
    FreeAmalgam.isFreeAmalgam Root T Base rL rR
  have hContainedL : rL.ContainedInIrreducible := by
    obtain ⟨X, E, hIrred, emb, hSub⟩ := hMarkContained
    refine ⟨X, E, hIrred, emb, ?_⟩
    intro z
    exact hSub z.1
  have hContainedR : rR.ContainedInIrreducible := by
    refine ⟨VB, Base, hBase, Embedding.id Base, ?_⟩
    intro z
    exact ⟨rR z, rfl⟩
  have hBTree : TreeAmalgam Base _ Tplus :=
    FreeAmalgam.treeAmalgam Root T Base rL rR
      Base hTree
      (TreeAmalgam.copy (Embedding.id Base) (fun b => ⟨b, rfl⟩))
      hContainedL hContainedR
  let fNew : I → FreeAmalgam.Vertex Root T Base rL rR :=
    jL ∘ f
  let freshMark : Embedding A Tplus := jR.comp eAB
  have hTrace : ProtectedAMark alpha (id : P → P)
      I fNew freshMark := by
    intro x a
    constructor
    · intro hHit
      have hEq : jL (f x) = jR (eAB a) := hHit
      obtain ⟨z, hLeft, hRight⟩ :=
        (hFree.overlap (f x) (eAB a)).mp hEq
      have ha : a = z.1 := eAB.injective hRight
      have haI : alpha a ∈ I := by
        rw [ha]
        exact z.2
      have hxy : f x = f ⟨alpha a, haI⟩ := by
        calc
          f x = mark z.1 := hLeft
          _ = mark a := congrArg mark ha.symm
          _ = f ⟨alpha a, haI⟩ := hAgree a haI
      have hSingle := hHist (Set.singleton x.1)
        (hSingletons x.1) x (⟨alpha a, haI⟩ : I) hxy
      have hMember : alpha a ∈ (Set.singleton x.1 : Set P) :=
        hSingle.mp (by change x.1 = x.1; rfl)
      exact (Set.mem_singleton_iff.mp hMember).symm
    · intro hx
      have haI : alpha a ∈ I := by
        rw [← hx]
        exact x.2
      let z : H := ⟨a, haI⟩
      have hGlue :
          jL (mark a) = jR (eAB a) :=
        (hFree.overlap (mark a) (eAB a)).mpr ⟨z, rfl, rfl⟩
      have hOwned :
          jL (f ⟨alpha a, haI⟩) = jR (eAB a) := by
        calc
          jL (f ⟨alpha a, haI⟩) =
              jL (mark a) := congrArg jL (hAgree a haI).symm
          _ = jR (eAB a) := hGlue
      have hSame : x = (⟨alpha a, haI⟩ : I) :=
        Subtype.ext hx
      change jL (f x) = jR (eAB a)
      rw [hSame]
      exact hOwned
  have hMarkContainedNew : freshMark.ContainedInIrreducible := by
    refine ⟨VB, Base, hBase, jR, ?_⟩
    intro a
    exact ⟨eAB a, rfl⟩
  exact ⟨_, Tplus, hBTree, fNew,
    hWeak.postcomp_full jL,
    hCopies.postcomp_full jL,
    hHist.postcomp_full jL,
    freshMark, hMarkContainedNew, hTrace⟩

end StructuralRamsey.Structure
