import PartiteConstruction.Ramsey.CopywiseFreeFold

/-! # Strong-amalgamation completion of strict free trees

Theorem 2.18 of *All those Ramsey classes* requires a final
completion of a sparse Ramsey structure in a strongly amalgamating
class K which need NOT be free. A key case is U = empty.

This file proves, independently of any Ramsey argument, that every
strict tree of copies of an irreducible B in a finite strongly
amalgamating class K admits a FINITE K-completion relative to its
B-copies. The target may add mixed relations and is not assumed to be
a free amalgam. The completion map need not be a global homomorphism.

The proof uses the strict tree's irreducible containers to realize
each gluing root inside a B-copy. The previous stage's copywise
completion therefore restricts to a genuine embedding of that root
in K, which can be strongly amalgamated in the target category.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB W X Y : Type v}

/-- Finite strong amalgamation in a class of finite relational structures.
We do not assume closure under free amalgams, nor any JEP axiom. The
usual hereditary assumption is included. -/
structure FiniteStrongAmalgamationClass
    (K : StructureClass.{u,v} (L := L)) : Prop where
  hereditary :
    ∀ {A B : Type v} {S : RelStructure L A}
      {T : RelStructure L B},
      K T → Embedding S T → K S
  strong :
    ∀ {H A B : Type v}
      {Root : RelStructure L H}
      {Left : RelStructure L A} {Right : RelStructure L B}
      (hLeft : K Left) (hRight : K Right)
      (sL : Embedding Root Left) (sR : Embedding Root Right),
      ∃ (Z : Type v) (_ : Finite Z) (Target : RelStructure L Z),
        K Target ∧
        ∃ (jL : Embedding Left Target)
          (jR : Embedding Right Target),
          (∀ d, jL (sL d) = jR (sR d)) ∧
          (∀ a b, jL a = jR b →
            ∃ d, a = sL d ∧ b = sR d)

/-- Every strict gluing root, whose image is contained in an
irreducible source part, has a genuine embedding into a K-target of
a B-copywise completion. The map on the whole source tree does not
need to be globally injective, a homomorphism, or a full embedding. -/
theorem CopywiseCompletion.on_strictRoot
    {VB H W X : Type v}
    {Base : RelStructure L VB} {Root : RelStructure L H}
    {T : RelStructure L W} {Target : RelStructure L X}
    (hTree : TreeAmalgam Base W T)
    (r : Embedding Root T)
    (hContainer : r.ContainedInIrreducible)
    (f : W → X)
    (hCopy : CopywiseCompletion Base T Target f) :
    ∃ e : Embedding Root Target, ∀ d, e d = f (r d) := by
  classical
  obtain ⟨S,hS,hrangeS⟩ := hContainer
  let inc : Embedding (T.induce S) T := inclusion T S
  obtain ⟨β,hβ⟩ :=
    hTree.irreducible_contained_in_copy hS inc
  have hrange : ∀ d : H, ∃ b : VB, r d = β b := by
    intro d
    obtain ⟨b,hb⟩ := hβ ⟨r d,hrangeS d⟩
    exact ⟨b,hb⟩
  let eB : Embedding Root Base := r.factorThroughRange β hrange
  obtain ⟨β',hβ'⟩ := hCopy β
  refine ⟨β'.comp eB, ?_⟩
  intro d
  calc
    (β'.comp eB) d = β' (eB d) := rfl
    _ = f (β (eB d)) := hβ' (eB d)
    _ = f (r d) := by
      apply congrArg f
      exact (Classical.choose_spec (hrange d)).symm

/-- FINITE, class-preserving completion of every strict B-tree,
relative to its B-copies, in any finite strongly amalgamating class
containing an irreducible B. In fact the proof only needs compatible
target amalgams: the stronger overlap clause is not used. -/
theorem TreeAmalgam.copywiseCompletion_inStrongClass
    {K : StructureClass.{u,v} (L := L)}
    {Base : RelStructure L VB}
    [Finite VB]
    (hBase : Base.Irreducible)
    (hK : FiniteStrongAmalgamationClass K)
    (hB : K Base)
    {T : RelStructure L W}
    (hTree : TreeAmalgam Base W T) :
    HasCopywiseCompletion K Base T := by
  classical
  induction hTree with
  | copy hIso =>
      let h : Embedding Base T := hIso.toEmbedding
      have hrange : ∀ t : W, ∃ b : VB,
          (Embedding.id T) t = h b := by
        intro t
        refine ⟨hIso.toEquiv.symm t, ?_⟩
        change t = hIso.toEquiv (hIso.toEquiv.symm t)
        exact (hIso.toEquiv.apply_symm_apply t).symm
      let eInv : Embedding T Base :=
        (Embedding.id T).factorThroughRange h hrange
      refine ⟨VB,inferInstance,Base,hB,eInv,?_⟩
      intro β
      exact ⟨eInv.comp β,fun _ => rfl⟩
  | @glue W₁ W₂ H W T₁ T₂ Root T
      h₁ h₂ sL sR hcL hcR iL iR hfree ihL ihR =>
      obtain ⟨X,hX,D₁,hK₁,fL,hfL⟩ := ihL
      obtain ⟨Y,hY,D₂,hK₂,fR,hfR⟩ := ihR
      obtain ⟨eL,heL⟩ :=
        CopywiseCompletion.on_strictRoot h₁ sL hcL fL hfL
      obtain ⟨eR,heR⟩ :=
        CopywiseCompletion.on_strictRoot h₂ sR hcR fR hfR
      obtain ⟨Z,hZ,Q,hQ,jL,jR,hRoot,_hStrong⟩ :=
        hK.strong hK₁ hK₂ eL eR
      have hcompat :
          ∀ d, (jL ∘ fL) (sL d) = (jR ∘ fR) (sR d) := by
        intro d
        change jL (fL (sL d)) = jR (fR (sR d))
        calc
          jL (fL (sL d)) = jL (eL d) :=
            congrArg jL (heL d).symm
          _ = jR (eR d) := hRoot d
          _ = jR (fR (sR d)) :=
            congrArg jR (heR d)
      let p : W → Z :=
        hfree.compatibleFold (jL ∘ fL) (jR ∘ fR) hcompat
      have hp : CopywiseCompletion Base T Q p :=
        CopywiseCompletion.fold_free hBase hfree
          fL fR hfL hfR jL jR hcompat
      exact ⟨Z,hZ,Q,hQ,p,hp⟩

end StructuralRamsey.RelStructure
