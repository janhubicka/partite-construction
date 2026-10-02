import PartiteConstruction.Iterated.FinalAttachment

/-! # Finite completion of irreducible substructures

This file isolates property (3) of the sparsening theorem.  Starting from a
finite structure \`Orig\`, assume every irreducible induced substructure embeds
into the base structure \`Base\`.  By successively freely attaching copies of
\`Base\` over the images of all irreducible subsets of \`Orig\`, one obtains a
finite extension in which every irreducible substructure is contained in a
copy of \`Base\`.

The proof tracks a localization invariant: every irreducible in an
intermediate stage either lies in the embedded original core or is already
contained in one of the attached base copies.
-/
namespace StructuralRamsey.RelStructure.FinalCompletion

open FreeAmalgam

universe u v
variable {L : RelLanguage.{u}}
variable {O B C H : Type v}
variable {Orig : RelStructure L O} {Base : RelStructure L B}
variable {Current : RelStructure L C} {D : RelStructure L H}

/-- Every irreducible substructure of the current stage is either contained
in the embedded original core or already contained in a copy of the base. -/
def CoreOrBase
    (j : Embedding Orig Current) : Prop :=
  ∀ (S : Set C), (Current.induce S).Irreducible →
    (∀ z : S, ∃ o : O, z.1 = j o) ∨
    ∃ β : Embedding Base Current, ∀ z : S, ∃ b : B, z.1 = β b

/-- The trivial stage satisfies the localization invariant. -/
theorem coreOrBase_id :
    CoreOrBase (Orig := Orig) (Base := Base) (Embedding.id Orig) := by
  intro S _
  left
  intro z
  exact ⟨z.1, rfl⟩

/-- Localization is preserved by attaching one fresh base copy. -/
theorem coreOrBase_amalgam
    {fCurrent : Embedding D Current} {fBase : Embedding D Base}
    {j : Embedding Orig Current}
    (h : CoreOrBase (Orig := Orig) (Base := Base) j) :
    CoreOrBase (Orig := Orig) (Base := Base)
      ((leftEmbedding D Current Base fCurrent fBase).comp j) := by
  classical
  let Whole := amalgam D Current Base fCurrent fBase
  intro S hS
  let inc : Embedding (Whole.induce S) Whole :=
    inclusion Whole S
  have hsplit :=
    Attachment.irreducible_core_or_copy
      (B := Base) (S := support D Current Base fCurrent fBase)
      (D := Current)
      (f := fun _ : Unit =>
        overlapEmbedding D Current Base fCurrent fBase) S hS
  rcases hsplit with hcore | ⟨i, hcopy⟩
  · have hrange :
        ∀ z : S, ∃ c : C,
          inc z = leftEmbedding D Current Base fCurrent fBase c := by
      intro z
      rcases hcore z with ⟨c, hc⟩
      exact ⟨c, hc⟩
    let eS : Embedding (Whole.induce S) Current :=
      inc.factorThroughRange
        (leftEmbedding D Current Base fCurrent fBase) hrange
    let Rng : Set C := Set.range eS
    have hRng : (Current.induce Rng).Irreducible :=
      hS.range_embedding eS
    rcases h Rng hRng with hOrig | ⟨β, hβ⟩
    · left
      intro z
      let q : Rng := ⟨eS z, ⟨z, rfl⟩⟩
      obtain ⟨o, ho⟩ := hOrig q
      refine ⟨o, ?_⟩
      have hz := Classical.choose_spec (hrange z)
      change
        z.1 =
          leftEmbedding D Current Base fCurrent fBase (j o)
      calc
        z.1 = inc z := rfl
        _ = leftEmbedding D Current Base fCurrent fBase (eS z) := hz
        _ = leftEmbedding D Current Base fCurrent fBase (j o) :=
          congrArg (leftEmbedding D Current Base fCurrent fBase) ho
    · right
      refine ⟨(leftEmbedding D Current Base fCurrent fBase).comp β, ?_⟩
      intro z
      let q : Rng := ⟨eS z, ⟨z, rfl⟩⟩
      obtain ⟨b, hb⟩ := hβ q
      refine ⟨b, ?_⟩
      have hz := Classical.choose_spec (hrange z)
      change
        z.1 =
          leftEmbedding D Current Base fCurrent fBase (β b)
      calc
        z.1 = inc z := rfl
        _ = leftEmbedding D Current Base fCurrent fBase (eS z) := hz
        _ = leftEmbedding D Current Base fCurrent fBase (β b) :=
          congrArg (leftEmbedding D Current Base fCurrent fBase) hb
  · right
    have hi : i = () := Subsingleton.elim _ _
    subst i
    refine ⟨rightEmbedding D Current Base fCurrent fBase, ?_⟩
    intro z
    rcases hcopy z with ⟨b, hb⟩
    exact ⟨b, hb⟩

/-- Copies already guaranteed for the irreducible members of a finite list of
original subsets. -/
def CoversIrrList
    (j : Embedding Orig Current) (sets : List (Finset O)) : Prop :=
  ∀ (S : Finset O), S ∈ sets →
    (Orig.induce (↑S : Set O)).Irreducible →
    ∃ β : Embedding Base Current,
      ∀ z : ↥(↑S : Set O), ∃ b : B, j z.1 = β b

/-- Adding a base copy over one original subset adds that subset to the list
of covered irreducibles and preserves all previous coverage. -/
theorem coversIrrList_amalgam
    {j : Embedding Orig Current}
    (sets : List (Finset O)) (S₀ : Finset O)
    (fBase : Embedding (Orig.induce (↑S₀ : Set O)) Base)
    (h : CoversIrrList (Orig := Orig) (Base := Base) j sets) :
    let fCurrent : Embedding (Orig.induce (↑S₀ : Set O)) Current :=
      j.comp (inclusion Orig (↑S₀ : Set O))
    CoversIrrList (Orig := Orig) (Base := Base)
      ((leftEmbedding (Orig.induce (↑S₀ : Set O)) Current Base
        fCurrent fBase).comp j)
      (S₀ :: sets) := by
  classical
  dsimp
  let D₀ := Orig.induce (↑S₀ : Set O)
  let fCurrent : Embedding D₀ Current :=
    j.comp (inclusion Orig (↑S₀ : Set O))
  let l := leftEmbedding D₀ Current Base fCurrent fBase
  let r := rightEmbedding D₀ Current Base fCurrent fBase
  intro S hmem hS
  simp only [List.mem_cons] at hmem
  rcases hmem with hEq | hmem
  · subst S
    refine ⟨r, ?_⟩
    intro z
    refine ⟨fBase z, ?_⟩
    change l (j z.1) = r (fBase z)
    exact left_right_overlap D₀ Current Base fCurrent fBase z
  · obtain ⟨β, hβ⟩ := h S hmem hS
    refine ⟨l.comp β, ?_⟩
    intro z
    obtain ⟨b, hb⟩ := hβ z
    exact ⟨b, congrArg l hb⟩

/-- Process an arbitrary finite list of subsets, attaching a base copy exactly
at the irreducible members. -/
theorem completion_list
    [Finite O] [Finite B]
    (sets : List (Finset O))
    (hEmb : ∀ (S : Finset O), S ∈ sets →
      (Orig.induce (↑S : Set O)).Irreducible →
      Nonempty (Embedding (Orig.induce (↑S : Set O)) Base)) :
    ∃ (Y : Type v) (_ : Finite Y) (C' : RelStructure L Y)
      (j : Embedding Orig C'),
      CoreOrBase (Orig := Orig) (Base := Base) j ∧
      CoversIrrList (Orig := Orig) (Base := Base) j sets := by
  classical
  induction sets with
  | nil =>
      refine ⟨O, inferInstance, Orig, Embedding.id Orig, coreOrBase_id, ?_⟩
      intro S hmem
      simp at hmem
  | cons S₀ sets ih =>
      have hEmbTail :
          ∀ (S : Finset O), S ∈ sets →
            (Orig.induce (↑S : Set O)).Irreducible →
            Nonempty (Embedding (Orig.induce (↑S : Set O)) Base) := by
        intro S hmem hS
        exact hEmb S (List.mem_cons_of_mem S₀ hmem) hS
      obtain ⟨Y, hY, C', j, hCore, hCov⟩ := ih hEmbTail
      letI : Finite Y := hY
      by_cases hS₀ : (Orig.induce (↑S₀ : Set O)).Irreducible
      · obtain ⟨fBase⟩ := hEmb S₀ (by simp) hS₀
        let D₀ := Orig.induce (↑S₀ : Set O)
        let fCurrent : Embedding D₀ C' :=
          j.comp (inclusion Orig (↑S₀ : Set O))
        let Whole := amalgam D₀ C' Base fCurrent fBase
        let j' : Embedding Orig Whole :=
          (leftEmbedding D₀ C' Base fCurrent fBase).comp j
        have hCore' : CoreOrBase (Orig := Orig) (Base := Base) j' := by
          exact coreOrBase_amalgam
            (fCurrent := fCurrent) (fBase := fBase) hCore
        have hCov' :
            CoversIrrList (Orig := Orig) (Base := Base) j' (S₀ :: sets) := by
          simpa [D₀, fCurrent, Whole, j'] using
            (coversIrrList_amalgam
              (Orig := Orig) (Base := Base) (Current := C')
              sets S₀ fBase hCov)
        exact ⟨_, inferInstance, Whole, j', hCore', hCov'⟩
      · refine ⟨Y, hY, C', j, hCore, ?_⟩
        intro S hmem hS
        simp only [List.mem_cons] at hmem
        rcases hmem with hEq | hmem
        · subst S
          exact (hS₀ hS).elim
        · exact hCov S hmem hS

/-- If every irreducible induced substructure of a finite original structure
embeds into the base, there is a finite extension in which every irreducible
substructure extends to a base copy. -/
theorem exists_completion
    [Fintype O] [DecidableEq O] [Finite B]
    (hEmb : ∀ (S : Set O), (Orig.induce S).Irreducible →
      Nonempty (Embedding (Orig.induce S) Base)) :
    ∃ (Y : Type v) (_ : Finite Y) (C' : RelStructure L Y)
      (j : Embedding Orig C'),
      IrreduciblesExtendTo Base C' := by
  classical
  let sets : List (Finset O) := (Finset.univ.powerset).toList
  have hEmbList :
      ∀ (S : Finset O), S ∈ sets →
        (Orig.induce (↑S : Set O)).Irreducible →
        Nonempty (Embedding (Orig.induce (↑S : Set O)) Base) := by
    intro S _ hS
    exact hEmb (↑S : Set O) hS
  obtain ⟨Y, hY, C', j, hCore, hCov⟩ :=
    completion_list (Orig := Orig) (Base := Base) sets hEmbList
  refine ⟨Y, hY, C', j, ?_⟩
  intro T hT
  rcases hCore T hT with hOrig | hBase
  · let inc : Embedding (C'.induce T) C' := inclusion C' T
    let eT : Embedding (C'.induce T) Orig :=
      inc.factorThroughRange j hOrig
    let Rng : Set O := Set.range eT
    have hRng : (Orig.induce Rng).Irreducible :=
      hT.range_embedding eT
    let S : Finset O := Finset.univ.filter (fun o => o ∈ Rng)
    have hSset : (↑S : Set O) = Rng := by
      ext o
      simp [S]
    have hSirr : (Orig.induce (↑S : Set O)).Irreducible := by
      rw [hSset]
      exact hRng
    have hSmem : S ∈ sets := by
      simp [sets]
    obtain ⟨β, hβ⟩ := hCov S hSmem hSirr
    refine ⟨β, ?_⟩
    intro z
    have heTmem : eT z ∈ (↑S : Set O) := by
      rw [hSset]
      exact ⟨z, rfl⟩
    let q : ↥(↑S : Set O) := ⟨eT z, heTmem⟩
    obtain ⟨b, hb⟩ := hβ q
    refine ⟨b, ?_⟩
    have hz := Classical.choose_spec (hOrig z)
    calc
      z.1 = inc z := rfl
      _ = j (eT z) := hz
      _ = β b := hb
  · exact hBase

end StructuralRamsey.RelStructure.FinalCompletion
