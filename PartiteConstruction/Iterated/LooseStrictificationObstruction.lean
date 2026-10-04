import PartiteConstruction.Iterated.LooseTreeAmalgam
import PartiteConstruction.Iterated.FinalAttachment

/-! # A loose tree which cannot be strictified

For the graph language, let B be the four-vertex path P4.  Strict tree
amalgams of copies of P4 are bipartite, because every strict gluing root is
contained in a graph-irreducible set and the two side 2-colourings can be
aligned on such a root.

In contrast, a loose amalgam of two copies of P4 can glue the same two-point
independent root at distances 3 and 2.  The result contains a 5-cycle.
Hence it has no homomorphism to any strict P4-tree.

This rules out the shortcut “strictify every loose tree”.
-/
namespace StructuralRamsey.RelStructure.LooseNotStrictifiable

universe u

/-- One binary relation, regarded as an undirected graph edge relation. -/
def L : RelLanguage where
  Symbol := Unit
  arity := fun _ => 2

/-- A graph-like structure is two-colourable if every relation tuple has
different endpoint colours. -/
def TwoColorable {V : Type u} (C : RelStructure L V) : Prop :=
  ∃ c : V → Bool, ∀ x : Fin 2 → V, C.rel () x → c (x 0) ≠ c (x 1)

/-- Pull a two-colouring back through a homomorphism. -/
theorem TwoColorable.pullback
    {V W : Type u} {A : RelStructure L V} {B : RelStructure L W}
    (hB : TwoColorable B)
    (f : V → W) (hf : A.IsHomomorphism B f) :
    TwoColorable A := by
  rcases hB with ⟨c, hc⟩
  refine ⟨c ∘ f, ?_⟩
  intro x hx
  have hrel := hf () x hx
  exact hc (f ∘ x) hrel

/-- In a two-coloured binary structure, an irreducible induced set receives
pairwise distinct colours. -/
theorem color_injective_on_irreducible
    {V : Type u} {C : RelStructure L V}
    (c : V → Bool)
    (hc : ∀ x : Fin 2 → V, C.rel () x → c (x 0) ≠ c (x 1))
    (S : Set V) (hS : (C.induce S).Irreducible) :
    Function.Injective (fun x : S => c x.1) := by
  intro x y hcol
  by_contra hxy
  obtain ⟨R, z, i, j, hz, hzi, hzj⟩ := hS hxy
  cases R
  have hrel : C.rel () (Subtype.val ∘ z) := hz
  have hneq := hc (Subtype.val ∘ z) hrel
  have hij : i ≠ j := by
    intro hij
    apply hxy
    calc
      x = z i := hzi.symm
      _ = z j := congrArg z hij
      _ = y := hzj
  fin_cases i <;> fin_cases j
  · exact hij rfl
  · apply hneq
    calc
      c ((Subtype.val ∘ z) 0) = c x.1 := congrArg c (congrArg Subtype.val hzi)
      _ = c y.1 := hcol
      _ = c ((Subtype.val ∘ z) 1) :=
        (congrArg c (congrArg Subtype.val hzj)).symm
  · apply hneq
    symm
    calc
      c ((Subtype.val ∘ z) 1) = c x.1 := congrArg c (congrArg Subtype.val hzi)
      _ = c y.1 := hcol
      _ = c ((Subtype.val ∘ z) 0) :=
        (congrArg c (congrArg Subtype.val hzj)).symm
  · exact hij rfl

/-- If an embedded root is contained in an irreducible set, any proper
two-colouring is injective on the root. -/
theorem root_color_injective
    {D V : Type u} {Root : RelStructure L D} {C : RelStructure L V}
    (e : Embedding Root C) (he : e.ContainedInIrreducible)
    (c : V → Bool)
    (hc : ∀ x : Fin 2 → V, C.rel () x → c (x 0) ≠ c (x 1)) :
    Function.Injective (fun d => c (e d)) := by
  rcases he with ⟨S, hS, hsub⟩
  have hinjS := color_injective_on_irreducible c hc S hS
  intro x y hxy
  let xs : S := ⟨e x, hsub x⟩
  let ys : S := ⟨e y, hsub y⟩
  have hs : xs = ys := hinjS hxy
  exact e.injective (congrArg Subtype.val hs)

/-- Two injective Bool-valued maps on the same type agree after either
keeping or flipping the second colouring. -/
theorem align_bool_injections
    {D : Type u} (a b : D → Bool)
    (ha : Function.Injective a) (hb : Function.Injective b) :
    ∃ σ : Bool → Bool, Function.Injective σ ∧
      ∀ d, a d = σ (b d) := by
  classical
  by_cases hD : Nonempty D
  · let d₀ : D := Classical.choice hD
    by_cases h0 : a d₀ = b d₀
    · refine ⟨id, Function.injective_id, ?_⟩
      intro d
      by_cases hd : d = d₀
      · subst d
        simpa using h0
      · have ha' : a d ≠ a d₀ := by
          intro h
          exact hd (ha h)
        have hb' : b d ≠ b d₀ := by
          intro h
          exact hd (hb h)
        cases had : a d₀ <;> cases hbd : b d₀ <;>
          cases had' : a d <;> cases hbd' : b d <;>
          simp_all
    · let σ : Bool → Bool := fun x => !x
      have hσ : Function.Injective σ := by
        intro x y h
        cases x <;> cases y <;> simp_all [σ]
      refine ⟨σ, hσ, ?_⟩
      intro d
      by_cases hd : d = d₀
      · subst d
        cases ha0 : a d₀ <;> cases hb0 : b d₀ <;> simp_all [σ]
      · have ha' : a d ≠ a d₀ := by
          intro h
          exact hd (ha h)
        have hb' : b d ≠ b d₀ := by
          intro h
          exact hd (hb h)
        cases ha0 : a d₀ <;> cases hb0 : b d₀ <;>
          cases had : a d <;> cases hbd : b d <;>
          simp_all [σ]
  · letI : IsEmpty D := ⟨fun d => hD ⟨d⟩⟩
    refine ⟨id, Function.injective_id, ?_⟩
    intro d
    exact isEmptyElim d

/-- Glue compatible two-colourings across an arbitrary concrete free
amalgam. -/
theorem IsFreeAmalgam.twoColorable
    {D V W X : Type u}
    {Root : RelStructure L D}
    {A : RelStructure L V} {B : RelStructure L W}
    {C : RelStructure L X}
    {fA : Embedding Root A} {fB : Embedding Root B}
    {iA : Embedding A C} {iB : Embedding B C}
    (hfree : IsFreeAmalgam fA fB iA iB)
    (cA : V → Bool) (cB : W → Bool)
    (hA : ∀ x : Fin 2 → V, A.rel () x → cA (x 0) ≠ cA (x 1))
    (hB : ∀ x : Fin 2 → W, B.rel () x → cB (x 0) ≠ cB (x 1))
    (hcompat : ∀ d, cA (fA d) = cB (fB d)) :
    TwoColorable C := by
  classical
  let c : X → Bool := fun z =>
    if hz : ∃ a : V, z = iA a then
      cA (Classical.choose hz)
    else
      cB (Classical.choose ((hfree.covers z).resolve_left hz))
  have c_left (a : V) : c (iA a) = cA a := by
    have h : ∃ a' : V, iA a = iA a' := ⟨a, rfl⟩
    simp only [c, dif_pos h]
    have hs := Classical.choose_spec h
    exact congrArg cA (iA.injective hs)
  have c_right (b : W) : c (iB b) = cB b := by
    by_cases hleft : ∃ a : V, iB b = iA a
    · rcases hleft with ⟨a, hab⟩
      have hov : ∃ d : D, a = fA d ∧ b = fB d :=
        (hfree.overlap a b).mp hab.symm
      rcases hov with ⟨d, rfl, rfl⟩
      rw [← hcompat d]
      exact c_left (fA d)
    · simp only [c, dif_neg hleft]
      have hs := Classical.choose_spec ((hfree.covers (iB b)).resolve_left hleft)
      exact congrArg cB (iB.injective hs)
  refine ⟨c, ?_⟩
  intro x hx
  rcases (hfree.rel_iff () x).mp hx with hside | hside
  · rcases hside with ⟨y, hy, rfl⟩
    simpa [Function.comp_apply, c_left] using hA y hy
  · rcases hside with ⟨y, hy, rfl⟩
    simpa [Function.comp_apply, c_right] using hB y hy

/-- Strict tree amalgams of copies of a two-colourable binary base remain
two-colourable. -/
theorem TreeAmalgam.twoColorable
    {V W : Type u} {Base : RelStructure L V} {T : RelStructure L W}
    (hBase : TwoColorable Base)
    (hT : TreeAmalgam Base W T) :
    TwoColorable T := by
  induction hT with
  | copy hIso =>
      rcases hBase with ⟨c, hc⟩
      let cT : _ → Bool := fun x => c (hIso.toEquiv.symm x)
      refine ⟨cT, ?_⟩
      intro x hx
      have hs : Base.rel () (hIso.toEquiv.symm ∘ x) := by
        exact (hIso.map_rel_iff () (hIso.toEquiv.symm ∘ x)).mp (by
          convert hx using 1
          funext i
          simp)
      exact hc (hIso.toEquiv.symm ∘ x) hs
  | @glue W₁ W₂ Z W T₁ T₂ D T
      h₁ h₂ f₁ f₂ hc₁ hc₂ i₁ i₂ hfree ih₁ ih₂ =>
      rcases ih₁ with ⟨c₁, hcol₁⟩
      rcases ih₂ with ⟨c₂, hcol₂⟩
      have hinj₁ := root_color_injective f₁ hc₁ c₁ hcol₁
      have hinj₂ := root_color_injective f₂ hc₂ c₂ hcol₂
      obtain ⟨σ, hσ, halign⟩ :=
        align_bool_injections (fun d => c₁ (f₁ d))
          (fun d => c₂ (f₂ d)) hinj₁ hinj₂
      let c₂' : W₂ → Bool := σ ∘ c₂
      have hcol₂' :
          ∀ x : Fin 2 → W₂, T₂.rel () x →
            c₂' (x 0) ≠ c₂' (x 1) := by
        intro x hx
        exact hσ.ne (hcol₂ x hx)
      apply hfree.twoColorable c₁ c₂' hcol₁ hcol₂'
      intro d
      exact halign d

/-- The four-vertex path. -/
def P4 : RelStructure L (Fin 4) where
  rel := fun _ x =>
    ((x 0).val + 1 = (x 1).val) ∨
    ((x 1).val + 1 = (x 0).val)

def p4Color : Fin 4 → Bool
  | ⟨0, _⟩ => false
  | ⟨1, _⟩ => true
  | ⟨2, _⟩ => false
  | ⟨3, _⟩ => true

theorem P4_twoColorable : TwoColorable P4 := by
  refine ⟨p4Color, ?_⟩
  intro x hx
  change ((x 0).val + 1 = (x 1).val) ∨
    ((x 1).val + 1 = (x 0).val) at hx
  have h0 : (x 0).val < 4 := (x 0).isLt
  have h1 : (x 1).val < 4 := (x 1).isLt
  interval_cases h0v : (x 0).val <;>
    interval_cases h1v : (x 1).val <;>
    simp [p4Color, h0v, h1v] at hx ⊢

/-- Empty two-point root. -/
def Root : RelStructure L Bool where
  rel := fun _ _ => False

def leftRoot : Embedding Root P4 where
  toFun
    | false => 0
    | true => 3
  injective := by decide
  map_rel_iff := by
    intro R x
    cases R
    constructor
    · intro h
      change
        ((((leftRoot.toFun (x 0) : Fin 4).val + 1 =
          (leftRoot.toFun (x 1) : Fin 4).val) ∨
         ((leftRoot.toFun (x 1) : Fin 4).val + 1 =
          (leftRoot.toFun (x 0) : Fin 4).val))) at h
      cases h0 : x 0 <;> cases h1 : x 1 <;>
        simp [leftRoot, h0, h1] at h
    · intro h
      exact h.elim

def rightRoot : Embedding Root P4 where
  toFun
    | false => 0
    | true => 2
  injective := by decide
  map_rel_iff := by
    intro R x
    cases R
    constructor
    · intro h
      change
        ((((rightRoot.toFun (x 0) : Fin 4).val + 1 =
          (rightRoot.toFun (x 1) : Fin 4).val) ∨
         ((rightRoot.toFun (x 1) : Fin 4).val + 1 =
          (rightRoot.toFun (x 0) : Fin 4).val))) at h
      cases h0 : x 0 <;> cases h1 : x 1 <;>
        simp [rightRoot, h0, h1] at h
    · intro h
      exact h.elim

abbrev OddLoose :=
  FreeAmalgam.amalgam Root P4 P4 leftRoot rightRoot

/-- The odd loose amalgam is indeed a loose P4-tree. -/
theorem OddLoose_loose : LooseTreeAmalgam P4 _ OddLoose := by
  exact .glue (.copy (Iso.refl P4)) (.copy (Iso.refl P4))
    leftRoot rightRoot
    (FreeAmalgam.leftEmbedding Root P4 P4 leftRoot rightRoot)
    (FreeAmalgam.rightEmbedding Root P4 P4 leftRoot rightRoot)
    (FreeAmalgam.isFreeAmalgam Root P4 P4 leftRoot rightRoot)

/-- In Bool, two consecutive inequalities force equality. -/
theorem bool_eq_of_ne_ne {a b c : Bool} (hab : a ≠ b) (hbc : b ≠ c) :
    a = c := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- The loose amalgam contains an odd 5-cycle, hence is not two-colourable. -/
theorem OddLoose_not_twoColorable : ¬ TwoColorable OddLoose := by
  rintro ⟨c, hc⟩
  let l := FreeAmalgam.leftEmbedding Root P4 P4 leftRoot rightRoot
  let r := FreeAmalgam.rightEmbedding Root P4 P4 leftRoot rightRoot
  have edgeP4 (a b : Fin 4)
      (h : a.val + 1 = b.val ∨ b.val + 1 = a.val) :
      P4.rel () ![a, b] := h
  have h01 : c (l 0) ≠ c (l 1) := by
    apply hc ![l 0, l 1]
    exact (l.map_rel_iff () ![(0 : Fin 4), (1 : Fin 4)]).mpr
      (edgeP4 0 1 (by omega))
  have h12 : c (l 1) ≠ c (l 2) := by
    apply hc ![l 1, l 2]
    exact (l.map_rel_iff () ![(1 : Fin 4), (2 : Fin 4)]).mpr
      (edgeP4 1 2 (by omega))
  have h23 : c (l 2) ≠ c (l 3) := by
    apply hc ![l 2, l 3]
    exact (l.map_rel_iff () ![(2 : Fin 4), (3 : Fin 4)]).mpr
      (edgeP4 2 3 (by omega))
  have hr21 : c (r 2) ≠ c (r 1) := by
    apply hc ![r 2, r 1]
    exact (r.map_rel_iff () ![(2 : Fin 4), (1 : Fin 4)]).mpr
      (edgeP4 2 1 (by omega))
  have hr10 : c (r 1) ≠ c (r 0) := by
    apply hc ![r 1, r 0]
    exact (r.map_rel_iff () ![(1 : Fin 4), (0 : Fin 4)]).mpr
      (edgeP4 1 0 (by omega))
  have hroot0 : l 0 = r 0 := by
    exact FreeAmalgam.left_right_overlap Root P4 P4 leftRoot rightRoot false
  have hroot3 : l 3 = r 2 := by
    exact FreeAmalgam.left_right_overlap Root P4 P4 leftRoot rightRoot true
  have heq02 : c (l 0) = c (l 2) := bool_eq_of_ne_ne h01 h12
  have heq24 : c (l 2) = c (r 1) := by
    have h34 : c (l 3) ≠ c (r 1) := by
      rw [hroot3]
      exact hr21
    exact bool_eq_of_ne_ne h23 h34
  have heq : c (l 0) = c (r 1) := heq02.trans heq24
  have hlast : c (r 1) ≠ c (l 0) := by
    rw [hroot0]
    exact hr10
  exact hlast heq.symm

/-- No homomorphism-embedding from the odd loose P4-tree can land in any
strict P4-tree. -/
theorem OddLoose_no_strictification :
    ¬ ∃ (W : Type u) (T : RelStructure L W),
      TreeAmalgam P4 W T ∧
      ∃ f : OddLoose.Carrier → W,
        OddLoose.IsHomomorphismEmbedding T f := by
  rintro ⟨W, T, hT, f, hf⟩
  have hTC : TwoColorable T :=
    hT.twoColorable P4_twoColorable
  exact OddLoose_not_twoColorable
    (hTC.pullback f hf.1)

end StructuralRamsey.RelStructure.LooseNotStrictifiable
