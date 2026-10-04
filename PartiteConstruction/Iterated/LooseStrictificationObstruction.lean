import PartiteConstruction.Iterated.LooseTreeAmalgam
import PartiteConstruction.Iterated.FinalAttachment

/-! # A loose P4-tree which cannot be strictified

Let B be the four-vertex path P4. Strict tree amalgams of copies of P4 are
bipartite: the strict gluing condition places every root inside an
irreducible graph substructure, hence the two side colourings can be aligned
on the root.

A loose amalgam of two P4 copies can instead identify an independent pair at
distance three in one copy with an independent pair at distance two in the
other. The resulting graph contains a 5-cycle and is not bipartite.

Consequently there is no homomorphism-embedding from this loose P4-tree into
any strict P4-tree. This rules out the shortcut of strictifying arbitrary
loose trees after the fact.
-/
namespace StructuralRamsey.RelStructure.LooseNotStrictifiable

noncomputable section

/-- One binary relation symbol. -/
def L : RelLanguage where
  Symbol := Unit
  arity := fun _ => 2

def i0 : Fin (L.arity ()) := ⟨0, by simp [L]⟩
def i1 : Fin (L.arity ()) := ⟨1, by simp [L]⟩

theorem i0_ne_i1 : i0 ≠ i1 := by
  intro h
  have := congrArg Fin.val h
  simp [i0, i1] at this

/-- Proper two-colourability for the unique binary relation. -/
def TwoColorable {V : Type} (C : RelStructure L V) : Prop :=
  ∃ c : V → Bool, ∀ x : Fin (L.arity ()) → V,
    C.rel () x → c (x i0) ≠ c (x i1)

/-- Pull a two-colouring back through a homomorphism. -/
theorem TwoColorable.pullback
    {V W : Type} {A : RelStructure L V} {B : RelStructure L W}
    (hB : TwoColorable B)
    (f : V → W) (hf : A.IsHomomorphism B f) :
    TwoColorable A := by
  rcases hB with ⟨c, hc⟩
  refine ⟨c ∘ f, ?_⟩
  intro x hx
  exact hc (f ∘ x) (hf () x hx)

/-- On an irreducible set, any proper Bool colouring is injective. -/
theorem color_injective_on_irreducible
    {V : Type} {C : RelStructure L V}
    (c : V → Bool)
    (hc : ∀ x : Fin (L.arity ()) → V,
      C.rel () x → c (x i0) ≠ c (x i1))
    (S : Set V) (hS : (C.induce S).Irreducible) :
    Function.Injective (fun x : S => c x.1) := by
  intro x y hcol
  by_contra hxy
  obtain ⟨R, z, i, j, hz, hzi, hzj⟩ := hS hxy
  cases R
  have hij : i ≠ j := by
    intro hij
    apply hxy
    calc
      x = z i := hzi.symm
      _ = z j := congrArg z hij
      _ = y := hzj
  have hi : i = i0 ∨ i = i1 := by
    have hiLt := i.isLt
    simp [L] at hiLt
    have hv : i.val = 0 ∨ i.val = 1 := by omega
    rcases hv with hv | hv
    · left; apply Fin.ext; simpa [i0] using hv
    · right; apply Fin.ext; simpa [i1] using hv
  have hj : j = i0 ∨ j = i1 := by
    have hjLt := j.isLt
    simp [L] at hjLt
    have hv : j.val = 0 ∨ j.val = 1 := by omega
    rcases hv with hv | hv
    · left; apply Fin.ext; simpa [i0] using hv
    · right; apply Fin.ext; simpa [i1] using hv
  have hneq := hc (Subtype.val ∘ z) hz
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact hij (hi.trans hj.symm)
  · apply hneq
    calc
      c ((Subtype.val ∘ z) i0) = c x.1 := by
        rw [← hi]
        exact congrArg c (congrArg Subtype.val hzi)
      _ = c y.1 := hcol
      _ = c ((Subtype.val ∘ z) i1) := by
        rw [← hj]
        exact (congrArg c (congrArg Subtype.val hzj)).symm
  · apply hneq
    symm
    calc
      c ((Subtype.val ∘ z) i1) = c x.1 := by
        rw [← hi]
        exact congrArg c (congrArg Subtype.val hzi)
      _ = c y.1 := hcol
      _ = c ((Subtype.val ∘ z) i0) := by
        rw [← hj]
        exact (congrArg c (congrArg Subtype.val hzj)).symm
  · exact hij (hi.trans hj.symm)

/-- Strict-root containment forces the colouring to be injective on the root. -/
theorem root_color_injective
    {D V : Type} {Root : RelStructure L D} {C : RelStructure L V}
    (e : Embedding Root C) (he : e.ContainedInIrreducible)
    (c : V → Bool)
    (hc : ∀ x : Fin (L.arity ()) → V,
      C.rel () x → c (x i0) ≠ c (x i1)) :
    Function.Injective (fun d => c (e d)) := by
  rcases he with ⟨S, hS, hsub⟩
  have hinj := color_injective_on_irreducible c hc S hS
  intro x y hxy
  let xs : S := ⟨e x, hsub x⟩
  let ys : S := ⟨e y, hsub y⟩
  have hs : xs = ys := hinj hxy
  exact e.injective (congrArg Subtype.val hs)

/-- Two injective Bool-valued maps agree after either keeping or flipping
the second colouring. -/
theorem align_bool_injections
    {D : Type} (a b : D → Bool)
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
        exact h0
      · have ha' : a d ≠ a d₀ := fun h => hd (ha h)
        have hb' : b d ≠ b d₀ := fun h => hd (hb h)
        cases had0 : a d₀ <;> cases hbd0 : b d₀ <;>
          cases had : a d <;> cases hbd : b d <;>
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
      · have ha' : a d ≠ a d₀ := fun h => hd (ha h)
        have hb' : b d ≠ b d₀ := fun h => hd (hb h)
        cases ha0 : a d₀ <;> cases hb0 : b d₀ <;>
          cases had : a d <;> cases hbd : b d <;>
          simp_all [σ]
  · letI : IsEmpty D := ⟨fun d => hD ⟨d⟩⟩
    exact ⟨id, Function.injective_id, fun d => isEmptyElim d⟩

/-- Compatible proper colourings glue across a concrete free amalgam. -/
theorem IsFreeAmalgam.twoColorable
    {D V W X : Type}
    {Root : RelStructure L D}
    {A : RelStructure L V} {B : RelStructure L W}
    {C : RelStructure L X}
    {fA : Embedding Root A} {fB : Embedding Root B}
    {jA : Embedding A C} {jB : Embedding B C}
    (hfree : IsFreeAmalgam fA fB jA jB)
    (cA : V → Bool) (cB : W → Bool)
    (hA : ∀ x : Fin (L.arity ()) → V,
      A.rel () x → cA (x i0) ≠ cA (x i1))
    (hB : ∀ x : Fin (L.arity ()) → W,
      B.rel () x → cB (x i0) ≠ cB (x i1))
    (hcompat : ∀ d, cA (fA d) = cB (fB d)) :
    TwoColorable C := by
  classical
  let c : X → Bool := fun z =>
    if hz : ∃ a : V, z = jA a then
      cA (Classical.choose hz)
    else
      cB (Classical.choose ((hfree.covers z).resolve_left hz))
  have cAmap (a : V) : c (jA a) = cA a := by
    have h : ∃ a' : V, jA a = jA a' := ⟨a, rfl⟩
    simp only [c, dif_pos h]
    have hs := Classical.choose_spec h
    exact congrArg cA (jA.injective hs).symm
  have cBmap (b : W) : c (jB b) = cB b := by
    by_cases hleft : ∃ a : V, jB b = jA a
    · rcases hleft with ⟨a, hab⟩
      rcases (hfree.overlap a b).mp hab.symm with ⟨d, rfl, rfl⟩
      have hover : jA (fA d) = jB (fB d) :=
        (hfree.overlap (fA d) (fB d)).mpr ⟨d, rfl, rfl⟩
      calc
        c (jB (fB d)) = c (jA (fA d)) := congrArg c hover.symm
        _ = cA (fA d) := cAmap (fA d)
        _ = cB (fB d) := hcompat d
    · simp only [c, dif_neg hleft]
      have hs := Classical.choose_spec
        ((hfree.covers (jB b)).resolve_left hleft)
      exact congrArg cB (jB.injective hs).symm
  refine ⟨c, ?_⟩
  intro x hx
  rcases (hfree.rel_iff () x).mp hx with hside | hside
  · rcases hside with ⟨y, hy, hxy⟩
    have hx0 : x i0 = jA (y i0) := congrFun hxy i0
    have hx1 : x i1 = jA (y i1) := congrFun hxy i1
    intro heq
    apply hA y hy
    calc
      cA (y i0) = c (jA (y i0)) := (cAmap (y i0)).symm
      _ = c (x i0) := congrArg c hx0.symm
      _ = c (x i1) := heq
      _ = c (jA (y i1)) := congrArg c hx1
      _ = cA (y i1) := cAmap (y i1)
  · rcases hside with ⟨y, hy, hxy⟩
    have hx0 : x i0 = jB (y i0) := congrFun hxy i0
    have hx1 : x i1 = jB (y i1) := congrFun hxy i1
    intro heq
    apply hB y hy
    calc
      cB (y i0) = c (jB (y i0)) := (cBmap (y i0)).symm
      _ = c (x i0) := congrArg c hx0.symm
      _ = c (x i1) := heq
      _ = c (jB (y i1)) := congrArg c hx1
      _ = cB (y i1) := cBmap (y i1)

/-- Strict tree amalgams of a two-colourable binary base remain
two-colourable. -/
theorem TreeAmalgam.twoColorable
    {V W : Type} {Base : RelStructure L V} {T : RelStructure L W}
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
        apply (hIso.map_rel_iff () (hIso.toEquiv.symm ∘ x)).mp
        convert hx using 1
        funext k
        simp [Function.comp_apply]
      exact hc (hIso.toEquiv.symm ∘ x) hs
  | @glue W₁ W₂ Z W T₁ T₂ D T
      h₁ h₂ f₁ f₂ hc₁ hc₂ j₁ j₂ hfree ih₁ ih₂ =>
      rcases ih₁ with ⟨c₁, hcol₁⟩
      rcases ih₂ with ⟨c₂, hcol₂⟩
      have hinj₁ := root_color_injective f₁ hc₁ c₁ hcol₁
      have hinj₂ := root_color_injective f₂ hc₂ c₂ hcol₂
      obtain ⟨σ, hσ, halign⟩ :=
        align_bool_injections (fun d => c₁ (f₁ d))
          (fun d => c₂ (f₂ d)) hinj₁ hinj₂
      let c₂' : W₂ → Bool := σ ∘ c₂
      have hcol₂' :
          ∀ x : Fin (L.arity ()) → W₂,
            T₂.rel () x → c₂' (x i0) ≠ c₂' (x i1) := by
        intro x hx
        exact hσ.ne (hcol₂ x hx)
      exact IsFreeAmalgam.twoColorable
        hfree c₁ c₂' hcol₁ hcol₂' halign

/-- The four-vertex path. -/
def P4 : RelStructure L (Fin 4) where
  rel := fun _ x =>
    ((x i0).val + 1 = (x i1).val) ∨
    ((x i1).val + 1 = (x i0).val)

def p4Color (x : Fin 4) : Bool :=
  x.val % 2 == 1

theorem P4_twoColorable : TwoColorable P4 := by
  refine ⟨p4Color, ?_⟩
  intro x hx
  have h0 : (x i0).val < 4 := (x i0).isLt
  have h1 : (x i1).val < 4 := (x i1).isLt
  interval_cases h0v : (x i0).val <;>
    interval_cases h1v : (x i1).val <;>
    simp [P4, p4Color, h0v, h1v] at hx ⊢

/-- Empty two-point root. -/
def Root : RelStructure L Bool where
  rel := fun _ _ => False

def leftRootMap : Bool → Fin 4
  | false => 0
  | true => 3

def rightRootMap : Bool → Fin 4
  | false => 0
  | true => 2

theorem leftRootMap_nonedge (x : Fin (L.arity ()) → Bool) :
    ¬ P4.rel () (leftRootMap ∘ x) := by
  intro h
  cases h0 : x i0 <;> cases h1 : x i1 <;>
    simp [P4, leftRootMap, Function.comp_apply, h0, h1] at h

theorem rightRootMap_nonedge (x : Fin (L.arity ()) → Bool) :
    ¬ P4.rel () (rightRootMap ∘ x) := by
  intro h
  cases h0 : x i0 <;> cases h1 : x i1 <;>
    simp [P4, rightRootMap, Function.comp_apply, h0, h1] at h

def leftRoot : Embedding Root P4 where
  toFun := leftRootMap
  injective := by
    intro x y h
    cases x <;> cases y <;> simp_all [leftRootMap]
  map_rel_iff := by
    intro R x
    cases R
    constructor
    · exact fun h => (leftRootMap_nonedge x h).elim
    · intro h
      exact h.elim

def rightRoot : Embedding Root P4 where
  toFun := rightRootMap
  injective := by
    intro x y h
    cases x <;> cases y <;> simp_all [rightRootMap]
  map_rel_iff := by
    intro R x
    cases R
    constructor
    · exact fun h => (rightRootMap_nonedge x h).elim
    · intro h
      exact h.elim

abbrev OddLoose :=
  FreeAmalgam.amalgam Root P4 P4 leftRoot rightRoot

theorem OddLoose_loose : LooseTreeAmalgam P4 _ OddLoose := by
  exact .glue (.copy (Iso.refl P4)) (.copy (Iso.refl P4))
    leftRoot rightRoot
    (FreeAmalgam.leftEmbedding Root P4 P4 leftRoot rightRoot)
    (FreeAmalgam.rightEmbedding Root P4 P4 leftRoot rightRoot)
    (FreeAmalgam.isFreeAmalgam Root P4 P4 leftRoot rightRoot)

theorem bool_eq_of_ne_ne {a b c : Bool} (hab : a ≠ b) (hbc : b ≠ c) :
    a = c := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- The loose amalgam contains the odd cycle
0_L-1_L-2_L-3_L(=2_R)-1_R-0_R(=0_L). -/
theorem OddLoose_not_twoColorable : ¬ TwoColorable OddLoose := by
  rintro ⟨c, hc⟩
  let l := FreeAmalgam.leftEmbedding Root P4 P4 leftRoot rightRoot
  let r := FreeAmalgam.rightEmbedding Root P4 P4 leftRoot rightRoot
  have edgeP4 (a b : Fin 4)
      (h : a.val + 1 = b.val ∨ b.val + 1 = a.val) :
      P4.rel () (fun k => if k = i0 then a else b) := by
    have hi10 : i1 ≠ i0 := Ne.symm i0_ne_i1
    simpa [P4, hi10] using h
  have edge_image_left (a b : Fin 4)
      (h : a.val + 1 = b.val ∨ b.val + 1 = a.val) :
      OddLoose.rel () (fun k => if k = i0 then l a else l b) := by
    let q : Fin (L.arity ()) → Fin 4 := fun k => if k = i0 then a else b
    have hP : P4.rel () q := edgeP4 a b h
    have hm := (l.map_rel_iff () q).mpr hP
    convert hm using 1
    funext k
    by_cases hk : k = i0 <;> simp [q, hk, Function.comp_apply]
  have edge_image_right (a b : Fin 4)
      (h : a.val + 1 = b.val ∨ b.val + 1 = a.val) :
      OddLoose.rel () (fun k => if k = i0 then r a else r b) := by
    let q : Fin (L.arity ()) → Fin 4 := fun k => if k = i0 then a else b
    have hP : P4.rel () q := edgeP4 a b h
    have hm := (r.map_rel_iff () q).mpr hP
    convert hm using 1
    funext k
    simp [q, Function.comp_apply]
  have neq_of_edge (a b : _) (hrel : OddLoose.rel ()
      (fun k => if k = i0 then a else b)) :
      c a ≠ c b := by
    have h := hc _ hrel
    have hi10 : i1 ≠ i0 := Ne.symm i0_ne_i1
    simpa [hi10] using h
  have h01 : c (l 0) ≠ c (l 1) :=
    neq_of_edge _ _ (edge_image_left 0 1 (by omega))
  have h12 : c (l 1) ≠ c (l 2) :=
    neq_of_edge _ _ (edge_image_left 1 2 (by omega))
  have h23 : c (l 2) ≠ c (l 3) :=
    neq_of_edge _ _ (edge_image_left 2 3 (by omega))
  have hr21 : c (r 2) ≠ c (r 1) :=
    neq_of_edge _ _ (edge_image_right 2 1 (by omega))
  have hr10 : c (r 1) ≠ c (r 0) :=
    neq_of_edge _ _ (edge_image_right 1 0 (by omega))
  have hroot0 : l 0 = r 0 :=
    FreeAmalgam.left_right_overlap Root P4 P4 leftRoot rightRoot false
  have hroot3 : l 3 = r 2 :=
    FreeAmalgam.left_right_overlap Root P4 P4 leftRoot rightRoot true
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

theorem OddLoose_no_strictification :
    ¬ ∃ (W : Type) (T : RelStructure L W),
      TreeAmalgam P4 W T ∧
      ∃ f : FreeAmalgam.Vertex Root P4 P4 leftRoot rightRoot → W,
        OddLoose.IsHomomorphismEmbedding T f := by
  rintro ⟨W, T, hT, f, hf⟩
  have hTC : TwoColorable T :=
    TreeAmalgam.twoColorable P4_twoColorable hT
  exact OddLoose_not_twoColorable
    (hTC.pullback f hf.1)

end

end StructuralRamsey.RelStructure.LooseNotStrictifiable
