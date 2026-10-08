import PartiteConstruction.Functional.RankedTreeReduct
import PartiteConstruction.Functional.NoSquareFreeGluing

/-! # A square-free function-domain invariant for strict functional trees

The template B has three vertices 0 (input X), 1 (input Y),
and 2 (output Z), with one binary function value F(0,1)={2}.
Unary role predicates distinguish the input positions.

In a full strict tree of B-copies the bipartite input-domain relation
contains no square. At a strict free gluing, the root lies in an irreducible
piece on each side, hence inside a full B-copy. The root therefore has
at most one vertex in either input role. The abstract free-union lemma
then preserves square-freeness.

This is a genuine full-function target statement, not a theorem about
arbitrary relational function-graph trees. -/

namespace StructuralRamsey.Structure.NativePowerObstruction

open StructuralRamsey.Structure

/-- Three unary role predicates and one binary set-valued function. -/
def toyLanguage : Language where
  RelSymbol := Fin 3
  FuncSymbol := Unit
  relArity _ := 1
  funcArity _ := 2

/-- A single binary-function hyperedge. -/
def toyBase : Structure toyLanguage (Fin 3) where
  rel R x := x (0 : Fin 1) = R
  func _ x := {y | x (0 : Fin 2) = 0 ∧ x (1 : Fin 2) = 1 ∧ y = 2}

def Role {W : Type} (T : Structure toyLanguage W)
    (r : Fin 3) (x : W) : Prop :=
  T.rel r (fun _ : Fin 1 => x)

def Domain {W : Type} (T : Structure toyLanguage W)
    (x y : W) : Prop :=
  (T.func () ![x, y]).Nonempty

def SquareFree {W : Type} (T : Structure toyLanguage W) : Prop :=
  SquareFreeOn (Role T 0) (Role T 1) (fun _ => True) (Domain T)

/-- Every role has a unique vertex in one copy of the template. -/
theorem toyBase_role_unique (r : Fin 3) (a b : Fin 3)
    (ha : Role toyBase r a) (hb : Role toyBase r b) : a = b := by
  change a = r at ha
  change b = r at hb
  exact ha.trans hb.symm

theorem toyBase_squareFree : SquareFree toyBase := by
  intro x₁ x₂ y₁ y₂ hx₁ hx₂ _ _ hxx _ _ _ _ _ _ _ _ _
  exact hxx (toyBase_role_unique 0 x₁ x₂ hx₁ hx₂)

theorem role_embedding_iff
    {U W : Type}
    {S : Structure toyLanguage U} {T : Structure toyLanguage W}
    (e : Embedding S T) (r : Fin 3) (x : U) :
    Role T r (e x) ↔ Role S r x := by
  change T.rel r (e ∘ (fun _ : Fin 1 => x)) ↔
    S.rel r (fun _ : Fin 1 => x)
  exact e.map_rel_iff r (fun _ : Fin 1 => x)

/-- A full function embedding preserves and reflects whether its binary
function has any output over an input pair. -/
theorem domain_embedding_iff
    {U W : Type}
    {S : Structure toyLanguage U} {T : Structure toyLanguage W}
    (e : Embedding S T) (x y : U) :
    Domain T (e x) (e y) ↔ Domain S x y := by
  have htuple : e ∘ ![x, y] = ![e x, e y] := by
    funext i
    fin_cases i <;> rfl
  constructor
  · rintro ⟨z, hz⟩
    have hzT : z ∈ T.func () (e ∘ ![x, y]) := by
      simpa only [htuple] using hz
    rw [← e.map_func () ![x, y]] at hzT
    rcases hzT with ⟨w, hw, _⟩
    exact ⟨w, hw⟩
  · rintro ⟨w, hw⟩
    have hImage : e w ∈ imageSet e (S.func () ![x, y]) :=
      ⟨w, hw, rfl⟩
    rw [e.map_func () ![x, y]] at hImage
    refine ⟨e w, ?_⟩
    simpa only [htuple] using hImage

/-- Square-freeness of one side, as read in the ambient structure through
a full embedding. -/
theorem squareFreeOn_embedding
    {U W : Type}
    {S : Structure toyLanguage U} {T : Structure toyLanguage W}
    (hS : SquareFree S) (e : Embedding S T) :
    SquareFreeOn (Role T 0) (Role T 1)
      (fun z => ∃ a, z = e a) (Domain T) := by
  intro x₁ x₂ y₁ y₂ hx₁ hx₂ hy₁ hy₂ hxx hyy
    h₁₁ h₁₂ h₂₁ h₂₂
    ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩
  subst x₁
  subst x₂
  subst y₁
  subst y₂
  have hab : a ≠ b := by
    intro heq
    exact hxx (congrArg e heq)
  have hcd : c ≠ d := by
    intro heq
    exact hyy (congrArg e heq)
  exact hS a b c d
    ((role_embedding_iff e 0 a).mp hx₁)
    ((role_embedding_iff e 0 b).mp hx₂)
    ((role_embedding_iff e 1 c).mp hy₁)
    ((role_embedding_iff e 1 d).mp hy₂)
    hab hcd
    ((domain_embedding_iff e a c).mp h₁₁)
    ((domain_embedding_iff e a d).mp h₁₂)
    ((domain_embedding_iff e b c).mp h₂₁)
    ((domain_embedding_iff e b d).mp h₂₂)
    trivial trivial trivial trivial

/-- A root carried inside one irreducible piece of a strict B-tree has
at most one vertex of any prescribed role. -/
theorem root_role_unique
    {H W : Type}
    {Root : Structure toyLanguage H} {T : Structure toyLanguage W}
    (hTree : TreeAmalgam toyBase W T)
    (f : Embedding Root T)
    (hf : f.ContainedInIrreducible)
    (r : Fin 3) (d e : H)
    (hd : Role Root r d) (he : Role Root r e) : d = e := by
  obtain ⟨Q, Irred, hIrred, j, hj⟩ := hf
  obtain ⟨copy, hcopy⟩ :=
    hTree.irreducible_contained_in_copy hIrred j
  obtain ⟨u, hu⟩ := hj d
  obtain ⟨v, hv⟩ := hj e
  obtain ⟨a, ha⟩ := hcopy u
  obtain ⟨b, hb⟩ := hcopy v
  have hdT : Role T r (copy a) := by
    rw [← ha, ← hu]
    exact (role_embedding_iff f r d).mpr hd
  have heT : Role T r (copy b) := by
    rw [← hb, ← hv]
    exact (role_embedding_iff f r e).mpr he
  have haB : Role toyBase r a :=
    (role_embedding_iff copy r a).mp hdT
  have hbB : Role toyBase r b :=
    (role_embedding_iff copy r b).mp heT
  have hab : a = b := toyBase_role_unique r a b haB hbB
  apply f.injective
  calc
    f d = j u := hu
    _ = copy a := ha
    _ = copy b := congrArg copy hab
    _ = j v := hb.symm
    _ = f e := hv.symm

/-- Every strict full-functional B-tree has a square-free bipartite
function-domain graph. -/
theorem strictTree_squareFree
    {W : Type} {T : Structure toyLanguage W}
    (hTree : TreeAmalgam toyBase W T) : SquareFree T := by
  induction hTree with
  | copy e hsurj =>
      have hRange : ∀ z, ∃ a : Fin 3, z = e a := by
        intro z
        obtain ⟨a, ha⟩ := hsurj z
        exact ⟨a, ha.symm⟩
      have h := squareFreeOn_embedding toyBase_squareFree e
      intro x₁ x₂ y₁ y₂ hx₁ hx₂ hy₁ hy₂ hxx hyy
        h₁₁ h₁₂ h₂₁ h₂₂ _ _ _ _
      exact h x₁ x₂ y₁ y₂ hx₁ hx₂ hy₁ hy₂ hxx hyy
        h₁₁ h₁₂ h₂₁ h₂₂
        (hRange x₁) (hRange x₂) (hRange y₁) (hRange y₂)
  | @glue W₁ W₂ Z W T₁ T₂ Root T
      h₁ h₂ f₁ f₂ hc₁ hc₂ i₁ i₂ hfree ih₁ ih₂ =>
      let Left : W → Prop := fun z => ∃ a : W₁, z = i₁ a
      let Right : W → Prop := fun z => ∃ b : W₂, z = i₂ b
      have hCover : ∀ z : W, Left z ∨ Right z := hfree.covers
      have hEdge : ∀ x y : W, Domain T x y →
          (Left x ∧ Left y) ∨ (Right x ∧ Right y) := by
        intro x y hxy
        obtain ⟨z, hz⟩ := hxy
        rcases (hfree.func_iff () ![x, y] z).mp hz with
          ⟨args, out, hval, heq, hout⟩ |
          ⟨args, out, hval, heq, hout⟩
        · left
          exact ⟨⟨args (0 : Fin 2), congrFun heq (0 : Fin 2)⟩,
            ⟨args (1 : Fin 2), congrFun heq (1 : Fin 2)⟩⟩
        · right
          exact ⟨⟨args (0 : Fin 2), congrFun heq (0 : Fin 2)⟩,
            ⟨args (1 : Fin 2), congrFun heq (1 : Fin 2)⟩⟩
      have hShared (z : W) (hl : Left z) (hr : Right z) :
          ∃ d : Z, z = i₁ (f₁ d) := by
        obtain ⟨a, ha⟩ := hl
        obtain ⟨b, hb⟩ := hr
        have hab : i₁ a = i₂ b := ha.symm.trans hb
        obtain ⟨d, hd, _⟩ := (hfree.overlap a b).mp hab
        exact ⟨d, ha.trans (congrArg i₁ hd)⟩
      have hRoleOverlap :
          ∀ r : Fin 3, ∀ x y : W,
            Role T r x → Role T r y →
            Left x → Right x → Left y → Right y → x = y := by
        intro r x y hx hy hxl hxr hyl hyr
        obtain ⟨d, hd⟩ := hShared x hxl hxr
        obtain ⟨e, he⟩ := hShared y hyl hyr
        have hdRole : Role Root r d := by
          have hT : Role T r (i₁ (f₁ d)) := by
            rw [← hd]
            exact hx
          exact (role_embedding_iff f₁ r d).mp
            ((role_embedding_iff i₁ r (f₁ d)).mp hT)
        have heRole : Role Root r e := by
          have hT : Role T r (i₁ (f₁ e)) := by
            rw [← he]
            exact hy
          exact (role_embedding_iff f₁ r e).mp
            ((role_embedding_iff i₁ r (f₁ e)).mp hT)
        have hde : d = e :=
          root_role_unique h₁ f₁ hc₁ r d e hdRole heRole
        calc
          x = i₁ (f₁ d) := hd
          _ = i₁ (f₁ e) := congrArg (fun t => i₁ (f₁ t)) hde
          _ = y := he.symm
      have hLeft :
          SquareFreeOn (Role T 0) (Role T 1) Left (Domain T) :=
        squareFreeOn_embedding ih₁ i₁
      have hRight :
          SquareFreeOn (Role T 0) (Role T 1) Right (Domain T) :=
        squareFreeOn_embedding ih₂ i₂
      exact squareFree_of_freeUnion
        (Role T 0) (Role T 1) Left Right (Domain T)
        hCover hEdge
        (hRoleOverlap 0) (hRoleOverlap 1)
        hLeft hRight

end StructuralRamsey.Structure.NativePowerObstruction
