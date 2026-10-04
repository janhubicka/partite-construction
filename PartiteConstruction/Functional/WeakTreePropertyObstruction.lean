import PartiteConstruction.Functional.FunctionalTreeAmalgam
import PartiteConstruction.Structure.WeakSubstructure

/-! # Weak substructures obstruct full functional tree completions

The function-language form of sparsening property (2), if read with the
survey's full set-valued-function homomorphism, is already false for a
two-point unary-function structure.

Let B have two vertices and one unary function which sends each vertex to the
other vertex.  Every vertex of every tree amalgam of copies of B has a
nonempty function fibre.  But if a copy of B sits in an ambient structure C,
the weak substructure on the single image of false forgets the output
e(true), so its unique unary fibre is empty.  No full function homomorphism
from this weak singleton into any B-tree can therefore exist.

Thus the weak-substructure statement can only use the weak/graph
homomorphism-embedding notion, or else the test substructures must be closed.
-/

namespace StructuralRamsey.Structure.WeakTreePropertyObstruction

def language : Language where
  RelSymbol := Empty
  FuncSymbol := Unit
  relArity := Empty.elim
  funcArity _ := 1

/-- The two-cycle unary partial-function structure. -/
def base : Structure language Bool where
  rel R := Empty.elim R
  func _ x := {y | y ≠ x (0 : Fin 1)}

def inputFalse : Fin 1 → Bool := fun _ => false

theorem true_mem_false_fibre :
    true ∈ base.func () inputFalse := by
  change true ≠ false
  decide

/-- The base is irreducible in the full free-amalgamation sense. -/
theorem base_irreducible : base.Irreducible := by
  intro H E F C Dsrc Esrc Fsrc Csrc sE sF iE iF hfree e
  have hval :
      e true ∈ Csrc.func () (e ∘ inputFalse) := by
    have himg :
        e true ∈ imageSet e (base.func () inputFalse) :=
      ⟨true, true_mem_false_fibre, rfl⟩
    rw [e.map_func () inputFalse] at himg
    exact himg
  rcases (hfree.func_iff () (e ∘ inputFalse) (e true)).mp hval with
    hleft | hright
  · rcases hleft with ⟨a, b, hb, hargs, hout⟩
    refine Or.inl ?_
    intro q
    cases q with
    | false =>
        refine ⟨a (0 : Fin 1), ?_⟩
        have h := congrFun hargs (0 : Fin 1)
        calc
          e false = (e ∘ inputFalse) (0 : Fin 1) := rfl
          _ = (iE ∘ a) (0 : Fin 1) := h
          _ = iE (a (0 : Fin 1)) := rfl
    | true =>
        exact ⟨b, hout⟩
  · rcases hright with ⟨a, b, hb, hargs, hout⟩
    refine Or.inr ?_
    intro q
    cases q with
    | false =>
        refine ⟨a (0 : Fin 1), ?_⟩
        have h := congrFun hargs (0 : Fin 1)
        calc
          e false = (e ∘ inputFalse) (0 : Fin 1) := rfl
          _ = (iF ∘ a) (0 : Fin 1) := h
          _ = iF (a (0 : Fin 1)) := rfl
    | true =>
        exact ⟨b, hout⟩

/-- Every input has at least one output. -/
def HasOutput {X : Type} (A : Structure language X) : Prop :=
  ∀ x : X, ∃ y : X, y ∈ A.func () (fun _ : Fin 1 => x)

theorem base_hasOutput : HasOutput base := by
  intro x
  cases x with
  | false =>
      exact ⟨true, by
        change true ≠ false
        decide⟩
  | true =>
      exact ⟨false, by
        change false ≠ true
        decide⟩

/-- Full embeddings preserve existence of an output over image inputs. -/
theorem HasOutput.at_embedding
    {X Y : Type} {A : Structure language X} {B : Structure language Y}
    (hA : HasOutput A) (e : Embedding A B) (x : X) :
    ∃ y : Y, y ∈ B.func () (fun _ : Fin 1 => e x) := by
  obtain ⟨z, hz⟩ := hA x
  refine ⟨e z, ?_⟩
  have himg :
      e z ∈ imageSet e (A.func () (fun _ : Fin 1 => x)) :=
    ⟨z, hz, rfl⟩
  rw [e.map_func () (fun _ : Fin 1 => x)] at himg
  have hargs :
      e ∘ (fun _ : Fin 1 => x) =
        (fun _ : Fin 1 => e x) := by
    funext i
    rfl
  rw [hargs] at himg
  exact himg

/-- Every vertex of a tree amalgam of copies of the base still has an output. -/
theorem TreeAmalgam.hasOutput
    {X : Type} {T : Structure language X}
    (hT : TreeAmalgam base X T) :
    HasOutput T := by
  induction hT with
  | copy e hsurj =>
      intro x
      obtain ⟨b, rfl⟩ := hsurj x
      exact base_hasOutput.at_embedding e b
  | @glue X₁ X₂ Z X T₁ T₂ D T
      h₁ h₂ f₁ f₂ hc₁ hc₂ i₁ i₂ hfree ih₁ ih₂ =>
      intro x
      rcases hfree.covers x with ⟨a, rfl⟩ | ⟨b, rfl⟩
      · exact ih₁.at_embedding i₁ a
      · exact ih₂.at_embedding i₂ b

variable {X : Type} {C : Structure language X}

/-- The singleton consisting of the false vertex of an embedded base copy. -/
def badSet (e : Embedding base C) : Set X :=
  {x | x = e false}

def badPoint (e : Embedding base C) : badSet e :=
  ⟨e false, rfl⟩

/-- The weak singleton forgets the unique output e(true). -/
theorem bad_fibre_empty
    (e : Embedding base C) :
    (C.weakInduce (badSet e)).func ()
        (fun _ : Fin 1 => badPoint e) = ∅ := by
  ext y
  constructor
  · intro hy
    have hyC :
        y.1 ∈ C.func (show language.FuncSymbol from ())
          (fun _ : Fin 1 => e false) := hy
    have hargs :
        (fun _ : Fin 1 => e false) = e ∘ inputFalse := by
      funext i
      rfl
    have hyC' :
        y.1 ∈ C.func (show language.FuncSymbol from ())
          (e ∘ inputFalse) :=
      Eq.mp
        (congrArg
          (fun args =>
            y.1 ∈ C.func (show language.FuncSymbol from ()) args)
          hargs)
        hyC
    have hyImg :
        y.1 ∈ imageSet e (base.func () inputFalse) := by
      rw [e.map_func () inputFalse]
      exact hyC'
    rcases hyImg with ⟨b, hb, heq⟩
    change b ≠ false at hb
    have hyFalse : y.1 = e false := y.2
    have heb : e b = e false := heq.trans hyFalse
    have hbFalse : b = false := e.injective heb
    exact hb hbFalse
  · intro hy
    change False at hy
    exact hy.elim

/-- No full function homomorphism from the bad weak singleton can land in a
tree amalgam of copies of the base. -/
theorem no_homomorphism_to_tree
    (e : Embedding base C)
    {Y : Type} {T : Structure language Y}
    (hT : TreeAmalgam base Y T) :
    ¬ ∃ f : badSet e → Y,
        (C.weakInduce (badSet e)).IsHomomorphism T f := by
  rintro ⟨f, hf⟩
  obtain ⟨y, hy⟩ := hT.hasOutput (f (badPoint e))
  have hfun := hf.2 () (fun _ : Fin 1 => badPoint e)
  have hy' :
      y ∈ T.func () (f ∘ (fun _ : Fin 1 => badPoint e)) := by
    have hargs :
        f ∘ (fun _ : Fin 1 => badPoint e) =
          (fun _ : Fin 1 => f (badPoint e)) := by
      funext i
      rfl
    rw [hargs]
    exact hy
  have himg :
      y ∈ imageSet f
        ((C.weakInduce (badSet e)).func ()
          (fun _ : Fin 1 => badPoint e)) := by
    rw [hfun]
    exact hy'
  rw [bad_fibre_empty e] at himg
  rcases himg with ⟨z, hz, _⟩
  change False at hz
  exact hz.elim

/-- A fortiori, no survey full homomorphism-embedding exists. -/
theorem no_homomorphismEmbedding_to_tree
    (e : Embedding base C)
    {Y : Type} {T : Structure language Y}
    (hT : TreeAmalgam base Y T) :
    ¬ ∃ f : badSet e → Y,
        (C.weakInduce (badSet e)).IsHomomorphismEmbedding T f := by
  rintro ⟨f, hf⟩
  exact no_homomorphism_to_tree e hT ⟨f, hf.1⟩

end StructuralRamsey.Structure.WeakTreePropertyObstruction
