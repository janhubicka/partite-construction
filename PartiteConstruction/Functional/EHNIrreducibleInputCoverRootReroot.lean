import PartiteConstruction.Functional.OriginalPartialFaithfulRootReroot

/-!
# Track D: full root reflection from actual irreducible input-test covers

The EHN projection is FULL on every irreducible full source test. Here we
make an exact positive use of that property: if each primitive old relation
input tuple and each primitive old function input tuple lies inside a
FULL irreducible source substructure, then the global map reflects old
relations and nonempty function domains. For a vertex-injective EHN map,
this gives a FULL embedding on the same vertex map.

This condition is explicitly quantified over ACTUAL original source
input tuples; no weak vertex test is closed or replaced, and defined-empty
Option(Set) applications are not confused with source-undefined fibres.

A corollary feeds the criterion into the previously isolated strict
original-partial side-tree rerooting theorem. It still requires a selected
absolute side target whose rooted image is contained in a single B-piece.
The input-cover premise is STRONG and does not hold for arbitrary reducible
roots; the colliding HJ-history target problem remains open.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V : Type v}

/-- Every old relation INPUT tuple (positive or negative) is carried by
some genuinely FULL irreducible closed source test on the same carrier.
This is stronger than covering only source-positive relation incidences. -/
def RelationInputsCoveredByIrreducibles (C : Structure L U) : Prop :=
  ∀ R (xs : Fin (L.relArity R) → U),
    ∃ (S : Set U) (hS : C.IsClosed S),
      (C.induce S hS).Irreducible ∧ ∀ i, xs i ∈ S

/-- Every old function INPUT tuple is carried by some genuinely FULL
irreducible closed source test, even when its source value is undefined.
That latter inclusion is essential for domain reflection. -/
def FunctionInputsCoveredByIrreducibles (C : Structure L U) : Prop :=
  ∀ F (xs : Fin (L.funcArity F) → U),
    ∃ (S : Set U) (hS : C.IsClosed S),
      (C.induce S hS).Irreducible ∧ ∀ i, xs i ∈ S

/-- Any EHN projection reflects positive target relations on all actual
source tuples when the inputs are covered by FULL irreducible tests.
No injectivity hypothesis on the global EHN map is required. -/
theorem IsEHNHomomorphismEmbedding.reflect_rel_of_irreducible_input_cover
    {C : Structure L U} {D : Structure L V}
    {p : U → V}
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (hCover : RelationInputsCoveredByIrreducibles C) :
    ∀ R (xs : Fin (L.relArity R) → U),
      D.rel R (p ∘ xs) → C.rel R xs := by
  intro R xs hTarget
  obtain ⟨S, hS, hIrr, hInputs⟩ := hCover R xs
  let Small : Structure L S := C.induce S hS
  let inc : Embedding Small C := inclusion C S hS
  obtain ⟨e, he⟩ := hp.2 Small hIrr inc
  let q : Fin (L.relArity R) → S := fun i => ⟨xs i, hInputs i⟩
  have hEq : e ∘ q = p ∘ xs := by
    funext i
    exact he (q i)
  have hTarget' : D.rel R (e ∘ q) := by
    rw [hEq]
    exact hTarget
  have hSmall : Small.rel R q := (e.map_rel_iff R q).mp hTarget'
  change C.rel R (Subtype.val ∘ q) at hSmall
  have hq : Subtype.val ∘ q = xs := by
    funext i
    rfl
  rw [hq] at hSmall
  exact hSmall

/-- Any EHN projection reflects source-defined function DOMAIN status
when every input tuple is contained in an irreducible FULL source test.
Complete output-fibre reflection on defined tuples is already the
previously verified EHN fibre-exactness theorem. -/
theorem IsEHNHomomorphismEmbedding.reflect_domain_of_irreducible_input_cover
    {C : Structure L U} {D : Structure L V}
    {p : U → V}
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (hCover : FunctionInputsCoveredByIrreducibles C) :
    ∀ F (xs : Fin (L.funcArity F) → U),
      (D.func F (p ∘ xs)).Nonempty →
        (C.func F xs).Nonempty := by
  intro F xs hTarget
  obtain ⟨S, hS, hIrr, hInputs⟩ := hCover F xs
  let Small : Structure L S := C.induce S hS
  let inc : Embedding Small C := inclusion C S hS
  obtain ⟨e, he⟩ := hp.2 Small hIrr inc
  let q : Fin (L.funcArity F) → S := fun i => ⟨xs i, hInputs i⟩
  have hEq : e ∘ q = p ∘ xs := by
    funext i
    exact he (q i)
  obtain ⟨y, hy⟩ := hTarget
  have hy' : y ∈ D.func F (e ∘ q) := by
    rw [hEq]
    exact hy
  have himg : y ∈ imageSet e (Small.func F q) := by
    rw [e.map_func F q]
    exact hy'
  obtain ⟨z, hz, _⟩ := himg
  refine ⟨z.1, ?_⟩
  change z.1 ∈ C.func F (Subtype.val ∘ q) at hz
  have hq : Subtype.val ∘ q = xs := by
    funext i
    rfl
  rw [hq] at hz
  exact hz

/-- A VERTEX-INJECTIVE EHN map becomes a FULL native embedding whenever
all original primitive input tuples are covered by full irreducible tests.
We do not assume root irreducibility and do not add extra output-fibre
hypotheses for source-defined function applications. -/
theorem IsEHNHomomorphismEmbedding.fullEmbedding_of_irreducible_input_covers
    {C : Structure L U} {D : Structure L V}
    {p : U → V}
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (hInjective : Function.Injective p)
    (hRelCover : RelationInputsCoveredByIrreducibles C)
    (hFuncCover : FunctionInputsCoveredByIrreducibles C) :
    ∃ e : Embedding C D, ∀ x : U, e x = p x :=
  hp.fullEmbedding_iff_inj_reflect_rel_domain.mpr
    ⟨hInjective,
      hp.reflect_rel_of_irreducible_input_cover hRelCover,
      hp.reflect_domain_of_irreducible_input_cover hFuncCover⟩

end StructuralRamsey.Structure


namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {H E VB Y : Type v}

/-- Input-cover specialization of the strict original-partial reroot
criterion for a REDUCIBLE common separator.  All nonfull behaviour of
the ambient SIDE outside the chosen Root is still permitted.

It does NOT say that the HJ mixed root satisfies the stated covers or
that its canonical part labels are injective. -/
theorem HasOriginalPartialTreeExtensionCompletion.of_partial_side_root_input_covers
    {Root : Structure L H} {Side : Structure L E}
    (Base : Structure L VB)
    (hBase : Base.Irreducible)
    (s : Embedding Root Side)
    (q : Embedding Root Base)
    (T : Structure L Y)
    (hT : TreeAmalgam Base Y T)
    (p : E → Y)
    (hp : Side.IsOriginalPartialHomomorphismEmbedding T p)
    (hInjective : Function.Injective (p ∘ s))
    (hRelCover : RelationInputsCoveredByIrreducibles Root)
    (hFuncCover : FunctionInputsCoveredByIrreducibles Root)
    (piece : Embedding Base T)
    (hPiece : ∀ x : H, ∃ y : VB, p (s x) = piece y) :
    HasOriginalPartialTreeExtensionCompletion
      (Start := Base) Base s q := by
  have hRoot : Root.IsEHNHomomorphismEmbedding T (p ∘ s) :=
    hp.toEHN.comp s.isEHNHomomorphismEmbedding
  exact HasOriginalPartialTreeExtensionCompletion.of_partial_side_root_defects_absent
    Base hBase s q T hT p hp hInjective
    (hRoot.reflect_rel_of_irreducible_input_cover hRelCover)
    (hRoot.reflect_domain_of_irreducible_input_cover hFuncCover)
    piece hPiece

end StructuralRamsey.Structure
