import PartiteConstruction.Functional.AmbientRelativeWeakPullback
import PartiteConstruction.Functional.AmbientACopyOriginalPartialHistory
import PartiteConstruction.Functional.FunctionalTreeAmalgam

/-!
# Strict functional B-tree witnesses with exact ambient A-copy histories

This is the general SET-VALUED FUNCTION-LANGUAGE small-projected-image
transfer. The test is the precise vertex set S; the image is the precise
set p '' S. There is no generated closure hull, singleton-value
reduction or temporary nonfunctional intermediate picture.

A local witness consists of:
* a genuine STRICT full-functional tree amalgam of Base-copies;
* the ambient-relative weak functional HE, which preserves all positive
  incidences, and whole fibres whenever their ambient outputs survive;
* one compatible full A-copy inside an irreducible constituent of
  the target for EACH ACTUAL ambient full A-copy intersecting S;
* a finite list of arbitrary projected history predicates that
  identify exactly which projected bits survive equality in the
  completion target.

Every EHN projection pulls such a witness back from p[S] to S;
the original A must be irreducible to turn an EHN A-image into a FULL
target A-embedding. On genuinely closed S the same completion map
becomes an original-2019 partial homomorphism-embedding.

This establishes the conditional SMALL-PROJECTION branch of the
published two-case induction. It does not manufacture predecessor
strict-tree witnesses, or solve the MAXIMAL-PROJECTION mixed root.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {U VB W P : Type v}

/-- Exact ambient A-copy intersection control for any vertex set S.
A partial A-copy is protected only when it comes by restricting an
ACTUAL full embedding A -> C, not when weak truncation creates a
new irreducible partial structure with missing function outputs. -/
def SetAmbientACopyIntersections
    (A : Structure L U) (C : Structure L W)
    {Z : Type v} (Target : Structure L Z)
    (S : Set W) (f : S → Z) : Prop :=
  ∀ e : Embedding A C,
    ∃ eT : Embedding A Target,
      eT.ContainedInIrreducible ∧
      ∀ (a : U) (ha : e a ∈ S),
        eT a = f ⟨e a, ha⟩

/-- Equality in the target respects every specified projected
membership predicate on the EXACT tested set. -/
def SetRespectsProjectedHistory
    (p : W → P) (S : Set W)
    {Z : Type v} (f : S → Z)
    (history : List (Set P)) : Prop :=
  ∀ H ∈ history, ∀ x y : S,
    f x = f y → (p x.1 ∈ H ↔ p y.1 ∈ H)

/-- Full-functional strict B-tree witness at an arbitrary exact WEAK
source set, with the original-partial relative fibre law, actual
ambient full A-copy protection and projected history. -/
def SetAmbientRelativeWeakTreeWitness
    (A : Structure L U) (Base : Structure L VB)
    (C : Structure L W) (p : W → P)
    (S : Set W) (history : List (Set P)) : Prop :=
  ∃ (Z : Type v) (Target : Structure L Z),
    TreeAmalgam Base Z Target ∧
    ∃ f : S → Z,
      IsAmbientRelativeWeakHE C S Target f ∧
      SetAmbientACopyIntersections A C Target S f ∧
      SetRespectsProjectedHistory p S f history

namespace SetAmbientRelativeWeakTreeWitness

/-- A tree witness of an exact weak set becomes a genuine original
partial-function HE on the same target whenever S is closed in C. -/
theorem closed_test
    {A : Structure L U} {Base : Structure L VB}
    {C : Structure L W} {p : W → P}
    {S : Set W} {history : List (Set P)}
    (h : SetAmbientRelativeWeakTreeWitness A Base C p S history)
    (hClosed : C.IsClosed S) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : S → Z,
        IsOriginalPartialHomomorphismEmbedding (C.induce S hClosed) Target f ∧
        SetAmbientACopyIntersections A C Target S f ∧
        SetRespectsProjectedHistory p S f history := by
  obtain ⟨Z, Target, hTree, f, hWeak, hCopies, hHist⟩ := h
  exact ⟨Z, Target, hTree, f,
    hWeak.toOriginalPartialHE_of_closed hClosed, hCopies, hHist⟩

/-- The exact image of an EHN projection carries all the predecessor
strict functional completion data back to the tested source, including
actual ambient A-copy embeddings and finite projected history.

The projection is assumed only EHN, not globally a full function
homomorphism. All values can be genuinely multivalued, but the
underlying functional PARTITE systems still retain transversal
output fibres in the actual recursive construction. -/
theorem pullback_ehn
    {A : Structure L U} {Base : Structure L VB}
    {C : Structure L W} {D : Structure L P}
    {p : W → P}
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (hA : A.Irreducible)
    (S : Set W) (history : List (Set P))
    (hD : SetAmbientRelativeWeakTreeWitness
      A Base D (id : P → P) (p '' S) history) :
    SetAmbientRelativeWeakTreeWitness
      A Base C p S history := by
  obtain ⟨Z, Target, hTree, g, hWeakD, hCopiesD, hHistD⟩ := hD
  let pS : S → p '' S :=
    fun x => ⟨p x.1, ⟨x.1, x.2, rfl⟩⟩
  let f : S → Z := g ∘ pS
  have hWeak : IsAmbientRelativeWeakHE C S Target f :=
    hWeakD.pullback_ehn_exact hp S g
  have hCopies : SetAmbientACopyIntersections A C Target S f := by
    intro e
    obtain ⟨eD, heD⟩ := hp.2 A hA e
    obtain ⟨eT, hContains, hAgrees⟩ := hCopiesD eD
    refine ⟨eT, hContains, ?_⟩
    intro a ha
    have haD : eD a ∈ p '' S := by
      rw [heD a]
      exact ⟨e a, ha, rfl⟩
    calc
      eT a = g ⟨eD a, haD⟩ := hAgrees a haD
      _ = f ⟨e a, ha⟩ := by
        change g (⟨eD a, haD⟩ : p '' S) =
          g (pS ⟨e a, ha⟩)
        congr 1
        apply Subtype.ext
        exact heD a
  have hHist : SetRespectsProjectedHistory p S f history := by
    intro H hH x y hxy
    have hh := hHistD H hH (pS x) (pS y) hxy
    change (p x.1 ∈ H ↔ p y.1 ∈ H) at hh
    exact hh
  exact ⟨Z, Target, hTree, f, hWeak, hCopies, hHist⟩

/-- Small-image branch specialized to a CLOSED source test:
the source has an original-partial HE into a genuine strict
full-functional B-tree, and A-intersections and all requested
histories survive. The only premise is the predecessor's witness
for the exact weak image, not an unproved arbitrary-root lemma. -/
theorem pullback_closed_ehn
    {A : Structure L U} {Base : Structure L VB}
    {C : Structure L W} {D : Structure L P}
    {p : W → P}
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (hA : A.Irreducible)
    (S : Set W) (hClosed : C.IsClosed S)
    (history : List (Set P))
    (hD : SetAmbientRelativeWeakTreeWitness
      A Base D (id : P → P) (p '' S) history) :
    ∃ (Z : Type v) (Target : Structure L Z),
      TreeAmalgam Base Z Target ∧
      ∃ f : S → Z,
        IsOriginalPartialHomomorphismEmbedding
          (C.induce S hClosed) Target f ∧
        SetAmbientACopyIntersections A C Target S f ∧
        SetRespectsProjectedHistory p S f history :=
  (pullback_ehn hp hA S history hD).closed_test hClosed

end SetAmbientRelativeWeakTreeWitness

end StructuralRamsey.Structure
