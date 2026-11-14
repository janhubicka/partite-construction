import PartiteConstruction.Functional.TrackCDomainEmptyFaithfulNative
import PartiteConstruction.Structure.FreeAmalgam

/-!
# Track C: true defined-empty irreducibility transfers to faithful native encoding

The standalone 2019 genuine partial syntax allows
  F(x)=none, F(x)=some empty, F(x)=some U (U nonempty).
The native collapse alone is NOT irreducibility faithful:
a mixed defined-empty binary input disappears under collapse.

In the faithful expansion every source-defined input has a Dom_F
relation, even if its value is empty. Hence any native free cut
localizes each genuine partial input to one side and, by function
closure, all outputs to that same side.

Define a direct genuine closed-free-cover irreducibility predicate on
PartialSetStructure. It quantifies over ALL pairs of actual
function-closed vertex subsets covering the source and requires
localization of every genuine primitive relation and every
source-DEFINED partial function input (including some empty).
For this precise rich source predicate, a canonical Dom/Empty native
encoding is IRREDUCIBLE in the universal native sense, against
ARBITRARY ambient native free amalgams (which need not be legal).
No predefined canonical target, root irreducibility or image hull.

A separate bridge to a previously defined *universal genuinely
partial* Irreducible predicate will be required if one is introduced
with another interface. This module makes no unjustified identification
with irreducibility of the collapsed native function graph.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Genuine definedness-sensitive closed-free-cover irreducibility.
A free cover requires closed sides, localizes each original relation,
and localizes each SOURCE-DEFINED function input irrespective of
whether its entire value is empty.

For finite full partial functions this is the direct closed-subset
no-proper-free-cut formulation, not the collapsed native predicate. -/
def IsOptionClosedFreeIrreducible (A : PartialSetStructure L V) : Prop :=
  ∀ (S T : Set V),
    A.IsClosed S →
    A.IsClosed T →
    (∀ x : V, x ∈ S ∨ x ∈ T) →
    (∀ (R : L.RelSymbol) (xs : Fin (L.relArity R) → V),
      A.rel R xs →
      (∀ i, xs i ∈ S) ∨ (∀ i, xs i ∈ T)) →
    (∀ (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → V)
      (U : Set V), A.func F xs = some U →
      (∀ i, xs i ∈ S) ∨ (∀ i, xs i ∈ T)) →
    (∀ x : V, x ∈ S) ∨ (∀ x : V, x ∈ T)

/-- Every genuine Option(Set) irreducible closed-free source is
irreducible as a native Structure after faithful Dom/Empty encoding.

The proof works against an arbitrary target native free amalgam:
the two side images pull back to truly function-closed subsets of
the source. Its native Dom relation captures even defined-empty
mixed inputs, which plain collapsing loses. -/
theorem IsOptionClosedFreeIrreducible.domainEmptyEncode_irreducible
    (A : PartialSetStructure L V)
    (hA : A.IsOptionClosedFreeIrreducible) :
    (A.domainEmptyEncode).Irreducible := by
  intro H E F C Dsrc Esrc Fsrc Csrc sE sF iE iF hFree e
  let S : Set V := {x | ∃ a : E, e.toFun x = iE.toFun a}
  let T : Set V := {x | ∃ b : F, e.toFun x = iF.toFun b}
  have hSClosed : A.IsClosed S := by
    intro G xs U hArgs hValue y hy
    have hSourceValue : y ∈ A.domainEmptyEncode.func G xs := by
      change y ∈ (A.func G xs).getD ∅
      simpa only [hValue, Option.getD_some] using hy
    have hTargetValue :
        e.toFun y ∈ Csrc.func G (e.toFun ∘ xs) := by
      rw [← e.map_func G xs]
      exact ⟨y, hSourceValue, rfl⟩
    exact iE.range_isClosed G (e.toFun ∘ xs) hArgs hTargetValue
  have hTClosed : A.IsClosed T := by
    intro G xs U hArgs hValue y hy
    have hSourceValue : y ∈ A.domainEmptyEncode.func G xs := by
      change y ∈ (A.func G xs).getD ∅
      simpa only [hValue, Option.getD_some] using hy
    have hTargetValue :
        e.toFun y ∈ Csrc.func G (e.toFun ∘ xs) := by
      rw [← e.map_func G xs]
      exact ⟨y, hSourceValue, rfl⟩
    exact iF.range_isClosed G (e.toFun ∘ xs) hArgs hTargetValue
  have hCovered : ∀ x : V, x ∈ S ∨ x ∈ T := by
    intro x
    rcases hFree.covers (e.toFun x) with hL | hR
    · exact Or.inl hL
    · exact Or.inr hR
  have hRelations :
      ∀ (R : L.RelSymbol) (xs : Fin (L.relArity R) → V),
        A.rel R xs →
        (∀ i, xs i ∈ S) ∨ (∀ i, xs i ∈ T) := by
    intro R xs hRel
    have hMapped :
        Csrc.rel (.inl R) (e.toFun ∘ xs) :=
      (e.map_rel_iff (.inl R) xs).mpr hRel
    rcases (hFree.rel_iff (.inl R) (e.toFun ∘ xs)).mp hMapped with
      ⟨a, _ha, hx⟩ | ⟨a, _ha, hx⟩
    · left
      intro i
      exact ⟨a i, congrFun hx i⟩
    · right
      intro i
      exact ⟨a i, congrFun hx i⟩
  have hDefined :
      ∀ (G : L.FuncSymbol) (xs : Fin (L.funcArity G) → V)
        (U : Set V), A.func G xs = some U →
        (∀ i, xs i ∈ S) ∨ (∀ i, xs i ∈ T) := by
    intro G xs U hValue
    have hRel : A.domainEmptyEncode.rel (.inr (.inl G)) xs := by
      change A.Defined G xs
      exact ⟨U, hValue⟩
    have hMapped :
        Csrc.rel (.inr (.inl G)) (e.toFun ∘ xs) :=
      (e.map_rel_iff (.inr (.inl G)) xs).mpr hRel
    rcases (hFree.rel_iff (.inr (.inl G)) (e.toFun ∘ xs)).mp hMapped with
      ⟨a, _ha, hx⟩ | ⟨a, _ha, hx⟩
    · left
      intro i
      exact ⟨a i, congrFun hx i⟩
    · right
      intro i
      exact ⟨a i, congrFun hx i⟩
  rcases hA S T hSClosed hTClosed hCovered hRelations hDefined with
    hLeft | hRight
  · exact Or.inl hLeft
  · exact Or.inr hRight

end StructuralRamsey.PartialSetStructure
