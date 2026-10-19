import PartiteConstruction.Functional.ControlMissingOutputDichotomy
import PartiteConstruction.Functional.FibreExactness

/-!
# Local EHN source-domain reflection suffices for closed projected images

An EHN/original-2019 partial function projection preserves complete
set-valued fibres ON DEFINED SOURCE INPUTS, but need not reflect
undefined source inputs globally. The correct sufficient
requirement to preserve closure of ONE exact source vertex set S is
only LOCAL source-domain reflection on tuples whose arguments lie
in S.

\`NoPhantomOn C D p S\` records that every D-defined input over
p[S] obtained from an actual input tuple in S is also defined in C.
Given S function-closed, EHN defined-fibre exactness then proves
that the LITERAL image p[S] is closed in D. This covers arbitrary
function arities, genuinely multivalued set-valued fibres,
repeated arguments and nullaries, without taking a closure hull or
requiring a globally full functional homomorphism.

For a genuine native partite System, the predicate exactly excludes
every \`ProjectedUndefinedAtPart\` (phantom target-output slot)
over tuples of the same exact weak S. Its absence does not
construct a compatible strict B-tree TARGET common-root profile.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V : Type v}

/-- LOCAL EHN domain reflection on one exact subset S.

For each source input tuple with all arguments in S, every
nonempty projected target function fibre must correspond to a
nonempty ambient source fibre. No condition is imposed outside
S and no function closure of S is taken. -/
def NoPhantomOn
    (C : Structure L U) (D : Structure L V)
    (p : U → V) (S : Set U) : Prop :=
  ∀ (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → S),
      (D.func F (p ∘ (Subtype.val ∘ xs))).Nonempty →
      (C.func F (Subtype.val ∘ xs)).Nonempty

/-- A FULL functional homomorphism automatically reflects defined
target domains on any exact source subset S. This is stronger
than what the EHN/native Picture projection supplies globally. -/
theorem IsHomomorphism.noPhantomOn
    {C : Structure L U} {D : Structure L V}
    {p : U → V}
    (hp : C.IsHomomorphism D p)
    (S : Set U) :
    NoPhantomOn C D p S := by
  intro F xs hTarget
  obtain ⟨y, hy⟩ := hTarget
  have hImage :
      y ∈ imageSet p (C.func F (Subtype.val ∘ xs)) := by
    rw [hp.2 F (Subtype.val ∘ xs)]
    exact hy
  obtain ⟨z, hz, _⟩ := hImage
  exact ⟨z, hz⟩

/-- All-arity LOCAL functional EHN image-closedness theorem.

The genuine source test S is required to be function-closed.
At every input tuple of that exact S, local absence of a
phantom target-defined/source-undefined domain makes the
verified EHN defined-fibre image law applicable. It lifts
any target function output back into S, proving p[S] is
function-closed in D.

No global homomorphism p or globally injective part map,
no singleton-valuedness, and no rank/vertex enlargement. -/
theorem IsEHNHomomorphismEmbedding.image_isClosed_of_noPhantom
    {C : Structure L U} {D : Structure L V}
    {p : U → V}
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (S : Set U) (hClosed : C.IsClosed S)
    (hNo : NoPhantomOn C D p S) :
    D.IsClosed (p '' S) := by
  classical
  intro F ys hys y hy
  have hLifts :
      ∀ i : Fin (L.funcArity F),
        ∃ x : S, p x.1 = ys i := by
    intro i
    obtain ⟨x, hxS, hpx⟩ := hys i
    exact ⟨⟨x, hxS⟩, hpx⟩
  choose xs hxs using hLifts
  have hArgs :
      p ∘ (Subtype.val ∘ xs) = ys := by
    funext i
    exact hxs i
  have hTarget :
      y ∈ D.func F (p ∘ (Subtype.val ∘ xs)) := by
    rw [hArgs]
    exact hy
  have hSourceDefined :
      (C.func F (Subtype.val ∘ xs)).Nonempty :=
    hNo F xs ⟨y, hTarget⟩
  have hExact :=
    hp.map_func_of_nonempty F (Subtype.val ∘ xs) hSourceDefined
  have hImage :
      y ∈ imageSet p (C.func F (Subtype.val ∘ xs)) := by
    rw [hExact]
    exact hTarget
  obtain ⟨z, hz, hpy⟩ := hImage
  exact ⟨z, hClosed F (Subtype.val ∘ xs)
    (fun i => (xs i).2) hz, hpy⟩

end StructuralRamsey.Structure

namespace StructuralRamsey.FunctionalPartite

open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {P V : Type v}

/-- For an ACTUAL native partite functional System, local
source-domain reflection on exact S is EQUIVALENT to having
NO projected source-undefined/control-defined OUTPUT-PART slot.

The equivalence does not require per-part output transversality
beyond the already encoded genuine System structure: a nonempty
target fibre supplies some output q, and any phantom slot
exhibits the corresponding domain-reflection failure. -/
theorem System.noPhantomOn_iff_noProjectedUndefined
    (B : System L P V) (D : Structure L P) (S : Set V) :
    B.toStructure.NoPhantomOn D B.part S ↔
      ∀ (F : L.FuncSymbol)
        (xs : Fin (L.funcArity F) → S) (q : P),
          ¬ B.ProjectedUndefinedAtPart D S F xs q := by
  constructor
  · intro hNo F xs q hPhantom
    exact hPhantom.1 (hNo F xs ⟨q, hPhantom.2⟩)
  · intro hNo F xs hTarget
    by_contra hSourceEmpty
    obtain ⟨q, hq⟩ := hTarget
    exact hNo F xs q ⟨hSourceEmpty, hq⟩

end StructuralRamsey.FunctionalPartite
