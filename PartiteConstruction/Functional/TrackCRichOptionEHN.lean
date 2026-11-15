import PartiteConstruction.Functional.TrackCOptionIrredNative
import PartiteConstruction.Structure.PartialSetFunctionsClosed
import PartiteConstruction.Functional.WeakInvariant

/-!
# Track C: an EHN map of faithful Dom/Empty encodings is a rich partial HE

This is the F3+F4 SAME-MAP interface needed before completing the
English-first second native B-cover route for Appendix A.

A rich genuine Option(Set) structure has independent input definedness,
so an undefined value is NOT a defined empty fibre. The globally
positive native EHN map between the canonical Dom/Empty encodings
preserves all defined source values by the already verified F3 theorem.

For every full genuinely closed-free-irreducible partial test E,
the already verified F4 theorem makes its canonical Dom/Empty encoding
native irreducible. The EHN condition is therefore FULL on that exact
test. The verified F1 inverse embedding dictionary translates this
same map back to an exact FULL genuine Option(Set) copy, including
domain reflection and defined-empty applications on E.

The result does not assert global injectivity, global domain
reflection, or arbitrary native-to-OLD tagged protection. The native
source and target here are both the exact canonical faithful
Dom/Empty encodings, not arbitrary legal targets.

We name the resulting ORIGINAL source-defined rich HE notion using
the actual *closed-free-cover* irreducibility predicate. Its
equivalence with any separately defined universal rich partial
irreducibility API remains a distinct formal obligation.
-/

namespace StructuralRamsey.PartialSetStructure

open StructuralRamsey
open StructuralRamsey.Structure

universe u v

variable {L : Language.{u}} {U V W : Type v}

/-- Original source-defined genuinely partial HE with FULL protection
of every genuinely irreducible closed-free-cover test. A full test
includes the entire Option(Set) domain bit, not merely the native
output incidence graph. -/
def IsOptionClosedFreeHomomorphismEmbedding
    (A : PartialSetStructure L U)
    (B : PartialSetStructure L V)
    (f : U → V) : Prop :=
  IsOriginalPartialHomomorphism A B f ∧
  ∀ {X : Type v} (E : PartialSetStructure L X),
    E.IsOptionClosedFreeIrreducible →
    ∀ e : Embedding E A,
      ∃ g : Embedding E B,
        ∀ x : X, g.toFun x = f (e.toFun x)

/-- The composed map is again genuinely partial source-defined
and protected on every original irreducible closed-free test,
without enlarging the source or taking any closure hull. -/
theorem IsOptionClosedFreeHomomorphismEmbedding.comp
    {A : PartialSetStructure L U}
    {B : PartialSetStructure L V}
    {C : PartialSetStructure L W}
    {f : U → V} {g : V → W}
    (hg : IsOptionClosedFreeHomomorphismEmbedding B C g)
    (hf : IsOptionClosedFreeHomomorphismEmbedding A B f) :
    IsOptionClosedFreeHomomorphismEmbedding A C (g ∘ f) := by
  constructor
  · exact hg.1.comp hf.1
  · intro X E hE e
    obtain ⟨m, hm⟩ := hf.2 E hE e
    obtain ⟨n, hn⟩ := hg.2 E hE m
    refine ⟨n, ?_⟩
    intro x
    exact (hn x).trans (congrArg g (hm x))

/-- A genuine native EHN projection between canonical faithful
Dom/Empty encodings induces a genuinely partial ORIGINAL
source-defined homomorphism-embedding on precisely the same
vertex map, including FULL copies of every rich
closed-free-irreducible test.

No no-defined-empty restriction is made. -/
theorem IsOptionClosedFreeHomomorphismEmbedding.ofDomainEmptyEHN
    {A : PartialSetStructure L U}
    {B : PartialSetStructure L V}
    {f : U → V}
    (hf : A.domainEmptyEncode.IsEHNHomomorphismEmbedding
      B.domainEmptyEncode f) :
    IsOptionClosedFreeHomomorphismEmbedding A B f := by
  refine ⟨hf.ofDomainEmptyEncode_originalPartial, ?_⟩
  intro X E hE e
  let eNative : Structure.Embedding
      E.domainEmptyEncode A.domainEmptyEncode :=
    e.domainEmptyEncode
  have hNativeIrred : E.domainEmptyEncode.Irreducible :=
    IsOptionClosedFreeIrreducible.domainEmptyEncode_irreducible E hE
  obtain ⟨g, hg⟩ := hf.2 E.domainEmptyEncode hNativeIrred eNative
  let gPartial : Embedding E B :=
    Embedding.ofDomainEmptyEncode g
  refine ⟨gPartial, ?_⟩
  intro x
  exact hg x

end StructuralRamsey.PartialSetStructure
