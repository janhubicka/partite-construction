import PartiteConstruction.Functional.ActiveOutputRootTransport

/-!
# Characterization of FULL functional partite embeddings by U-style masks

Between TRUE partite systems with TRANSVERSAL set-valued output fibres,
a part-preserving injective map which reflects ordinary relations,
preserves positive function incidences, and preserves-and-reflects
EVERY output-part ACTIVE mask is automatically a FULL FUNCTIONAL
embedding.

Indeed each target output z has a part q. The matching active-source
mask supplies y of the same part, whose image is a target output.
Target transversality forces z=f(y), proving fibre SURJECTIVITY.
No singleton-function assumption is needed.

The reverse direction is immediate for full embeddings, using the
previously verified activeOutputAtPart_iff.

This is the native function-language substitute for full closure-root
embedding tests in the verified All Those Ramsey Classes argument.
It is not a theorem about weak EHN projections, which need not
REFLECT newly active target domains, nor a proof that two arbitrary
weak boundary completions have compatible target B-trees.
-/

namespace StructuralRamsey.FunctionalPartite

universe u v
variable {L : Language.{u}} {P V W : Type v}

/-- Build a FULL partite functional embedding from
  1. injectivity and ordinary relation reflection,
  2. part preservation,
  3. POSITIVE function-incidence preservation,
  4. exact active OUTPUT-PART masks for all input tuples.

The target System's `funcTransversal` establishes the missing
fibre-surjectivity, even for genuinely multivalued functions. -/
def Embedding.of_activeMasks
    (A : System L P V) (B : System L P W)
    (f : V → W)
    (hfInj : Function.Injective f)
    (hfRel : ∀ R xs, B.rel R (f ∘ xs) ↔ A.rel R xs)
    (hfPart : ∀ x, B.part (f x) = A.part x)
    (hfPositive : ∀ F xs y,
      y ∈ A.func F xs → f y ∈ B.func F (f ∘ xs))
    (hfMasks : ∀ F xs q,
      A.ActiveOutputAtPart F xs q ↔
      B.ActiveOutputAtPart F (f ∘ xs) q) :
    Embedding A B where
  toEmbedding := {
    toFun := f
    injective := hfInj
    map_rel_iff := hfRel
    map_func := by
      intro F xs
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hfPositive F xs y hy
      · intro hz
        have hActive :
            B.ActiveOutputAtPart F (f ∘ xs) (B.part z) :=
          ⟨z, hz, rfl⟩
        obtain ⟨y, hy, hyPart⟩ :=
          (hfMasks F xs (B.part z)).mpr hActive
        have hfy : f y ∈ B.func F (f ∘ xs) :=
          hfPositive F xs y hy
        have hPart : B.part (f y) = B.part z :=
          (hfPart y).trans hyPart
        have hSame : f y = z :=
          B.funcTransversal F (f ∘ xs) (f y) z hfy hz hPart
        exact ⟨y, hy, hSame⟩
  }
  map_part := hfPart

/-- On a FIXED underlying map, the usual FULL functional partite
embedding is EQUIVALENT to positive incidences plus a complete
U-style family of output-part masks, relation reflection,
injectivity and part preservation.

This equivalence holds for arbitrary set-valued operations because
the actual target's output fibres are transversal. -/
theorem System.fullEmbedding_iff_activeMasks
    (A : System L P V) (B : System L P W)
    (f : V → W) :
    (∃ e : Embedding A B, ∀ x, e x = f x) ↔
      Function.Injective f ∧
      (∀ R xs, B.rel R (f ∘ xs) ↔ A.rel R xs) ∧
      (∀ x, B.part (f x) = A.part x) ∧
      (∀ F xs y, y ∈ A.func F xs →
        f y ∈ B.func F (f ∘ xs)) ∧
      (∀ F xs q, A.ActiveOutputAtPart F xs q ↔
        B.ActiveOutputAtPart F (f ∘ xs) q) := by
  constructor
  · rintro ⟨e, he⟩
    have heq : e.toFun = f := funext he
    rw [← heq]
    refine ⟨e.injective, e.map_rel_iff, e.map_part, ?_, ?_⟩
    · intro F xs y hy
      have hMember :
          e y ∈ Structure.imageSet e.toFun (A.func F xs) :=
        ⟨y, hy, rfl⟩
      rw [e.map_func F xs] at hMember
      exact hMember
    · intro F xs q
      exact e.activeOutputAtPart_iff F xs q
  · rintro ⟨hfInj, hfRel, hfPart, hfPositive, hfMasks⟩
    let e : Embedding A B :=
      Embedding.of_activeMasks A B f
        hfInj hfRel hfPart hfPositive hfMasks
    exact ⟨e, fun _ => rfl⟩

end StructuralRamsey.FunctionalPartite
