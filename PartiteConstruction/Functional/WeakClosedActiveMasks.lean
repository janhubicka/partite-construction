import PartiteConstruction.Functional.ActiveOutputRootTransport
import PartiteConstruction.Functional.WeakTransversalTests

/-!
# Function-closed weak vertex sets are exactly the mask-complete ones

The true U-closed analogue in a genuine TRANSVERSAL functional
partite system is: every ambient output-part root mask over
inputs in S is still active in the EXACT weak restriction to S.

The implication from closure to mask preservation is immediate.
Conversely, given any ambient function output y, choose its part q.
Mask preservation supplies a surviving output z of the SAME part;
ambient target transversality forces y=z, so y belongs to S.

This is stronger than nonempty-domain preservation for multivalued
functions. A weak set can retain one output part of a fibre while
losing another. The exact weak vertex set is never enlarged to a
generated closure.

The unary lost-output and two-output different-part regressions
are explained in docs/functional-closed-iff-active-masks-20261017.md.
The theorem is internal to ONE genuine functional System, not a
domain-reflecting assertion about arbitrary EHN projections.
-/

namespace StructuralRamsey.FunctionalPartite

universe u v
variable {L : Language.{u}} {P V : Type v}

/-- The exact functional analogue of U-closedness for a genuine
partite system: the weak substructure on S has ALL the SAME
ambient active output-part root bits precisely when S is closed.

No finite carrier, singleton-valuedness or artificial closure
hull is assumed; the implication from masks to closure uses the
actual fibre-output transversality invariant. -/
theorem System.isClosed_iff_weakActiveOutputMasks
    (B : System L P V) (S : Set V) :
    B.toStructure.IsClosed S ↔
      ∀ (F : L.FuncSymbol)
        (xs : Fin (L.funcArity F) → S)
        (q : P),
        B.ActiveOutputAtPart F (Subtype.val ∘ xs) q ↔
          (B.weakInduce S).ActiveOutputAtPart F xs q := by
  constructor
  · intro hClosed F xs q
    constructor
    · rintro ⟨y, hy, hPart⟩
      have hyS : y ∈ S :=
        hClosed F (Subtype.val ∘ xs)
          (fun i => (xs i).2) hy
      exact ⟨⟨y, hyS⟩, hy, hPart⟩
    · rintro ⟨y, hy, hPart⟩
      exact ⟨y.1, hy, hPart⟩
  · intro hMasks F args hArgs y hy
    let xs : Fin (L.funcArity F) → S :=
      fun i => ⟨args i, hArgs i⟩
    have hAmbient :
        B.ActiveOutputAtPart F (Subtype.val ∘ xs)
          (B.part y) := by
      exact ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzPart⟩ :=
      (hMasks F xs (B.part y)).mp hAmbient
    have hPartEq : B.part y = B.part z.1 := hzPart.symm
    have hEq : y = z.1 :=
      B.funcTransversal F args y z.1 hy hz hPartEq
    rw [hEq]
    exact z.2

/-- It is enough to REFLECT ambient active output-part masks in
the exact weak restriction; the opposite implication holds for
every weak subset without any closedness hypothesis. -/
theorem System.isClosed_iff_ambientActiveMasks_reflected
    (B : System L P V) (S : Set V) :
    B.toStructure.IsClosed S ↔
      ∀ (F : L.FuncSymbol)
        (xs : Fin (L.funcArity F) → S) (q : P),
        B.ActiveOutputAtPart F (Subtype.val ∘ xs) q →
          (B.weakInduce S).ActiveOutputAtPart F xs q := by
  constructor
  · intro hc F xs q h
    exact ((B.isClosed_iff_weakActiveOutputMasks S).mp hc F xs q).mp h
  · intro h
    apply (B.isClosed_iff_weakActiveOutputMasks S).mpr
    intro F xs q
    constructor
    · exact h F xs q
    · rintro ⟨y, hy, hq⟩
      exact ⟨y.1, hy, hq⟩

/-- The canonical weak vertex inclusion can be a FULL functional
partite embedding exactly when the weak set is function-closed.

For arbitrary S the inclusion is already a WEAK graph embedding;
the extra fibre-surjectivity required by a genuine full embedding
is equivalent to the absence of missing ambient output vertices.
No other re-embedding of the abstract weak structure is ruled out. -/
theorem System.isClosed_iff_weakInclusion_full
    (B : System L P V) (S : Set V) :
    B.toStructure.IsClosed S ↔
      ∃ e : Embedding (B.weakInduce S) B,
        ∀ x : S, e x = x.1 := by
  constructor
  · intro hClosed
    let e : Embedding (B.weakInduce S) B := {
      toEmbedding := Structure.inclusion B.toStructure S hClosed
      map_part := by
        intro x
        rfl
    }
    exact ⟨e, fun _ => rfl⟩
  · rintro ⟨e, hInclusion⟩
    intro F xs hArgs y hy
    let sourceArgs : Fin (L.funcArity F) → S :=
      fun i => ⟨xs i, hArgs i⟩
    have hArgsEq : (e.toFun ∘ sourceArgs) = xs := by
      funext i
      exact hInclusion (sourceArgs i)
    have hyTarget : y ∈ B.func F (e.toFun ∘ sourceArgs) := by
      simpa only [hArgsEq] using hy
    rw [← e.map_func F sourceArgs] at hyTarget
    obtain ⟨z, hz, hImage⟩ := hyTarget
    have hSame : y = z.1 := by
      calc
        y = e z := hImage.symm
        _ = z.1 := hInclusion z
    rw [hSame]
    exact z.2

end StructuralRamsey.FunctionalPartite
