import PartiteConstruction.Ramsey.ClosureNativePicture
import PartiteConstruction.Ramsey.ClosureClosedMapGlue

/-! # Protected projections under native part restriction and Picture gluing

The working closed-test map predicate is strictly stronger than ordinary
partiteness. We do not change the literal 2019 predicate.

A protected part map restricts to any induced part structure through
an embedding, on the EXACT vertex support. The native Picture.build,
with all restricted-system embeddings as copy indices, then preserves the
working protected part projection as long as its core part map does.

Every protected closed U-irreducible test in a closed Picture also lies in
the core or a single old copy. The core tests embed in the restricted
part structure, and hence in any old B containing that structure.

These are genuine preservation results for the real all-embeddings
Picture construction. The native positive-power projection still needs
its own proof for arbitrary exponents.
-/

namespace StructuralRamsey.Partite.Induced

open RelStructure
universe u v
variable {L : RelLanguage.{u}} {P Q V W : Type v}

/-- Restriction to an embedded part structure preserves the protected
part projection. Weakly restricted source vertices are NOT closed here. -/
theorem restrict_isClosedPartiteOver
    {rules : ClosureDescription L}
    (A : RelStructure L Q) (D : RelStructure L P)
    (B : System L P V) (alpha : RelStructure.Embedding A D)
    (hPart : IsClosedUHomomorphismEmbedding rules B.toRelStructure D B.part) :
    IsClosedUHomomorphismEmbedding rules
      (B.restrict alpha.toFunctionEmbedding).toRelStructure
      A (B.restrict alpha.toFunctionEmbedding).part := by
  classical
  let af := alpha.toFunctionEmbedding
  let R := B.restrict af
  constructor
  · intro S z hz
    have hD : D.rel S (B.part ∘ (Subtype.val ∘ z)) :=
      hPart.1 S (Subtype.val ∘ z) hz
    have heq : alpha ∘ (R.part ∘ z) =
        B.part ∘ (Subtype.val ∘ z) := by
      funext j
      exact B.restrictedPart_spec af (z j)
    apply (alpha.map_rel_iff S (R.part ∘ z)).mp
    rw [heq]
    exact hD
  · intro Z Test hClosed hIrred e
    let eB : RelStructure.Embedding Test B.toRelStructure :=
      (RelStructure.inclusion B.toRelStructure (B.support af)).comp e
    obtain ⟨d, hd⟩ := hPart.on_test Test hClosed hIrred eB
    have hRange (x : Z) : ∃ q : Q, d x = alpha q := by
      refine ⟨R.part (e x), ?_⟩
      calc
        d x = B.part (e x).1 := hd x
        _ = alpha (R.part (e x)) :=
          (B.restrictedPart_spec af (e x)).symm
    let dA : RelStructure.Embedding Test A :=
      d.factorThroughRange alpha hRange
    refine ⟨dA, ?_⟩
    intro x
    apply alpha.injective
    calc
      alpha (dA x) = d x := (Classical.choose_spec (hRange x)).symm
      _ = B.part (e x).1 := hd x
      _ = alpha (R.part (e x)) :=
        (B.restrictedPart_spec af (e x)).symm

/-- Working protected part projections glue in the REAL all-embeddings
Picture.build. Closedness of the support and whole Picture is derived
from the closed old picture, closed core, and closed part structures. -/
theorem picture_build_isClosedPartiteOver
    {rules : ClosureDescription L}
    (A : RelStructure L Q) (D : RelStructure L P)
    (B : System L P V) (alpha : RelStructure.Embedding A D)
    (E : System L Q W)
    (hA : IsUClosed rules A) (hD : IsUClosed rules D)
    (hB : IsUClosed rules B.toRelStructure)
    (hE : IsUClosed rules E.toRelStructure)
    (hBPart : IsClosedUHomomorphismEmbedding rules
      B.toRelStructure D B.part)
    (hEPart : IsClosedUHomomorphismEmbedding rules
      E.toRelStructure A E.part) :
    IsClosedUHomomorphismEmbedding rules
      (Picture.build B alpha.toFunctionEmbedding E).toRelStructure
      D (Picture.build B alpha.toFunctionEmbedding E).part := by
  let af := alpha.toFunctionEmbedding
  let S := B.support af
  let maps : Partite.Embedding (B.restrict af) E →
      RelStructure.Embedding (B.toRelStructure.induce S)
        (E.relabel af).toRelStructure :=
    fun i => (Picture.attachingMap B af E i).toEmbedding
  have hSupport : IsUSubstructure rules B.toRelStructure S :=
    (alpha.range_isUSubstructure hA hD).preimage_homomorphism hBPart.1
  have hWhole : IsUClosed rules
      (RelStructure.Attachment.attach B.toRelStructure S
        (E.relabel af).toRelStructure maps) :=
    RelStructure.Attachment.attach_isUClosed
      B.toRelStructure S (E.relabel af).toRelStructure maps
      hB hE hSupport
  let pCore : W → P := fun x => alpha (E.part x)
  let pCopy : Partite.Embedding (B.restrict af) E → V → P :=
    fun _ x => B.part x
  have hCore : IsClosedUHomomorphismEmbedding rules
      (E.relabel af).toRelStructure D pCore :=
    (alpha.isClosedUHomomorphismEmbedding rules).comp hEPart
  have hCompat : ∀ i (x : S),
      pCore (maps i x) = pCopy i x.1 := by
    intro i x
    exact (Picture.attachingMap B af E i).map_part x
  have hFold := RelStructure.Attachment.fold_isClosedUHomomorphismEmbedding
    B.toRelStructure S (E.relabel af).toRelStructure maps
    hB hSupport hWhole D pCore pCopy hCore (fun _ => hBPart) hCompat
  exact hFold

/-- Protected tests in the real closed Picture are covered by the old B,
if all closed tests of the core embed in A and A embeds in B. The core
projection itself need only be protected; its target may be A. -/
theorem picture_build_closedTests_embed_old
    {rules : ClosureDescription L}
    (A : RelStructure L Q) (D : RelStructure L P)
    (B : System L P V) (alpha : RelStructure.Embedding A D)
    (E : System L Q W)
    (hA : IsUClosed rules A) (hD : IsUClosed rules D)
    (hB : IsUClosed rules B.toRelStructure)
    (hE : IsUClosed rules E.toRelStructure)
    (hBHom : B.toRelStructure.IsHomomorphism D B.part)
    (hEPart : IsClosedUHomomorphismEmbedding rules
      E.toRelStructure A E.part)
    (aB : RelStructure.Embedding A B.toRelStructure) :
    ∀ {Z : Type v} (Test : RelStructure L Z),
      IsUClosed rules Test → IsUIrreducible rules Test →
      RelStructure.Embedding Test
        (Picture.build B alpha.toFunctionEmbedding E).toRelStructure →
      Nonempty (RelStructure.Embedding Test B.toRelStructure) := by
  let af := alpha.toFunctionEmbedding
  let S := B.support af
  let maps : Partite.Embedding (B.restrict af) E →
      RelStructure.Embedding (B.toRelStructure.induce S)
        (E.relabel af).toRelStructure :=
    fun i => (Picture.attachingMap B af E i).toEmbedding
  have hSupport : IsUSubstructure rules B.toRelStructure S :=
    (alpha.range_isUSubstructure hA hD).preimage_homomorphism hBHom
  have hWhole : IsUClosed rules
      (RelStructure.Attachment.attach B.toRelStructure S
        (E.relabel af).toRelStructure maps) :=
    RelStructure.Attachment.attach_isUClosed
      B.toRelStructure S (E.relabel af).toRelStructure maps
      hB hE hSupport
  intro Z Test hClosed hIrred e
  rcases RelStructure.Attachment.closed_test_core_or_copy
      B.toRelStructure S (E.relabel af).toRelStructure maps
      hB hSupport hWhole Test hClosed hIrred e with
    ⟨g, _⟩ | ⟨i, g, _⟩
  · obtain ⟨d, _⟩ := hEPart.on_test Test hClosed hIrred g
    exact ⟨aB.comp d⟩
  · exact ⟨g⟩

/-- The positive Picture step preserves both the protected projection
and the coverage invariant, conditional only on protection of the core
part map. It uses the actual all-embeddings Picture.build. -/
theorem picture_build_protected_step
    {rules : ClosureDescription L}
    (A : RelStructure L Q) (D : RelStructure L P)
    (B : System L P V) (alpha : RelStructure.Embedding A D)
    (E : System L Q W)
    (hA : IsUClosed rules A) (hD : IsUClosed rules D)
    (hB : IsUClosed rules B.toRelStructure)
    (hE : IsUClosed rules E.toRelStructure)
    (hBPart : IsClosedUHomomorphismEmbedding rules
      B.toRelStructure D B.part)
    (hEPart : IsClosedUHomomorphismEmbedding rules
      E.toRelStructure A E.part)
    (aB : RelStructure.Embedding A B.toRelStructure) :
    IsUClosed rules (Picture.build B alpha.toFunctionEmbedding E).toRelStructure ∧
    IsClosedUHomomorphismEmbedding rules
      (Picture.build B alpha.toFunctionEmbedding E).toRelStructure
      D (Picture.build B alpha.toFunctionEmbedding E).part ∧
    (∀ {Z : Type v} (Test : RelStructure L Z),
      IsUClosed rules Test → IsUIrreducible rules Test →
      RelStructure.Embedding Test
        (Picture.build B alpha.toFunctionEmbedding E).toRelStructure →
      Nonempty (RelStructure.Embedding Test B.toRelStructure)) := by
  let af := alpha.toFunctionEmbedding
  have hSupport : IsUSubstructure rules B.toRelStructure (B.support af) :=
    (alpha.range_isUSubstructure hA hD).preimage_homomorphism hBPart.1
  have hPictureClosed :=
    RelStructure.Attachment.attach_isUClosed B.toRelStructure
      (B.support af) (E.relabel af).toRelStructure
      (fun i => (Picture.attachingMap B af E i).toEmbedding)
      hB hE hSupport
  exact ⟨hPictureClosed,
    picture_build_isClosedPartiteOver A D B alpha E hA hD hB hE
      hBPart hEPart,
    picture_build_closedTests_embed_old A D B alpha E hA hD hB hE
      hBPart.1 hEPart aB⟩

end StructuralRamsey.Partite.Induced
