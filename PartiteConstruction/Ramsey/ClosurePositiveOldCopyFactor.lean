import PartiteConstruction.Ramsey.ClosureIrreducibleHulls
import PartiteConstruction.Ramsey.ClosureMaximalWeakRankHereditary
import PartiteConstruction.Relational.Attachment

/-!
# Factor ordinary and protected maps through an ACTUAL attached copy

The repaired closed-test projection of a U-closed Ramsey witness to
its temporarily conflicting little Picture is positive and protects
closed irreducible tests. It need NOT be globally injective. Yet
since the SOURCE is U-closed, the projection is an ORDINARY
homomorphism-embedding on the whole source.

Whenever the image of an exact induced source piece lies inside
one of the *genuine attached old-picture copies*, the piece
has an ordinary homomorphism-embedding into Old, obtained by
factoring its projection through that full induced copy.

This does NOT require the original projection to be injective
or preserve absent relations globally. Nor does it imply that the
OTHER source side also has a compatible map to Old; that separate
map/root compatibility is the remaining multi-line geometry task.

The first lemma is a general factorization theorem for relational
homomorphism-embeddings and will be useful independently of the
partite construction.
-/

namespace StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V W : Type v}

/-- An ordinary homomorphism-embedding whose entire image lies in
a full induced embedded B-copy factors as another ordinary
homomorphism-embedding into B. The factor need not be injective
globally; source and target are not required to be U-closed. -/
theorem IsHomomorphismEmbedding.factorThroughEmbeddingRange
    {A : RelStructure L U} {B : RelStructure L V}
    {C : RelStructure L W} {f : U → W}
    (hf : A.IsHomomorphismEmbedding C f)
    (e : Embedding B C)
    (hRange : ∀ x : U, ∃ b : V, f x = e b) :
    ∃ g : U → V, A.IsHomomorphismEmbedding B g ∧
      ∀ x : U, f x = e (g x) := by
  classical
  let g : U → V := fun x => Classical.choose (hRange x)
  have hEq (x : U) : f x = e (g x) :=
    Classical.choose_spec (hRange x)
  have hMap : A.IsHomomorphism B g := by
    intro R z hz
    have hzC : C.rel R (e ∘ (g ∘ z)) := by
      convert hf.1 R z hz using 1
      funext i
      exact (hEq (z i)).symm
    exact (e.map_rel_iff R (g ∘ z)).mp hzC
  refine ⟨g, ⟨hMap, ?_⟩, hEq⟩
  intro S hIrred
  obtain ⟨d, hd⟩ := hf.embeddingOn S hIrred
  have hDS (x : S) : ∃ b : V, d x = e b := by
    obtain ⟨b, hb⟩ := hRange x.1
    exact ⟨b, (hd x).trans hb⟩
  let c : Embedding (A.induce S) B :=
    d.factorThroughRange e hDS
  refine ⟨c, ?_⟩
  intro x
  apply e.injective
  calc
    e (c x) = d x :=
      (Classical.choose_spec (hDS x)).symm
    _ = f x.1 := hd x
    _ = e (g x.1) := hEq x.1

end StructuralRamsey.RelStructure

namespace StructuralRamsey.RelStructure.Attachment

universe u v
variable {L : RelLanguage.{u}}
variable {U V W I : Type v}

/-- Any ordinary homomorphism-embedding of an arbitrary WEAK source
into the real attachment restricts to an ordinary map of a chosen
exact source piece into Old, whenever its image stays inside one
selected attached-copy range. No intrinsic source closedness
or global map injectivity is assumed. -/
theorem ordinary_source_piece_factors_old_copy
    (Source : RelStructure L U) (Old : RelStructure L V)
    (Support : Set V) (Core : RelStructure L W)
    (maps : I → Embedding (Old.induce Support) Core)
    (p : U → Vertex Support (W := W) (I := I))
    (hp : Source.IsHomomorphismEmbedding
      (attach Old Support Core maps) p)
    (S : Set U) (i : I)
    (hInCopy : ∀ x : S,
      ∃ y : V, p x.1 = copyEmbedding Old Support Core maps i y) :
    ∃ g : S → V,
      (Source.induce S).IsHomomorphismEmbedding Old g ∧
      ∀ x : S,
        p x.1 = copyEmbedding Old Support Core maps i (g x) := by
  let f : S → Vertex Support (W := W) (I := I) :=
    fun x => p x.1
  have hf : (Source.induce S).IsHomomorphismEmbedding
      (attach Old Support Core maps) f :=
    hp.comp (inclusion Source S).isHomomorphismEmbedding
  exact hf.factorThroughEmbeddingRange
    (copyEmbedding Old Support Core maps i) hInCopy

/-- In particular, for a MAXIMAL-RANK WEAK source the resulting
old-copy piece map protects all embedded CLOSED U-irreducible tests,
even though the source piece need not be intrinsically U-closed.
This is the exact type of small-side projection accepted by the
checked generated-A-boundary gluing criterion. -/
theorem maximal_weak_piece_protected_in_old_copy
    {rules : ClosureDescription L}
    (Source : RelStructure L U) (Old : RelStructure L V)
    [Fintype U]
    (hMax : USize rules Source = Fintype.card U)
    (Support : Set V) (Core : RelStructure L W)
    (maps : I → Embedding (Old.induce Support) Core)
    (p : U → Vertex Support (W := W) (I := I))
    (hp : Source.IsHomomorphismEmbedding
      (attach Old Support Core maps) p)
    (S : Set U) [Fintype S] (i : I)
    (hInCopy : ∀ x : S,
      ∃ y : V, p x.1 = copyEmbedding Old Support Core maps i y) :
    ∃ g : S → V,
      IsClosedUHomomorphismEmbedding rules (Source.induce S) Old g ∧
      ∀ x : S,
        p x.1 = copyEmbedding Old Support Core maps i (g x) := by
  obtain ⟨g, hg, hFact⟩ :=
    ordinary_source_piece_factors_old_copy
      Source Old Support Core maps p hp S i hInCopy
  have hMaxS : USize rules (Source.induce S) = Fintype.card S :=
    induced_USize_eq_card_of_max_USize rules Source hMax S
  exact ⟨g, hg.toClosedMap_of_max_USize hMaxS, hFact⟩

/-- Let T be U-closed with its actual protected POSITIVE map p into
a native Hales--Jewett little Picture (possibly non-semi-closed).
If one exact induced vertex set S of T projects into the range of
a chosen attached old-picture copy, S has an ordinary HE to Old,
even though p may collapse other vertices.

This constructs one of the genuinely required side maps for the
multiple-line rank argument; it does not invent the map of the
complementary rest piece or a generated K-boundary. -/
theorem closed_source_piece_factors_old_copy
    {rules : ClosureDescription L}
    (Test : RelStructure L U) (hClosed : IsUClosed rules Test)
    (Old : RelStructure L V) (Support : Set V)
    (Core : RelStructure L W)
    (maps : I → Embedding (Old.induce Support) Core)
    (p : U → Vertex Support (W := W) (I := I))
    (hp : IsClosedUHomomorphismEmbedding rules Test
      (attach Old Support Core maps) p)
    (S : Set U) (i : I)
    (hInCopy : ∀ x : S,
      ∃ y : V, p x.1 = copyEmbedding Old Support Core maps i y) :
    ∃ g : S → V,
      (Test.induce S).IsHomomorphismEmbedding Old g ∧
      ∀ x : S,
        p x.1 = copyEmbedding Old Support Core maps i (g x) := by
  let f : S → Vertex Support (W := W) (I := I) :=
    fun x => p x.1
  have hOrd : Test.IsHomomorphismEmbedding
      (attach Old Support Core maps) p :=
    hp.toHomomorphismEmbedding_of_closed hClosed
  have hPiece :
      (Test.induce S).IsHomomorphismEmbedding
        (attach Old Support Core maps) f :=
    hOrd.comp (inclusion Test S).isHomomorphismEmbedding
  exact hPiece.factorThroughEmbeddingRange
    (copyEmbedding Old Support Core maps i) hInCopy

end StructuralRamsey.RelStructure.Attachment
