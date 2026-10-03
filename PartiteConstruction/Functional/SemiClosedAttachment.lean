import PartiteConstruction.Functional.SemiClosedPartite
import PartiteConstruction.Functional.ClosedAttachment

/-! # Local closure through a non-closed free attachment

A free attachment over a non-closed overlap need not preserve the whole
attached copy as a closed copy.  The recursive closure construction needs
less: selected closed A-subcopies whose vertices lie in the overlap must stay
closed.

In the domain-expanded partial-function language this follows from:
* A has an output on every declared function domain;
* the old picture B is output-to-domain compatible and singleton-valued;
* every attaching map from the overlap into the core is closed.

A competing output contributed by another attached copy first forces the same
root tuple in the core.  The selected A-copy supplies a core output; closedness
of the competing overlap map pulls that output back into the overlap, and
singleton-valuedness of B identifies it with the allegedly outside output.
-/
namespace StructuralRamsey.Partite.Attachment

open RelStructure Structure

universe u v
variable {L : Language.{u}}
variable {P U V W I : Type v}

/-- Restrict a closed relational embedding to an induced target containing
its image. -/
def restrictClosedToInduce
    {A : RelStructure L.withFunctionDomains.graph U}
    {B : Partite.System L.withFunctionDomains.graph P V}
    {S : Set V}
    (e : RelStructure.ClosedEmbedding A B.toRelStructure)
    (heS : ∀ a, e a ∈ S) :
    RelStructure.ClosedEmbedding
      A (B.induce S).toRelStructure where
  toEmbedding := {
    toFun := fun a => ⟨e a, heS a⟩
    injective := by
      intro a b hab
      apply e.toEmbedding.injective
      exact congrArg Subtype.val hab
    map_rel_iff := by
      intro R x
      change B.rel R (e ∘ x) ↔ A.rel R x
      exact e.toEmbedding.map_rel_iff R x
  }
  closed := by
    intro F x y hy
    have hyB :
        B.rel (.inr F)
          (Structure.funcTuple (e ∘ x) y.1) := by
      change
        B.rel (.inr F)
          (Subtype.val ∘
            Structure.funcTuple
              ((fun a => (⟨e a, heS a⟩ : S)) ∘ x) y) at hy
      have ht :
          Subtype.val ∘
              Structure.funcTuple
                ((fun a => (⟨e a, heS a⟩ : S)) ∘ x) y =
            Structure.funcTuple (e ∘ x) y.1 := by
        funext j
        refine Fin.lastCases ?_ (fun k => ?_) j
        · simp [Structure.funcTuple, Function.comp_apply]
        · simp [Structure.funcTuple, Function.comp_apply]
      exact Eq.mp
        (congrArg (fun t => B.rel (.inr F) t) ht)
        hy
    obtain ⟨z, hz, hzy⟩ :=
      e.closed F x y.1 hyB
    refine ⟨z, hz, ?_⟩
    apply Subtype.ext
    exact hzy

/-- A selected closed A-copy stays closed through an ordinary free attachment
as soon as it is fully contained in the overlap and every overlap embedding
used by the attachment is closed.  The overlap itself need not be closed. -/
theorem selectedCopy_closed
    {A : RelStructure L.withFunctionDomains.graph U}
    {B : Partite.System L.withFunctionDomains.graph P V}
    {S : Set V}
    {D : Partite.System L.withFunctionDomains.graph P W}
    {f : I → Partite.Closed.Embedding (B.induce S) D}
    (hAtotal : A.FunctionDomainTotal)
    (hBroot : B.OutputImpliesDomain)
    (hBsingle : B.FunctionOutputSingleValued)
    (i : I)
    (e : RelStructure.ClosedEmbedding A B.toRelStructure)
    (heS : ∀ a, e a ∈ S) :
    RelStructure.FunctionClosedMap
      A
      (Partite.Attachment.attach
        B S D (fun j => (f j).1)).toRelStructure
      ((Partite.Attachment.copyEmbedding
        B S D (fun j => (f j).1) i).toEmbedding ∘ e) := by
  classical
  let g :
      I → RelStructure.Embedding
        (B.toRelStructure.induce S) D.toRelStructure :=
    fun j => {
      toFun := (f j).1
      injective := (f j).1.toEmbedding.injective
      map_rel_iff := (f j).1.toEmbedding.map_rel_iff
    }
  let ei := restrictClosedToInduce e heS
  let d : RelStructure.ClosedEmbedding A D.toRelStructure :=
    RelStructure.ClosedEmbedding.comp (f i).toRelClosed ei
  let core : W →
      RelStructure.Attachment.Vertex S (W := W) (I := I) :=
    Sum.inl
  let cm (j : I) : V →
      RelStructure.Attachment.Vertex S (W := W) (I := I) :=
    RelStructure.Attachment.copyMap
      B.toRelStructure S D.toRelStructure g j
  have hselected (a : U) :
      (Partite.Attachment.copyEmbedding
          B S D (fun j => (f j).1) i).toEmbedding (e a) =
        core (d a) := by
    change
      RelStructure.Attachment.copyMap
        B.toRelStructure S D.toRelStructure g i (e a) =
        Sum.inl (d a)
    rw [RelStructure.Attachment.copyMap_mem
      (B := B.toRelStructure) (S := S)
      (D := D.toRelStructure) (f := g)
      i (e a) (heS a)]
    rfl
  intro F x y hy
  have hy0 :
      (RelStructure.Attachment.attach
        B.toRelStructure S D.toRelStructure g).rel
        (.inr F)
        (Structure.funcTuple
          ((core ∘ d) ∘ x) y) := by
    change
      (Partite.Attachment.attach
        B S D (fun j => (f j).1)).rel
        (.inr F)
        (Structure.funcTuple
          (((Partite.Attachment.copyEmbedding
              B S D (fun j => (f j).1) i).toEmbedding ∘ e) ∘ x) y) at hy
    have hargs :
        (((Partite.Attachment.copyEmbedding
            B S D (fun j => (f j).1) i).toEmbedding ∘ e) ∘ x) =
          (core ∘ d) ∘ x := by
      funext k
      exact hselected (x k)
    rw [hargs] at hy
    exact hy
  rcases hy0 with ⟨q, hq, hcore⟩ | ⟨j, q, hq, hcopy⟩
  · let args : Fin (L.withFunctionDomains.funcArity F) → W :=
      fun k => q (Fin.castSucc k)
    let out : W := q (Fin.last (L.withFunctionDomains.funcArity F))
    have hargsEq : d ∘ x = args := by
      funext k
      have hk := congrFun hcore (Fin.castSucc k)
      rw [Structure.funcTuple_castSucc] at hk
      exact Sum.inl.inj hk
    have houtEq : y = core out := by
      have hk := congrFun hcore (Fin.last (L.withFunctionDomains.funcArity F))
      rw [Structure.funcTuple_last] at hk
      exact hk
    have hrelD :
        D.rel (.inr F) (Structure.funcTuple (d ∘ x) out) := by
      have heta : Structure.funcTuple args out = q := by
        simpa [args, out,
          Language.graph] using
          (Structure.funcTuple_eta (t := q))
      rw [hargsEq, heta]
      exact hq
    obtain ⟨z, hz, hzd⟩ :=
      d.closed F x out hrelD
    refine ⟨z, hz, ?_⟩
    change
      (Partite.Attachment.copyEmbedding
        B S D (fun j => (f j).1) i).toEmbedding (e z) = y
    rw [hselected z, houtEq]
    exact congrArg core hzd
  · let args : Fin (L.withFunctionDomains.funcArity F) → V :=
      fun k => q (Fin.castSucc k)
    let out : V := q (Fin.last (L.withFunctionDomains.funcArity F))
    have hrelB :
        B.rel (.inr F)
          (Structure.funcTuple args out) := by
      have heta : Structure.funcTuple args out = q := by
        simpa [args, out, Language.graph] using
          (Structure.funcTuple_eta (t := q))
      rw [heta]
      exact hq
    have hargsS : ∀ k, args k ∈ S := by
      intro k
      apply RelStructure.Attachment.mem_of_copyMap_eq_inl
        (B := B.toRelStructure) (S := S)
        (D := D.toRelStructure) (f := g)
      have hk := congrFun hcopy (Fin.castSucc k)
      rw [Structure.funcTuple_castSucc] at hk
      change
        core (d (x k)) = cm j (args k) at hk
      exact hk.symm
    let argsS : Fin (L.withFunctionDomains.funcArity F) → S :=
      fun k => ⟨args k, hargsS k⟩
    have hrootB :
        B.rel (.inl (.inr F)) args :=
      hBroot F args out hrelB
    have hrootS :
        (B.induce S).rel (.inl (.inr F)) argsS := by
      change
        B.rel (.inl (.inr F))
          (Subtype.val ∘ argsS)
      simpa [argsS] using hrootB
    have hfjargs :
        (f j).toRelClosed ∘ argsS = d ∘ x := by
      funext k
      have hk := congrFun hcopy (Fin.castSucc k)
      rw [Structure.funcTuple_castSucc] at hk
      change
        core (d (x k)) =
          RelStructure.Attachment.copyMap
            B.toRelStructure S D.toRelStructure g j (args k) at hk
      rw [RelStructure.Attachment.copyMap_mem
        (B := B.toRelStructure) (S := S)
        (D := D.toRelStructure) (f := g)
        j (args k) (hargsS k)] at hk
      exact Sum.inl.inj hk.symm
    have hrootD0 :
        D.rel (.inl (.inr F))
          ((f j).toRelClosed ∘ argsS) :=
      ((f j).1.toEmbedding.map_rel_iff
        (.inl (.inr F)) argsS).mpr hrootS
    have hrootD :
        D.rel (.inl (.inr F)) (d ∘ x) := by
      exact Eq.mp
        (congrArg
          (fun t => D.rel (.inl (.inr F)) t)
          hfjargs)
        hrootD0
    have hrootA :
        A.rel (.inl (.inr F)) x :=
      (d.toEmbedding.map_rel_iff
        (.inl (.inr F)) x).mp hrootD
    obtain ⟨z, hz⟩ := hAtotal F x hrootA
    have hdzD0 :
        D.rel (.inr F)
          (d.toEmbedding ∘
            Structure.funcTuple x z) :=
      (d.toEmbedding.map_rel_iff
        (.inr F) (Structure.funcTuple x z)).mpr hz
    have hdzD :
        D.rel (.inr F)
          (Structure.funcTuple (d ∘ x) (d z)) := by
      have ht :
          d.toEmbedding ∘
              Structure.funcTuple x z =
            Structure.funcTuple
              (d ∘ x) (d z) :=
        Structure.comp_funcTuple d.toEmbedding x z
      exact Eq.mp
        (congrArg (fun t => D.rel (.inr F) t) ht)
        hdzD0
    have hdzDj :
        D.rel (.inr F)
          (Structure.funcTuple
            ((f j).toRelClosed ∘ argsS) (d z)) := by
      have ht :
          Structure.funcTuple
              ((f j).toRelClosed ∘ argsS) (d z) =
            Structure.funcTuple (d ∘ x) (d z) := by
        congr 1
        exact hfjargs
      exact Eq.mpr
        (congrArg (fun t => D.rel (.inr F) t) ht)
        hdzD
    obtain ⟨r, hr, hrd⟩ :=
      (f j).toRelClosed.closed F argsS (d z) hdzDj
    have hrB0 :
        B.rel (.inr F)
          (Subtype.val ∘
            Structure.funcTuple argsS r) := hr
    have hrB :
        B.rel (.inr F)
          (Structure.funcTuple args r.1) := by
      have ht :
          Subtype.val ∘
              Structure.funcTuple argsS r =
            Structure.funcTuple args r.1 :=
        Structure.comp_funcTuple Subtype.val argsS r
      exact Eq.mp
        (congrArg (fun t => B.rel (.inr F) t) ht)
        hrB0
    have hout : out = r.1 :=
      hBsingle F args out r.1 hrelB hrB
    have hyEq : y = cm j out := by
      have hk := congrFun hcopy
        (Fin.last (L.withFunctionDomains.funcArity F))
      rw [Structure.funcTuple_last] at hk
      exact hk
    refine ⟨z, hz, ?_⟩
    change
      (Partite.Attachment.copyEmbedding
        B S D (fun j => (f j).1) i).toEmbedding (e z) = y
    calc
      (Partite.Attachment.copyEmbedding
          B S D (fun j => (f j).1) i).toEmbedding (e z) =
          core (d z) := hselected z
      _ = core ((f j).toRelClosed r) :=
          congrArg core hrd.symm
      _ = RelStructure.Attachment.copyMap
          B.toRelStructure S D.toRelStructure g j r.1 := by
          symm
          exact RelStructure.Attachment.copyMap_mem
            (B := B.toRelStructure) (S := S)
            (D := D.toRelStructure) (f := g)
            j r.1 r.2
      _ = RelStructure.Attachment.copyMap
          B.toRelStructure S D.toRelStructure g j out :=
          congrArg
            (RelStructure.Attachment.copyMap
              B.toRelStructure S D.toRelStructure g j)
            hout.symm
      _ = y := hyEq.symm

end StructuralRamsey.Partite.Attachment
