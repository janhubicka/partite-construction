import PartiteConstruction.Structure.FreeAmalgam

/-! # Reassociation of full functional free amalgams

This is the elementary pushout calculation needed by strict functional tree
extensions.  If Mid is the free amalgam of M and T over Start, Ext is obtained
from T by one further free attachment, and Out is obtained by making the same
attachment to the T-copy inside Mid, then Out is again the free amalgam of M
and Ext over Start.

The statement is phrased for arbitrary free-amalgam diagrams.  In
`TreeExtension` the embedding of Ext into Out is supplied by the exact
functional lift.
-/

namespace StructuralRamsey.Structure.IsFreeAmalgam

universe u v

variable {L : Language.{u}}
variable {S M T C R P E X : Type v}
variable {Start : Structure L S}
variable {Mstr : Structure L M} {Tstr : Structure L T}
variable {Mid : Structure L C}
variable {Root : Structure L R} {Piece : Structure L P}
variable {Ext : Structure L E} {Out : Structure L X}

variable {sM : Embedding Start Mstr} {sT : Embedding Start Tstr}
variable {iM : Embedding Mstr Mid} {iT : Embedding Tstr Mid}
variable {rT : Embedding Root Tstr} {rP : Embedding Root Piece}
variable {jT : Embedding Tstr Ext} {jP : Embedding Piece Ext}
variable {kMid : Embedding Mid Out} {kP : Embedding Piece Out}

/-- Adjoining the common structure itself on the right is a degenerate free
amalgam.  This is the base case for replaying a tree extension over a new
ambient target. -/
theorem right_identity
    {S M : Type v}
    {Start : Structure L S} {Mstr : Structure L M}
    (e : Embedding Start Mstr) :
    IsFreeAmalgam
      e (Embedding.id Start)
      (Embedding.id Mstr) e := by
  classical
  constructor
  · intro z
    exact Or.inl ⟨z, rfl⟩
  · intro m s
    constructor
    · intro h
      exact ⟨s, h, rfl⟩
    · rintro ⟨d, hm, hs⟩
      subst s
      simpa using hm
  · intro Rel z
    constructor
    · intro hz
      exact Or.inl ⟨z, hz, by
        funext q
        rfl⟩
    · rintro (⟨x, hx, hzx⟩ | ⟨x, hx, hzx⟩)
      · simpa using Eq.mp
          (congrArg (fun t => Mstr.rel Rel t) hzx.symm) hx
      · have he : Mstr.rel Rel (e ∘ x) :=
          (e.map_rel_iff Rel x).2 hx
        exact Eq.mp
          (congrArg (fun t => Mstr.rel Rel t) hzx.symm) he
  · intro F args y
    constructor
    · intro hy
      exact Or.inl ⟨args, y, hy, by
        funext q
        rfl, rfl⟩
    · rintro (⟨a, b, hb, hargs, hout⟩ |
        ⟨a, b, hb, hargs, hout⟩)
      · have hargs' : args = a := by
          simpa using hargs
        have hout' : y = b := by
          simpa using hout
        simpa [hargs', hout'] using hb
      · have himg :
            e b ∈ imageSet e (Start.func F a) :=
          ⟨b, hb, rfl⟩
        rw [e.map_func F a] at himg
        have hargs' : args = e ∘ a := by
          simpa using hargs
        have hout' : y = e b := by
          simpa using hout
        simpa [hargs', hout'] using himg

/-- Push one free attachment through the right side of another free amalgam. -/
theorem reassociate_right
    (hOuter : IsFreeAmalgam sM sT iM iT)
    (hExt : IsFreeAmalgam rT rP jT jP)
    (hOut : IsFreeAmalgam (iT.comp rT) rP kMid kP)
    (eExt : Embedding Ext Out)
    (heT : ∀ t, eExt (jT t) = kMid (iT t))
    (heP : ∀ p, eExt (jP p) = kP p) :
    IsFreeAmalgam
      sM (jT.comp sT)
      (kMid.comp iM) eExt := by
  classical
  constructor
  · intro z
    rcases hOut.covers z with ⟨c, hc⟩ | ⟨p, hp⟩
    · rcases hOuter.covers c with ⟨m, hm⟩ | ⟨t, ht⟩
      · exact Or.inl ⟨m, by
          calc
            z = kMid c := hc
            _ = kMid (iM m) := congrArg kMid hm
            _ = (kMid.comp iM) m := rfl⟩
      · exact Or.inr ⟨jT t, by
          calc
            z = kMid c := hc
            _ = kMid (iT t) := congrArg kMid ht
            _ = eExt (jT t) := (heT t).symm⟩
    · exact Or.inr ⟨jP p, by
        calc
          z = kP p := hp
          _ = eExt (jP p) := (heP p).symm⟩
  · intro m e
    constructor
    · intro hme
      rcases hExt.covers e with ⟨t, ht⟩ | ⟨p, hp⟩
      · have hmid : iM m = iT t := by
          apply kMid.injective
          calc
            kMid (iM m) = (kMid.comp iM) m := rfl
            _ = eExt e := hme
            _ = eExt (jT t) := congrArg eExt ht
            _ = kMid (iT t) := heT t
        obtain ⟨s, hm, htS⟩ := (hOuter.overlap m t).mp hmid
        exact ⟨s, hm, by
          calc
            e = jT t := ht
            _ = jT (sT s) := congrArg jT htS
            _ = (jT.comp sT) s := rfl⟩
      · have hout : kMid (iM m) = kP p := by
          calc
            kMid (iM m) = (kMid.comp iM) m := rfl
            _ = eExt e := hme
            _ = eExt (jP p) := congrArg eExt hp
            _ = kP p := heP p
        obtain ⟨r, hmr, hpr⟩ :=
          (hOut.overlap (iM m) p).mp hout
        have hmid : iM m = iT (rT r) := by
          simpa using hmr
        obtain ⟨s, hm, hts⟩ := (hOuter.overlap m (rT r)).mp hmid
        exact ⟨s, hm, by
          calc
            e = jP p := hp
            _ = jP (rP r) := congrArg jP hpr
            _ = jT (rT r) :=
              ((hExt.overlap (rT r) (rP r)).mpr ⟨r, rfl, rfl⟩).symm
            _ = jT (sT s) := congrArg jT hts
            _ = (jT.comp sT) s := rfl⟩
    · rintro ⟨s, hm, he⟩
      calc
        (kMid.comp iM) m = kMid (iM m) := rfl
        _ = kMid (iM (sM s)) := congrArg (fun x => kMid (iM x)) hm
        _ = kMid (iT (sT s)) :=
          congrArg kMid
            ((hOuter.overlap (sM s) (sT s)).mpr ⟨s, rfl, rfl⟩)
        _ = eExt (jT (sT s)) := (heT (sT s)).symm
        _ = eExt ((jT.comp sT) s) := rfl
        _ = eExt e := congrArg eExt he.symm
  · intro Rel z
    constructor
    · intro hz
      rcases (hOut.rel_iff Rel z).mp hz with
        ⟨c, hc, hzc⟩ | ⟨p, hp, hzp⟩
      · rcases (hOuter.rel_iff Rel c).mp hc with
          ⟨m, hm, hcm⟩ | ⟨t, ht, hct⟩
        · refine Or.inl ⟨m, hm, ?_⟩
          funext q
          have hzq := congrFun hzc q
          have hcq := congrFun hcm q
          calc
            z q = kMid (c q) := hzq
            _ = kMid (iM (m q)) := congrArg kMid hcq
            _ = ((kMid.comp iM) ∘ m) q := rfl
        · let e : Fin (L.relArity Rel) → E := jT ∘ t
          have heRel : Ext.rel Rel e := by
            exact (jT.map_rel_iff Rel t).2 ht
          refine Or.inr ⟨e, heRel, ?_⟩
          funext q
          have hzq := congrFun hzc q
          have hcq := congrFun hct q
          calc
            z q = kMid (c q) := hzq
            _ = kMid (iT (t q)) := congrArg kMid hcq
            _ = eExt (jT (t q)) := (heT (t q)).symm
            _ = (eExt ∘ e) q := rfl
      · let e : Fin (L.relArity Rel) → E := jP ∘ p
        have heRel : Ext.rel Rel e := by
          exact (jP.map_rel_iff Rel p).2 hp
        refine Or.inr ⟨e, heRel, ?_⟩
        funext q
        have hzq := congrFun hzp q
        calc
          z q = kP (p q) := hzq
          _ = eExt (jP (p q)) := (heP (p q)).symm
          _ = (eExt ∘ e) q := rfl
    · rintro (⟨m, hm, rfl⟩ | ⟨e, he, rfl⟩)
      · exact ((kMid.comp iM).map_rel_iff Rel m).2 hm
      · exact (eExt.map_rel_iff Rel e).2 he
  · intro F args y
    constructor
    · intro hy
      rcases (hOut.func_iff F args y).mp hy with
        ⟨a, b, hb, hargs, hout⟩ |
        ⟨a, b, hb, hargs, hout⟩
      · rcases (hOuter.func_iff F a b).mp hb with
          ⟨margs, mb, hma, hmb⟩ |
          ⟨targs, tb, hta, htb⟩
        · refine Or.inl ⟨margs, mb, ?_, ?_⟩
          · funext q
            have haq := congrFun hargs q
            have hmaq := congrFun hma q
            calc
              args q = kMid (a q) := haq
              _ = kMid (iM (margs q)) := congrArg kMid hmaq
              _ = ((kMid.comp iM) ∘ margs) q := rfl
          · calc
              y = kMid b := hout
              _ = kMid (iM mb) := congrArg kMid hmb
              _ = (kMid.comp iM) mb := rfl
        · have tmem :
              jT tb ∈ Ext.func F (jT ∘ targs) := by
            have himg :
                jT tb ∈ imageSet jT (Tstr.func F targs) :=
              ⟨tb, tb, rfl⟩
            rw [jT.map_func F targs] at himg
            exact himg
          refine Or.inr ⟨jT ∘ targs, jT tb, tmem, ?_, ?_⟩
          · funext q
            have haq := congrFun hargs q
            have htaq := congrFun hta q
            calc
              args q = kMid (a q) := haq
              _ = kMid (iT (targs q)) := congrArg kMid htaq
              _ = eExt (jT (targs q)) := (heT (targs q)).symm
              _ = (eExt ∘ (jT ∘ targs)) q := rfl
          · calc
              y = kMid b := hout
              _ = kMid (iT tb) := congrArg kMid htb
              _ = eExt (jT tb) := (heT tb).symm
      · have pmem :
            jP b ∈ Ext.func F (jP ∘ a) := by
          have himg :
              jP b ∈ imageSet jP (Piece.func F a) :=
            ⟨b, hb, rfl⟩
          rw [jP.map_func F a] at himg
          exact himg
        refine Or.inr ⟨jP ∘ a, jP b, pmem, ?_, ?_⟩
        · funext q
          have haq := congrFun hargs q
          calc
            args q = kP (a q) := haq
            _ = eExt (jP (a q)) := (heP (a q)).symm
            _ = (eExt ∘ (jP ∘ a)) q := rfl
        · calc
            y = kP b := hout
            _ = eExt (jP b) := (heP b).symm
    · rintro (⟨a, b, hb, rfl, rfl⟩ | ⟨a, b, hb, rfl, rfl⟩)
      · have himg :
            (kMid.comp iM) b ∈
              imageSet (kMid.comp iM) (Mstr.func F a) :=
          ⟨b, hb, rfl⟩
        rw [(kMid.comp iM).map_func F a] at himg
        exact himg
      · have himg :
            eExt b ∈ imageSet eExt (Ext.func F a) :=
          ⟨b, hb, rfl⟩
        rw [eExt.map_func F a] at himg
        exact himg

end StructuralRamsey.Structure.IsFreeAmalgam
