import PartiteConstruction.Iterated.OddCycleEdgeTreeObstruction

/-!
# An exact fixed full A-collar is NOT available for every weak test

Adversarial audit of the proposed protected A-mark induction:

Take A=Base=K2, a strictly two-edge source path x0--x1--x2,
and let its projection into control D=K3 give labels (0,2,1).
Mark alpha:A↪D with labels (0,1). The desired protected trace
  f(s)=mark(a) IFF part(s)=alpha(a)
forces f(x0)=mark(0), f(x2)=mark(1).

In ANY strict Base=K2 tree the edge mark endpoints have different
bipartite colours, whereas images of endpoints of an even source
path must have the SAME colour. Hence NO such witness exists.

This does NOT refute the corrected unrestricted sparsening theorem
or the conditional protected-mark gluing theorem. It proves that
the protected mark cannot be assumed unconditionally for an arbitrary
strict B-tree or added to the published induction by fiat. Relative
root images must be chosen according to the actual weak-test geometry.

The proof below is in the function-free relational reduct: it is
therefore already an obstruction to a general theorem with arbitrary
set-valued functions and transversal outputs (vacuously).
-/

namespace StructuralRamsey.RelStructure.LooseNotStrictifiable

/-- An even two-edge source path cannot have endpoints mapped to
the endpoints of a FULL marked K2 edge in any strict K2-tree. -/
theorem two_step_path_no_fixed_edge_mark
    {W : Type} {T : RelStructure L W}
    (hT : TreeAmalgam Edge W T)
    (f : Fin 3 → W)
    (h01 : T.rel () (fun i => if i = i0 then f 0 else f 1))
    (h12 : T.rel () (fun i => if i = i0 then f 1 else f 2))
    (mark : Embedding Edge T)
    (hMark0 : f 0 = mark 0)
    (hMark2 : f 2 = mark 1) : False := by
  obtain ⟨c, hc⟩ :=
    TreeAmalgam.twoColorable Edge_twoColorable hT
  have hi10 : i1 ≠ i0 := Ne.symm i0_ne_i1
  have h01ne : c (f 0) ≠ c (f 1) := by
    simpa [hi10] using
      (hc (fun i => if i = i0 then f 0 else f 1) h01)
  have h12ne : c (f 1) ≠ c (f 2) := by
    simpa [hi10] using
      (hc (fun i => if i = i0 then f 1 else f 2) h12)
  have h02 : c (f 0) = c (f 2) :=
    bool_eq_of_ne_ne h01ne h12ne
  have hEdge : Edge.rel ()
      (fun i => if i = i0 then (0 : Fin 2) else 1) := by
    simp [Edge, hi10, i0_ne_i1]
  have hm : T.rel ()
      (fun i => if i = i0 then mark (0 : Fin 2) else mark 1) := by
    have he := (mark.map_rel_iff ()
      (fun i => if i = i0 then (0 : Fin 2) else 1)).mpr hEdge
    convert he using 1
  have hMarkNe : c (mark 0) ≠ c (mark 1) := by
    simpa [hi10] using
      (hc (fun i => if i = i0 then mark (0 : Fin 2) else mark 1) hm)
  apply hMarkNe
  calc
    c (mark 0) = c (f 0) := congrArg c hMark0.symm
    _ = c (f 2) := h02
    _ = c (mark 1) := congrArg c hMark2

end StructuralRamsey.RelStructure.LooseNotStrictifiable
