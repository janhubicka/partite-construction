import PartiteConstruction.Functional.EHNLineAttachmentRetraction

/-!
# Track D: actual Hales–Jewett line irreducible source trace lifting

English proof FIRST:
docs/track-d-english-hj-irreducible-line-trace-lift-20261113.md

A genuine HJ line W has a parameter coordinate i. Evaluation of the
full coordinate power at i is a verified EHN map and splits the
FULL selected-support HJ line embedding.

Therefore every actual FULL irreducible A-copy in the power
evaluates to an actual FULL irreducible A-copy in the original
selected support, with equality on EVERY original vertex
of its intersection with the particular line.

The old-picture corollary composes with the FULL selected-support
inclusion. This repairs the *power-core-to-new-old-copy* pure-trace
case in ONE real HJ line attachment. It does NOT automatically
synchronize an A-copy situated in an earlier DIFFERENT attached line
copy, nor preserve the full union of multiple line histories.
-/

namespace StructuralRamsey.FunctionalPartite.Induced

open StructuralRamsey.Structure
open StructuralRamsey.HalesJewett

universe u v
variable {L : Language.{u}} {P V X : Type v}
variable {A : Structure L P} {B : System L P V}
variable {N : ℕ}

/-- Every FULL irreducible source copy inside the ACTUAL functional
Hales–Jewett power evaluates to a FULL source copy in the original
selected partite structure at ANY parameter coordinate of W.

The second conclusion is the crucial ACTUAL TRACE equality: at
every meeting with the FULL line range, the lifted copy has
exactly the original source vertex, not merely its part label.

No closure of a weak tested set or global fibre-domain reflection. -/
theorem line_irreducible_trace_lifts_full_to_source
    (hB : B.WeaklyPartiteOver A)
    (W : Line (Letter A B) N)
    (i : Fin N) (hi : W.symbol i = .parameter)
    (Source : Structure L X) (hSource : Source.Irreducible)
    (e : Structure.Embedding Source (power B N).toStructure) :
    ∃ eOld : Structure.Embedding Source B.toStructure,
      (∀ x : X, eOld x = (e x).coord i) ∧
      (∀ (x : X) (b : V),
        e x = lineMap W b → eOld x = b) := by
  have hCoord :
      (power B N).toStructure.IsEHNHomomorphismEmbedding
        B.toStructure (fun z => z.coord i) :=
    (line_parameter_coordinate_EHN_retraction hB W i hi).1
  obtain ⟨eOld, hEval⟩ := hCoord.2 Source hSource e
  refine ⟨eOld, hEval, ?_⟩
  intro x b hx
  calc
    eOld x = (e x).coord i := hEval x
    _ = (lineMap W b).coord i :=
      congrArg (fun z : Vertex B N => z.coord i) hx
    _ = b := (line_parameter_coordinate_EHN_retraction hB W i hi).2 b

end StructuralRamsey.FunctionalPartite.Induced

namespace StructuralRamsey.FunctionalPartite.EHN

open StructuralRamsey.Structure
open StructuralRamsey.HalesJewett

universe u v
variable {L : Language.{u}} {P U V X : Type v}

/-- Specialize to the ACTUAL selected CLOSED old-picture support
R=Old.weakRestrict(D,alpha), with an honest FULL embedding R→Old.

Any genuine FULL irreducible power A-copy which meets the
particular HJ line on an original support vertex has a FULL
old-picture A-copy extending that exact traced vertex.
The map on the original source support is literally inclusion,
not a new part-label map.

One pair of lines need not carry a common parameter, so no
multi-line strict B-tree or global EHN retraction is claimed. -/
theorem selected_hj_line_irreducible_trace_lifts_to_old
    (Old : System L P V) (D : Structure L P)
    (hOld : Old.WeaklyPartiteOver D)
    (A : Structure L U) (alpha : Structure.Embedding A D)
    (N : ℕ)
    (W : Line (Induced.Letter A
      (Old.weakRestrict D hOld.1 A alpha)) N)
    (i : Fin N) (hi : W.symbol i = .parameter)
    (Source : Structure L X) (hSource : Source.Irreducible)
    (e : Embedding Source
      (Induced.power (Old.weakRestrict D hOld.1 A alpha) N).toStructure) :
    ∃ eOld : Structure.Embedding Source Old.toStructure,
      ∀ (x : X)
        (r : Old.support alpha.toFunctionEmbedding),
        e x = Induced.lineMap W r → eOld x = r.1 := by
  let R := Old.weakRestrict D hOld.1 A alpha
  have hR : R.WeaklyPartiteOver A :=
    Old.weakRestrict_invariant D hOld.1 A alpha hOld
  obtain ⟨g, _hEval, hOnLine⟩ :=
    Induced.line_irreducible_trace_lifts_full_to_source
      hR W i hi Source hSource e
  let inc : Structure.Embedding R.toStructure Old.toStructure :=
    Old.weakRestrictInclusion D hOld.1 A alpha
  refine ⟨inc.comp g, ?_⟩
  intro x r hx
  have hgr : g x = r := hOnLine x r hx
  change inc (g x) = r.1
  rw [hgr]
  rfl

end StructuralRamsey.FunctionalPartite.EHN
