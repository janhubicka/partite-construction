import PartiteConstruction.Ramsey.ClosureSemiClosedLines

/-!
# The intersection of two transverse Hales--Jewett lines

The unresolved higher-rank proof needs to understand the ACTUAL
multi-line attachment, rather than an arbitrary free amalgam. Two
canonical lines whose variable-coordinate sets are disjoint meet only
inside ONE canonical transversal word copy of A in the coordinate
power.

Indeed, at a variable coordinate k of W, the other line W' must be
constant with some letter e:A→B. Equality of the coordinatewise
images forces the original B vertex of W to equal e of its part.
This identifies every common vertex as the image of one of the
vertices of A under the single word W.eval e.

When the core is semi-closed and A is closed, that whole word copy of
A is a relative U-substructure of the coordinate power. Thus the
actual overlap of two lines is contained in a CLOSED irreducible
K-boundary candidate. Nothing here says that the U-size of the
separator hull has dropped: that remaining projected-generator
budget is the precise independent obstruction in Lemma 2.30.
-/

namespace StructuralRamsey.Partite.Induced

open RelStructure HalesJewett SuccessorTree

universe u v
variable {L : RelLanguage.{u}} {P V : Type v} {N : ℕ}

/-- If two native parameter lines have no common variable coordinate,
their intersection is contained in a SINGLE canonical word image of A.
The result uses the REAL coordinate maps of the induced power and
does not assume any closure description or partite projection theorem. -/
theorem disjoint_parameter_lines_overlap_in_word
    (A : RelStructure L P) (B : System L P V)
    (W W' : Line (Letter A B) N)
    (hDisjoint : ∀ k : Fin N,
      W.symbol k = .parameter → W'.symbol k ≠ .parameter) :
    ∃ e : Letter A B,
      ∀ z : Vertex B N,
        z ∈ Set.range (NonInduced.lineMap W) →
        z ∈ Set.range (NonInduced.lineMap W') →
        ∃ p : P, z = NonInduced.wordMap (W.eval e) p := by
  obtain ⟨k, hk⟩ := W.hasParameter
  cases hs : W'.symbol k with
  | parameter =>
      exact False.elim (hDisjoint k hk hs)
  | const e =>
      refine ⟨e, ?_⟩
      intro z hz hz'
      obtain ⟨x, hx⟩ := hz
      obtain ⟨y, hy⟩ := hz'
      have hxy : NonInduced.lineMap W x =
          NonInduced.lineMap W' y := hx.trans hy.symm
      have hCoordinate := congrArg
        (fun v : Vertex B N => v.coord k) hxy
      have he : x = e (B.part y) := by
        simpa only [NonInduced.lineMap, hk, hs] using hCoordinate
      refine ⟨B.part y, ?_⟩
      calc
        z = NonInduced.lineMap W x := hx.symm
        _ = NonInduced.lineMap W (e (B.part y)) :=
          congrArg (NonInduced.lineMap W) he
        _ = NonInduced.wordMap (W.eval e) (B.part y) :=
          NonInduced.lineMap_comp_letter W e (B.part y)

/-- In a SEMI-CLOSED native core, the word copy that contains the
two disjoint-parameter line images' overlap is itself a relatively
U-closed copy of the original U-closed A. In particular it is an
explicit closed target-boundary *candidate*, not a fictitious
generator-free separator. The two line ranges are the actual
induced line embeddings of the power. -/
theorem disjoint_lines_overlap_in_closed_word
    {rules : ClosureDescription L}
    (A : RelStructure L P) (B : System L P V)
    (hA : IsUClosed rules A)
    (hB : IsUSemiClosed rules B.toRelStructure)
    (hPart : B.IsPartiteOver A)
    (W W' : Line (Letter A B) N)
    (hDisjoint : ∀ k : Fin N,
      W.symbol k = .parameter → W'.symbol k ≠ .parameter) :
    ∃ e : Letter A B,
      (Set.range (lineEmbedding hPart W).toEmbedding ∩
        Set.range (lineEmbedding hPart W').toEmbedding) ⊆
          Set.range
            (wordEmbedding hPart W.length_pos (W.eval e)).toEmbedding ∧
      IsUSubstructure rules (power B N).toRelStructure
        (Set.range
          (wordEmbedding hPart W.length_pos (W.eval e)).toEmbedding) := by
  obtain ⟨e, he⟩ :=
    disjoint_parameter_lines_overlap_in_word A B W W' hDisjoint
  refine ⟨e, ?_, ?_⟩
  · intro z hz
    rcases hz with ⟨hzW, hzW'⟩
    obtain ⟨x, hx⟩ := hzW
    obtain ⟨y, hy⟩ := hzW'
    obtain ⟨p, hp⟩ := he z ⟨x, hx⟩ ⟨y, hy⟩
    refine ⟨p, ?_⟩
    calc
      (wordEmbedding hPart W.length_pos (W.eval e)).toEmbedding p =
          NonInduced.wordMap (W.eval e) p :=
        wordEmbedding_apply hPart W.length_pos (W.eval e) p
      _ = z := hp.symm
  · have hCore : IsUSemiClosed rules (power B N).toRelStructure :=
      power_isUSemiClosed B hB W.length_pos
    exact Embedding.range_isUSubstructure_of_semiClosed
      hA hCore ((wordEmbedding hPart W.length_pos (W.eval e)).toEmbedding)

end StructuralRamsey.Partite.Induced
