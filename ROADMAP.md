# Roadmap

The target is all of Appendix A. Each step should export reusable statements
and update the survey's validation markers at an immutable proof commit.

1. **Complete:** relational structures and induced embeddings; structural
   arrows; partite systems and unary-predicate equivalence; fixed-length HJ;
   the finite non-induced Partite Lemma; projected copies and backward fusion.
2. **Complete:** reusable finite free attachment; the Picture Lemma; initial
   pictures; finite iteration; preservation of projected relation constraints;
   extraction from a Ramsey family of placements; order completion preserving
   induced embeddings and the arrow.
3. **Complete:** ordinary finite Ramsey for strictly increasing tuples;
   translation of a homogeneous subset to increasing placements and
   `ProjectionRamsey`; the unconditional unrestricted ordered
   Nešetřil–Rödl theorem.
4. **Complete for relational languages — induced construction:**
   homomorphism-embeddings, positive coordinatewise powers, the induced
   Partite and Picture Lemmas, disjoint-union initial pictures, formally based
   stages, the irreducible-image invariant, finite iteration, and the final
   Ramsey extraction with a trace certifying every stage.
5. **Checked under hereditary irreducibility — applications and iteration:**
   weak substructures for function languages, tree amalgams, weak local
   tree-likeness, the actual induced-construction trace, repeated sparsening
   iteration, projected irreducible coverage, the final finite attachment
   phase, and an end-to-end strengthened sparsening theorem are formalized.
   The checked theorem assumes hereditary irreducibility of both A and B.
   Remaining: resolve the gap from the survey's stated hypothesis that only A
   is irreducible (and the corresponding function-language/graph-encoding
   presentation issue).
6. **Recursive construction / functions — in progress:** set-valued functions,
   closed embeddings, U-transversality, the ordinary-indexed closed initial
   picture, and the half-closed induced partite construction are formalized.
   The non-closed free-attachment obstruction is isolated.  A post-processing
   repair is also checked: retain only tuples lying in closed copies of the
   previous stage; this preserves the closed Ramsey arrow and forces
   U-transversality. Remaining: carry the outer D-partition through the nested
   half-closed construction and assemble `thm:models2`.

Keep hypotheses visible. An abstract fusion lemma is not a proof of existence
of its input pictures. A library representation change is not a manuscript
error. Mathematical errors or missing arguments in the text should be marked
with `\todo[inline]{Řehořek: ...}`.
