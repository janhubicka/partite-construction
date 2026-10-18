# Exact mixed functional gluing from TWO protected projected-side witnesses

**18 October 2026. English proof and adversarial audit before Lean.**

The native functional Appendix A iteration now has two ways to construct
protected target A-marks from a predecessor witness:

* the verified ordinary exact WEAK rank-m predecessor;
* the verified weaker CLOSED-control-only rank-m predecessor, when
  the exact projected side image is closed.

The final operation combining those marks is the SAME in both cases.
Previously it was embedded inside
\`IsFreeAmalgam.weakTree_of_closedOccupied_alpha_sides\`.
We extract that final step as a reusable theorem, without modifying
the printed survey proof or inventing an intermediate U-closed
relational Picture.

## Theorem

Let Whole = Left *_{Root} Right be a genuine FULL functional free
amalgam with FULL side maps iL,iR. Let p:Whole→D be a genuine EHN
(original-2019 partial-function) projection to the fixed full
functional control D. Let alpha:A↪D be a selected FULL A-copy,
and suppose the projection of the genuine common attaching root
lies in alpha(A). The A-copy A is irreducible, and the Base B is
a full genuine finite function structure.

For an ARBITRARY exact weak vertex set S⊆Whole, define its
two exact projected source-side image sets

  I_L = (p∘iL)[iL^{-1} S],   I_R = (p∘iR)[iR^{-1} S].

Assume only that we already have two genuine
\`SetAmbientProtectedWeakTreeWitness\` witnesses on EXACT I_L,I_R
relative to that same alpha and the same requested projected
history list. Each consists of a STRICT B-tree, an ambient-relative
weak HE of the exact projected test, ambient actual full A-copy
intersections, the projected history tests, and a protected FULL
target alpha-mark.

**Conclusion:** the original exact weak source S has a genuine
\`SetAmbientRelativeWeakTreeWitness\` into a STRICT full-functional
B-tree, with all surviving set-valued function fibres, actual
ambient full A-copy intersections, and every projected history.

## Proof

Restrict the EHN projection to each FULL embedded source side.
The maps p_L:Left→D and p_R:Right→D are still EHN. Pull the given
two protected control witnesses on I_L,I_R back to their EXACT
source weak preimages using the already checked
\`SetAmbientProtectedWeakTreeWitness.pullback_ehn_commutingParts\`.
This carries the SAME full marked A-copy, protected iff trace,
ambient A-intersection certificates, and projected histories,
without enlarging any weak test or reflecting undefined domains.

The two source-root maps agree in Whole because the attachment is
an actual FULL functional free amalgam. Every root vertex projects
inside alpha(A); the protected traces therefore make the two pulled
target maps agree on every actual tested common-root vertex.

Finally invoke the verified
\`IsFreeAmalgam.protectedAMarkWeakTree_glue\`. It freely glues
the STRICT target functional B-trees over the two FULL protected
A-marks, not over the possibly NONCLOSED source weak root.
The target function operations remain genuine and all output
part transversality holds in the actual source Picture; no
weak-root functional amalgam is used.

## Independent adversarial audit

* This is a **conditional sufficient theorem**: it consumes two
  protected target witnesses, and does NOT construct them.
  The known K2 parity obstruction refutes demanding such marks for
  arbitrary predecessor weak sets.
* It is valid even for source S nonclosed and for multi-valued
  function fibres; full function-closedness is required only for the
  FULL attaching maps and protected TARGET marks.
* It does not claim that a globally full total-fibre projection
  p exists. The actual EHN map need only be source-defined,
  and the verified pullback interface handles undefined inputs.
* An arbitrary nonclosed partial A-boundary may not support the
  fresh-target mark construction; that is handled separately by
  the closed-occupied-boundary criterion. Extracting this theorem
  must not conceal that premise.
* The requested histories must be the same finite list in the two
  control witnesses. Independent witnesses with incompatible
  projected history certificates are not silently synchronized.
* The arbitrary-stage C5 counterexample is not contradicted:
  it has no compatible strict projected-side protected witnesses.
* Exact weak S, I_L, I_R are all literal vertex sets; no function
  closures are counted as extra test vertices.

## Lean acceptance

Import the existing verified protected weak-tree pullback and
protected mark gluing modules. State the result using the exact
Set-image forms, no finite cardinal assumptions. The proof
should be a direct reuse of existing kernel-certified declarations,
rather than duplicating the free-amalgam construction.

The next PR can apply this abstraction to a unary function language:
for a closed finite mixed test, unary EHN projections are FULL and
the projected side tests are closed, so \`AtMostClosed\` supplies the
required marks from the weaker predecessor property.
