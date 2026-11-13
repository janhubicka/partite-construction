# Track D — English proof FIRST: irreducible power-copy traces lift along a genuine Hales–Jewett line

**13 November 2026.** This is an additive mathematical lemma for the
real native functional Hales–Jewett line geometry, not for arbitrary
support embeddings. The numbered survey and previously removed TODOs
remain frozen. Source functions are genuinely set-valued and EHN maps
use the original 2019 source-defined partial-function law.

## Statement 1 — exact parameter-coordinate trace lifting

Let R be a genuine full-functional partite system with an EHN
part map R→A. Let N>0 and W be a genuine Hales–Jewett line
over the selected letter alphabet of R, with parameter coordinate
i∈Fin(N). Write

    ell_W : R ↪ R^N

for its FULL partite line embedding and

    ev_i : R^N → R,   ev_i(z)=z.coord(i)

for coordinate evaluation.

Take ANY irreducible full native L-structure E and ANY FULL
embedding gamma:E↪R^N. Then there is a FULL embedding

    gamma_i:E↪R

satisfying, for every vertex x of E,

    gamma_i(x)=ev_i(gamma(x)).

Moreover, for every source vertex r of R and x of E,

    gamma(x)=ell_W(r)  =>  gamma_i(x)=r.

The implication is pointwise on the ACTUAL source vertices;
it introduces no weak closure, no generator-rank inflation, and
no false target-domain reflection.

**Proof.** The already checked theorem
`Induced.coordinateEHN` says ev_i is a genuine EHN
homomorphism-embedding from the full functional power to R.
Apply its irreducible-test clause to the FULL embedding gamma
of the irreducible E. This produces gamma_i as an actual FULL
functional embedding agreeing pointwise with ev_i∘gamma.
By the checked parameter-coordinate retraction formula
`Induced.line_parameter_coordinate_EHN_retraction`,
ev_i(ell_W(r))=r. Substitution establishes the final equation.

## Statement 2 — actual selected old-picture corollary

Let Old be an EHN-partite source over D, select a FULL
alpha:A↪D, and let

    R = Old.weakRestrict(D,alpha)

be the genuine FULL closed-support selected subsystem. The
checked `weakRestrictInclusion` provides a FULL embedding
inc:R↪Old. Let ell_W be a real HJ line embedding of R into
its power. Then any FULL irreducible gamma:E↪R^N
has a FULL OLD-stage extension

    old_gamma := inc ∘ gamma_i : E↪Old

and for every old-support vertex r corresponding to
an actual meeting gamma(x)=ell_W(r),

    old_gamma(x)=inc(r).

Consequently a **pure OLD tested subset** of a *single*
line attachment that meets an ambient full irreducible E-copy
situated in the power core only along the selected line root
can appeal to the Old-stage full E-copy intersection certificate:
the traced source vertices genuinely belong to the FULL
old_gamma(E), not just to some arbitrary weak partial E-copy.

This is a mathematically substantive repair of ONE component
of the pure-copy trace problem identified in PR #648.

## Sharp remaining multi-line obstruction

A later native Picture stage contains the power and several
copies of the Old picture along distinct HJ lines. A new
ambient irreducible copy may lie inside an EARLIER attached
Old copy, not the original power core. Its intersection
with the incoming line support is governed by the checked
`HJLineOverlapDichotomy`:

* When two lines share a parameter coordinate, equal image
  vertices have the same original source coordinate. The
  corresponding earlier Old A-copy can be transported to
  the newly attached Old copy on those vertices.
* When their parameter sets are disjoint, the pairwise
  overlap lies inside ONE full A-letter copy of the selected
  support. However this does NOT say that the ORIGINAL
  earlier A-copy's vertex index mapping extends to a full
  A-copy in the new Old source. A *partial A-copy
  correspondence* may not extend to an automorphism of A.

Moreover a single new line can meet the UNION of several
earlier line images in different full letter copies;
the checked two-coordinate multi-line audit exhibits this
explicitly. Thus pairwise trace lifting does not, by itself,
construct one compatible full target collar for the entire
ordered line history.

The productive next theorem is a **multi-line partial-A
trace transport** for a source A-copy in an earlier attached
Old copy, with a test-dependent finite record of its
intersections with the incoming line and the original
control part labels. A record might need to be a weak
root/closure profile, not a fixed full embedded A-copy.
Do not infer the unrestricted native n-pass sparsening
theorem from the present one-line result.

## Lean validation gate

Formalize first the two explicit exact, pointwise FULL
embedding theorems above, using the already checked
coordinate EHN and line retraction declarations. Include
two named `#print axioms` checks and an exact-head complete
build. No `sorry`, `admit`, or new axiom; no manuscript
changes or duplicate author TODOs.
