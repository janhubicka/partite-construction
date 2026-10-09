# Theorem 2.18: native closure of the power and Picture witness

9 October 2026, PR #175. Continues #174 and the interrupted native-closure
branch. The literal 2019 predicates and frozen manuscript remain unchanged.
Source context: Hubicka--Nesetril, All those Ramsey classes (2019),
arXiv:1606.07979v4, Sections 2.3--2.5.

## 1. A root-cover criterion with no circular closedness assumption

`isUClosed_of_closed_root_cover` proves that a structure is U-closed when:
its prescribed root embeddings and closure-relation tuples are covered by
U-closed embedded pieces, and the piece ranges are relative U-substructures.
The closure tuple for a root exists in its selected piece. Any competing
tuple in the whole must stay in that piece by relative range closure, so
uniqueness in the piece establishes uniqueness in the whole.

The criterion has no finiteness or global projection hypothesis. It handles
all closure rules, not only unary closure rules or function-graph encodings.

## 2. Closedness of the actual arbitrary-index attachment

`Attachment.attach_isUClosed` derives closedness from a U-closed old picture,
a U-closed core, and a relatively closed attaching support in the old picture.
The attachment and its tuple relation are the existing native construction.
The index set can be arbitrary, including empty or infinite.

The proof establishes relative closedness of the core range FIRST: a copy
tuple with its roots in the core has all source root vertices in the attaching
support, hence its outputs remain there. To close a particular copy range,
separate roots entirely in the core from a root with an exterior vertex.
In the former case use the closed attaching-map image inside the already
closed core; in the latter the tuple must belong to that unique copy.
Neither step assumes the attachment is already closed.

Finally each prescribed root is ordinarily irreducible, so the existing
core-or-copy theorem localises it. The root-cover criterion now proves
whole-attachment closedness without the old whole-closedness premise.
No irreducibility of the entire old picture, core or support is required.

## 3. Closedness of the native positive coordinatewise power

`Induced.coordinate_isHomomorphismEmbedding` proves that evaluation at any
coordinate is an ORDINARY homomorphism-embedding under ordinary partiteness.
This is not the stronger protected-test map assertion.

`Induced.power_isUClosed` assumes the part structure A and the A-partite
system B are U-closed, and N>0. For an embedded prescribed root in the native
power, each coordinate is an embedded prescribed root in B and therefore
has a unique closure tuple. Project these coordinate tuples to A. They
all extend the same root in A, so uniqueness in A forces their part labels
to agree. They consequently assemble into genuine tagged power vertices.
Coordinate uniqueness and N>0 give uniqueness of the assembled tuple.
The no-spurious-roots direction is proved separately, using the coordinate
root embeddings and one fixed coordinate for reflection.

This proves a previously assumed construction fact. It does NOT infer that
the power's part projection preserves every closed U-irreducible test.
That stronger projection invariant remains a separate proof obligation.
The positive exponent is explicit; no assertion is made at N=0.

## 4. A finite closed local Picture witness, with the original indices

The support selected by a closed A-copy inside a closed part structure D is
relatively closed in any positively projecting old system. Thus restricting
a U-closed old picture to that support gives a U-closed restricted system.
Its positive native power is closed by Section 3.

`Induced.picture_build_power_isUClosed` then proves closedness of the ACTUAL
`Picture.build`: the attached-copy index type consists of all partite
embeddings of the restriction into the power, as in the existing implementation.
It is not silently replaced by only Hales--Jewett line indices.

`Induced.pictureLemma_isUClosed` uses the existing finite Hales--Jewett lemma
to construct a finite C which is simultaneously:

- ordinarily partite over the given D;
- U-closed;
- a witness to the original local `PictureProperty A B alpha C Color`.

The theorem produces its witness; it does not assume a closed Ramsey core
or a closed whole attachment. It is a LOCAL Picture lemma, not the full
iterated construction and not a claim that all protected tests are covered
by old copies. The part structure D is explicitly closed in this theorem;
this is not a theorem about an arbitrary nonclosed initial Ramsey witness.

## 5. Connection to the already verified local-coordinate completion

`Induced.line_attachment_isUClosed` proves the analogous closedness for the
line-indexed attachment used in #174. The wrapper
`completion_of_common_coordinate_from_closed_pieces` removes the former
assumed whole-attachment closedness from that local completion theorem.
It now follows from the closed old picture, closed part structure, and
relatively closed support, with positivity of the exponent supplied by
the selected coordinate.

The protected part projection of the core and the local common-parameter
coordinate premise remain explicit. This patch neither assumes a globally
common coordinate (which #174 refutes) nor closes the no-common-coordinate
case by an absolute boundary-rank shortcut (which #173 refutes).

## 6. Next substantive construction obligations

Prove the stronger protected core-projection/coverage invariant for the
appropriate native refinement, using its actual construction history.
Then complete the no-common-coordinate rank branch with the correct
boundary data and earlier-stage completions. The existing ordinary
partite projection cannot simply be relabelled as a protected projection.

Closed inputs suffice for the new local witness. Any use in the temporarily
semi-closed recursive construction must be separately justified; nothing
here changes semi-closed inputs into closed ones by definition.

The literal Definition 2.17 bridge, the complete rank increment and its
iteration, and transport to genuine partial-function languages remain
separate obligations. Theorem 2.18 is not marked complete.

## Validation scope

Twelve new theorem declarations in four modules are individually printed in
CheckClosureAxioms. All previous audit checks must remain present in the
final diff. No new axioms, `sorry`, or provisional main-theorem validation
marks are introduced. The final combined-head full project build and
permitted-axiom audit, not a partial earlier import build, are required
before merging or labelling these statements Lean-validated. Review scope
is recorded directly; no independent-referee process is claimed.
