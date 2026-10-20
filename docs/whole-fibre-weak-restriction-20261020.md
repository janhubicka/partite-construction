# Whole-fibre weak restriction and source-defined projections

20 October 2026. English proof and semantic audit before Lean validation.

## Convention

For a partial set-valued function, an application is either undefined or has
a specified complete set of values. On a vertex subset S, retain an application
with value U exactly when U is contained in S. Otherwise the whole application
becomes undefined. A defined empty value survives, because the empty set is
contained in every S.

This is the whole-fibre convention requested for the functional Appendix.
The existing `Structure.weakInduce` and `PartialSetStructure.weakInduce` instead
retain individual surviving outputs. They agree with this convention when
every fibre is wholly retained or wholly omitted, including for singleton
fibres, but disagree on a partially retained multivalued fibre. For example,
F(a)={b,c} restricted to {a,b} is undefined under whole-fibre restriction and
has value {b} under the existing clipping convention. No old definition or
checked theorem is silently changed by the new module.

## Exact-preimage restriction of full embeddings

Let f:A→B be a full embedding and T a set of target vertices. Put S=f⁻¹(T).
For every source value U,

    f[U] ⊆ T  if and only if  U ⊆ S.

Hence the whole application survives on one side exactly when it survives on
the other. When it survives, the image of its subtype value is precisely the
subtype of its image. Undefined applications remain undefined on both sides;
defined empty applications remain defined empty. Relations restrict as usual.
The exact restricted map is consequently a full embedding A|S→B|T. No closure
of S or T is required, and constants are allowed.

## Restriction of source-defined partial homomorphisms

Let f:A→B preserve every defined source application with its complete image
set, and let g:S→T be any map obtained by restricting f to vertex subsets.
If an application survives in A|S, its ambient value U is contained in S.
Its value in B is exactly f[U], which is contained in T because g maps S to T.
The target application therefore also survives, and its value is exactly
g[U]. Nothing is required of an application that is undefined in A|S.

Thus g is again a source-defined partial homomorphism between the exact weak
restrictions. In particular this proves the inclusion A|S→A and the exact
image projection A|S→B|f[S]. The latter is the projection property required
by the weak-substructure induction; S is not replaced by its generated hull.

## Agreement and limits

If each ambient fibre is either contained in S or disjoint from S, the old
clipping restriction and the whole-fibre restriction agree, including their
independent defined-empty bits. In the retained case both keep the full value;
in the omitted nonempty case both become undefined; an originally empty
defined value remains defined in both conventions.

If a fibre meets both S and its complement, the two value operations provably
differ. Therefore existing closure/USize statements for clipped weak tests
cannot be cited as statements about whole-fibre tests without an additional
comparison theorem. Output-part singletonization alone does not supply this
comparison: splitting first can retain one output from a fibre that the
whole-fibre operation discards entirely.

The new module supplies restriction and projection lemmas, not a Ramsey
theorem. It does not equate a source-defined homomorphism with a full embedding,
does not assert reflection of undefined source applications, and does not
construct compatible target B-tree completions over nonclosed mixed roots.

## Validation

The new Lean module imports only the existing partial-set-function restriction
API. Named axiom checks cover the value/preimage law, full embedding restriction,
source-defined restriction, exact-image projection, and the comparison and
separation of the two weak conventions. Compilation and the repository axiom
audit must succeed before any manuscript validation marker is added.
