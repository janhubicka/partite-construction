# Free amalgams restricted to whole-fibre weak substructures

Let a partial set-valued function have values in `Option (Set V)`.
Thus `none` means undefined and `some ∅` means defined with empty value.
On a vertex set S, retain an application exactly when all its outputs
belong to S; otherwise make it undefined. In particular a defined empty
value remains defined. We call this the whole-fibre weak restriction.

## Statement

Suppose a structure C is a free amalgam of L and R over H, with full
embeddings sL:H→L, sR:H→R, iL:L→C and iR:R→C. For every vertex set S⊆C,
put

* SL = iL⁻¹[S];
* SR = iR⁻¹[S];
* SH = (iL∘sL)⁻¹[S] = (iR∘sR)⁻¹[S].

Then the whole-fibre weak restriction of C to S is a full free amalgam
of the whole-fibre weak restrictions of L to SL and R to SR, over the
whole-fibre weak restriction of H to SH. The four maps are the literal
restrictions of the original maps.

No subset above is required to be closed in its ambient structure.
No closure hull is substituted for S, SL, SR or SH. The statement holds
for arbitrary arities, repeated inputs, multivalued outputs and defined
empty values.

## Proof

A full embedding preserves the complete partial value, including its
domain bit. An ambient source value is wholly contained in the preimage
of a target set precisely when its complete image is contained in that
target set. Therefore each full embedding restricts to a full embedding
on the displayed weak structures.

The cover and intersection identities restrict to S immediately.
An ordinary relation tuple of C on S comes from one original side.
Its source tuple then lies in the corresponding exact preimage, so the
same relation identity holds between the weak structures.

Consider a function application that is defined in the weak restriction
of C. It is defined in C, so the free-amalgam domain condition puts its
whole input tuple in one side, say L. Its lifted tuple belongs to SL.
The full embedding from the weak restriction of L into the weak
restriction of C reflects definedness on this tuple, and preserves the
entire value. This gives the required side application. Conversely,
each defined application of either weak side maps to its complete
defined value in the weak amalgam.

For partial set-valued functions it is necessary to include domain
tuples in the free-amalgam condition. A crossing input with defined
empty value has no output incidence and would escape a condition
phrased only in terms of function graphs. The new free-amalgam
interface includes this domain condition. Its derived `func_iff`
states the complete-value decomposition, including empty values.

## Application to the existing native construction

The existing native `Structure` convention represents undefined inputs
by empty fibres. `Structure.toNonemptyPartial` exposes exactly that
convention in the Option language: a nonempty fibre becomes `some F(x)`
and an empty fibre becomes `none`. Full embeddings and full native free
amalgams preserve this translation.

Consequently `Structure.IsFreeAmalgam.wholeWeakPartialInduce_withMaps`
applies directly to every full native attachment already constructed by
the Hales--Jewett Picture. In particular it applies to the actual
one-copy-versus-rest diagram proved by `unit_isFreeAmalgam_full`.
It does not require a new relational Ramsey construction.

## Scope and audit

This is a source decomposition theorem. It does not construct compatible
strict target-tree completions across the resulting weak root.

An external original-partial projection is not assumed to reflect
undefined applications. Only the four full attaching embeddings use
domain reflection. Moreover, a homomorphism of whole-fibre weak tests
does not automatically become a homomorphism-embedding on all intrinsic
irreducibles of those tests. The eventual completion argument must keep
its intended ambient closed-irreducible test convention explicit.

The translation from the existing native API covers its nonempty-defined
fibre convention. The general Option free-amalgam theorem additionally
handles defined empty values, but this does not extend the existing
Ramsey construction to that richer semantics by itself.

The new modules require full Lean compilation and named axiom audits
before receiving validation markers.
