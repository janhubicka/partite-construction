# Why one Hales–Jewett coordinate cannot retract every attached copy

**Status:** adversarial proof note, 16 October 2026. This is a small
relational example; function-output transversality is vacuous here.
It is an obstruction to an overly strong *multi-line coordinate
retraction strategy*, **not** an obstruction to the published functional
Ramsey or sparsening theorem.

## A three-vertex example

Take the language of undirected graphs. Let the original control
`D` consist of the edge with vertices `0,1`. Let the old partite
system `Old` have three vertices

- `a` and `a'` in part `0`,
- `b` in part `1`,

with the only edge `a--b`. In particular `a'` is isolated.

The part map `Old→D` is an EHN homomorphism-embedding: the only
non-singleton irreducible induced substructure is the edge
`{a,b}`, and it maps fully to the edge in `D`; the singleton
`{a'}` maps fully to part `0`.

Let `A` be the one-vertex graph, placed at `alpha(A)={0}`.
Its complete selected support in `Old` is
`S={a,a'}`; as there are no function symbols, this is closed.

The native Hales–Jewett alphabet contains the constant letter
`e:A↪Old|S` sending the single vertex of `A` to `a'`.

Fix a coordinate `i` of the genuine HJ power. For any HJ line
whose symbol at `i` is this constant letter, coordinate evaluation
on the power core sends **both** attached support vertices
`a,a'` to `a'`.

To extend this coordinate shadow across the attached whole copy
of `Old`, while keeping the original control labels, an EHN
endomorphism `r:Old→Old` would have to satisfy

```
r(a) = a',     r(a') = a',     part(r(b)) = 1.
```

But the only vertex in part `1` is `b`, so `r(b)=b`.
The source edge `a--b` would map to the nonedge `a'--b`.
Thus **no graph homomorphism**, let alone an EHN map, extends the
constant-letter coordinate shadow to the whole old copy.

The example uses a genuinely EHN-partite old system and a closed
selected support. In a functional language, the necessary
per-fibre output transversality would be an additional invariant,
but it cannot resolve this graph-level obstruction.

## What is proved and what is not

- Each coordinate evaluation of the *power core* is EHN:
  `FunctionalPartite.Induced.coordinateEHN` (PR #354, merged).
- An attachment whose HJ line has a PARAMETER symbol at that
  coordinate retracts EHN onto the copied Old:
  `FunctionalPartite.EHN.lineUnitAttachment_EHN_retraction`
  (PR #357, merged).
- A general binary attachment has an EHN shadow when the core
  shadow and a copied-side EHN map agree on the full selected support:
  `unitAttachment_EHN_shadow_of_compatible`
  (PR #359, pending verification).

For a constant symbol the required copied-side self-map need not
exist, as above. Hence a fixed coordinate **cannot** provide
a global retraction for the whole HJ Picture in general.

The remaining maximal mixed step must use more flexible strict
relative completions (with actual HJ history), rather than postulate
constant-letter extensions or reuse a different line's parameter
coordinate. The full conditional functional tree/history gluing and
transversal-image infrastructure is already verified in #342/#347;
the **existence** of compatible side witnesses is still open.

## The actual Picture attaches more than Hales–Jewett lines

The verified `FunctionalPartite.EHN.pictureLemma` constructs the full
coordinatewise power `E`, and then calls `EHN.attachAll` indexed by
**every** full partite embedding

```
g : FunctionalPartite.Embedding R E
```

of the selected support `R` into `E`. Hales–Jewett LINE embeddings
are a special family used to extract a monochromatic line, but they
are not the entire attachment index set.

An arbitrary full partite embedding need not split at ANY coordinate.
Already in the empty language, take a single part with selected
support `R={a,b,c}` and its two-coordinate power `E=R²`.
The injection

```
g(a)=(a,a),   g(b)=(a,b),   g(c)=(b,a)
```

is a full partite embedding (there are no relations or functions).
Neither coordinate projection is injective on its image:
coordinate 0 identifies `a` with `b`, and coordinate 1
identifies `a` with `c`. Thus neither coordinate evaluation
composed with `g` can equal the identity on the support.

This second obstruction differs from the constant-letter example
above. In the empty language a non-coordinate retraction of
`E` onto `R` can of course be defined, but the `EHNPicture`
theorem supplies no such compatible retraction for arbitrary
genuinely functional `R`, nor a simultaneous one for all
attachments. The source supports and output fibres are already
correctly function-closed/transversal; neither condition manufactures
a splitting coordinate.

**Proof acceptance test:** a claimed preservation theorem for the
FULL native Picture must quantify over the complete
`FunctionalPartite.Embedding R E` attachment family, not merely
`Line (Letter A R) N`. The current one-line strict locality
theorem covers only the latter and must not be promoted to the
unrestricted Picture case without further work.
