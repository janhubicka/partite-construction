# Vertex closure for partial set-valued functions

20 October 2026. English proof before Lean validation.

A partial operation has values in `Option (Set V)`. Its domain is independent
of its output incidences: `none` and `some ∅` are distinct. Nevertheless,
neither state forces a new vertex into a function-closed set. Therefore
collapsing both states to an empty output fibre preserves the predicate
that a vertex set is closed under the operations. This does not identify
the original structures, their operation domains, or their full maps.

For a vertex set T, one implication is immediate: a defined original value
U contributes exactly U to the collapsed structure. For the converse, split
the partial value into `none` and `some U`. The undefined case has no output
to consider; the defined case uses original closedness. This proves the
closed-set equivalence, including empty values and nullary operations.

Define the function closure of S using the already checked native closure
of `collapseDomain`. By the closed-set equivalence, this is exactly the
intersection of all original partial-function-closed sets containing S.
Consequently it contains S, is closed, is least among such sets, is monotone,
and is idempotent. A generating set is a set whose closure is the whole
carrier; the finite generator bound is the usual cardinality bound on one
finite generating set.

For the whole-fibre weak structure on an exact carrier S, a value survives
precisely when an ambient value U is defined and U is entirely contained in
S. Thus a set Q of vertices of S is intrinsically closed exactly when every
such complete ambient value on input coordinates in Q has all its subtype
outputs in Q. The equivalence is obtained in both directions from the
already checked `wholeWeakValue_eq_some_iff`. It uses whole containment
U ⊆ S; an individual surviving output is insufficient. Neither S nor Q is
replaced by an ambient closure.

A source-defined partial homomorphism pulls closed sets back to closed
sets: an original defined value maps to its entire image value, which is
contained in the target closed set whenever the input tuple is there.
It follows that the image of the source closure of a seed is contained in
the target closure of the image seed. This needs no reflection of source
undefined inputs. A surjective such map therefore does not increase a
finite generator bound.

Apply this to the checked whole-weak image map from S onto f[S]. It is a
source-defined partial homomorphism between the exact weak structures:
every surviving source value is a complete ambient value contained in S,
and its complete image is therefore contained in f[S]. The map is
surjective because a vertex of f[S] comes with a witness x in S whose
image is that vertex.

Consequently the intrinsic generator bound of the whole-weak structure on
f[S] is no larger than that of the whole-weak structure on S. The target
may acquire additional defined operations from the ambient target; these
can only lower its generator requirement. The proof uses the images of
the original finite generators, and replaces neither S nor f[S] by an
ambient closed hull.

Finally the existing native nonempty-defined conversion followed by
`collapseDomain` returns the original native structure. If its original
value is nonempty the claim is immediate; if it is empty both sides have
empty incidence fibre. The closure and generator-bound identities follow.
This is a bridge for vertex closure only. The richer partial interface
continues to preserve defined-empty values independently.

## Independent mathematical audit

The dictionary audit approved this argument, emphasizing that domain data
must not be inferred from vertex closure, and that weak closedness requires
the entire ambient output fibre to lie in the tested carrier. Constants
are supported by this closure API; positive-root restrictions of the later
canonical U-language are a separate issue.
