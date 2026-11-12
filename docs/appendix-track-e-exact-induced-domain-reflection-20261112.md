# Appendix A / Track E — exact induced OLD-domain reflection (12 November 2026)

## Why this is a useful intermediate theorem

The merged upstream [Track E #1045](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/1045) retains an **induced-closed U-homomorphism-embedding** on the actual selected global control map f. Merged [#1048](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/1048) derives native source-defined HE only under the strong assumption that *every* full native irreducible E-copy has a **full canonical tagged** lift on the exact E carrier. The latter is not yet proved.

There is a smaller intermediate assertion that avoids demanding canonical equality of the whole source OLD description: on ANY exact vertex test S for which a FULL tagged embedding

    g: C|S -> Tag(Target)

has *already* been obtained on the chosen map, the actual final decoder reflects primitive function-domain membership:

    Decoder(C).Defined(F, x)  <->  Target.Defined(F, g(x))

for every primitive input x with vertices in S. Here Source C is the FINAL U-closed, protected-B-covered tagged witness. This reflects **domain membership on S**; it is **not** global all-tuple domain reflection of the source-defined control map.

## Lean lemmas

- `hasWholeMaskDomain_induce_iff`: for the OLD domain predicate, `HasWholeMaskDomain (E.induce S) F x ↔ HasWholeMaskDomain E F (Subtype.val ∘ x)` with **no closure or finite-rank assumption**. Proof reconstructs every root vertex from a primitive input using surjectivity of the equality-pattern argument map. In particular it handles repeated arguments, nullaries and defined-empty outputs.
- `wholeMaskDecoded_defined_iff_of_exact_tagged_embedding`: composes the first lemma, the already verified OLD `hasWholeMaskDomain_map_iff` for a full embedding, and canonical target `hasWholeMaskDomain_iff_sourceDefined`, assuming only the OLD-decoder domain dictionary for C.
- `wholeMaskCovered_defined_iff_of_exact_tagged_embedding`: invokes the *existing verified* `wholeMaskPartialDecode_defined_iff_OLD_domain_of_closed_coverage` to discharge the domain dictionary for the actual final 2019 object. This step retains the positive-arity hypothesis and real protected canonical B-copy coverage; it does not treat arbitrary intermediate Pictures as canonical.

The proofs preserve the literal S, original global map on S and original arity; they do NOT enlarge S to a U-closure or replace the fixed cutoff n.

## Next unproved geometry / semantic bridge

For every FULL native irreducible `e : E ↪ D` in the exact final decoded native System D, let `S = range e` in the **actual** tagged C. Show that `C.induce S` satisfies the exact closed and U-irreducible hypotheses of the corrected induced-closed map, or otherwise construct a full tagged test on the **same carrier**. Then the actual selected hTag produces g, the new lemma reflects all native function domains on E, and the existing source-defined whole-fibre law plus full old relation reflection should give a native FULL E-copy in the control. This path does not require a global equality `C = Tag(Decoder(C))`, which is stronger and not currently certified.

**Warning:** the alternative trivial implication “source-defined Hom + Ramsey + B-coverage ⇒ HE on the same map” is refuted by the existing actual Ramsey counterexample in local Track E #572. No new green marker or survey prose change is justified by this PR alone.

## Validation policy

This is an additive Lean branch: new module, three named root axiom checks and one active root import, plus this note. Do not merge until exact-head full Lean build and standard-axiom prints pass. The survey manuscript remains frozen and no removed author TODO is restored.
