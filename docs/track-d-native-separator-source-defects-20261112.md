# Track D — exact native one-copy separator defect alternatives (12 November 2026)

## Scope and theorem

The exact, FULL native common separator `pb.common` of the existing
`closedTestPullback` attached along a selected full `alpha:A↪Douter`
has the **canonical** EHN map
`q = (B.weakRestrict ...).part ∘ pb.commonMap : pb.Common → A`.
This is the actual closed-test pullback of one full functional
`UnitAttachD` attachment, not a freely enlarged weak test.

The new theorem states that either this **same** canonical q is
realized by a FULL embedding of the whole common separator into A,
or one of the following ACTUAL original-source defects exists:

* two distinct common-separator vertices have the same q-label;
* some OLD relation symbol and an ACTUAL common-separator input
  tuple with **two distinct source input vertices** is absent in
  the source but positive at its projected tuple in A;
* some OLD function symbol and an ACTUAL common-separator input
  tuple with **two distinct source input vertices** is
  source-undefined but target-defined.

The proof uses the verified native `closedTestPullback_common_EHN`
and the already checked #589/#603 three-defect and minimum-two-input
theorems. It assumes no global source finiteness, no full native
source homomorphism, and no all-input test-cover assumption.

## Useful low-arity corollary

When ALL OLD primitive function and relation arities are at most one,
the canonical q is the underlying map of a FULL root embedding **iff
q is vertex-injective**. This is a literal native-attachment
specialization, stronger than merely saying the root decomposes
when a full embedding does not exist. Nullaries and repeated tuple
arguments are not silently discarded.

## Adversarial limitations

This is a SINGLE generic full native one-copy attachment. It is
not yet the genuine Hales–Jewett power with its ORDERED collection
of all parameter-line embeddings and previous attachment histories.
It therefore cannot replace the missing full-history-relative
old-side target construction.

Nor does full root injectivity/embedding alone supply a relative
strict B-tree completion of each outer side over one prescribed
Start, nor can a diagnostic source input hull be counted in lieu of
the literal weak test or its original vertex/generator rank. Source
defined-empty values in the genuine Option(Set) representation
remain distinct from native undefined=empty fibres: the theorem is
about the original-2019 nonempty-source-defined convention in the
native Structure formalization.

There is no change to the frozen numbered survey manuscript or
collaborator TODOs. This PR is **DRAFT** until the entire exact-head
Lean build and both named `#print axioms` checks pass.
