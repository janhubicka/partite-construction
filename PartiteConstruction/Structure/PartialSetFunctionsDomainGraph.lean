import PartiteConstruction.Structure.PartialSetFunctionsClosed
import PartiteConstruction.Relational.Homomorphism

/-!
# Relational encoding of genuinely partial set-valued operations

One incidence relation of arity r+1 is NOT sufficient: it loses
the distinction between an undefined input and a defined input
whose output set is empty.

For every F of arity r, we therefore introduce TWO relational
symbols:
  * Dom_F of arity r, recording that F is defined;
  * Graph_F of arity r+1, recording each actual output.
The graph is always contained in the domain cylinder.

In particular, defined-empty inputs contribute genuine domain
tuples and may contribute irreducibility even though no output
vertex is present. An original-2019 partial homomorphism carries
these two relations forward, but may add new domain tuples at
source-undefined inputs. It is NOT generally a relational
embedding or a domain-reflecting homomorphism.

This is an auxiliary encoding only. Graph/Hales--Jewett powers,
weak substructures, and completion maps have not been transferred
to this richer language by fiat.
-/

namespace StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {V : Type v} {W : Type w}

/-- Ordinary relations, definedness relations, output graphs. -/
def domainGraphLanguage (L : Language.{u}) : RelLanguage.{u} where
  Symbol := Sum L.RelSymbol (Sum L.FuncSymbol L.FuncSymbol)
  arity
    | .inl R => L.relArity R
    | .inr (.inl F) => L.funcArity F
    | .inr (.inr F) => L.funcArity F + 1

/-- Full relational information of a partial set-valued structure.
The `Dom_F` relation is independent of the output-incidence
relation `Graph_F`. -/
def domainGraph (A : PartialSetStructure L V) :
    RelStructure (domainGraphLanguage L) V where
  rel
    | .inl R => A.rel R
    | .inr (.inl F) => A.Defined F
    | .inr (.inr F) =>
        fun x =>
          A.HasOutput F (fun i => x i.castSucc)
            (x (Fin.last (L.funcArity F)))

/-- 2019-style partial homomorphisms preserve both the independent
domain relation and every existing output incidence.

The converse need not hold for genuinely multivalued functions:
positive relational preservation alone guarantees inclusion of
the mapped output set, not equality with the target value set. -/
theorem IsOriginalPartialHomomorphism.to_domainGraph_hom
    {A : PartialSetStructure L V}
    {B : PartialSetStructure L W}
    {f : V → W}
    (h : IsOriginalPartialHomomorphism A B f) :
    (domainGraph A).IsHomomorphism (domainGraph B) f := by
  intro symbol x hx
  cases symbol with
  | inl R =>
      exact h.1 R x hx
  | inr symbol =>
      cases symbol with
      | inl F =>
          obtain ⟨S, hS⟩ := hx
          exact ⟨Structure.imageSet f S, h.2 F x S hS⟩
      | inr F =>
          obtain ⟨S, hS, hy⟩ := hx
          refine ⟨Structure.imageSet f S, ?_, ?_⟩
          · exact h.2 F (fun i => x i.castSucc) S hS
          · exact ⟨x (Fin.last (L.funcArity F)), hy, rfl⟩

/-- The domain predicate detects a genuinely defined empty value,
which the old one-relation output graph would miss. -/
theorem example_domain_distinguishes :
    (domainGraph definedEmptyExample).rel
      (.inr (.inl ())) (fun _ : Fin 1 => ()) ∧
    ¬ (domainGraph undefinedExample).rel
      (.inr (.inl ())) (fun _ : Fin 1 => ()) := by
  constructor
  · exact ⟨∅, rfl⟩
  · rintro ⟨S, hS⟩
    cases hS

/-- Neither example has an output incidence. In particular the
output graph alone cannot distinguish their operation domains. -/
theorem example_no_output :
    (¬ (domainGraph definedEmptyExample).rel
      (.inr (.inr ())) (fun _ : Fin 2 => ())) ∧
    (¬ (domainGraph undefinedExample).rel
      (.inr (.inr ())) (fun _ : Fin 2 => ())) := by
  constructor
  · rintro ⟨S, hS, hy⟩
    have hs : S = ∅ := by
      cases hS
      rfl
    subst S
    exact hy
  · rintro ⟨S, hS, _hy⟩
    cases hS

end StructuralRamsey.PartialSetStructure
