---
Template: Symbol
Name: InductiveRecursor
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/InductiveRecursor
Keywords: [recursor, induction, recursion, eliminator, inductive type, motive]
SeeAlso: [TypeTheoryInductiveType, TypeTheoryTactic, WeakHeadNormalForm]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[InductiveRecursor]()[*type*]</code> is the recursor of the inductive type *type*, generated when the type is declared.

## Details & Options

- Its arguments are the type's parameters (implicit), a motive, one minor premise per constructor, the indices (implicit) and the term to eliminate.
- A minor premise takes the constructor's fields and an induction hypothesis for each recursive field; applied to a constructor, the recursor reduces to its minor premise.
- The recursor is how definitions recurse and how proofs go by induction: the tactic `"Induction"` builds an application of it.

## Basic Examples

The recursor of the natural numbers:

```wl
TypeOf[TypeTheoryTerm[InductiveRecursor[Naturals]]]
```

<!-- => ∀_m∶ℕ → Sort u m[0] → (∀_n∶ℕ m[n] → m[n + 1]) → ∀_t∶ℕ m[t] -->

---

Recursion: double a natural number, adding 2 for each successor:

```wl
double = TypeTheoryTerm[Function[{Typed[n, Naturals]}, InductiveRecursor[Naturals][
    Function[{Typed[t, Naturals]}, Naturals],
    0,
    Function[{Typed[k, Naturals], Typed[r, Naturals]}, r + 2],
    n
]]];
WeakHeadNormalForm[TypeTheoryTerm[double[5]]]
```

<!-- => 10 -->
