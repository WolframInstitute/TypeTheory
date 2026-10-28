---
Template: Symbol
Name: MultiplicationSuccessorRight
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MultiplicationSuccessorRight
Keywords: [multiplication, successor, right, prelude, natural numbers]
SeeAlso: [MultiplicationSuccessorLeft, MultiplicationDistributivityLeft, Times]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[MultiplicationSuccessorRight]()[*m*, *n*]</code> proves <code>*m* * (*n* + 1) == *m* * *n* + *m*</code>.

## Details & Options

- [MultiplicationSuccessorRight]() is a theorem of the prelude that holds by computation: it is how [Times]() is defined.

## Basic Examples

The statement of [MultiplicationSuccessorRight]():

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationSuccessorRight]]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ m (n + 1) == m n + m -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationSuccessorRight[3, 4]]]
```

<!-- => 3 (4 + 1) == 3 × 4 + 3 -->

## Scope

The tactic `"Reflexivity"` proves it, since it is how multiplication computes:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals], Typed[n, Naturals]}, m * (n + 1) == m * n + m], {
    TypeTheoryTactic["Introduce", m, n],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Proof complete -->

---

Applied again and again, it turns a product by a literal into a sum, so `m * 3` is `0 + m + m + m` by computation:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Function[{Typed[m, Naturals]}, m * 3]], TypeTheoryTerm[Function[{Typed[m, Naturals]}, 0 + m + m + m]]]
```

<!-- => True -->

## Properties and Relations

The successor on the left is not by computation, so `"Reflexivity"` does not prove [MultiplicationSuccessorLeft]():

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals], Typed[n, Naturals]}, (m + 1) * n == m * n + n], {
    TypeTheoryTactic["Introduce", m, n],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Failure["NotReflexive", ...] -->
