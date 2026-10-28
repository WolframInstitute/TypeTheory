---
Template: Symbol
Name: MultiplicationOneRight
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MultiplicationOneRight
Keywords: [multiplication, one, right, prelude, natural numbers]
SeeAlso: [MultiplicationOneLeft, MultiplicationZeroRight, AdditionZeroLeft]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[MultiplicationOneRight]()[*n*]</code> proves <code>*n* * 1 == *n*</code>.

## Details & Options

- [MultiplicationOneRight]() is a theorem of the prelude: `n * 1` computes to `0 + n`, and [AdditionZeroLeft]() proves the rest.

## Basic Examples

The statement of [MultiplicationOneRight]():

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationOneRight]]
```

<!-- => ∀_n∶ℕ n 1 == n -->

---

For a variable:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[n, Naturals]}, MultiplicationOneRight[n]]]]
```

<!-- => ∀_n∶ℕ n 1 == n -->

## Scope

The tactic `"Simplify"` removes every factor of 1 on the right:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, x * 1 + y * 1 == x + y], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Simplify", {MultiplicationOneRight}]
}]
```

<!-- => Proof complete -->

## Properties and Relations

`n * 1` computes to `0 + n`, as `"Change"` shows, and [AdditionZeroLeft]() proves the rest:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, n * 1 == n], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Change", 0 + n == n]
}]
```

<!-- => Proof, 1 goal: n ∶ ℕ ⊢ 0 + n == n -->

---

The integers have the same law, [IntegerMultiplicationOne]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerMultiplicationOne, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ x 1 == x -->

## Possible Issues

Unlike `n + 0`, `n * 1` is not *n* by computation, so `"Reflexivity"` does not prove it:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, n * 1 == n], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Failure["NotReflexive", ...] -->
