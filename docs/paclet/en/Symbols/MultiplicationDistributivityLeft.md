---
Template: Symbol
Name: MultiplicationDistributivityLeft
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MultiplicationDistributivityLeft
Keywords: [multiplication, distributivity, left, prelude, natural numbers]
SeeAlso: [MultiplicationDistributivityRight, MultiplicationAssociativity, AdditionAssociativity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[MultiplicationDistributivityLeft]()[*a*, *b*, *c*]</code> proves <code>*a* * (*b* + *c*) == *a* * *b* + *a* * *c*</code>.

## Details & Options

- [MultiplicationDistributivityLeft]() is a theorem of the prelude, proved by induction on *c* with [AdditionAssociativity]().

## Basic Examples

The statement of [MultiplicationDistributivityLeft]():

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationDistributivityLeft]]
```

<!-- => ∀_a∶ℕ ∀_b∶ℕ ∀_c∶ℕ a (b + c) == a b + a c -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationDistributivityLeft[2, 3, 4]]]
```

<!-- => 2 (3 + 4) == 2 × 3 + 2 × 4 -->

## Scope

The tactic `"Rewrite"` multiplies out a product inside a goal, and the goal closes:

```wl
TypeTheoryProof[ForAll[{Typed[a, Naturals], Typed[b, Naturals], Typed[c, Naturals]}, a * (b + c) + 1 == a * b + a * c + 1], {
    TypeTheoryTactic["Introduce", a, b, c],
    TypeTheoryTactic["Rewrite", MultiplicationDistributivityLeft[a, b, c]]
}]
```

<!-- => Proof complete -->

---

With `"RightToLeft"`, `"Rewrite"` collects a common factor instead:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, x * y + x * y == x * (y + y)], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Rewrite", MultiplicationDistributivityLeft[x, y, y], "RightToLeft"]
}]
```

<!-- => Proof complete -->

## Properties and Relations

The tactic `"Ring"` proves the same statement without naming the law:

```wl
TypeTheoryProof[ForAll[{Typed[a, Naturals], Typed[b, Naturals], Typed[c, Naturals]}, a * (b + c) == a * b + a * c], {
    TypeTheoryTactic["Introduce", a, b, c],
    TypeTheoryTactic["Ring"]
}]
```

<!-- => Proof complete -->

---

The integers have the same law, [IntegerDistributivity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerDistributivity, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ ∀_y∶ℤ ∀_z∶ℤ x (y + z) == x y + x z -->
