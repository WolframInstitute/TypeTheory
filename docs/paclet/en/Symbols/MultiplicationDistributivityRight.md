---
Template: Symbol
Name: MultiplicationDistributivityRight
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MultiplicationDistributivityRight
Keywords: [multiplication, distributivity, right, prelude, natural numbers]
SeeAlso: [MultiplicationDistributivityLeft, MultiplicationCommutativity, MultiplicationSuccessorLeft]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[MultiplicationDistributivityRight]()[*a*, *b*, *c*]</code> proves <code>(*a* + *b*) * *c* == *a* * *c* + *b* * *c*</code>.

## Details & Options

- [MultiplicationDistributivityRight]() is a theorem of the prelude, proved from [MultiplicationDistributivityLeft]() and [MultiplicationCommutativity]().

## Basic Examples

The statement of [MultiplicationDistributivityRight]():

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationDistributivityRight]]
```

<!-- => ∀_a∶ℕ ∀_b∶ℕ ∀_c∶ℕ (a + b) c == a c + b c -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationDistributivityRight[2, 3, 4]]]
```

<!-- => (2 + 3) 4 == 2 × 4 + 3 × 4 -->

## Scope

The tactic `"Rewrite"` multiplies out a product inside a goal, and the goal closes:

```wl
TypeTheoryProof[ForAll[{Typed[a, Naturals], Typed[b, Naturals], Typed[c, Naturals]}, (a + b) * c + 1 == a * c + b * c + 1], {
    TypeTheoryTactic["Introduce", a, b, c],
    TypeTheoryTactic["Rewrite", MultiplicationDistributivityRight[a, b, c]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

With *b* equal to 1 and [MultiplicationOneLeft](), it gives [MultiplicationSuccessorLeft]():

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, (x + 1) * y == x * y + y], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Rewrite", MultiplicationDistributivityRight[x, 1, y]],
    TypeTheoryTactic["Rewrite", MultiplicationOneLeft[y]]
}]
```

<!-- => Proof complete -->

---

It follows from [MultiplicationDistributivityLeft]() and [MultiplicationCommutativity](), as the prelude proves it:

```wl
TypeTheoryProof[ForAll[{Typed[a, Naturals], Typed[b, Naturals], Typed[c, Naturals]}, (a + b) * c == a * c + b * c], {
    TypeTheoryTactic["Introduce", a, b, c],
    TypeTheoryTactic["Rewrite", MultiplicationCommutativity[a + b, c]],
    TypeTheoryTactic["Rewrite", MultiplicationDistributivityLeft[c, a, b]],
    TypeTheoryTactic["Rewrite", MultiplicationCommutativity[c, a]],
    TypeTheoryTactic["Rewrite", MultiplicationCommutativity[c, b]]
}]
```

<!-- => Proof complete -->

---

The tactic `"Ring"` proves the same statement without naming the law:

```wl
TypeTheoryProof[ForAll[{Typed[a, Naturals], Typed[b, Naturals], Typed[c, Naturals]}, (a + b) * c == a * c + b * c], {
    TypeTheoryTactic["Introduce", a, b, c],
    TypeTheoryTactic["Ring"]
}]
```

<!-- => Proof complete -->
