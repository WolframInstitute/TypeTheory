---
Template: Symbol
Name: MultiplicationAssociativity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MultiplicationAssociativity
Keywords: [multiplication, associativity, prelude, natural numbers]
SeeAlso: [MultiplicationCommutativity, AdditionAssociativity, PowerAddition]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[MultiplicationAssociativity]()[*a*, *b*, *c*]</code> proves <code>*a* * *b* * *c* == *a* * (*b* * *c*)</code>.

## Details & Options

- [MultiplicationAssociativity]() is a theorem of the prelude, proved by induction on *c* with [MultiplicationDistributivityLeft]().
- `a * b * c` is read from the left, as `(a * b) * c`.

## Basic Examples

The statement of [MultiplicationAssociativity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationAssociativity]]
```

<!-- => ∀_a∶ℕ ∀_b∶ℕ ∀_c∶ℕ a b c == a (b c) -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationAssociativity[2, 3, 4]]]
```

<!-- => 2 × 3 × 4 == 2 (3 × 4) -->

## Scope

The tactic `"Rewrite"` regroups a product inside a goal, and the goal closes:

```wl
TypeTheoryProof[ForAll[{Typed[a, Naturals], Typed[b, Naturals], Typed[c, Naturals]}, a * b * c + 1 == a * (b * c) + 1], {
    TypeTheoryTactic["Introduce", a, b, c],
    TypeTheoryTactic["Rewrite", MultiplicationAssociativity[a, b, c]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

The tactic `"Ring"` proves the same statement without naming the law:

```wl
TypeTheoryProof[ForAll[{Typed[a, Naturals], Typed[b, Naturals], Typed[c, Naturals]}, a * b * c == a * (b * c)], {
    TypeTheoryTactic["Introduce", a, b, c],
    TypeTheoryTactic["Ring"]
}]
```

<!-- => Proof complete -->

---

The integers have the same law, [IntegerMultiplicationAssociativity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerMultiplicationAssociativity, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ ∀_y∶ℤ ∀_z∶ℤ x y z == x (y z) -->

## Possible Issues

The tactic `"Reflexivity"` does not prove it for variables, since the products do not compute while *c* is a variable:

```wl
TypeTheoryProof[ForAll[{Typed[a, Naturals], Typed[b, Naturals], Typed[c, Naturals]}, a * b * c == a * (b * c)], {
    TypeTheoryTactic["Introduce", a, b, c],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Failure["NotReflexive", ...] -->
