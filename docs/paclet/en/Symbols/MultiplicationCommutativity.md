---
Template: Symbol
Name: MultiplicationCommutativity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MultiplicationCommutativity
Keywords: [multiplication, commutativity, prelude, natural numbers]
SeeAlso: [MultiplicationAssociativity, AdditionCommutativity, MultiplicationDistributivityRight]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[MultiplicationCommutativity]()[*m*, *n*]</code> proves <code>*m* * *n* == *n* * *m*</code>.

## Details & Options

- [MultiplicationCommutativity]() is a theorem of the prelude, proved by induction on *n* from [MultiplicationZeroLeft]() and [MultiplicationSuccessorLeft]().

## Basic Examples

The statement of [MultiplicationCommutativity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationCommutativity]]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ m n == n m -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationCommutativity[3, 4]]]
```

<!-- => 3 × 4 == 4 × 3 -->

## Scope

The tactic `"Rewrite"` swaps the factors of a product inside a goal, and the goal closes:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, x * y + 1 == y * x + 1], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Rewrite", MultiplicationCommutativity[x, y]]
}]
```

<!-- => Proof complete -->

## Applications

[MultiplicationMonotonicity]() multiplies an inequality on the right, and with commutativity it multiplies on the left:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, Implies[x <= y, 3 x <= 3 y]], {
    TypeTheoryTactic["Introduce", x, y, h],
    TypeTheoryTactic["Rewrite", MultiplicationCommutativity[3, x]],
    TypeTheoryTactic["Rewrite", MultiplicationCommutativity[3, y]],
    TypeTheoryTactic["Exact", MultiplicationMonotonicity[3, h]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

The integers have the same law, [IntegerMultiplicationCommutativity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerMultiplicationCommutativity, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ ∀_y∶ℤ x y == y x -->

## Possible Issues

`x * 2` computes to `0 + x + x`, but `2 * x` does not compute, so `"Reflexivity"` does not prove that they are equal:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals]}, x * 2 == 2 * x], {
    TypeTheoryTactic["Introduce", x],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Failure["NotReflexive", ...] -->
