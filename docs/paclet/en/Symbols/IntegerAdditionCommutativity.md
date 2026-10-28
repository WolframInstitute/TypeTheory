---
Template: Symbol
Name: IntegerAdditionCommutativity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntegerAdditionCommutativity
Keywords: [integers, addition, commutativity, theorem, Lean]
SeeAlso: [IntegerAdditionAssociativity, IntegerMultiplicationCommutativity, AdditionCommutativity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheIntegers]
---

## Usage

<code>[IntegerAdditionCommutativity]()[*x*, *y*]</code> proves <code>*x* + *y* == *y* + *x*</code> for integers *x* and *y*.

## Details & Options

- [IntegerAdditionCommutativity]() is a theorem of <code>[TypeTheoryEnvironment]()["Integers"]</code>, the prelude with the integers.
- It is a law of the integers as a commutative ring, as Lean's `Int.add_comm`.
- It is proved by `"Induction"` on each integer, a class of pairs of natural numbers, [QuotientSoundness](), which leaves an equation of the pairs, and `"Ring"`, which proves it.

## Basic Examples

The statement of [IntegerAdditionCommutativity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerAdditionCommutativity, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ ∀_y∶ℤ x + y == y + x -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerAdditionCommutativity[-2, 5], TypeTheoryEnvironment["Integers"]]]
```

<!-- => -2 + 5 == 5 + -2 -->

## Scope

The law holds for any integer terms, here `a` and `2 b`:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[a, Integers], Typed[b, Integers]}, IntegerAdditionCommutativity[a, 2 b]], TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_a∶ℤ ∀_b∶ℤ a + 2 b == 2 b + a -->

## Applications

`"Rewrite"` with an instance swaps two terms inside a larger sum:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers], Typed[z, Integers]}, (x + y) + z == (y + x) + z], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, y, z],
    TypeTheoryTactic["Rewrite", IntegerAdditionCommutativity[x, y]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

An instance of literals is decided by `"Decide"`, since [IntegerEqualityDecidable]() decides equations of integers:

```wl
TypeTheoryProof[Typed[-2 + 5, Integers] == 5 + -2, TypeTheoryEnvironment["Integers"], {TypeTheoryTactic["Decide"]}]
```

<!-- => Proof complete -->

## Possible Issues

On natural numbers the law states an equation of their integers, so it does not prove `m + n == n + m` of the natural numbers themselves:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals], Typed[n, Naturals]}, m + n == n + m], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", m, n],
    TypeTheoryTactic["Exact", IntegerAdditionCommutativity[m, n]]
}]
```

<!-- => Failure["TypeMismatch", ...] -->

The prelude's [AdditionCommutativity]() proves it:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals], Typed[n, Naturals]}, m + n == n + m], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", m, n],
    TypeTheoryTactic["Exact", AdditionCommutativity[m, n]]
}]
```

<!-- => Proof complete -->
