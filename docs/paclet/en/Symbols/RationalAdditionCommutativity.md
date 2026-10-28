---
Template: Symbol
Name: RationalAdditionCommutativity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/RationalAdditionCommutativity
Keywords: [rationals, addition, commutativity, theorem, Lean]
SeeAlso: [RationalAdditionAssociativity, RationalMultiplicationCommutativity, IntegerAdditionCommutativity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheRationals]
---

## Usage

<code>[RationalAdditionCommutativity]()[*x*, *y*]</code> proves <code>*x* + *y* == *y* + *x*</code> for rationals *x* and *y*.

## Details & Options

- [RationalAdditionCommutativity]() is a theorem of <code>[TypeTheoryEnvironment]()["Rationals"]</code>, the environment of the integers with the rationals.
- It is a law of the rationals as a commutative ring, as Lean's `Rat.add_comm`.
- It is proved by `"Induction"` on each rational, a class of pairs of an integer and a natural number, [QuotientSoundness](), which leaves an equation of integers of the pairs, and `"Ring"`, which proves it.

## Basic Examples

The statement of [RationalAdditionCommutativity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalAdditionCommutativity, TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_x∶ℚ ∀_y∶ℚ x + y == y + x -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalAdditionCommutativity[1/2, -3], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => 1/2 + -3 == -3 + 1/2 -->

## Scope

An integer is coerced to a rational:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Rationals], Typed[a, Integers]}, RationalAdditionCommutativity[x, a]], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_x∶ℚ ∀_a∶ℤ x + ↑a == ↑a + x -->

## Applications

`"Rewrite"` with an instance swaps the terms of a sum inside a fraction:

```wl
TypeTheoryProof[ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, (x + y) / 2 == (y + x) / 2], TypeTheoryEnvironment["Rationals"], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Rewrite", RationalAdditionCommutativity[x, y]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

An instance of literals is decided by `"Decide"`, since [RationalEqualityDecidable]() decides equations of rationals:

```wl
TypeTheoryProof[Typed[1/2 + 2/3, Rationals] == 2/3 + 1/2, TypeTheoryEnvironment["Rationals"], {TypeTheoryTactic["Decide"]}]
```

<!-- => Proof complete -->

## Possible Issues

On integers the law states an equation of their rationals, so it does not prove `a + b == b + a` of the integers themselves:

```wl
TypeTheoryProof[ForAll[{Typed[a, Integers], Typed[b, Integers]}, a + b == b + a], TypeTheoryEnvironment["Rationals"], {
    TypeTheoryTactic["Introduce", a, b],
    TypeTheoryTactic["Exact", RationalAdditionCommutativity[a, b]]
}]
```

<!-- => Failure["TypeMismatch", ...] -->

[IntegerAdditionCommutativity]() proves it:

```wl
TypeTheoryProof[ForAll[{Typed[a, Integers], Typed[b, Integers]}, a + b == b + a], TypeTheoryEnvironment["Rationals"], {
    TypeTheoryTactic["Introduce", a, b],
    TypeTheoryTactic["Exact", IntegerAdditionCommutativity[a, b]]
}]
```

<!-- => Proof complete -->
