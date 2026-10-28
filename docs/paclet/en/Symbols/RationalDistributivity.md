---
Template: Symbol
Name: RationalDistributivity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/RationalDistributivity
Keywords: [rationals, multiplication, addition, distributivity, theorem, Lean]
SeeAlso: [RationalMultiplicationCommutativity, RationalAdditionAssociativity, IntegerDistributivity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheRationals]
---

## Usage

<code>[RationalDistributivity]()[*x*, *y*, *z*]</code> proves <code>*x* (*y* + *z*) == *x* *y* + *x* *z*</code> for rationals *x*, *y* and *z*.

## Details & Options

- [RationalDistributivity]() is a theorem of <code>[TypeTheoryEnvironment]()["Rationals"]</code>, the environment of the integers with the rationals.
- It is a law of the rationals as a commutative ring, as Lean's `Rat.mul_add`.
- It is proved by `"Induction"` on each rational, a class of pairs of an integer and a natural number, [QuotientSoundness](), which leaves an equation of integers of the pairs, and `"Ring"`, which proves it.

## Basic Examples

The statement of [RationalDistributivity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalDistributivity, TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_x∶ℚ ∀_y∶ℚ ∀_z∶ℚ x (y + z) == x y + x z -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalDistributivity[2, 3, 5], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => 2 (3 + 5) == 2 3 + 2 5 -->

## Scope

With `1/2` as the factor, the law halves a sum:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Rationals], Typed[y, Rationals]}, RationalDistributivity[1/2, x, y]], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_x∶ℚ ∀_y∶ℚ (1/2) (x + y) == (1/2) x + (1/2) y -->

## Applications

With [RationalMultiplicationOne](), `"Rewrite"` multiplies out `x (y + 1)`:

```wl
TypeTheoryProof[ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, x (y + 1) == x y + x], TypeTheoryEnvironment["Rationals"], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Rewrite", RationalDistributivity],
    TypeTheoryTactic["Rewrite", RationalMultiplicationOne]
}]
```

<!-- => Proof complete -->

## Properties and Relations

`"Ring"` multiplies out products of sums with fractions:

```wl
TypeTheoryProof[ForAll[{Typed[x, Rationals]}, (x + 1/2) (x - 1/2) == x^2 - 1/4], TypeTheoryEnvironment["Rationals"], {
    TypeTheoryTactic["Introduce", x],
    TypeTheoryTactic["Ring"]
}]
```

<!-- => Proof complete -->

## Possible Issues

The law multiplies a sum on the left, so `"Exact"` with it does not prove `(x + y) z == x z + y z`:

```wl
TypeTheoryProof[ForAll[{Typed[x, Rationals], Typed[y, Rationals], Typed[z, Rationals]}, (x + y) z == x z + y z], TypeTheoryEnvironment["Rationals"], {
    TypeTheoryTactic["Introduce", x, y, z],
    TypeTheoryTactic["Exact", RationalDistributivity[z, x, y]]
}]
```

<!-- => Failure["TypeMismatch", ...] -->

`"Ring"` proves it:

```wl
TypeTheoryProof[ForAll[{Typed[x, Rationals], Typed[y, Rationals], Typed[z, Rationals]}, (x + y) z == x z + y z], TypeTheoryEnvironment["Rationals"], {
    TypeTheoryTactic["Introduce", x, y, z],
    TypeTheoryTactic["Ring"]
}]
```

<!-- => Proof complete -->
