---
Template: Symbol
Name: RationalMultiplicationAssociativity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/RationalMultiplicationAssociativity
Keywords: [rationals, multiplication, associativity, theorem, Lean]
SeeAlso: [RationalMultiplicationCommutativity, RationalAdditionAssociativity, IntegerMultiplicationAssociativity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheRationals]
---

## Usage

<code>[RationalMultiplicationAssociativity]()[*x*, *y*, *z*]</code> proves <code>(*x* *y*) *z* == *x* (*y* *z*)</code> for rationals *x*, *y* and *z*.

## Details & Options

- [RationalMultiplicationAssociativity]() is a theorem of <code>[TypeTheoryEnvironment]()["Rationals"]</code>, the environment of the integers with the rationals.
- It is a law of the rationals as a commutative ring, as Lean's `Rat.mul_assoc`.
- It is proved by `"Induction"` on each rational, a class of pairs of an integer and a natural number, [QuotientSoundness](), which leaves an equation of integers of the pairs, and `"Ring"`, which proves it.

## Basic Examples

The statement of [RationalMultiplicationAssociativity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalMultiplicationAssociativity, TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_x∶ℚ ∀_y∶ℚ ∀_z∶ℚ x y z == x (y z) -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalMultiplicationAssociativity[2, 3, 5], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => 2 3 5 == 2 (3 5) -->

## Scope

An instance with an integer, coerced to a rational:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[a, Integers], Typed[x, Rationals]}, RationalMultiplicationAssociativity[a, x, x]], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_a∶ℤ ∀_x∶ℚ ↑a x x == ↑a (x x) -->

## Applications

`"Rewrite"` regroups a coefficient with the rest of a product:

```wl
TypeTheoryProof[ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, (2 x) y == 2 (x y)], TypeTheoryEnvironment["Rationals"], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Rewrite", RationalMultiplicationAssociativity]
}]
```

<!-- => Proof complete -->

## Properties and Relations

An instance of literals is decided by `"Decide"`, since [RationalEqualityDecidable]() decides equations of rationals:

```wl
TypeTheoryProof[Typed[(1/2 2/3) 3/4, Rationals] == 1/2 (2/3 3/4), TypeTheoryEnvironment["Rationals"], {TypeTheoryTactic["Decide"]}]
```

<!-- => Proof complete -->

## Possible Issues

For rational variables the two sides are not equal by computation, so `"Reflexivity"` does not prove the law:

```wl
TypeTheoryProof[ForAll[{Typed[x, Rationals], Typed[y, Rationals], Typed[z, Rationals]}, (x y) z == x (y z)], TypeTheoryEnvironment["Rationals"], {
    TypeTheoryTactic["Introduce", x, y, z],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Failure["NotReflexive", ...] -->
