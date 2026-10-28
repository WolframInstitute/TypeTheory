---
Template: Symbol
Name: RationalMultiplicationCommutativity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/RationalMultiplicationCommutativity
Keywords: [rationals, multiplication, commutativity, theorem, Lean]
SeeAlso: [RationalMultiplicationAssociativity, RationalAdditionCommutativity, IntegerMultiplicationCommutativity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheRationals]
---

## Usage

<code>[RationalMultiplicationCommutativity]()[*x*, *y*]</code> proves <code>*x* *y* == *y* *x*</code> for rationals *x* and *y*.

## Details & Options

- [RationalMultiplicationCommutativity]() is a theorem of <code>[TypeTheoryEnvironment]()["Rationals"]</code>, the environment of the integers with the rationals.
- It is a law of the rationals as a commutative ring, as Lean's `Rat.mul_comm`.
- It is proved by `"Induction"` on each rational, a class of pairs of an integer and a natural number, [QuotientSoundness](), which leaves an equation of integers of the pairs, and `"Ring"`, which proves it.

## Basic Examples

The statement of [RationalMultiplicationCommutativity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalMultiplicationCommutativity, TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_x∶ℚ ∀_y∶ℚ x y == y x -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalMultiplicationCommutativity[2/3, 5], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => (2/3) 5 == 5 (2/3) -->

## Scope

An integer factor is coerced to a rational:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[a, Integers], Typed[x, Rationals]}, RationalMultiplicationCommutativity[a, x]], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_a∶ℤ ∀_x∶ℚ ↑a x == x ↑a -->

## Applications

With [RationalDistributivity](), which multiplies a sum on the left, the law multiplies a sum on the right:

```wl
TypeTheoryProof[ForAll[{Typed[x, Rationals], Typed[y, Rationals], Typed[z, Rationals]}, (x + y) z == x z + y z], TypeTheoryEnvironment["Rationals"], {
    TypeTheoryTactic["Introduce", x, y, z],
    TypeTheoryTactic["Rewrite", RationalMultiplicationCommutativity[x + y, z]],
    TypeTheoryTactic["Rewrite", RationalDistributivity],
    TypeTheoryTactic["Rewrite", RationalMultiplicationCommutativity[z, x]],
    TypeTheoryTactic["Rewrite", RationalMultiplicationCommutativity[z, y]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

An instance of literals is decided by `"Decide"`, since [RationalEqualityDecidable]() decides equations of rationals:

```wl
TypeTheoryProof[Typed[2/3 5, Rationals] == 5 (2/3), TypeTheoryEnvironment["Rationals"], {TypeTheoryTactic["Decide"]}]
```

<!-- => Proof complete -->

## Possible Issues

For rational variables the two sides are not equal by computation, so `"Reflexivity"` does not prove the law:

```wl
TypeTheoryProof[ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, x y == y x], TypeTheoryEnvironment["Rationals"], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Failure["NotReflexive", ...] -->
