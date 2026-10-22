---
Template: Symbol
Name: RationalMultiplicationInverse
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/RationalMultiplicationInverse
Keywords: [rationals, inverse, reciprocal, division, field, theorem, Lean]
SeeAlso: [RationalInverseZero, RationalMultiplicationOne, RationalEqualityDecidable]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheRationals]
---

## Usage

<code>[RationalMultiplicationInverse]()[*x*, *h*]</code> proves <code>*x* *x*^-1 == 1</code> from a proof *h* of <code>[Not]()[*x* == 0]</code>, for a rational *x*.

## Details & Options

- [RationalMultiplicationInverse]() is a theorem of <code>[TypeTheoryEnvironment]()["Rationals"]</code>, the environment of the integers with the rationals. With the laws of a commutative ring it makes the rationals a field, as Lean's `Rat.mul_inv_cancel`.
- `x^-1` is `"rationalInverse"`, and `x / y` is `x y^-1`; <code>*x* *x*^-1</code> shows as <code>*x*/*x*</code>, as it does in the Wolfram Language. The inverse of the class of (a, b), standing for a / (b + 1), is the class of (b + 1, |a| - 1) with the sign of a, computed by recursion on the pair of natural numbers of the integer a; the inverse of 0 is 0, [RationalInverseZero]().
- It is proved by induction on the class of *x*: a numerator 0 makes *x* equal to 0, and otherwise the product of the class with its inverse is 1.

## Basic Examples

The statement of [RationalMultiplicationInverse]():

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalMultiplicationInverse, TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_x∶ℚ (¬x == 0) ⇒ x/x == 1 -->

---

The rationals:

```wl
rationals = TypeTheoryEnvironment["Rationals"]
```

<!-- => TypeTheoryEnvironment summary box: 323 constants -->

The inverse computes, so `"Decide"` checks an equation with one:

```wl
TypeTheoryProof[Typed[(2/3)^-1, Rationals] == 3/2, rationals, {TypeTheoryTactic["Decide"]}]
```

<!-- => Proof complete -->
