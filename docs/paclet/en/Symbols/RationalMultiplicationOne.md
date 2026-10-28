---
Template: Symbol
Name: RationalMultiplicationOne
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/RationalMultiplicationOne
Keywords: [rationals, multiplication, one, identity, theorem, Lean]
SeeAlso: [RationalAdditionZero, RationalMultiplicationInverse, IntegerMultiplicationOne]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheRationals]
---

## Usage

<code>[RationalMultiplicationOne]()[*x*]</code> proves <code>*x* * 1 == *x*</code> for a rational *x*.

## Details & Options

- [RationalMultiplicationOne]() is a theorem of <code>[TypeTheoryEnvironment]()["Rationals"]</code>, the environment of the integers with the rationals.
- It is a law of the rationals as a commutative ring, as Lean's `Rat.mul_one`.
- It is proved by `"Induction"` on each rational, a class of pairs of an integer and a natural number, [QuotientSoundness](), which leaves an equation of integers of the pairs, and `"Ring"`, which proves it.

## Basic Examples

The statement of [RationalMultiplicationOne]():

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalMultiplicationOne, TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_x∶ℚ x 1 == x -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalMultiplicationOne[7], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => 7 1 == 7 -->

## Scope

An instance with a sum:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Rationals], Typed[y, Rationals]}, RationalMultiplicationOne[x + y]], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_x∶ℚ ∀_y∶ℚ (x + y) 1 == x + y -->

## Applications

One on the left follows with [RationalMultiplicationCommutativity]():

```wl
TypeTheoryProof[ForAll[{Typed[x, Rationals]}, 1 x == x], TypeTheoryEnvironment["Rationals"], {
    TypeTheoryTactic["Introduce", x],
    TypeTheoryTactic["Rewrite", RationalMultiplicationCommutativity],
    TypeTheoryTactic["Exact", RationalMultiplicationOne[x]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

An instance of literals is decided by `"Decide"`, since [RationalEqualityDecidable]() decides equations of rationals:

```wl
TypeTheoryProof[Typed[3/4 1, Rationals] == 3/4, TypeTheoryEnvironment["Rationals"], {TypeTheoryTactic["Decide"]}]
```

<!-- => Proof complete -->

## Possible Issues

For a rational variable `x 1 == x` does not hold by computation, so `"Reflexivity"` does not prove it:

```wl
TypeTheoryProof[ForAll[{Typed[x, Rationals]}, x 1 == x], TypeTheoryEnvironment["Rationals"], {
    TypeTheoryTactic["Introduce", x],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Failure["NotReflexive", ...] -->
