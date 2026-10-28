---
Template: TechNote
Name: TheRationals
Title: The Rationals
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/tutorial/TheRationals
Keywords: [rationals, quotient, quotient type, field, inverse, division, coercion, Ring, Decide, PolynomialReduce, Lean]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheIntegers, ThePrelude, InstancesAndCoercions]
---

<code>[TypeTheoryEnvironment]()["Rationals"]</code> is the environment of the integers with the rationals, built and checked the first time it is asked for. A rational there is a class of pairs of an integer and a natural number: (a, b) stands for a / (b + 1), and (a, b) and (c, d) are the same rational when a (d + 1) == c (b + 1). The denominator b + 1 is never 0, so every pair stands for a rational. It is a quotient type over the integers, as the integers are one over the natural numbers; Lean's `Rat` is a structure of a numerator and a denominator in lowest terms instead. The operations are lifted from pairs, and the laws of a field are proved by TypeTheory's own tactics, then checked by the kernel.

## The Rationals as a Quotient

The environment, the integers with the rationals:

```wl
rationals = TypeTheoryEnvironment["Rationals"]
```

<!-- => TypeTheoryEnvironment summary box: 323 constants -->

[Rationals]() is the quotient of pairs by a relation, and shows as ℚ:

```wl
rationals[Rationals]
```

<!-- => definition ℚ : Type := QuotientType[rationalRelation] -->

The relation, an equation of integers:

```wl
rationals["rationalRelation"]
```

<!-- => definition rationalRelation : CartesianProductType[ℤ, ℕ] → CartesianProductType[ℤ, ℕ] → Prop := (p ∶ CartesianProductType[ℤ, ℕ]) (q ∶ CartesianProductType[ℤ, ℕ]) ↦ p〚1〛 ↑(q〚2〛 + 1) == q〚1〛 ↑(p〚2〛 + 1) -->

An integer x is the class of (x, 0), the fraction x/1, which shows as x, and the function that takes it there is a coercion, inserted where an integer, or a natural number by way of the integers, stands for a rational:

```wl
rationals["rationalOfInteger"]
```

<!-- => coercion rationalOfInteger : ℤ → ℚ := (x ∶ ℤ) ↦ x -->

## Arithmetic

In this environment `+`, `*`, `-`, `/`, `^`, `x^-1` and the comparisons are the rationals' wherever the types say so, and those of the integers or the natural numbers otherwise:

```wl
TypeTheoryTerm[Function[{Typed[x, Rationals], Typed[n, Naturals]}, x / 2 + n <= x^2], rationals]
```

<!-- => (x ∶ ℚ) (n ∶ ℕ) ↦ x/2 + n ≤ x^2 -->

Its type; the natural number `n` is coerced to a rational where it is added to one:

```wl
TypeOf[TypeTheoryTerm[Function[{Typed[x, Rationals], Typed[n, Naturals]}, x / 2 + n <= x^2], rationals]]
```

<!-- => ℚ → ℕ → Prop -->

A fraction of literals is a rational where one is expected:

```wl
TypeOf[TypeTheoryTerm[Typed[-3/4, Rationals], rationals]]
```

<!-- => ℚ -->

## Equations of Rationals

Two pairs of the same ratio are two representatives of one rational. They are not equal by computation:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Typed[1/2, Rationals], rationals], TypeTheoryTerm[Typed[2/4, Rationals], rationals]]
```

<!-- => False -->

[RationalEqualityDecidable]() decides equations of rationals by comparing a (d + 1) and c (b + 1), so `"Decide"` proves them:

```wl
TypeTheoryProof[Typed[1/2, Rationals] == 2/4, rationals, {TypeTheoryTactic["Decide"]}]
```

<!-- => Proof complete -->

---

Sums, products and inverses of literals compute, and are decided:

```wl
TypeTheoryProof[Typed[1/2 + 1/3, Rationals] == 5/6, rationals, {TypeTheoryTactic["Decide"]}]
```

<!-- => Proof complete -->

A false equation is decided false:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[Typed[1/2, Rationals] == 1/3], rationals]]
```

<!-- => false -->

## The Laws

The laws of a commutative ring are theorems, such as [RationalDistributivity]():

```wl
rationals[RationalDistributivity]
```

<!-- => theorem RationalDistributivity : ∀_x∶ℚ ∀_y∶ℚ ∀_z∶ℚ x (y + z) == x y + x z -->

`"Ring"` proves identities of rationals: `"Induction"` on each rational gives the class of a pair, [QuotientSoundness]() the relation of two pairs, an equation of integers, which `"Ring"` proves by the integers' normal forms. That equation multiplies each side by the other's denominator, so its degree, and the time `"Ring"` takes, grows with the denominators of the two sides:

```wl
TypeTheoryProof[ForAll[{Typed[x, Rationals]}, (x + 1) (x - 1) == x^2 - 1], rationals, {
    TypeTheoryTactic["Introduce", x],
    TypeTheoryTactic["Ring"]
}]
```

<!-- => Proof complete -->

Fractions of literals are classes of pairs too:

```wl
TypeTheoryProof[ForAll[{Typed[x, Rationals]}, x / 2 + x / 3 == 5 x / 6], rationals, {
    TypeTheoryTactic["Introduce", x],
    TypeTheoryTactic["Ring"]
}]
```

<!-- => Proof complete -->

## The Inverse

[RationalMultiplicationInverse]() makes the rationals a field:

```wl
rationals[RationalMultiplicationInverse]
```

<!-- => theorem RationalMultiplicationInverse : ∀_x∶ℚ (¬x == 0) ⇒ x/x == 1 -->

The inverse computes. For the class of (a, b) it is the class of (b + 1, |a| - 1) with the sign of a, found by recursion on the pair of natural numbers of the integer a, and the inverse of 0 is 0, [RationalInverseZero]():

```wl
TypeTheoryProof[Typed[(2/3)^-1, Rationals] == 3/2, rationals, {TypeTheoryTactic["Decide"]}]
```

<!-- => Proof complete -->

## Order

`x <= y` means that `y` is `x` plus n / (d + 1) for natural numbers n and d. A square is at least 0, [RationalSquareNonnegative]():

```wl
rationals[RationalSquareNonnegative]
```

<!-- => theorem RationalSquareNonnegative : ∀_x∶ℚ 0 ≤ x x -->
