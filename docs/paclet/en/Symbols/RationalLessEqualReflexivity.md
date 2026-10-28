---
Template: Symbol
Name: RationalLessEqualReflexivity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/RationalLessEqualReflexivity
Keywords: [rationals, order, reflexivity, theorem, Lean]
SeeAlso: [RationalAdditionZero, RationalSquareNonnegative, IntegerLessEqualReflexivity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheRationals]
---

## Usage

<code>[RationalLessEqualReflexivity]()[*x*]</code> proves <code>*x* <= *x*</code> for a rational *x*.

## Details & Options

- [RationalLessEqualReflexivity]() is a theorem of <code>[TypeTheoryEnvironment]()["Rationals"]</code>, the environment of the integers with the rationals.
- `x <= y` means that `y` is `x` plus a rational n / (d + 1) for natural numbers n and d, here 0 / 1, as Lean's `Rat.le_refl`.
- It is proved from [RationalAdditionZero]().

## Basic Examples

The statement of [RationalLessEqualReflexivity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalLessEqualReflexivity, TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_x∶ℚ x ≤ x -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalLessEqualReflexivity[-2/3], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => (-2)/3 ≤ (-2)/3 -->

## Scope

An instance with a fraction of a variable:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Rationals]}, RationalLessEqualReflexivity[x / 2]], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_x∶ℚ x/2 ≤ x/2 -->

## Applications

Once `"Rewrite"` makes the two sides the same, the law closes the goal:

```wl
TypeTheoryProof[ForAll[{Typed[x, Rationals]}, x + 0 <= x], TypeTheoryEnvironment["Rationals"], {
    TypeTheoryTactic["Introduce", x],
    TypeTheoryTactic["Rewrite", RationalAdditionZero],
    TypeTheoryTactic["Exact", RationalLessEqualReflexivity[x]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

`x <= x` unfolds to natural numbers `n` and `d` with `x == x + n / (d + 1)`, the class of the pair (n, d), and the proof gives 0 for both, with [RationalAdditionZero]():

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Rationals]}, Typed[ExistsIntroduction[0, ExistsIntroduction[0, EqualitySymmetry[RationalAdditionZero[x]]]], x <= x]], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_x∶ℚ ∃_n∶ℕ ∃_d∶ℕ x == x + rationalOfPair[(↑n, d)] -->

## Possible Issues

`"Decide"` does not prove an inequality of rationals, which has no instance of [Decidable]():

```wl
TypeTheoryProof[Typed[-2/3, Rationals] <= -2/3, TypeTheoryEnvironment["Rationals"], {TypeTheoryTactic["Decide"]}]
```

<!-- => Failure["NotDecidable", ...] -->

The law proves it:

```wl
TypeTheoryProof[Typed[-2/3, Rationals] <= -2/3, TypeTheoryEnvironment["Rationals"], {TypeTheoryTactic["Exact", RationalLessEqualReflexivity[-2/3]]}]
```

<!-- => Proof complete -->
