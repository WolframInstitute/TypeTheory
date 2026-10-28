---
Template: Symbol
Name: IntegerLessEqualReflexivity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntegerLessEqualReflexivity
Keywords: [integers, order, reflexivity, theorem, Lean]
SeeAlso: [IntegerAdditionZero, LessEqualReflexivity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheIntegers]
---

## Usage

<code>[IntegerLessEqualReflexivity]()[*x*]</code> proves <code>*x* <= *x*</code> for an integer *x*.

## Details & Options

- [IntegerLessEqualReflexivity]() is a theorem of <code>[TypeTheoryEnvironment]()["Integers"]</code>, the prelude with the integers.
- `x <= y` means that `y` is `x` plus a natural number, here 0, as Lean's `Int.le_refl`.
- It is proved from [IntegerAdditionZero]().

## Basic Examples

The statement of [IntegerLessEqualReflexivity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerLessEqualReflexivity, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ x ≤ x -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerLessEqualReflexivity[-4], TypeTheoryEnvironment["Integers"]]]
```

<!-- => -4 ≤ -4 -->

## Scope

An instance with a difference:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Integers], Typed[y, Integers]}, IntegerLessEqualReflexivity[x - y]], TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ ∀_y∶ℤ x - y ≤ x - y -->

## Applications

Once `"Rewrite"` makes the two sides the same, the law closes the goal:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers]}, x + 0 <= x], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x],
    TypeTheoryTactic["Rewrite", IntegerAdditionZero],
    TypeTheoryTactic["Exact", IntegerLessEqualReflexivity[x]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

`x <= x` unfolds to a natural number `n` with `x == x + n`, and the proof gives 0 for `n`, with [IntegerAdditionZero]():

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Integers]}, Typed[ExistsIntroduction[0, EqualitySymmetry[IntegerAdditionZero[x]]], x <= x]], TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ ∃_n∶ℕ x == x + ↑n -->

## Possible Issues

`"Decide"` does not prove an inequality of integers, which has no instance of [Decidable]():

```wl
TypeTheoryProof[Typed[-4, Integers] <= -4, TypeTheoryEnvironment["Integers"], {TypeTheoryTactic["Decide"]}]
```

<!-- => Failure["NotDecidable", ...] -->

The law proves it:

```wl
TypeTheoryProof[Typed[-4, Integers] <= -4, TypeTheoryEnvironment["Integers"], {TypeTheoryTactic["Exact", IntegerLessEqualReflexivity[-4]]}]
```

<!-- => Proof complete -->
