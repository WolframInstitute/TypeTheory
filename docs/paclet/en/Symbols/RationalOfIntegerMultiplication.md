---
Template: Symbol
Name: RationalOfIntegerMultiplication
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/RationalOfIntegerMultiplication
Keywords: [rationals, integers, coercion, multiplication, theorem, Lean]
SeeAlso: [RationalOfIntegerAddition, IntegerOfNaturalMultiplication]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheRationals]
---

## Usage

<code>[RationalOfIntegerMultiplication]()[*a*, *b*]</code> proves that the rational of <code>*a* *b*</code> is the product of the rationals of the integers *a* and *b*.

## Details & Options

- [RationalOfIntegerMultiplication]() is a theorem of <code>[TypeTheoryEnvironment]()["Rationals"]</code>, the environment of the integers with the rationals.
- The integers are rationals by the coercion `"rationalOfInteger"`, which shows as `↑`; the law says it keeps their products, as Mathlib's `Int.cast_mul`.
- It is proved by [QuotientSoundness]() and `"Ring"`.

## Basic Examples

The statement of [RationalOfIntegerMultiplication]():

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalOfIntegerMultiplication, TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_a∶ℤ ∀_b∶ℤ ↑(a b) == ↑a ↑b -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalOfIntegerMultiplication[2, -5], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ↑(2 (-5)) == 2 (-5) -->

## Scope

An instance with a variable:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[a, Integers]}, RationalOfIntegerMultiplication[a, a]], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_a∶ℤ ↑(a a) == ↑a ↑a -->

## Applications

`"Rewrite"` with the law turns the rational of a product into a product of rationals, here a square, which [RationalSquareNonnegative]() bounds:

```wl
TypeTheoryProof[ForAll[{Typed[a, Integers]}, 0 <= "rationalOfInteger"[a a]], TypeTheoryEnvironment["Rationals"], {
    TypeTheoryTactic["Introduce", a],
    TypeTheoryTactic["Rewrite", RationalOfIntegerMultiplication],
    TypeTheoryTactic["Exact", RationalSquareNonnegative[a]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

The laws of the integers apply inside the coercion, such as [IntegerMultiplicationCommutativity]():

```wl
TypeTheoryProof[ForAll[{Typed[a, Integers], Typed[b, Integers]}, "rationalOfInteger"[a b] == "rationalOfInteger"[b a]], TypeTheoryEnvironment["Rationals"], {
    TypeTheoryTactic["Introduce", a, b],
    TypeTheoryTactic["Rewrite", IntegerMultiplicationCommutativity[a, b]]
}]
```

<!-- => Proof complete -->

## Possible Issues

`Typed[a b, Rationals]` is the product of the rationals of `a` and `b`, not the rational of their product, which is written with the coercion `"rationalOfInteger"`:

```wl
TypeTheoryProof[ForAll[{Typed[a, Integers], Typed[b, Integers]}, Typed[a b, Rationals] == a b], TypeTheoryEnvironment["Rationals"]]
```

<!-- => Proof, 1 goal: ⊢ ∀_a∶ℤ ∀_b∶ℤ ↑a ↑b == ↑a ↑b -->
