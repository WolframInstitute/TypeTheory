---
Template: Symbol
Name: QuotientIntroduction
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/QuotientIntroduction
Keywords: [quotient, equivalence class, Quot.mk, Lean, prelude]
SeeAlso: [QuotientType, QuotientLift, QuotientSoundness, TypeTheoryQuotients]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude, RulesAndComputation]
---

## Usage

<code>[QuotientIntroduction]()[*r*, *a*]</code> is the class of *a* in <code>[QuotientType]()[*r*]</code>.

## Details & Options

- [QuotientIntroduction]() is a constant of the kernel, declared by [TypeTheoryQuotients]() in the prelude, as Lean's `Quot.mk`.
- The type α of *a* is an implicit argument.
- The classes of two elements that *r* relates are equal by [QuotientSoundness](), not by computation.

## Basic Examples

The type of [QuotientIntroduction]():

```wl
TypeTheoryCheck[TypeTheoryTerm[QuotientIntroduction]]
```

<!-- => ∀_{α ∶ Sort u} ∀_r∶α → α → Prop α → QuotientType[r] -->

---

The class of the pair (2, 5), the integer -3:

```wl
differences = TypeTheoryEnvironment[{
    TypeTheoryDefinition[SameDifference, Function[{Typed[p, CartesianProductType[Naturals, Naturals]], Typed[q, CartesianProductType[Naturals, Naturals]]}, p[[1]] + q[[2]] == q[[1]] + p[[2]]]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

```wl
TypeTheoryCheck[TypeTheoryTerm[QuotientIntroduction[SameDifference, Pair[2, 5]], differences]]
```

<!-- => QuotientType[SameDifference] -->

## Properties and Relations

The pairs with the same difference again:

```wl
differences = TypeTheoryEnvironment[{
    TypeTheoryDefinition[SameDifference, Function[{Typed[p, CartesianProductType[Naturals, Naturals]], Typed[q, CartesianProductType[Naturals, Naturals]]}, p[[1]] + q[[2]] == q[[1]] + p[[2]]]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

The classes of (2, 5) and (3, 6) are equal by [QuotientSoundness](), since 2 + 6 and 3 + 5 compute to 8:

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed[QuotientSoundness[EqualityReflexivity[8]], QuotientIntroduction[SameDifference, Pair[2, 5]] == QuotientIntroduction[SameDifference, Pair[3, 6]]], differences]]
```

<!-- => QuotientIntroduction[SameDifference, (2, 5)] == QuotientIntroduction[SameDifference, (3, 6)] -->

They are not equal by computation:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[QuotientIntroduction[SameDifference, Pair[2, 5]], differences], TypeTheoryTerm[QuotientIntroduction[SameDifference, Pair[3, 6]], differences]]
```

<!-- => False -->
