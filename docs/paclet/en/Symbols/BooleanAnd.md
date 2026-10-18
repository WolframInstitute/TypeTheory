---
Template: Symbol
Name: BooleanAnd
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/BooleanAnd
Keywords: [Boolean, conjunction, and, Booleans, prelude]
SeeAlso: [BooleanOr, BooleanNot, BooleanTrue, BooleanFalse, And]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[BooleanAnd]()[*a*, *b*]</code> is the conjunction of the Booleans *a* and *b*.

## Details & Options

- [BooleanAnd]() is a definition of the prelude, by cases on *a*: <code>[BooleanAnd]()[[BooleanFalse](), *b*]</code> is [BooleanFalse](), and <code>[BooleanAnd]()[[BooleanTrue](), *b*]</code> is *b*, as with Lean's `Bool`.
- <code>[And]()[*a*, *b*]</code> and `a && b` stand for it when *a* and *b* are Booleans. `a && b && c` is `(a && b) && c` for Booleans, as in Lean, and `a && (b && c)` for propositions.
- It shows as `a && b`.

## Basic Examples

The type of [BooleanAnd]():

```wl
TypeTheoryCheck[TypeTheoryTerm[BooleanAnd]]
```

<!-- => 𝔹 → 𝔹 → 𝔹 -->

---

True and false:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Typed[True && False, Booleans]]]
```

<!-- => false -->

## Properties and Relations

With true first, a conjunction is its second argument by computation:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Function[{Typed[b, Booleans]}, True && b]], TypeTheoryTerm[Function[{Typed[b, Booleans]}, b]]]
```

<!-- => True -->

With true second, it is not, since the cases are on the first argument:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Function[{Typed[b, Booleans]}, b && True]], TypeTheoryTerm[Function[{Typed[b, Booleans]}, b]]]
```

<!-- => False -->
