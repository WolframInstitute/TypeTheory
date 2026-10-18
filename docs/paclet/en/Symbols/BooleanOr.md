---
Template: Symbol
Name: BooleanOr
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/BooleanOr
Keywords: [Boolean, disjunction, or, Booleans, prelude]
SeeAlso: [BooleanAnd, BooleanNot, BooleanTrue, BooleanFalse, Or]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[BooleanOr]()[*a*, *b*]</code> is the disjunction of the Booleans *a* and *b*.

## Details & Options

- [BooleanOr]() is a definition of the prelude, by cases on *a*: <code>[BooleanOr]()[[BooleanFalse](), *b*]</code> is *b*, and <code>[BooleanOr]()[[BooleanTrue](), *b*]</code> is [BooleanTrue](), as with Lean's `Bool`.
- <code>[Or]()[*a*, *b*]</code> and `a || b` stand for it when *a* and *b* are Booleans. `a || b || c` is `(a || b) || c` for Booleans, as in Lean, and `a || (b || c)` for propositions.
- It shows as `a || b`.

## Basic Examples

The type of [BooleanOr]():

```wl
TypeTheoryCheck[TypeTheoryTerm[BooleanOr]]
```

<!-- => 𝔹 → 𝔹 → 𝔹 -->

---

False or true:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Typed[False || True, Booleans]]]
```

<!-- => true -->
