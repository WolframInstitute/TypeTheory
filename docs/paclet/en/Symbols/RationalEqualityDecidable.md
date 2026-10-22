---
Template: Symbol
Name: RationalEqualityDecidable
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/RationalEqualityDecidable
Keywords: [rationals, decidable, decision, equation, instance, Decide]
SeeAlso: [Decidable, Decide, IntegerEqualityDecidable, DecideSoundness]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheRationals]
---

## Usage

<code>[RationalEqualityDecidable]()[*x*, *y*]</code> decides *x* == *y* for rationals *x* and *y*; it is the instance of <code>[Decidable]()[*x* == *y*]</code> in <code>[TypeTheoryEnvironment]()["Rationals"]</code>.

## Details & Options

- The decision compares a (d + 1) and c (b + 1) for the pairs (a, b) and (c, d) of the two classes with the integers' decision, lifted from pairs as the operations are, with proofs that it is `"true"` exactly where the rationals are equal.
- It is declared with `"Instance" -> True`, so [Decide]() and the tactic `"Decide"` find it, as [IntegerEqualityDecidable]() for the integers.
- It is a definition of <code>[TypeTheoryEnvironment]()["Rationals"]</code>; terms that use it name that environment.

## Basic Examples

The rationals:

```wl
rationals = TypeTheoryEnvironment["Rationals"]
```

<!-- => TypeTheoryEnvironment summary box: 323 constants -->

The decision of an equation computes:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[Typed[1/2, Rationals] == 2/4], rationals]]
```

<!-- => true -->

---

The rationals:

```wl
rationals = TypeTheoryEnvironment["Rationals"]
```

<!-- => TypeTheoryEnvironment summary box: 323 constants -->

`"Decide"` proves a closed equation:

```wl
TypeTheoryProof[Typed[1/2 + 1/3, Rationals] == 5/6, rationals, {TypeTheoryTactic["Decide"]}]
```

<!-- => Proof complete -->
