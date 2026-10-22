---
Template: Symbol
Name: IntegerEqualityDecidable
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntegerEqualityDecidable
Keywords: [integers, decidable, decision, equation, instance, Decide]
SeeAlso: [Decidable, Decide, NaturalNumberEqualityDecidable, DecideSoundness]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheIntegers]
---

## Usage

<code>[IntegerEqualityDecidable]()[*x*, *y*]</code> decides *x* == *y* for integers *x* and *y*; it is the instance of <code>[Decidable]()[*x* == *y*]</code> in <code>[TypeTheoryEnvironment]()["Integers"]</code>.

## Details & Options

- The decision is the Boolean comparison of a + d and c + b for the pairs (a, b) and (c, d) of the two classes, lifted from pairs as the operations are, with proofs that it is `"true"` exactly where the integers are equal.
- It is declared with `"Instance" -> True`, so [Decide]() and the tactic `"Decide"` find it, as [NaturalNumberEqualityDecidable]() for the natural numbers.
- It is a definition of <code>[TypeTheoryEnvironment]()["Integers"]</code>; terms that use it name that environment.

## Basic Examples

The integers:

```wl
integers = TypeTheoryEnvironment["Integers"]
```

<!-- => TypeTheoryEnvironment summary box: 230 constants -->

The decision of an equation computes:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[Typed[2 - 5, Integers] == 3], integers]]
```

<!-- => false -->

---

The integers:

```wl
integers = TypeTheoryEnvironment["Integers"]
```

<!-- => TypeTheoryEnvironment summary box: 230 constants -->

`"Decide"` proves a closed equation:

```wl
TypeTheoryProof[Typed[7 * (-3) + 21, Integers] == 0, integers, {TypeTheoryTactic["Decide"]}]
```

<!-- => Proof complete -->
