---
Template: Symbol
Name: DoubleNegationElimination
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/DoubleNegationElimination
Keywords: [double negation, classical logic, negation, prelude]
SeeAlso: [ExcludedMiddle, Not, FalseElimination]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[DoubleNegationElimination]()[*p*]</code> proves <code>[Implies]()[[Not]()[[Not]()[*p*]], *p*]</code>.

## Details & Options

- [DoubleNegationElimination]() is a theorem of the prelude, proved by cases on <code>[ExcludedMiddle]()[*p*]</code>.
- Its argument *p* is explicit.
- The constructive environment, <code>[TypeTheoryEnvironment]()["Constructive"]</code>, does not have it.

## Basic Examples

The statement of [DoubleNegationElimination]():

```wl
TypeTheoryCheck[TypeTheoryTerm[DoubleNegationElimination]]
```

<!-- => ∀_p∶Prop (¬¬p) ⇒ p -->

---

From the double negation of `1 == 1`, `1 == 1`:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[h, Not[Not[1 == 1]]]}, DoubleNegationElimination[1 == 1][h]]]]
```

<!-- => (¬¬1 == 1) ⇒ 1 == 1 -->
