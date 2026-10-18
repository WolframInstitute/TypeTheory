---
Template: Symbol
Name: PowerOne
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/PowerOne
Keywords: [power, one, prelude, natural numbers]
SeeAlso: [PowerZero, PowerAddition, MultiplicationOneLeft]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[PowerOne]()[*m*]</code> proves <code>*m*^1 == *m*</code>.

## Details & Options

- [PowerOne]() is a theorem of the prelude: `m^1` computes to `1 * m`, and [MultiplicationOneLeft]() proves the rest.

## Basic Examples

The statement of [PowerOne]():

```wl
TypeTheoryCheck[TypeTheoryTerm[PowerOne]]
```

<!-- => ∀_m∶ℕ m^1 == m -->

---

For a variable:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[m, Naturals]}, PowerOne[m]]]]
```

<!-- => ∀_m∶ℕ m^1 == m -->
