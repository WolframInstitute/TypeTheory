---
Template: Symbol
Name: PowerZero
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/PowerZero
Keywords: [power, zero, prelude, natural numbers]
SeeAlso: [PowerSuccessor, PowerOne, Power]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[PowerZero]()[*m*]</code> proves <code>*m*^0 == 1</code>.

## Details & Options

- [PowerZero]() is a theorem of the prelude that holds by computation: [Power]() recurses on its second argument.

## Basic Examples

The statement of [PowerZero]():

```wl
TypeTheoryCheck[TypeTheoryTerm[PowerZero]]
```

<!-- => ∀_m∶ℕ m^0 == 1 -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[PowerZero[5]]]
```

<!-- => 5^0 == 1 -->
