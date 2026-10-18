---
Template: Symbol
Name: EquivalentReflexivity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/EquivalentReflexivity
Keywords: [equivalent, reflexivity, prelude, logic]
SeeAlso: [EquivalentSymmetry, EquivalentTransitivity, EquivalentIntroduction]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[EquivalentReflexivity]()[*a*]</code> proves <code>[Equivalent]()[*a*, *a*]</code>.

## Details & Options

- [EquivalentReflexivity]() is a theorem of the prelude; its argument *a* is explicit, as for [EqualityReflexivity]().

## Basic Examples

The statement of [EquivalentReflexivity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[EquivalentReflexivity]]
```

<!-- => ∀_a∶Prop (a ⧦ a) -->

---

Every proposition is equivalent to itself:

```wl
TypeTheoryCheck[TypeTheoryTerm[EquivalentReflexivity[1 + 1 == 2]]]
```

<!-- => 1 + 1 == 2 ⧦ 1 + 1 == 2 -->
