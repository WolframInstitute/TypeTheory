---
Template: Symbol
Name: SubtypeIntroduction
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/SubtypeIntroduction
Keywords: [subtype, introduction, element, property, prelude, classical logic]
SeeAlso: [Subtype, ExistsIntroduction, NonemptyIntroduction]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[SubtypeIntroduction]()[*x*, *h*]</code> is the element *x* of <code>[Subtype]()[*P*]</code>, with a proof *h* of <code>*P*[*x*]</code>.

## Details & Options

- [SubtypeIntroduction]() is the constructor of [Subtype]().
- The type of *x* and the property *P* are implicit arguments. *P* is found from the expected type: the type of *h* alone does not say which property it is.

## Basic Examples

The statement of [SubtypeIntroduction]():

```wl
TypeTheoryCheck[TypeTheoryTerm[SubtypeIntroduction]]
```

<!-- => ∀_{α ∶ Sort u} ∀_{P ∶ α → Prop} ∀_x∶α P[x] → Subtype[P] -->

---

4 is a natural number of at least 2:

```wl
TypeTheoryCheck[TypeTheoryTerm[SubtypeIntroduction[4, LessEqualStep[LessEqualStep[LessEqualReflexivity]]]], TypeTheoryTerm[Subtype[Function[{Typed[n, NonNegativeIntegers]}, 2 <= n]]]]
```

<!-- => True -->
