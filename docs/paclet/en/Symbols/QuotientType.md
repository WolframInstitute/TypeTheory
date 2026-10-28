---
Template: Symbol
Name: QuotientType
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/QuotientType
Keywords: [quotient, quotient type, equivalence class, Quot, Lean, prelude]
SeeAlso: [QuotientIntroduction, QuotientLift, QuotientInduction, QuotientSoundness, TypeTheoryQuotients]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude, RulesAndComputation]
---

## Usage

<code>[QuotientType]()[*r*]</code> is the type of the classes of the relation *r* on a type α.

## Details & Options

- [QuotientType]() is a constant of the kernel, declared by [TypeTheoryQuotients]() in the prelude, as Lean's `Quot`.
- α is an implicit argument, found from the type of *r*, which is `α -> α -> Prop`. Any relation will do: two elements have equal classes when the equivalence relation *r* generates relates them.
- <code>[QuotientType]()[*r*]</code> lives in the universe of α.
- [QuotientIntroduction]() makes the class of an element, [QuotientLift]() takes a function on elements that respects *r* to a function on classes, [QuotientInduction]() proves a property of every class, and [QuotientSoundness]() makes the classes of related elements equal.

## Basic Examples

The type of [QuotientType]():

```wl
TypeTheoryCheck[TypeTheoryTerm[QuotientType]]
```

<!-- => ∀_{α ∶ Sort u} (α → α → Prop) → Sort u -->

---

Pairs of natural numbers with the same difference, from which the integers are made:

```wl
differences = TypeTheoryEnvironment[{
    TypeTheoryDefinition[SameDifference, Function[{Typed[p, CartesianProductType[Naturals, Naturals]], Typed[q, CartesianProductType[Naturals, Naturals]]}, p[[1]] + q[[2]] == q[[1]] + p[[2]]]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

Their quotient is a type:

```wl
TypeTheoryCheck[TypeTheoryTerm[QuotientType[SameDifference], differences]]
```

<!-- => Type -->
