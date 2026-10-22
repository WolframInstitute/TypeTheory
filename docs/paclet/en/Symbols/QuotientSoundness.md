---
Template: Symbol
Name: QuotientSoundness
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/QuotientSoundness
Keywords: [quotient, soundness, Quot.sound, axiom, Lean, prelude, classical logic]
SeeAlso: [QuotientIntroduction, QuotientType, FunctionExtensionality, PropositionalExtensionality, Choice]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[QuotientSoundness]()[*h*]</code> proves <code>[QuotientIntroduction]()[*r*, *a*] == [QuotientIntroduction]()[*r*, *b*]</code> from a proof *h* of <code>*r*[*a*, *b*]</code>.

## Details & Options

- [QuotientSoundness]() is one of the three axioms of the prelude, as Lean's `Quot.sound`: the classes of related elements are equal.
- The type, the relation *r* and the elements *a* and *b* are implicit arguments, found from the type the proof is checked against.
- [FunctionExtensionality]() is proved from it, as Lean proves `funext`.
- The constructive environment, <code>[TypeTheoryEnvironment]()["Constructive"]</code>, has the quotient types but not this axiom.

## Basic Examples

The statement of [QuotientSoundness]():

```wl
TypeTheoryCheck[TypeTheoryTerm[QuotientSoundness]]
```

<!-- => ∀_{α ∶ Sort u} ∀_{r ∶ α → α → Prop} ∀_{a ∶ α} ∀_{b ∶ α} r[a, b] ⇒ QuotientIntroduction[r, a] == QuotientIntroduction[r, b] -->

---

The classes of (2, 5) and (3, 6), pairs with the same difference, are equal:

```wl
differences = TypeTheoryEnvironment[{
    TypeTheoryDefinition[SameDifference, Function[{Typed[p, CartesianProduct[Naturals, Naturals]], Typed[q, CartesianProduct[Naturals, Naturals]]}, p[[1]] + q[[2]] == q[[1]] + p[[2]]]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed[QuotientSoundness[EqualityReflexivity[8]], QuotientIntroduction[SameDifference, Pair[2, 5]] == QuotientIntroduction[SameDifference, Pair[3, 6]]], differences]]
```

<!-- => QuotientIntroduction[SameDifference, Pair[2, 5]] == QuotientIntroduction[SameDifference, Pair[3, 6]] -->

## Properties and Relations

The axioms of the prelude, Lean's three:

```wl
Information[$TypeTheoryEnvironment, "Axioms"]
```

<!-- => {PropositionalExtensionality, QuotientSoundness, Choice} -->
