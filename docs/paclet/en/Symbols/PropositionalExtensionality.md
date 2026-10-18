---
Template: Symbol
Name: PropositionalExtensionality
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/PropositionalExtensionality
Keywords: [propositional extensionality, axiom, equivalence, equality, prelude, classical logic]
SeeAlso: [Equivalent, EquivalentIntroduction, FunctionExtensionality, Choice, ExcludedMiddle]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[PropositionalExtensionality]()[*h*]</code> proves <code>*a* == *b*</code> from a proof *h* of <code>[Equivalent]()[*a*, *b*]</code>.

## Details & Options

- [PropositionalExtensionality]() is one of the three axioms of the prelude. With it, a proposition is determined by when it holds, and equivalent propositions replace each other anywhere, by [EqualitySubstitution]().
- *a* and *b* are implicit arguments, found from the type of *h*.
- The constructive environment, <code>[TypeTheoryEnvironment]()["Constructive"]</code>, does not have it.

## Basic Examples

The statement of [PropositionalExtensionality]():

```wl
TypeTheoryCheck[TypeTheoryTerm[PropositionalExtensionality]]
```

<!-- => ∀_{a ∶ Prop} ∀_{b ∶ Prop} (a ⧦ b) ⇒ a == b -->

---

[True]() is the same proposition as [True]() and [True]():

```wl
TypeTheoryCheck[TypeTheoryTerm[PropositionalExtensionality[EquivalentIntroduction[Function[{Typed[h, True]}, AndIntroduction[h, h]], Function[{Typed[h, True && True]}, AndEliminationLeft[h]]]]]]
```

<!-- => True == (True ∧ True) -->
