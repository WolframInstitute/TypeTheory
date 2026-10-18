---
Template: Symbol
Name: ExcludedMiddle
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/ExcludedMiddle
Keywords: [excluded middle, classical logic, disjunction, negation, Diaconescu, prelude]
SeeAlso: [DoubleNegationElimination, PropositionalExtensionality, Choice, Or, TypeTheoryAxiom]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[ExcludedMiddle]()[*p*]</code> proves <code>[Or]()[*p*, [Not]()[*p*]]</code>.

## Details & Options

- [ExcludedMiddle]() is a theorem of the prelude, proved from its axioms by Diaconescu's argument, as Lean proves it. [Choice]() picks an *x* with <code>*x* == [True]()</code> or *p*, and a *y* with <code>*y* == [False]()</code> or *p*. If *p* holds, the two properties are equal, by [PropositionalExtensionality]() and [FunctionExtensionality](), so *x* and *y* are equal; if *x* and *y* differ, *p* does not hold.
- Its argument *p* is explicit.
- The constructive environment, <code>[TypeTheoryEnvironment]()["Constructive"]</code>, does not have it; [TypeTheoryAxiom]() can assume it there.

## Basic Examples

The statement of [ExcludedMiddle]():

```wl
TypeTheoryCheck[TypeTheoryTerm[ExcludedMiddle]]
```

<!-- => ∀_p∶Prop (p ∨ ¬p) -->

---

Whether or not 2 + 2 is 5:

```wl
TypeTheoryCheck[TypeTheoryTerm[ExcludedMiddle[2 + 2 == 5]]]
```

<!-- => 2 + 2 == 5 ∨ ¬2 + 2 == 5 -->

## Possible Issues

The constructive environment has no excluded middle:

```wl
TypeTheoryCheck[TypeTheoryTerm[ExcludedMiddle, TypeTheoryEnvironment["Constructive"]]]
```

<!-- => Failure["ElaborationFailed", ...] -->
