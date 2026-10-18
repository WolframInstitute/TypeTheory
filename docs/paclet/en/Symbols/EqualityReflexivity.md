---
Template: Symbol
Name: EqualityReflexivity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/EqualityReflexivity
Keywords: [equality, reflexivity, proof, constructor, computation, prelude]
SeeAlso: [EqualitySymmetry, EqualityTransitivity, EqualityCongruence, EqualitySubstitution, DefinitionallyEqualQ, TypeTheoryTactic]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[EqualityReflexivity]()[*x*]</code> proves <code>*x* == *x*</code>.

## Details & Options

- [Equal]() is an inductive family of the prelude: <code>*x* == *y*</code> for *x* and *y* of one type. [EqualityReflexivity]() is its one constructor.
- The type of *x* and its universe level are implicit arguments.
- Types are compared by computation, so <code>[EqualityReflexivity]()[*x*]</code> also proves <code>*y* == *z*</code> whenever *y* and *z* both compute to *x*. The tactic `"Reflexivity"` proves an equation this way.

## Basic Examples

The type of [EqualityReflexivity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[EqualityReflexivity]]
```

<!-- => ∀_{α ∶ Sort u} ∀_x∶α x == x -->

---

A proof of `2 + 2 == 4` by computation:

```wl
TypeTheoryCheck[TypeTheoryTerm[EqualityReflexivity[4]], TypeTheoryTerm[2 + 2 == 4]]
```

<!-- => Success["TypeChecked", ...] -->

## Scope

Types are terms too, and can be equal:

```wl
TypeTheoryCheck[TypeTheoryTerm[EqualityReflexivity[Naturals]]]
```

<!-- => ℕ == ℕ -->

---

[Construct]() gives the implicit type argument explicitly:

```wl
TypeTheoryCheck[TypeTheoryTerm[Construct[EqualityReflexivity, Naturals, 3]]]
```

<!-- => 3 == 3 -->

## Possible Issues

Computation does not make `2 + 2` equal to `5`:

```wl
TypeTheoryCheck[TypeTheoryTerm[EqualityReflexivity[4]], TypeTheoryTerm[2 + 2 == 5]]
```

<!-- => Failure["TypeMismatch", ...] -->
