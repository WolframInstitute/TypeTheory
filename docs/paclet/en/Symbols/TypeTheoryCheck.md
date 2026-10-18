---
Template: Symbol
Name: TypeTheoryCheck
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryCheck
Keywords: [type checking, kernel, type inference, environment, replay, trust, proof checking]
SeeAlso: [TypeTheoryTerm, TypeTheoryEnvironment, DefinitionallyEqualQ, WeakHeadNormalForm, TypeTheoryTheorem]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[TypeTheoryCheck]()[*term*]</code> gives the type of the [TypeTheoryTerm]() *term* in its environment, or a [Failure]() if it does not type-check.

<code>[TypeTheoryCheck]()[*term*, *type*]</code> gives [True]() if *term* has the given *type*, and a [Failure]() otherwise.

<code>[TypeTheoryCheck]()[*env*]</code> checks every declaration of the [TypeTheoryEnvironment]() *env* again from scratch and gives [True](), or a [Failure]() for the first declaration that does not check.

## Details & Options

- <code>[TypeTheoryCheck]()[*term*]</code> is [TypeOf]() without holding its argument.
- A constant on its own has its declared type, with its implicit arguments and universe parameters.
- In <code>[TypeTheoryCheck]()[*term*, *type*]</code>, a term or type without an environment takes the other's, and both without one are in the prelude.
- An environment's store could be changed by hand. <code>[TypeTheoryCheck]()[*env*]</code> replays every declaration on an empty environment and compares each record with the one the replay produces, which catches a forged theorem or recursor. Axioms are taken on trust.

## Basic Examples

The type of a term:

```wl
TypeTheoryCheck[TypeTheoryTerm[EqualityReflexivity[4]]]
```

<!-- => 4 == 4 -->

---

A proof of `2 + 2 == 4` by computation:

```wl
TypeTheoryCheck[TypeTheoryTerm[EqualityReflexivity[4]], TypeTheoryTerm[2 + 2 == 4]]
```

<!-- => True -->

## Scope

Check an environment again from scratch, the prelude's declarations included:

```wl
TypeTheoryCheck[TypeTheoryEnvironment[{TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, EqualityReflexivity[4]]}]]
```

<!-- => True -->

---

The declared type of a constant:

```wl
TypeTheoryCheck[TypeTheoryTerm[AndIntroduction]]
```

<!-- => ∀_{a ∶ Prop} ∀_{b ∶ Prop} a ⇒ b ⇒ (a ∧ b) -->

## Possible Issues

A term against a type it does not have:

```wl
TypeTheoryCheck[TypeTheoryTerm[EqualityReflexivity[4]], TypeTheoryTerm[2 + 2 == 5]]
```

<!-- => Failure["TypeMismatch", ...] -->
