---
Template: Symbol
Name: FunctionExtensionality
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/FunctionExtensionality
Keywords: [function extensionality, axiom, functions, equality, prelude, classical logic]
SeeAlso: [PropositionalExtensionality, EqualityCongruence, Choice, DefinitionallyEqualQ]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[FunctionExtensionality]()[*h*]</code> proves <code>*f* == *g*</code> from a proof *h* that <code>*f*[*x*] == *g*[*x*]</code> for every *x*.

## Details & Options

- [FunctionExtensionality]() is one of the three axioms of the prelude. Lean proves it from quotients, which the kernel does not have.
- *f* and *g* may be dependent functions. Their domain, their codomain, *f* and *g* are implicit arguments, found from the type of *h*.
- The constructive environment, <code>[TypeTheoryEnvironment]()["Constructive"]</code>, does not have it.

## Basic Examples

The statement of [FunctionExtensionality]():

```wl
TypeTheoryCheck[TypeTheoryTerm[FunctionExtensionality]]
```

<!-- => ∀_{α ∶ Sort u} ∀_{β ∶ α → Sort v} ∀_{f ∶ ∀_x∶α β[x]} ∀_{g ∶ ∀_x∶α β[x]} (∀_x∶α f[x] == g[x]) ⇒ f == g -->

---

Adding 0 on the left is the identity function:

```wl
TypeTheoryCheck[TypeTheoryTerm[FunctionExtensionality[AdditionZeroLeft]]]
```

<!-- => ((n∶ℕ) ↦ 0 + n) == ((n∶ℕ) ↦ n) -->

## Properties and Relations

The two functions are not equal by computation, since `0 + n` does not compute for a variable `n`:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]}, 0 + n]], TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]}, n]]]
```

<!-- => False -->
