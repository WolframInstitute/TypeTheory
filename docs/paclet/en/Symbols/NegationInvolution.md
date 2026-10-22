---
Template: Symbol
Name: NegationInvolution
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/NegationInvolution
Keywords: [negation, involution, Booleans, cubical type theory]
SeeAlso: [NegationEquivalence, IsomorphismEquivalence]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[NegationInvolution]()[*b*]</code> is the path from `"not"["not"[b]]` to *b* for a Boolean *b*: the constant path, by cases on *b*.

## Details & Options

- It makes negation an isomorphism with itself, which [IsomorphismEquivalence]() turns into [NegationEquivalence]().
- It is a definition of <code>[TypeTheoryEnvironment]()["Cubical"]</code>; terms that use it name that environment.

## Basic Examples

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Its type:

```wl
TypeTheoryCheck[TypeTheoryTerm[NegationInvolution, cubical]]
```

<!-- => ∀_b∶𝔹 !!b ≡ b -->
