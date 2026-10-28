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

## Scope

On a Boolean written out, [NegationInvolution]() computes to the constant path, in the cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

The path for `"true"`:

```wl
WeakHeadNormalForm[TypeTheoryTerm[NegationInvolution["true"], cubical]]
```

<!-- => (i ∶ Interval) ↦ true -->

---

A path's values at 0 and 1 are its ends, the double negation and the Boolean, in the cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

At 0, the double negation:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Function[{Typed[b, Booleans]}, NegationInvolution[b][0]], cubical], TypeTheoryTerm[Function[{Typed[b, Booleans]}, "not"["not"[b]]], cubical]]
```

<!-- => True -->

At 1, the Boolean itself:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Function[{Typed[b, Booleans]}, NegationInvolution[b][1]], cubical], TypeTheoryTerm[Function[{Typed[b, Booleans]}, b], cubical]]
```

<!-- => True -->

## Properties and Relations

[NegationEquivalence]() is made from it by [IsomorphismEquivalence](), with `"not"` as its own inverse, in the cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

The declaration of [NegationEquivalence]():

```wl
cubical[NegationEquivalence]
```

<!-- => definition NegationEquivalence : Equivalence[𝔹, 𝔹] := IsomorphismEquivalence[not, not, NegationInvolution, NegationInvolution] -->

## Possible Issues

The prelude does not have it, so a term that uses it names the cubical environment:

```wl
TypeTheoryCheck[TypeTheoryTerm[NegationInvolution]]
```

<!-- => Failure["ElaborationFailed", ...] -->
