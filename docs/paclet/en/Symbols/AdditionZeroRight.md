---
Template: Symbol
Name: AdditionZeroRight
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/AdditionZeroRight
Keywords: [addition, zero, right, prelude, natural numbers]
SeeAlso: [AdditionZeroLeft, AdditionCommutativity, MultiplicationOneRight]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[AdditionZeroRight]()[*n*]</code> proves <code>*n* + 0 == *n*</code>.

## Details & Options

- [AdditionZeroRight]() is a theorem of the prelude. It holds by computation, since [Plus]() recurses on its second argument: its proof is <code>[EqualityReflexivity]()[*n*]</code>.

## Basic Examples

The statement of [AdditionZeroRight]():

```wl
TypeTheoryCheck[TypeTheoryTerm[AdditionZeroRight]]
```

<!-- => ∀_n∶ℕ n + 0 == n -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[AdditionZeroRight[7]]]
```

<!-- => 7 + 0 == 7 -->

## Scope

The tactic `"Reflexivity"` proves it, since `n + 0` computes to *n*:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, n + 0 == n], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Proof complete -->

## Properties and Relations

Adding 0 on the right is the identity function by computation:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Function[{Typed[n, Naturals]}, n + 0]], TypeTheoryTerm[Function[{Typed[n, Naturals]}, n]]]
```

<!-- => True -->

---

The integers have the same law, [IntegerAdditionZero]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerAdditionZero, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ x + 0 == x -->

## Possible Issues

Adding 0 on the left does not compute away, so it needs [AdditionZeroLeft]():

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Function[{Typed[n, Naturals]}, 0 + n]], TypeTheoryTerm[Function[{Typed[n, Naturals]}, n]]]
```

<!-- => False -->
