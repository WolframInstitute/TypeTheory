---
Template: Symbol
Name: OrIntroductionRight
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/OrIntroductionRight
Keywords: [Or, disjunction, proof, constructor, prelude, logic]
SeeAlso: [OrIntroductionLeft, AndIntroduction, TypeTheoryCheck]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[OrIntroductionRight]()[*q*]</code> proves <code>[Or]()[*a*, *b*]</code> from a proof *q* of *b*.

## Details & Options

- [Or]() is an inductive proposition of the prelude with two parameters, *a* and *b*, and two constructors, [OrIntroductionLeft]() and [OrIntroductionRight]().
- *a* and *b* are implicit arguments. *b* is found from the type of *q*, but *a* only from the type the proof is expected to have.

## Basic Examples

The type of [OrIntroductionRight]():

```wl
TypeTheoryCheck[TypeTheoryTerm[OrIntroductionRight]]
```

<!-- => ∀_{a ∶ Prop} ∀_{b ∶ Prop} b ⇒ (a ∨ b) -->

---

A proof of `False || 1 + 2 == 3`, whose right side holds by computation:

```wl
TypeTheoryCheck[TypeTheoryTerm[OrIntroductionRight[EqualityReflexivity[3]]], TypeTheoryTerm[Or[False, 1 + 2 == 3]]]
```

<!-- => Success["TypeChecked", ...] -->

## Scope

[Typed]() gives the expected type inside the term:

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed[OrIntroductionRight[EqualityReflexivity[3]], Or[False, 1 + 2 == 3]]]]
```

<!-- => False ∨ 1 + 2 == 3 -->

---

`"Apply"` leaves the right side as the goal:

```wl
proof = TypeTheoryProof[Or[2 == 3, 2 + 2 == 4], {TypeTheoryTactic["Apply", OrIntroductionRight]}]
```

<!-- => Proof, 1 goal: ⊢ 2 + 2 == 4 -->

It holds by computation:

```wl
TypeTheoryTactic["Reflexivity"][proof]
```

<!-- => Proof complete -->

## Applications

Every natural number is 0 or a successor: `"Cases"` splits the number, and each case proves one side:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, Or[n == 0, Exists[{Typed[k, Naturals]}, n == k + 1]]], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Cases", n],
    TypeTheoryTactic["Exact", OrIntroductionLeft[EqualityReflexivity[0]]],
    TypeTheoryTactic["Introduce", m],
    TypeTheoryTactic["Exact", OrIntroductionRight[ExistsIntroduction[m, EqualityReflexivity[m + 1]]]]
}]
```

<!-- => Proof complete -->

## Possible Issues

Without an expected type, the left side of the disjunction is unknown:

```wl
TypeTheoryCheck[TypeTheoryTerm[OrIntroductionRight[TrueIntroduction]]]
```

<!-- => Failure["UnsolvedImplicitArgument", ...] -->
