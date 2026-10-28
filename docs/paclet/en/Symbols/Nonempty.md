---
Template: Symbol
Name: Nonempty
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Nonempty
Keywords: [nonempty, inhabited, element, choice, prelude, classical logic]
SeeAlso: [NonemptyIntroduction, Choice, Exists, Subtype]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[Nonempty]()[*a*]</code> is the proposition that the type *a* has an element.

## Details & Options

- [Nonempty]() is an inductive proposition of the prelude, with the one constructor [NonemptyIntroduction]().
- A proof of <code>[Nonempty]()[*a*]</code> says that *a* has an element without giving one to compute with. [Choice]() takes such a proof to an element of *a*.
- *a* may be in any universe, a proposition among them.

## Basic Examples

The type of [Nonempty]():

```wl
TypeTheoryCheck[TypeTheoryTerm[Nonempty]]
```

<!-- => Sort u → Prop -->

---

The natural numbers are not empty:

```wl
TypeTheoryCheck[TypeTheoryTerm[NonemptyIntroduction[0]], TypeTheoryTerm[Nonempty[Naturals]]]
```

<!-- => Success["TypeChecked", ...] -->

## Scope

The type may be a proposition: a proof of [True]() shows that [True]() has a proof:

```wl
TypeTheoryCheck[TypeTheoryTerm[NonemptyIntroduction[TrueIntroduction]]]
```

<!-- => Nonempty[True] -->

## Applications

An element of a type gives a pair: `"Cases"` takes a proof of [Nonempty]() apart, which it may, since the goal is a proposition:

```wl
proof = TypeTheoryProof[ForAll[{Typed[A, TypeUniverse[1]], Typed[h, Nonempty[A]]}, Nonempty[CartesianProduct[A, A]]], {
    TypeTheoryTactic["Introduce", A, h],
    TypeTheoryTactic["Cases", h],
    TypeTheoryTactic["Introduce", x]
}]
```

<!-- => Proof, 1 goal: A ∶ Type, x ∶ A ⊢ Nonempty[CartesianProduct[A, A]] -->

The pair of the element with itself:

```wl
TypeTheoryTactic["Exact", NonemptyIntroduction[Pair[x, x]]][proof]
```

<!-- => Proof complete -->

## Properties and Relations

[Choice]() takes a proof of [Nonempty]() to an element:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[h, Nonempty[Naturals]]}, Choice[h]]]]
```

<!-- => Nonempty[ℕ] → ℕ -->

## Possible Issues

A proof of [Nonempty]() can be taken apart only to prove a proposition, not to compute data such as a natural number; [Choice]() gives an element instead:

```wl
TypeTheoryProof[ForAll[{Typed[h, Nonempty[Naturals]]}, Naturals], {TypeTheoryTactic["Introduce", h], TypeTheoryTactic["Cases", h]}]
```

<!-- => Failure["LargeElimination", ...] -->
