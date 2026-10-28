---
Template: Symbol
Name: OptionSome
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/OptionSome
Keywords: [option, some, value, constructor, prelude]
SeeAlso: [Option, OptionNone, Pair]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[OptionSome]()[*x*]</code> is the value *x* of <code>[Option]()[*α*]</code>.

## Details & Options

- [OptionSome]() is the second constructor of [Option]().
- *α* is an implicit argument, found from the type of *x*.

## Basic Examples

The statement of [OptionSome]():

```wl
TypeTheoryCheck[TypeTheoryTerm[OptionSome]]
```

<!-- => ∀_{α ∶ Type u} α → Option[α] -->

---

3 as an optional natural number:

```wl
TypeTheoryCheck[TypeTheoryTerm[OptionSome[3]]]
```

<!-- => Option[ℕ] -->

## Scope

An optional value of any type, here a pair of a number and a Boolean:

```wl
TypeTheoryCheck[TypeTheoryTerm[OptionSome[Pair[1, "true"]]]]
```

<!-- => Option[ℕ × 𝔹] -->

## Applications

The recursor of [Option]() takes the value out, with a default of 0 for [OptionNone]():

```wl
WeakHeadNormalForm[TypeTheoryTerm[InductiveRecursor[Option][Function[{Typed[t, Option[Naturals]]}, Naturals], 0, Function[{Typed[x, Naturals]}, x], OptionSome[7]]]]
```

<!-- => 7 -->

## Properties and Relations

Equal values give equal options, by [EqualityCongruence]():

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Naturals], Typed[y, Naturals], Typed[h, x == y]}, EqualityCongruence[Function[{Typed[z, Naturals]}, OptionSome[z]], h]]]]
```

<!-- => ∀_x∶ℕ ∀_y∶ℕ x == y ⇒ OptionSome[x] == OptionSome[y] -->

## Possible Issues

A proof is no value: [TrueIntroduction]() proves [True](), a proposition, and *α* must be a type of `Type u`. The failure names the sort of each type, Prop for [True]() and `Type u` for the one expected:

```wl
TypeTheoryCheck[TypeTheoryTerm[OptionSome[TrueIntroduction]]]
```

<!-- => Failure["TypeMismatch", ...] -->
