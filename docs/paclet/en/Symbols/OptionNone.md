---
Template: Symbol
Name: OptionNone
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/OptionNone
Keywords: [option, none, missing value, constructor, prelude]
SeeAlso: [Option, OptionSome, EmptyList]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

[OptionNone]() is the missing value of <code>[Option]()[*α*]</code>.

## Details & Options

- [OptionNone]() is the first constructor of [Option]().
- *α* is an implicit argument, found from the expected type.

## Basic Examples

The type of [OptionNone]():

```wl
TypeTheoryCheck[TypeTheoryTerm[OptionNone]]
```

<!-- => ∀_{α ∶ Type u} Option[α] -->

---

The missing natural number:

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed[OptionNone, Option[Naturals]]]]
```

<!-- => Option[ℕ] -->

## Scope

[Construct]() gives the type explicitly:

```wl
TypeTheoryCheck[TypeTheoryTerm[Construct[OptionNone, Naturals]]]
```

<!-- => Option[ℕ] -->

## Applications

The recursor of [Option]() gives a default for the missing value, here 0:

```wl
WeakHeadNormalForm[TypeTheoryTerm[InductiveRecursor[Option][Function[{Typed[t, Option[Naturals]]}, Naturals], 0, Function[{Typed[x, Naturals]}, x], OptionNone]]]
```

<!-- => 0 -->

## Properties and Relations

[OptionNone]() is a value of its own, not <code>[OptionSome]()[0]</code>:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Typed[OptionNone, Option[Naturals]]], TypeTheoryTerm[OptionSome[0]]]
```

<!-- => False -->

## Possible Issues

Inside another constructor, the type of [OptionNone]() is unknown without an expected type:

```wl
TypeTheoryCheck[TypeTheoryTerm[OptionSome[OptionNone]]]
```

<!-- => Failure["UnsolvedImplicitArgument", ...] -->

[Typed]() gives it:

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed[OptionSome[OptionNone], Option[Option[Naturals]]]]]
```

<!-- => Option[Option[ℕ]] -->
