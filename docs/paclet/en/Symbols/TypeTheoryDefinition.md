---
Template: Symbol
Name: TypeTheoryDefinition
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryDefinition
Keywords: [definition, declaration, function, unfolding, environment, universe polymorphism]
SeeAlso: [TypeTheoryEnvironment, TypeTheoryAxiom, TypeTheoryTheorem, WeakHeadNormalForm]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[TypeTheoryDefinition]()[*name*, *value*]</code> declares *name* as a definition with the given *value*, when added to a [TypeTheoryEnvironment]().

<code>[TypeTheoryDefinition]()[*name*, [Typed]()[*value*, *type*]]</code> gives the definition the given *type*.

## Details & Options

- A definition unfolds: computation replaces *name* by *value*. A definition may not mention itself; recursion goes through a recursor, [InductiveRecursor]().
- Without a type, the definition has the type of *value*.
- The option `"UniverseParameters" -> {u, ...}` lists the universe parameters; [Automatic]() takes the symbols and strings in universe levels, in the order they appear.

## Basic Examples

Define doubling, and compute with it:

```wl
doubled = TypeTheoryEnvironment[TypeTheoryDefinition[Double, Function[{Typed[n, Naturals]}, n + n]]];
WeakHeadNormalForm[TypeTheoryTerm[Double[21], doubled]]
```

<!-- => 42 -->

Its type:

```wl
TypeOf[TypeTheoryTerm[Double, doubled]]
```

<!-- => ℕ → ℕ -->

## Scope

A universe-polymorphic definition is used at each universe:

```wl
identity = TypeTheoryEnvironment[
    TypeTheoryDefinition[PolymorphicIdentity, Function[{TypedImplicit[A, TypeUniverse[u]], Typed[x, A]}, x]]
];
TypeOf[TypeTheoryTerm[PolymorphicIdentity[3], identity]]
```

<!-- => ℕ -->

```wl
TypeOf[TypeTheoryTerm[PolymorphicIdentity[Naturals], identity]]
```

<!-- => Type -->

## Possible Issues

A definition cannot refer to itself:

```wl
TypeTheoryEnvironment[
    TypeTheoryDefinition[Loop, Typed[Function[{Typed[n, Naturals]}, Loop[n]], TypeSpecifier[{Naturals} -> Naturals]]]
]
```

<!-- => Failure["ElaborationFailed", ...] -->
