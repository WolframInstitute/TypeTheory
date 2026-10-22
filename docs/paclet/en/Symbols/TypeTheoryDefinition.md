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

Define doubling:

```wl
doubled = TypeTheoryEnvironment[TypeTheoryDefinition[Double, Function[{Typed[n, Naturals]}, n + n]]]
```

<!-- => TypeTheoryEnvironment summary box: 162 constants -->

Compute with it:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Double[21], doubled]]
```

<!-- => 42 -->

Its type:

```wl
TypeOf[TypeTheoryTerm[Double, doubled]]
```

<!-- => ℕ → ℕ -->

## Scope

The identity function on a type in any universe:

```wl
identity = TypeTheoryEnvironment[
    TypeTheoryDefinition[PolymorphicIdentity, Function[{TypedImplicit[A, TypeUniverse[u]], Typed[x, A]}, x]]
]
```

<!-- => TypeTheoryEnvironment summary box: 162 constants -->

A universe-polymorphic definition is used at each universe:

```wl
TypeOf[TypeTheoryTerm[PolymorphicIdentity[3], identity]]
```

<!-- => ℕ -->

Applied to a type, it is used one universe up:

```wl
TypeOf[TypeTheoryTerm[PolymorphicIdentity[Naturals], identity]]
```

<!-- => Type -->

---

The composition of two functions, applied to an argument:

```wl
composite = TypeTheoryEnvironment[TypeTheoryDefinition[Composite,
    Function[{TypedImplicit[A, TypeUniverse[u]], TypedImplicit[B, TypeUniverse[v]], TypedImplicit[C, TypeUniverse[w]], Typed[g, TypeSpecifier[{B} -> C]], Typed[f, TypeSpecifier[{A} -> B]], Typed[x, A]}, g[f[x]]]
]]
```

<!-- => TypeTheoryEnvironment summary box: 162 constants -->

[MakeBoxes]() definitions give a definition a notation. A term shows the arguments that are not implicit, so the rule matches those:

```wl
MakeBoxes[Composite[g_, f_, x_], form_] := MakeBoxes[SmallCircle[g, f][x], form];
TypeTheoryTerm[Function[{Typed[f, TypeSpecifier[{Naturals} -> Naturals]], Typed[n, Naturals]}, Composite[f, f, n]], composite]
```

<!-- => (f ∶ ℕ → ℕ) (n ∶ ℕ) ↦ (f∘f)[n] -->

## Possible Issues

A definition cannot refer to itself:

```wl
TypeTheoryEnvironment[
    TypeTheoryDefinition[Loop, Typed[Function[{Typed[n, Naturals]}, Loop[n]], TypeSpecifier[{Naturals} -> Naturals]]]
]
```

<!-- => Failure["ElaborationFailed", ...] -->
