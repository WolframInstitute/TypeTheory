---
Template: Symbol
Name: TypeUniverse
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeUniverse
Keywords: [universe, sort, Prop, Type, universe level, universe polymorphism]
SeeAlso: [ImpredicativeMaximum, TypeTheoryTerm, TypeTheoryDefinition]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[TypeUniverse]()[*level*]</code> is the universe at *level*: <code>[TypeUniverse]()[0]</code> is Prop, the universe of propositions, and <code>[TypeUniverse]()[1]</code> is Type.

## Details & Options

- *level* is a non-negative integer, a universe parameter (a symbol or a string), <code>*level* + *k*</code>, <code>[Max]()[*level1*, *level2*]</code> or <code>[ImpredicativeMaximum]()[*level1*, *level2*]</code>.
- <code>[TypeUniverse]()[*l*]</code> has the type <code>[TypeUniverse]()[*l* + 1]</code>. There is no universe of all universes.
- Universes are not cumulative: a type in <code>[TypeUniverse]()[1]</code> is not also in <code>[TypeUniverse]()[2]</code>.
- A declaration's universe parameters are the symbols and strings in its universe levels.
- In a notebook, universes show as Prop, Type, Type *u*, Type (*u* + 1) and Sort *u*, the way Lean writes them.

## Basic Examples

Prop is in Type:

```wl
TypeOf[TypeTheoryTerm[TypeUniverse[0]]]
```

<!-- => Type -->

---

A universe at a parameter `u`:

```wl
TypeTheoryTerm[TypeUniverse[u + 1]]
```

<!-- => Type u -->

Its type is the next universe:

```wl
TypeOf[TypeTheoryTerm[TypeUniverse[u + 1]]]
```

<!-- => Type (u + 1) -->

## Possible Issues

Type is not in Type:

```wl
TypeTheoryCheck[TypeTheoryTerm[TypeUniverse[1]], TypeTheoryTerm[TypeUniverse[1]]]
```

<!-- => Failure["TypeMismatch", ...] -->
