---
Template: Symbol
Name: ImpredicativeMaximum
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/ImpredicativeMaximum
Keywords: [universe level, impredicativity, Prop, imax, function type]
SeeAlso: [TypeUniverse, TypeTheoryTerm]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[ImpredicativeMaximum]()[*level1*, *level2*]</code> is the universe level 0 when *level2* is 0, and <code>[Max]()[*level1*, *level2*]</code> otherwise: the level of a function type from <code>[TypeUniverse]()[*level1*]</code> to <code>[TypeUniverse]()[*level2*]</code>.

## Details & Options

- A function type into propositions is itself a proposition, whatever its domain: this is what makes Prop impredicative.
- A level written with [ImpredicativeMaximum]() simplifies when its second argument is known to be 0, or known never to be.
- A universe shows its level as Lean writes it: <code>[ImpredicativeMaximum]()[*u*, *v*]</code> as `imax u v` and <code>[Max]()[*u*, *v*]</code> as `max u v`.

## Basic Examples

A statement about every type is still a proposition:

```wl
TypeOf[TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[1]]}, Implies[True, True]]]]
```

<!-- => Prop -->

---

A universe at that level, for parameters `u` and `v`:

```wl
TypeOf[TypeTheoryTerm[TypeUniverse[ImpredicativeMaximum[u, v]]]]
```

<!-- => Type (imax u v) -->

## Scope

A level whose second argument is never 0 is a maximum:

```wl
TypeOf[TypeTheoryTerm[TypeUniverse[ImpredicativeMaximum[u, v + 1]]]]
```

<!-- => Type (max u (v + 1)) -->

---

A level whose second argument is 0 is 0:

```wl
TypeOf[TypeTheoryTerm[TypeUniverse[ImpredicativeMaximum[u, 0]]]]
```

<!-- => Type -->

---

A function type over a universe parameter has an impredicative level:

```wl
TypeOf[TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[u]]}, A]]]
```

<!-- => Sort (imax (u + 1) u) -->
