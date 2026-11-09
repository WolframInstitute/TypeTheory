---
Template: Symbol
Name: ImpredicativeMaximum
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/ImpredicativeMaximum
Keywords: [universe level, impredicativity, Prop, imax, max, function type, universe polymorphism]
SeeAlso: [TypeUniverse, TypeTheoryType, TypeTheoryTerm, Max]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[ImpredicativeMaximum]()[*level1*, *level2*]</code> is the universe level 0 when *level2* is 0, and <code>[Max]()[*level1*, *level2*]</code> otherwise: the level of a function type from <code>[TypeUniverse]()[*level1*]</code> to <code>[TypeUniverse]()[*level2*]</code>.

## Details & Options

- A function type into propositions is itself a proposition, whatever its domain: this is what makes Prop impredicative. Into any other universe, a function type is in the larger universe of its domain and its codomain. <code>[ImpredicativeMaximum]()[*u*, *v*]</code> covers both cases.
- The kernel gives the type of <code>[ForAll]()[{[Typed]()[*x*, *A*]}, *B*]</code>, for *A* in <code>[TypeUniverse]()[*u*]</code> and *B* in <code>[TypeUniverse]()[*v*]</code>, the level <code>[ImpredicativeMaximum]()[*u*, *v*]</code>.
- A level written with [ImpredicativeMaximum]() simplifies when its second argument is known to be 0, to 0, or known never to be, such as `v + 1` or a positive integer, to a [Max](); it also simplifies when its first argument is 0 or the two are the same. The kernel simplifies the levels it computes, and compares levels by these rules; [TypeTheoryTerm]() keeps a level as it is written.
- Its arguments are levels, not universes: `u`, not <code>[TypeUniverse]()[*u*]</code>.
- [ImpredicativeMaximum]() does not evaluate outside a term.
- A universe shows its level: <code>[ImpredicativeMaximum]()[*u*, *v*]</code> as `imax u v` and <code>[Max]()[*u*, *v*]</code> as `max u v`.

## Basic Examples

A statement about every type is still a proposition:

```wl
TypeTheoryType[ForAll[{Typed[A, TypeUniverse[1]]}, Implies[True, True]]]
```

<!-- => Prop -->

---

A function type over a universe parameter has an impredicative level, since its codomain `A` may be a proposition:

```wl
TypeTheoryType[ForAll[{Typed[A, TypeUniverse[u]]}, A]]
```

<!-- => Sort (imax (u + 1) u) -->

---

A universe at that level, for parameters `u` and `v`:

```wl
TypeTheoryType[TypeUniverse[ImpredicativeMaximum[u, v]]]
```

<!-- => Type (imax u v) -->

## Scope

A level whose second argument is never 0 is a maximum:

```wl
TypeTheoryType[TypeUniverse[ImpredicativeMaximum[u, v + 1]]]
```

<!-- => Type (max u (v + 1)) -->

---

A level whose second argument is 0 is 0, so the universe above it is Type:

```wl
TypeTheoryType[TypeUniverse[ImpredicativeMaximum[u, 0]]]
```

<!-- => Type -->

---

A level whose first argument is 0 is its second:

```wl
TypeTheoryType[TypeUniverse[ImpredicativeMaximum[0, u]]]
```

<!-- => Type u -->

---

A statement about the elements of a type of any universe is a proposition, since its body is:

```wl
TypeTheoryType[ForAll[{Typed[A, TypeUniverse[u]], Typed[x, A]}, x == x]]
```

<!-- => Prop -->

---

A function type between types of any universes nests the level for each binder:

```wl
TypeTheoryType[ForAll[{Typed[A, TypeUniverse[u]], Typed[B, TypeUniverse[v]]}, TypeSpecifier[{A} -> B]]]
```

<!-- => Sort (imax (u + 1) (imax (v + 1) (imax u v))) -->

---

A family of types is never a proposition, so its level is a maximum:

```wl
TypeTheoryType[ForAll[{Typed[A, TypeUniverse[u]]}, TypeSpecifier[{A} -> TypeUniverse[v]]]]
```

<!-- => Type (max u v) -->

---

On numbers it is the level itself, here of `imax 2 1`, which is 2:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[TypeUniverse[ImpredicativeMaximum[2, 1]]], TypeTheoryTerm[TypeUniverse[2]]]
```

<!-- => True -->

## Properties and Relations

With a second argument that is never 0, it is [Max]():

```wl
DefinitionallyEqualQ[TypeTheoryTerm[TypeUniverse[ImpredicativeMaximum[u, v + 1]]], TypeTheoryTerm[TypeUniverse[Max[u, v + 1]]]]
```

<!-- => True -->

---

With a parameter as its second argument, it is not, since `v` may be 0:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[TypeUniverse[ImpredicativeMaximum[u, v]]], TypeTheoryTerm[TypeUniverse[Max[u, v]]]]
```

<!-- => False -->

---

The maximum of a level with itself is the level:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[TypeUniverse[ImpredicativeMaximum[u, u]]], TypeTheoryTerm[TypeUniverse[u]]]
```

<!-- => True -->

---

Outside a term, [ImpredicativeMaximum]() stays as it is:

```wl
ImpredicativeMaximum[1, 0]
```

<!-- => ImpredicativeMaximum[1, 0] -->

## Possible Issues

[TypeTheoryTerm]() shows a level as it is written, here `imax u 0`:

```wl
TypeTheoryTerm[TypeUniverse[ImpredicativeMaximum[u, 0]]]
```

<!-- => Sort (imax u 0) -->

The kernel takes it as 0, so the universe is Prop:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[TypeUniverse[ImpredicativeMaximum[u, 0]]], TypeTheoryTerm[TypeUniverse[0]]]
```

<!-- => True -->

---

The arguments are levels, so a universe is not one:

```wl
TypeTheoryType[TypeUniverse[ImpredicativeMaximum[TypeUniverse[1], 0]]]
```

<!-- => Failure["ElaborationFailed", ...] -->
