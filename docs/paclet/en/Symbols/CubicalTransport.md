---
Template: Symbol
Name: CubicalTransport
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/CubicalTransport
Keywords: [transport, line of types, path of types, cubical type theory, face, univalence, coercion, transp, path induction, transport filler]
SeeAlso: [CubicalComposition, GlueType, Transport, IntervalMeet, IntervalReverse, TypeTheoryCubical]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[CubicalTransport]()[*A*, *φ*, *a*]</code> carries *a*, an element of *A*[0], along the line of types *A*, a function of the interval into a universe, to an element of *A*[1]. *A* must be constant where the face *φ* holds, and there the transport is *a*.

## Details & Options

- *A* may be written as a type, the constant line; as a path of types, such as the one `"equivalenceToPath"` makes from an equivalence; or as a function of the interval into a universe.
- The kernel checks that *A* is constant on every conjunction of the face *φ*, and fails with `"TransportNotConstant"` otherwise. Over the face 0 it asks nothing.
- Transport computes by the type it is in: it is *a* where *φ* holds, and in a universe or an inductive type with no parameters and no indices. In a function type it carries the argument back along the domain and the value forward along the codomain; in a path type it composes, with the path's endpoints as two more sides.
- In a Glue type, where *φ* is 0 and no face of the Glue type holds all along the line, it carries the element under *a* along the base and takes the centers of the fibers of the equivalences at the end: along the path of `"equivalenceToPath"`, it applies the equivalence.
- Where no rule applies the transport does not compute: in a type that is a variable, and along a line through a composition in a universe, such as the concatenation of two paths of types. Path induction, `"pathInduction"`, is a transport, so on the constant path it computes to its value only where transport in the family computes; in general it is its value up to a path, as in cubical type theory.
- [CubicalTransport]() must be given all three arguments. In the HoTT environment, [Transport]() is a definition by path induction, and univalence is an axiom, along which it does not compute.

## Basic Examples

Transport along the path of types that univalence makes from negation applies negation:

```wl
WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport["equivalenceToPath"["negationEquivalence"], 0, "true"], "Cubical"]]
```

<!-- => false -->

---

Transport along a path of types `P` from `A` to `B` is a function from `A` to `P` at 1, which is `B`:

```wl
TypeTheoryType[{TypedImplicit[A, TypeUniverse[1]], TypedImplicit[B, TypeUniverse[1]], Typed[P, Path[TypeUniverse[1], A, B]], Typed[a, A]} |-> CubicalTransport[P, 0, a], "Cubical"]
```

<!-- => ∀_{A ∶ Type} ∀_{B ∶ Type} ∀_P∶A ≡ B A → P[1] -->

---

Transport of the function `"not"` along a constant line of function types is a function, here applied to `"true"`:

```wl
WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport[i |-> TypeSpecifier[{Booleans} -> Booleans], 0, "not"]["true"], "Cubical"]]
```

<!-- => false -->

## Scope

Where its face holds, a transport is its element, even in a type `A` that has no rule of transport of its own:

```wl
NormalForm[TypeTheoryTerm[{TypedImplicit[A, TypeUniverse[1]], a} |-> CubicalTransport[A, 1, a], "Cubical"]]
```

<!-- => {A ∶ Type} (a ∶ A) ↦ a -->

---

A type is the constant line, and in an inductive type with no parameters and no indices transport is the identity:

```wl
WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport[Booleans, 0, "true"], "Cubical"]]
```

<!-- => true -->

---

In a universe, transport leaves a type as it is:

```wl
WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport[TypeUniverse[1], 0, Booleans], "Cubical"]]
```

<!-- => 𝔹 -->

---

In a function type, the argument goes back along the domain: transport of the identity of the Booleans, along the line of functions from the path of negation into the Booleans, applies the inverse of negation:

```wl
WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport[i |-> TypeSpecifier[{"equivalenceToPath"["negationEquivalence"][i]} -> Booleans], 0, b |-> b]["true"], "Cubical"]]
```

<!-- => false -->

---

The value goes forward along the codomain: along the line of functions from the Booleans into the path of negation, the identity becomes negation:

```wl
WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport[i |-> TypeSpecifier[{Booleans} -> "equivalenceToPath"["negationEquivalence"][i]], 0, b |-> b]["true"], "Cubical"]]
```

<!-- => false -->

---

Along the path that univalence makes from the identity equivalence, transport is the identity:

```wl
WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport["equivalenceToPath"["identityEquivalence"[Booleans]], 0, "true"], "Cubical"]]
```

<!-- => true -->

---

Along a path of types reversed, transport applies the inverse; negation is its own inverse:

```wl
WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport["pathSymmetry"["equivalenceToPath"["negationEquivalence"]], 0, "true"], "Cubical"]]
```

<!-- => false -->

---

Path induction is transport along the connection of a path, `p[Min[i, j]]`:

```wl
TypeTheoryEnvironment["Cubical"]["pathInduction"]
```

<!-- => definition pathInduction : ∀_{A ∶ Type u} ∀_{x ∶ A} ∀_P∶∀_y∶A x ≡ y → Type v P[x, (i ∶ Interval) ↦ x] → ∀_{y ∶ A} ∀_p∶x ≡ y P[y, p] := {A ∶ Type u} {x ∶ A} (P ∶ ∀_y∶A x ≡ y → Type v) (d ∶ P[x, (i ∶ Interval) ↦ x]) {y ∶ A} (p ∶ x ≡ y) ↦ CubicalTransport[(i ∶ Interval) ↦ P[p[i], (j ∶ Interval) ↦ p[i ∧ j]], 0, d] -->

---

In a family of Booleans, path induction on the constant path at `"true"` computes to its value:

```wl
WeakHeadNormalForm[TypeTheoryTerm["pathInduction"[Booleans &, "false", i |-> "true"], "Cubical"]]
```

<!-- => false -->

## Applications

The transport filler: over the face where `i` is 0, along the line `k ↦ P[Min[i, k]]` from `P[0]` to `P[i]`, transport is a path over `P` from `a` to its transport:

```wl
TypeTheoryType[
    {TypedImplicit[A, TypeUniverse[1]], TypedImplicit[B, TypeUniverse[1]], Typed[P, Path[TypeUniverse[1], A, B]], Typed[a, A]} |->
        Function[{Typed[i, Interval]}, CubicalTransport[k |-> P[Min[i, k]], 1 - i, a]],
    "Cubical"
]
```

<!-- => ∀_{A ∶ Type} ∀_{B ∶ Type} ∀_P∶A ≡ B ∀_a∶A Path[(i ∶ Interval) ↦ P[i ∧ 1], a, CubicalTransport[P, 0, a]] -->

---

Transport along univalence is the function of the equivalence, the first part of the pair:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[CubicalTransport["equivalenceToPath"["negationEquivalence"], 0, "true"], "Cubical"],
    TypeTheoryTerm["negationEquivalence"[[1]]["true"], "Cubical"]
]
```

<!-- => True -->

## Properties and Relations

In the HoTT environment univalence is an axiom, so transport along the path of negation stops at it:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Transport[X |-> X, "equivalenceToEquality"["negationEquivalence"], "true"], "HomotopyTypeTheory"]]
```

<!-- => Equal_rec[(z ∶ Type) (q ∶ 𝔹 == z) ↦ ((X ∶ Type) ↦ X)[z], true, equivalenceToEquality[negationEquivalence]] -->

## Possible Issues

A path of types `p` need not be constant where the face `1` holds, which is everywhere:

```wl
TypeTheoryType[Typed[p, Path[TypeUniverse[1], Booleans, Booleans]] |-> CubicalTransport[p, 1, "true"], "Cubical"]
```

<!-- => Failure["TransportNotConstant", ...] -->

---

Composition in a universe has no rule, so transport along the concatenation of two paths of types stops, though negation twice is the identity:

```wl
WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport["pathTransitivity"["equivalenceToPath"["negationEquivalence"], "equivalenceToPath"["negationEquivalence"]], 0, "true"], "Cubical"]]
```

<!-- => CubicalTransport[(i ∶ Interval) ↦ pathTransitivity[Type, 𝔹, 𝔹, 𝔹, equivalenceToPath[negationEquivalence], equivalenceToPath[negationEquivalence], i], 0, true] ∶ ((i ∶ Interval) ↦ pathTransitivity[...])[1] -->

---

In a family `P` that is a variable, transport has no rule, so path induction on the constant path is not its value `d`; it is `d` only up to a path, as in cubical type theory:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[{Typed[P, ForAll[{y}, Path[Booleans, "true", y] -> TypeUniverse[1]]], Typed[d, P["true", i |-> "true"]]} |-> "pathInduction"[P, d, i |-> "true"], "Cubical"],
    TypeTheoryTerm[{Typed[P, ForAll[{y}, Path[Booleans, "true", y] -> TypeUniverse[1]]], Typed[d, P["true", i |-> "true"]]} |-> d, "Cubical"]
]
```

<!-- => False -->

---

[CubicalTransport]() must be given all three arguments:

```wl
TypeTheoryType[Typed[P, Path[TypeUniverse[1], Booleans, Booleans]] |-> CubicalTransport[P, 0], "Cubical"]
```

<!-- => Failure["CubicalUnsaturated", ...] -->
