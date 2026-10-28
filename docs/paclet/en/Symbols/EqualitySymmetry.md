---
Template: Symbol
Name: EqualitySymmetry
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/EqualitySymmetry
Keywords: [equality, symmetry, theorem, prelude]
SeeAlso: [EqualityReflexivity, EqualityTransitivity, EqualityCongruence, EqualitySubstitution]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[EqualitySymmetry]()[*h*]</code> proves <code>*y* == *x*</code> from a proof *h* of <code>*x* == *y*</code>.

## Details & Options

- [EqualitySymmetry]() is a theorem of the prelude, proved with the recursor of [Equal]().
- The type of *x* and *y*, its universe level, *x* and *y* are implicit arguments, found from the type of *h*.

## Basic Examples

The type of [EqualitySymmetry]():

```wl
TypeTheoryCheck[TypeTheoryTerm[EqualitySymmetry]]
```

<!-- => ∀_{α ∶ Sort u} ∀_{x ∶ α} ∀_{y ∶ α} x == y ⇒ y == x -->

---

Turn an equation around:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Naturals], Typed[h, x + 0 == x]}, EqualitySymmetry[h]]]]
```

<!-- => ∀_x∶ℕ x + 0 == x ⇒ x == x + 0 -->

## Scope

`"Apply"` turns the goal around, so a theorem stated the other way finishes it:

```wl
proof = TypeTheoryProof[ForAll[{Typed[n, Naturals]}, n == 0 + n], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Apply", EqualitySymmetry]
}]
```

<!-- => Proof, 1 goal: n ∶ ℕ ⊢ 0 + n == n -->

[AdditionZeroLeft]() proves the new goal:

```wl
TypeTheoryTactic["Exact", AdditionZeroLeft[n]][proof]
```

<!-- => Proof complete -->

## Applications

Turn a theorem around, here [JoinEmptyRight]():

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[l, Lists[Naturals]]}, EqualitySymmetry[JoinEmptyRight[l]]]]]
```

<!-- => ∀_l∶Lists[ℕ] l == Join[l, EmptyList] -->

## Properties and Relations

Rewriting with the equation turned around replaces *b* by *a*, as `"Rewrite"` with `"RightToLeft"` does:

```wl
TypeTheoryProof[ForAll[{Typed[a, Naturals], Typed[b, Naturals]}, Implies[a == b, Implies[a + 1 == 3, b + 1 == 3]]], {
    TypeTheoryTactic["Introduce", a, b, h, k],
    TypeTheoryTactic["Rewrite", EqualitySymmetry[h]],
    TypeTheoryTactic["Exact", k]
}]
```

<!-- => Proof complete -->

---

In the HoTT environment [EqualitySymmetry]() is a definition, the inverse of a path, so it computes:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The inverse of reflexivity is reflexivity:

```wl
WeakHeadNormalForm[TypeTheoryTerm[EqualitySymmetry[EqualityReflexivity["true"]], hott]]
```

<!-- => EqualityReflexivity[true] -->

In the prelude it is a theorem, which does not compute:

```wl
WeakHeadNormalForm[TypeTheoryTerm[EqualitySymmetry[EqualityReflexivity[3]]]]
```

<!-- => EqualitySymmetry[EqualityReflexivity[3]] -->
