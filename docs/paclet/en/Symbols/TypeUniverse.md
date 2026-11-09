---
Template: Symbol
Name: TypeUniverse
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeUniverse
Keywords: [universe, sort, Prop, Type, universe level, universe parameter, universe polymorphism, impredicativity, cumulativity, proof irrelevance]
SeeAlso: [ImpredicativeMaximum, TypeTheoryType, TypeTheoryDefinition, TypeTheoryTheorem, Subscript]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[TypeUniverse]()[*level*]</code> is the universe at *level*: <code>[TypeUniverse]()[0]</code> is Prop, the universe of propositions, <code>[TypeUniverse]()[1]</code> is Type, the universe of data types such as [Naturals](), and <code>[TypeUniverse]()[*u*]</code>, for a universe parameter *u*, is Sort *u*, any of them.

## Details & Options

- *level* is a non-negative integer, a universe parameter (a symbol or a string), <code>*level* + *k*</code> for a positive integer *k*, <code>[Max]()[*level1*, *level2*]</code> or <code>[ImpredicativeMaximum]()[*level1*, *level2*]</code>. Anything else, such as `-1` or `u - 1`, is not a level, and the kernel gives a [Failure]() tagged `"ElaborationFailed"`.
- <code>[TypeUniverse]()[*l*]</code> has the type <code>[TypeUniverse]()[*l* + 1]</code>. There is no universe of all universes: Type is in Type 1, not in Type.
- Universes are not cumulative: a type in <code>[TypeUniverse]()[1]</code> is not also in <code>[TypeUniverse]()[2]</code>.
- Prop is impredicative: a statement about every type, or about every proposition, is still a proposition, and any two proofs of a proposition are equal. Above Prop, a function type is in the larger universe of its domain and its codomain; [ImpredicativeMaximum]() is the level that covers both cases.
- A declaration's universe parameters are the symbols and strings in its universe levels, unless the option `"UniverseParameters"` lists them. A constant with parameters is used at any levels, which elaboration finds, or which <code>[Subscript]()[*c*, *level1*, ...]</code> gives explicitly.
- Under rules without Prop, as those of <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code> and <code>[TypeTheoryEnvironment]()["Cubical"]</code>, <code>[TypeUniverse]()[0]</code> is no universe, and the kernel gives a [Failure]() tagged `"NoProp"`.
- In a notebook, universes show: Prop, Type, Type 1, ..., Type *u* for <code>[TypeUniverse]()[*u* + 1]</code>, and Sort *u* for <code>[TypeUniverse]()[*u*]</code>.

## Basic Examples

Prop is in Type:

```wl
TypeTheoryType[TypeUniverse[0]]
```

<!-- => Type -->

---

An equation is a proposition, in Prop:

```wl
TypeTheoryType[2 + 2 == 4]
```

<!-- => Prop -->

---

The natural numbers are a type, in Type:

```wl
TypeTheoryType[Naturals]
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
TypeTheoryType[TypeUniverse[u + 1]]
```

<!-- => Type (u + 1) -->

## Scope

Type, the universe of types, is in Type 1:

```wl
TypeTheoryType[TypeUniverse[1]]
```

<!-- => Type 1 -->

---

A family of types, a function from the natural numbers to types, is in Type 1:

```wl
TypeTheoryType[TypeSpecifier[{Naturals} -> TypeUniverse[1]]]
```

<!-- => Type 1 -->

---

A pair of a number and a type is in the universe of its larger part:

```wl
TypeTheoryType[CartesianProductType[Naturals, TypeUniverse[1]]]
```

<!-- => Type 1 -->

---

A universe at the maximum of two parameters:

```wl
TypeTheoryTerm[TypeUniverse[Max[u, v] + 1]]
```

<!-- => Type (max u v) -->

---

A statement about every proposition is a proposition:

```wl
TypeTheoryType[ForAll[{Typed[p, TypeUniverse[0]]}, Implies[p, p]]]
```

<!-- => Prop -->

---

A type of functions over every type is too large for Type, and is in Type 1:

```wl
TypeTheoryType[ForAll[{Typed[A, TypeUniverse[1]]}, TypeSpecifier[{A} -> A]]]
```

<!-- => Type 1 -->

### Universe Parameters

An identity function for the elements of a type of any universe, with the parameter `u`:

```wl
identity = TypeTheoryEnvironment[{TypeTheoryDefinition[PolymorphicIdentity, {Typed[A, TypeUniverse[u]], Typed[x, A]} |-> x]}]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

Its declaration:

```wl
identity[PolymorphicIdentity]
```

<!-- => definition PolymorphicIdentity : ∀_A∶Sort u A → A := (A ∶ Sort u) (x ∶ A) ↦ x -->

At a type, `u` is 1:

```wl
TypeTheoryType[PolymorphicIdentity[Naturals, 3], identity]
```

<!-- => ℕ -->

At a proposition, `u` is 0, and the identity takes a proof:

```wl
TypeTheoryType[PolymorphicIdentity[2 + 2 == 4, "equalityReflexivity"[4]], identity]
```

<!-- => 2 + 2 == 4 -->

[Subscript]() gives the level explicitly, here 0, the identity on proofs:

```wl
TypeTheoryType[Subscript[PolymorphicIdentity, 0], identity]
```

<!-- => ∀_A∶Prop A ⇒ A -->

---

[Option]() of the prelude at the level 1, the options of types:

```wl
TypeTheoryType[Subscript[Option, 1]]
```

<!-- => Type 1 → Type 1 -->

## Properties and Relations

Any two proofs of a proposition are equal, here two proofs of `1 <= 2`, one by a step of the order and one by computation:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Typed["lessEqualStep"["lessEqualReflexivity"], 1 <= 2]], TypeTheoryTerm[Typed["decideSoundness"["equalityReflexivity"["true"]], 1 <= 2]]]
```

<!-- => True -->

---

The level of a function type into a universe of any level is an [ImpredicativeMaximum]():

```wl
TypeTheoryType[ForAll[{Typed[A, TypeUniverse[u]]}, A]]
```

<!-- => Sort (imax (u + 1) u) -->

---

As Prop is impredicative, a proposition may quantify over every proposition, itself included. The Church booleans of Nederpelt and Geuvers's *Type Theory and Formal Proof* (Exercise 3.14) are a proposition:

```wl
booleans = TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[0]]}, A -> A -> A]]
```

<!-- => ∀_A∶Prop A → A → A -->

The two booleans choose their first argument and their second:

```wl
truth = TypeTheoryTerm[{Typed[A, TypeUniverse[0]], Typed[x, A], Typed[y, A]} |-> x];
falsity = TypeTheoryTerm[{Typed[A, TypeUniverse[0]], Typed[x, A], Typed[y, A]} |-> y];
negation = TypeTheoryTerm[Typed[z, booleans] |-> z[booleans, falsity, truth]]
```

<!-- => (z ∶ booleans) ↦ z[booleans, falsity, truth] -->

Negation instantiates the quantifier of its argument at the booleans themselves, and is a function of booleans:

```wl
TypeTheoryType[negation]
```

<!-- => (∀_A∶Prop A ⇒ A ⇒ A) ⇒ ∀_A∶Prop A ⇒ A ⇒ A -->

The negation of truth computes to falsity:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[negation[truth]], falsity]
```

<!-- => True -->

## Possible Issues

Type is not in Type:

```wl
TypeTheoryCheck[TypeTheoryTerm[TypeUniverse[1]], TypeTheoryTerm[TypeUniverse[1]]]
```

<!-- => Failure["TypeMismatch", ...] -->

---

Universes are not cumulative, so the natural numbers, in Type, are not in Type 1:

```wl
TypeTheoryCheck[TypeTheoryTerm[Naturals], TypeTheoryTerm[TypeUniverse[2]]]
```

<!-- => Failure["TypeMismatch", ...] -->

---

A level adds a number to a parameter, and never subtracts one:

```wl
TypeTheoryType[TypeUniverse[u - 1]]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

The homotopy type theory environment has no Prop:

```wl
TypeTheoryType[TypeUniverse[0], "HomotopyTypeTheory"]
```

<!-- => Failure["NoProp", ...] -->

---

Above Prop the same booleans cannot negate: over Type they are in Type 1, and the quantifier over Type does not take them:

```wl
typeBooleans = TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[1]]}, A -> A -> A]]
```

<!-- => ∀_A∶Type A → A → A -->

```wl
TypeTheoryType[Typed[z, typeBooleans] |-> z[typeBooleans]]
```

<!-- => Failure["TypeMismatch", ...] -->

---

In Prop, the Church numerals of Nederpelt and Geuvers's Exercise 3.12 are proofs of one proposition, and any two proofs are equal, so two and three are the same numeral:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[{Typed[A, TypeUniverse[0]], Typed[f, A -> A], Typed[x, A]} |-> f[f[x]]], TypeTheoryTerm[{Typed[A, TypeUniverse[0]], Typed[f, A -> A], Typed[x, A]} |-> f[f[f[x]]]]]
```

<!-- => True -->

Over Type the numerals are data, and two and three differ:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[{Typed[A, TypeUniverse[1]], Typed[f, A -> A], Typed[x, A]} |-> f[f[x]]], TypeTheoryTerm[{Typed[A, TypeUniverse[1]], Typed[f, A -> A], Typed[x, A]} |-> f[f[f[x]]]]]
```

<!-- => False -->
