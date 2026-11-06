---
Template: Symbol
Name: IsSet
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IsSet
Keywords: [set, uniqueness of identity proofs, UIP, paths between paths, proof irrelevance, HoTT, homotopy type theory, universe, univalence]
SeeAlso: [Equal, Equivalence, Transport]
RelatedGuides: [TypeTheory]
RelatedTutorials: [HomotopyTypeTheory]
---

## Usage

<code>[IsSet]()[*A*]</code> is the type of proofs that any two paths between the same elements of *A* are equal.

## Details & Options

- [IsSet]() is a definition: <code>[IsSet]()[*A*]</code> is <code>[ForAll]()[{[Typed]()[*x*, *A*], [Typed]()[*y*, *A*], [Typed]()[*p*, *x* == *y*], [Typed]()[*q*, *x* == *y*]}, *p* == *q*]</code>, the uniqueness of identity proofs for *A*.
- Under the prelude's rules every type is a set: an equation is a proposition, and any two proofs of a proposition are equal by computation. The prelude has no [IsSet]() to say it.
- In the HoTT environment, which has no Prop, two paths need not be equal, and some types are not sets: `"universeNotSet"` proves, with univalence, that the universe is not one, since negation gives a path from the Booleans to themselves other than reflexivity.
- <code>[IsSet]()[*A*]</code> is in the universe of *A*.
- It is a constant of <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code>; terms that use it name that environment.

## Basic Examples

The type of [IsSet](), in the HoTT environment:

```wl
TypeTheoryType[IsSet, "HomotopyTypeTheory"]
```

<!-- => Type u → Type u -->

---

What it says of the Booleans:

```wl
WeakHeadNormalForm[TypeTheoryTerm[IsSet[Booleans], "HomotopyTypeTheory"]]
```

<!-- => ∀_x∶𝔹 ∀_y∶𝔹 ∀_p∶x == y ∀_q∶x == y p == q -->

---

The universe of types is not a set:

```wl
TypeTheoryType["universeNotSet", "HomotopyTypeTheory"]
```

<!-- => ¬IsSet[Type] -->

## Scope

The empty type is a set, since there are no elements to have paths between:

```wl
TypeTheoryProof[IsSet[False], "HomotopyTypeTheory", {"Introduce"[x, y, p, q], "Exact"["falseElimination"[x]]}]
```

<!-- => Proof complete -->

---

The negation of [IsSet]() is a function into [False](): from a proof that the universe is a set, `"universeNotSet"` makes an element of the empty type:

```wl
TypeTheoryType[Typed[s, IsSet[TypeUniverse[1]]] |-> "universeNotSet"[s], "HomotopyTypeTheory"]
```

<!-- => IsSet[Type] → False -->

---

The statement about the universe of types is in the universe above it:

```wl
TypeTheoryType[IsSet[TypeUniverse[1]], "HomotopyTypeTheory"]
```

<!-- => Type 1 -->

## Properties and Relations

In the prelude, any two proofs of an equation of natural numbers are equal by computation, so the statement of [IsSet]() for the natural numbers holds by reflexivity:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals], Typed[p, x == y], Typed[q, x == y]}, p == q], {"Introduce"[x, y, p, q], "Reflexivity"}]
```

<!-- => Proof complete -->

---

The definition, in the HoTT environment:

```wl
TypeTheoryEnvironment["HomotopyTypeTheory"][IsSet]
```

<!-- => definition IsSet : Type u → Type u := (A ∶ Type u) ↦ ∀_x∶A ∀_y∶A ∀_p∶x == y ∀_q∶x == y p == q -->

## Possible Issues

In the HoTT environment two paths are not equal by computation, so reflexivity does not prove that the Booleans are a set:

```wl
TypeTheoryProof[IsSet[Booleans], "HomotopyTypeTheory", {"Introduce"[x, y, p, q], "Reflexivity"}]
```

<!-- => Failure["NotReflexive", ...] -->

---

The prelude has no [IsSet]():

```wl
TypeTheoryType[IsSet[Naturals]]
```

<!-- => Failure["ElaborationFailed", ...] -->
