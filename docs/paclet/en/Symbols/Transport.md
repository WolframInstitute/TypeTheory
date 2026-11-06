---
Template: Symbol
Name: Transport
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Transport
Keywords: [transport, path, path induction, substitution, HoTT, homotopy type theory, univalence, circle, family of types]
SeeAlso: [CubicalTransport, Equivalence, IsSet, InductiveRecursor, Equal]
RelatedGuides: [TypeTheory]
RelatedTutorials: [HomotopyTypeTheory, CubicalTypeTheory]
---

## Usage

<code>[Transport]()[*P*, *p*, *b*]</code> carries *b*, an element of <code>*P*[*x*]</code>, along the path *p* : <code>*x* == *y*</code> to an element of <code>*P*[*y*]</code>.

## Details & Options

- [Transport]() is a definition by path induction, the recursor of [Equal](), so it computes when *p* is reflexivity, and not along a path in a variable, an axiom such as `"circleLoop"`, or a path that univalence gives.
- The family *P*, a function into a universe, is explicit; *x*, *y* and their type are implicit.
- For a family of statements it is substitution: it carries a proof of <code>*P*[*x*]</code> to one of <code>*P*[*y*]</code>, as `"equalitySubstitution"` does for propositions in the prelude.
- For the identity of the universe, it takes a path of types <code>*A* == *B*</code> to a function from *A* to *B*. Along the path an equivalence gives by univalence, that function is the equivalence's, up to a path, by `"univalenceComputation"`.
- Other statements of the HoTT environment use it: `"transportConstant"`, that in a constant family transport leaves an element where it is up to a path; `"dependentCongruence"`, that a dependent function takes a path to a path over it; and `"circleInduction"`, which asks for a path over the loop of the circle.
- It is a constant of <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code>; terms that use it name that environment. In the cubical environment, [CubicalTransport]() carries elements along a line of types and computes by the type.

## Basic Examples

The statement of [Transport](), in the HoTT environment:

```wl
TypeTheoryType[Transport, "HomotopyTypeTheory"]
```

<!-- => ∀_{A ∶ Type u} ∀_P∶A → Type v ∀_{x ∶ A} ∀_{y ∶ A} x == y → P[x] → P[y] -->

---

Along reflexivity, transport leaves an element as it is; [True]() and [False]() stand for the Booleans where a Boolean is expected:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Transport[Typed[b, Booleans] |-> Booleans, "equalityReflexivity"[True], False], "HomotopyTypeTheory"]]
```

<!-- => false -->

---

Transport in a family of statements is substitution: a path from `x` to `y` carries a proof that `"not"[x]` is `"true"` to a proof that `"not"[y]` is:

```wl
TypeTheoryType[
    {Typed[x, Booleans], Typed[y, Booleans], Typed[p, x == y], Typed[h, "not"[x] == "true"]} |-> Transport[Typed[b, Booleans] |-> "not"[b] == "true", p, h],
    "HomotopyTypeTheory"
]
```

<!-- => ∀_x∶𝔹 ∀_y∶𝔹 x == y → !x == true → !y == true -->

## Scope

In the universe, along a path of types, transport is a function from one type to the other:

```wl
TypeTheoryType[
    {TypedImplicit[A, TypeUniverse[1]], TypedImplicit[B, TypeUniverse[1]], Typed[p, A == B], Typed[a, A]} |-> Transport[Typed[X, TypeUniverse[1]] |-> X, p, a],
    "HomotopyTypeTheory"
]
```

<!-- => ∀_{A ∶ Type} ∀_{B ∶ Type} A == B → A → B -->

---

Along reflexivity of a type, that function is the identity:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Transport[Typed[X, TypeUniverse[1]] |-> X, "equalityReflexivity"[Booleans], "true"], "HomotopyTypeTheory"]]
```

<!-- => true -->

---

In a constant family, transport leaves the element where it is, up to a path:

```wl
TypeTheoryType["transportConstant", "HomotopyTypeTheory"]
```

<!-- => ∀_{A ∶ Type u} ∀_{B ∶ Type v} ∀_{x ∶ A} ∀_{y ∶ A} ∀_p∶x == y ∀_b∶B Transport[(w ∶ A) ↦ B, p, b] == b -->

---

A dependent function takes a path to a path over it, from the transport of its value at one end to its value at the other:

```wl
TypeTheoryType["dependentCongruence", "HomotopyTypeTheory"]
```

<!-- => ∀_{A ∶ Type u} ∀_{P ∶ A → Type v} ∀_f∶∀_z∶A P[z] ∀_{x ∶ A} ∀_{y ∶ A} ∀_p∶x == y Transport[P, p, f[x]] == f[y] -->

## Applications

There is no path from `"true"` to `"false"`: carrying `"trueIntroduction"` along one, in the family that is [True]() at `"true"` and [False]() at `"false"`, would give an element of the empty type:

```wl
TypeTheoryProof[Not["true" == "false"], "HomotopyTypeTheory", {
    "Introduce"[p],
    "Exact"[Transport[Typed[b, Booleans] |-> InductiveRecursor[Booleans][Typed[t, Booleans] |-> TypeUniverse[1], False, True, b], p, "trueIntroduction"]]
}]
```

<!-- => Proof complete -->

---

Induction on the circle asks for an element at the base point and a path over the loop, stated with [Transport]():

```wl
TypeTheoryType["circleInduction", "HomotopyTypeTheory"]
```

<!-- => ∀_P∶𝕊¹ → Type u ∀_b∶P[circleBase] Transport[P, circleLoop, b] == b → ∀_x∶𝕊¹ P[x] -->

In a constant family, `"transportConstant"` gives the path over the loop, and induction computes on the base point:

```wl
WeakHeadNormalForm[TypeTheoryTerm["circleInduction"[Typed[x, Circle] |-> Booleans, "true", "transportConstant"["circleLoop", "true"], "circleBase"], "HomotopyTypeTheory"]]
```

<!-- => true -->

## Properties and Relations

[Transport]() is the recursor of [Equal]() with a family that ignores the path:

```wl
TypeTheoryEnvironment["HomotopyTypeTheory"][Transport]
```

<!-- => definition Transport : ∀_{A ∶ Type u} ∀_P∶A → Type v ∀_{x ∶ A} ∀_{y ∶ A} x == y → P[x] → P[y] := {A ∶ Type u} (P ∶ A → Type v) {x ∶ A} {y ∶ A} (p ∶ x == y) (b ∶ P[x]) ↦ Equal_rec[(z ∶ A) (q ∶ x == z) ↦ P[z], b, p] -->

---

In the prelude, `"equalitySubstitution"` does the same for propositions:

```wl
TypeTheoryType["equalitySubstitution"]
```

<!-- => ∀_{α ∶ Sort u} ∀_{P ∶ α → Prop} ∀_{x ∶ α} ∀_{y ∶ α} x == y ⇒ P[x] ⇒ P[y] -->

---

In the cubical environment, transport along the path of an equivalence computes to the equivalence applied, here negation:

```wl
WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport["equivalenceToPath"["negationEquivalence"], 0, "true"], "Cubical"]]
```

<!-- => false -->

## Possible Issues

Along a path that is not reflexivity, transport does not compute. Univalence is an axiom here, so transport along the path that negation gives stops at it:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Transport[Typed[X, TypeUniverse[1]] |-> X, "equivalenceToEquality"["negationEquivalence"], "true"], "HomotopyTypeTheory"]]
```

<!-- => Equal_rec[(z ∶ Type) (q ∶ 𝔹 == z) ↦ ((X ∶ Type) ↦ X)[z], true, equivalenceToEquality[negationEquivalence]] -->

---

The loop of the circle is an axiom too, so transport along it stops even in a constant family:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Transport[Typed[x, Circle] |-> Booleans, "circleLoop", "true"], "HomotopyTypeTheory"]]
```

<!-- => Equal_rec[(z ∶ 𝕊¹) (q ∶ circleBase == z) ↦ ((x ∶ 𝕊¹) ↦ 𝔹)[z], true, circleLoop] -->

---

The family is a function into a universe, not a type; a constant family is a function that ignores its argument:

```wl
TypeTheoryType[Transport[Booleans, "equalityReflexivity"["true"], "false"], "HomotopyTypeTheory"]
```

<!-- => Failure["TypeMismatch", ...] -->

---

The cubical environment has [CubicalTransport]() instead:

```wl
TypeTheoryType[Transport, "Cubical"]
```

<!-- => Failure["ElaborationFailed", ...] -->
