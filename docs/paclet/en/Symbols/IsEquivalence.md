---
Template: Symbol
Name: IsEquivalence
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IsEquivalence
Keywords: [equivalence, bi-invertible, inverse, HoTT, homotopy type theory, univalence, cubical type theory, contractible fibers]
SeeAlso: [EquivalenceProof, Equivalence, Fiber, IsContractible, InductiveRecursor]
RelatedGuides: [TypeTheory]
RelatedTutorials: [HomotopyTypeTheory, CubicalTypeTheory]
---

## Usage

<code>[IsEquivalence]()[*f*]</code> is the type of proofs that the function *f* is an equivalence: a left inverse and a right inverse, each with its path.

## Details & Options

- In <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code>, [IsEquivalence]() is an inductive type with the one constructor [EquivalenceProof](); <code>*e*[[1]]</code> to <code>*e*[[4]]</code> are the left inverse, its path, the right inverse and its path.
- This bi-invertible definition is the one under which being an equivalence is a proposition, as univalence requires.
- The types of *f* are implicit: for *f* from `Type u` to `Type v`, <code>[IsEquivalence]()[*f*]</code> is in `Type (max u v)`.
- The axiom `"univalence"` is a statement of this type: that the map `"equalityToEquivalence"` from paths between types to equivalences is an equivalence.
- In <code>[TypeTheoryEnvironment]()["Cubical"]</code>, [IsEquivalence]() is a definition instead: every fiber of the function is contractible, <code>[ForAll]()[{[Typed]()[*y*, *B*]}, [IsContractible]()[[Fiber]()[*f*, *y*]]]</code>, the type the kernel writes for Glue types.
- The prelude has no [IsEquivalence](); terms that use it name one of the two environments.

## Basic Examples

The type of [IsEquivalence](), in the HoTT environment:

```wl
TypeTheoryType[IsEquivalence, "HomotopyTypeTheory"]
```

<!-- => ∀_{A ∶ Type u} ∀_{B ∶ Type v} (A → B) → Type (max u v) -->

---

A proof that negation is an equivalence, with negation as its inverse on both sides and paths by cases:

```wl
TypeTheoryType[Typed[EquivalenceProof[
    "not",
    b |-> InductiveRecursor[Booleans][t |-> "not"["not"[t]] == t, "equalityReflexivity"["false"], "equalityReflexivity"["true"], b],
    "not",
    b |-> InductiveRecursor[Booleans][t |-> "not"["not"[t]] == t, "equalityReflexivity"["false"], "equalityReflexivity"["true"], b]
], IsEquivalence["not"]], "HomotopyTypeTheory"]
```

<!-- => IsEquivalence[not] -->

---

Univalence: taking a path between types to an equivalence is itself an equivalence:

```wl
TypeTheoryType["univalence", "HomotopyTypeTheory"]
```

<!-- => ∀_A∶Type u ∀_B∶Type u IsEquivalence[(p ∶ A == B) ↦ equalityToEquivalence[p]] -->

## Scope

Being an equivalence is a type, in the universe of the function's types, for negation that of the Booleans:

```wl
TypeTheoryType[IsEquivalence["not"], "HomotopyTypeTheory"]
```

<!-- => Type -->

---

The third field of a proof is a right inverse. That of univalence takes an equivalence to a path:

```wl
TypeTheoryType["univalence"[Booleans, Booleans][[3]], "HomotopyTypeTheory"]
```

<!-- => Equivalence[𝔹, 𝔹] → 𝔹 == 𝔹 -->

---

The second field of an equivalence is the proof that its function is one:

```wl
TypeTheoryType["negationEquivalence"[[2]], "HomotopyTypeTheory"]
```

<!-- => IsEquivalence[negationEquivalence〚1〛] -->

---

In the cubical environment, it unfolds to the contractibility of every fiber, here of negation:

```wl
WeakHeadNormalForm[TypeTheoryTerm[IsEquivalence["not"], "Cubical"]]
```

<!-- => ∀_y∶𝔹 IsContractible[Fiber[not, y]] -->

---

The cubical proof for negation gives, over `"true"`, the center of its fiber, whose element is `"not"["true"]`:

```wl
WeakHeadNormalForm[TypeTheoryTerm["negationEquivalence"[[2]]["true"][[1]], "Cubical"]]
```

<!-- => 〈!true, negationInvolution[true]〉 ∶ Fiber[negationEquivalence〚1〛, true] -->

## Properties and Relations

In the HoTT environment, [IsEquivalence]() is an inductive type with [EquivalenceProof]() as its constructor:

```wl
TypeTheoryEnvironment["HomotopyTypeTheory"][IsEquivalence]
```

<!-- => inductive IsEquivalence : ∀_{A ∶ Type u} ∀_{B ∶ Type v} (A → B) → Type (max u v) | EquivalenceProof : ∀_{A ∶ Type u} ∀_{B ∶ Type v} ∀_{f ∶ A → B} ∀_g∶B → A (∀_x∶A g[f[x]] == x) → ∀_h∶B → A (∀_y∶B f[h[y]] == y) → IsEquivalence[f] -->

---

Its recursor takes a function of the four fields:

```wl
TypeTheoryType[InductiveRecursor[IsEquivalence], "HomotopyTypeTheory"]
```

<!-- => ∀_{A ∶ Type u} ∀_{B ∶ Type v} ∀_{f ∶ A → B} ∀_m∶IsEquivalence[f] → Type w (∀_g∶B → A ∀_retraction∶∀_x∶A g[f[x]] == x ∀_h∶B → A ∀_section∶∀_y∶B f[h[y]] == y m[EquivalenceProof[g, retraction, h, section]]) → ∀_t∶IsEquivalence[f] m[t] -->

---

In the cubical environment, it is a definition:

```wl
TypeTheoryEnvironment["Cubical"][IsEquivalence]
```

<!-- => definition IsEquivalence : ∀_{A ∶ Type u} ∀_{B ∶ Type u} (A → B) → Type u := {A ∶ Type u} {B ∶ Type u} (f ∶ A → B) ↦ ∀_y∶B IsContractible[Fiber[f, y]] -->

## Possible Issues

[IsEquivalence]() takes a function, not a type:

```wl
TypeTheoryType[IsEquivalence[Booleans], "HomotopyTypeTheory"]
```

<!-- => Failure["TypeMismatch", ...] -->

---

The prelude has no equivalences:

```wl
TypeTheoryType[IsEquivalence["not"]]
```

<!-- => Failure["ElaborationFailed", ...] -->
