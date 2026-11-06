---
Template: Symbol
Name: EquivalenceProof
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/EquivalenceProof
Keywords: [equivalence, proof, inverse, left inverse, right inverse, retraction, section, bi-invertible, HoTT, homotopy type theory]
SeeAlso: [IsEquivalence, Equivalence, Transport]
RelatedGuides: [TypeTheory]
RelatedTutorials: [HomotopyTypeTheory]
---

## Usage

<code>[EquivalenceProof]()[*g*, *retraction*, *h*, *section*]</code> proves <code>[IsEquivalence]()[*f*]</code> from a function *g* with <code>*g*[*f*[*x*]] == *x*</code> for every *x*, and a function *h* with <code>*f*[*h*[*y*]] == *y*</code> for every *y*.

## Details & Options

- [EquivalenceProof]() is the constructor of [IsEquivalence]() in <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code>; terms that use it name that environment.
- *f* and its types are implicit, found from the types of the paths, or from the type [Typed]() gives.
- *g* is a left inverse and *h* a right inverse, each with its path for every element; they need not be the same function. <code>*e*[[1]]</code> to <code>*e*[[4]]</code> are the four fields of a proof *e*.
- The paths are functions that give a path for every element. Where the composite does not compute to the element, as `"not"["not"[b]]` for a variable `b`, a proof by cases gives each path.
- With `"equivalenceIntroduction"` it makes an [Equivalence]().
- The cubical environment has no [EquivalenceProof](): there an equivalence has contractible fibers, and `"isomorphismEquivalence"` builds one from the same data, an inverse with a path on each side.

## Basic Examples

The statement of [EquivalenceProof](), in the HoTT environment:

```wl
TypeTheoryType[EquivalenceProof, "HomotopyTypeTheory"]
```

<!-- => ∀_{A ∶ Type u} ∀_{B ∶ Type v} ∀_{f ∶ A → B} ∀_g∶B → A (∀_x∶A g[f[x]] == x) → ∀_h∶B → A (∀_y∶B f[h[y]] == y) → IsEquivalence[f] -->

---

Negation is its own inverse on both sides. The path from `"not"["not"[b]]` to `b` is by cases on `b`, reflexivity for each Boolean:

```wl
TypeTheoryType[EquivalenceProof[
    "not",
    b |-> InductiveRecursor[Booleans][t |-> "not"["not"[t]] == t, "equalityReflexivity"["false"], "equalityReflexivity"["true"], b],
    "not",
    b |-> InductiveRecursor[Booleans][t |-> "not"["not"[t]] == t, "equalityReflexivity"["false"], "equalityReflexivity"["true"], b]
], "HomotopyTypeTheory"]
```

<!-- => IsEquivalence[not] -->

---

The identity of the Booleans is its own inverse, and the paths are reflexivity; *f* is found from them:

```wl
TypeTheoryType[
    EquivalenceProof[Typed[x, Booleans] |-> x, x |-> "equalityReflexivity"[x], x |-> x, x |-> "equalityReflexivity"[x]],
    "HomotopyTypeTheory"
]
```

<!-- => IsEquivalence[(x ∶ 𝔹) ↦ x] -->

## Scope

The equivalence of negation is made from such a proof:

```wl
TypeTheoryEnvironment["HomotopyTypeTheory"]["negationEquivalence"]
```

<!-- => definition negationEquivalence : Equivalence[𝔹, 𝔹] := equivalenceIntroduction[not, EquivalenceProof[not, (b ∶ 𝔹) ↦ 𝔹_rec[(t ∶ 𝔹) ↦ !!t == t, equalityReflexivity[false], equalityReflexivity[true], b], not, (b ∶ 𝔹) ↦ 𝔹_rec[(t ∶ 𝔹) ↦ !!t == t, equalityReflexivity[false], equalityReflexivity[true], b]]] -->

---

The first field is the left inverse, which takes `"false"` back to `"true"`:

```wl
WeakHeadNormalForm[TypeTheoryTerm["negationEquivalence"[[2]][[1]]["false"], "HomotopyTypeTheory"]]
```

<!-- => true -->

---

The second field is the path for each element; at `"true"` it is the case for `"true"`, reflexivity:

```wl
WeakHeadNormalForm[TypeTheoryTerm["negationEquivalence"[[2]][[2]]["true"], "HomotopyTypeTheory"]]
```

<!-- => equalityReflexivity[true] -->

---

The fourth field of any proof is the path that makes the third a right inverse:

```wl
TypeTheoryType[{Typed[f, TypeSpecifier[{Booleans} -> Booleans]], Typed[e, IsEquivalence[f]]} |-> e[[4]], "HomotopyTypeTheory"]
```

<!-- => ∀_f∶𝔹 → 𝔹 ∀_e∶IsEquivalence[f] ∀_y∶𝔹 f[e〚3〛[y]] == y -->

## Applications

With `"equivalenceIntroduction"`, it makes an equivalence. The identity of the Booleans as an equivalence:

```wl
TypeTheoryType["equivalenceIntroduction"[
    Function[{Typed[x, Booleans]}, x],
    EquivalenceProof[x |-> x, x |-> "equalityReflexivity"[x], x |-> x, x |-> "equalityReflexivity"[x]]
], "HomotopyTypeTheory"]
```

<!-- => Equivalence[𝔹, 𝔹] -->

---

The paths from `"true"` to `"false"` are equivalent to the empty type. A path carries `"trueIntroduction"` to an element of [False](), along the family that is [True]() at `"true"` and [False]() at `"false"`; back, and for both paths, `"falseElimination"` gives anything from an element of [False]():

```wl
TypeTheoryType[Typed["equivalenceIntroduction"[
    p |-> Transport[b |-> InductiveRecursor[Booleans][TypeUniverse[1] &, False, True, b], p, "trueIntroduction"],
    EquivalenceProof[
        y |-> "falseElimination"[y],
        p |-> "falseElimination"[Transport[b |-> InductiveRecursor[Booleans][TypeUniverse[1] &, False, True, b], p, "trueIntroduction"]],
        y |-> "falseElimination"[y],
        y |-> "falseElimination"[y]
    ]
], Equivalence["true" == "false", False]], "HomotopyTypeTheory"]
```

<!-- => Equivalence[true == false, False] -->

## Properties and Relations

In the cubical environment, `"isomorphismEquivalence"` takes the same data, an inverse and a path on each side, and builds the contractible fibers:

```wl
TypeTheoryType["isomorphismEquivalence", "Cubical"]
```

<!-- => ∀_{A ∶ Type u} ∀_{B ∶ Type u} ∀_f∶A → B ∀_g∶B → A (∀_b∶B f[g[b]] ≡ b) → (∀_a∶A g[f[a]] ≡ a) → Equivalence[A, B] -->

## Possible Issues

The paths must hold for every element. For a variable `b`, `"not"["not"[b]]` does not compute to `b`, so reflexivity is refused; a proof by cases gives the path:

```wl
TypeTheoryType[Typed[EquivalenceProof["not", b |-> "equalityReflexivity"[b], "not", b |-> "equalityReflexivity"[b]], IsEquivalence["not"]], "HomotopyTypeTheory"]
```

<!-- => Failure["TypeMismatch", ...] -->

---

The cubical environment has an [IsEquivalence]() of its own, contractible fibers, and no [EquivalenceProof]():

```wl
TypeTheoryType[EquivalenceProof, "Cubical"]
```

<!-- => Failure["ElaborationFailed", ...] -->
