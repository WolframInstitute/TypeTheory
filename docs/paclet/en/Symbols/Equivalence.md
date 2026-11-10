---
Template: Symbol
Name: Equivalence
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Equivalence
Keywords: [equivalence, equivalence of types, types, HoTT, homotopy type theory, univalence, cubical type theory, negation, identity]
SeeAlso: [IsEquivalence, EquivalenceProof, Transport, Fiber, IsContractible, CubicalTransport, GlueType]
RelatedGuides: [TypeTheory]
RelatedTutorials: [HomotopyTypeTheory, CubicalTypeTheory]
---

## Usage

<code>[Equivalence]()[*A*, *B*]</code> is the type of equivalences from *A* to *B*: a function with a proof that it is an equivalence.

## Details & Options

- In <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code>, [Equivalence]() is a structure with the one constructor `"equivalenceIntroduction"`, which takes the function *f* and a proof of <code>[IsEquivalence]()[*f*]</code>; `e["function"]`, or `e[[1]]`, is the function of an equivalence *e* and `e["proof"]`, or `e[[2]]`, the proof, whose parts are the inverses.
- `"identityEquivalence"[A]` is the identity of *A*, and `"negationEquivalence"` is negation, from the Booleans to themselves.
- Univalence identifies the equivalences from *A* to *B* with the paths <code>*A* == *B*</code>. `"equalityToEquivalence"` takes a path to an equivalence, the identity for reflexivity; the axiom `"univalence"` says that this map is an equivalence, `"equivalenceToEquality"`, its right inverse, gives the path of an equivalence, and `"univalenceComputation"` says that the path gives the equivalence back. Since univalence is an axiom there, carrying an element along its path does not compute.
- In <code>[TypeTheoryEnvironment]()["Cubical"]</code>, [Equivalence]() is a definition: the dependent sum of a function and the proof that its fibers are contractible. `"isomorphismEquivalence"` makes one from an inverse, and `"equivalenceToPath"` is univalence, a path of [GlueType]() along which [CubicalTransport]() applies the equivalence by computation.
- The prelude has no [Equivalence](): the proof irrelevance of its Prop contradicts univalence. Terms that use it name one of the two environments.
- For *A* in `Type u` and *B* in `Type v`, <code>[Equivalence]()[*A*, *B*]</code> is in `Type (max u v)` in the HoTT environment; in the cubical one *A* and *B* are in the same universe.

## Basic Examples

The type of [Equivalence](), in the HoTT environment:

```wl
TypeTheoryType[Equivalence, "HomotopyTypeTheory"]
```

<!-- => Type u → Type v → Type (max u v) -->

---

Negation is an equivalence of the Booleans:

```wl
TypeTheoryType["negationEquivalence", "HomotopyTypeTheory"]
```

<!-- => Equivalence[𝔹, 𝔹] -->

---

Its function is negation, applied here to `"true"`:

```wl
WeakHeadNormalForm[TypeTheoryTerm["negationEquivalence"[[1]]["true"], "HomotopyTypeTheory"]]
```

<!-- => false -->

---

A path between types gives an equivalence; reflexivity gives the identity, with the identity as both its inverses:

```wl
WeakHeadNormalForm[TypeTheoryTerm["equalityToEquivalence"["equalityReflexivity"[Booleans]], "HomotopyTypeTheory"]]
```

<!-- => equivalenceIntroduction[(x ∶ 𝔹) ↦ x, EquivalenceProof[(x ∶ 𝔹) ↦ x, (x ∶ 𝔹) ↦ equalityReflexivity[x], (x ∶ 𝔹) ↦ x, (x ∶ 𝔹) ↦ equalityReflexivity[x]]] -->

## Scope

The identity is an equivalence of every type:

```wl
TypeTheoryType["identityEquivalence", "HomotopyTypeTheory"]
```

<!-- => ∀_A∶Type u Equivalence[A, A] -->

---

The inverse of an equivalence is a field of its proof. The right inverse of negation is negation:

```wl
WeakHeadNormalForm[TypeTheoryTerm["negationEquivalence"[[2]][[3]]["true"], "HomotopyTypeTheory"]]
```

<!-- => false -->

---

By univalence, an equivalence gives a path between its types. Negation gives a path from the Booleans to themselves:

```wl
TypeTheoryType["equivalenceToEquality"["negationEquivalence"], "HomotopyTypeTheory"]
```

<!-- => 𝔹 == 𝔹 -->

---

The path gives back the equivalence, up to a path:

```wl
TypeTheoryType["univalenceComputation"["negationEquivalence"], "HomotopyTypeTheory"]
```

<!-- => equalityToEquivalence[equivalenceToEquality[negationEquivalence]] == negationEquivalence -->

---

In the cubical environment, negation is an equivalence too, made from its inverse by `"isomorphismEquivalence"`:

```wl
TypeTheoryEnvironment["Cubical"]["negationEquivalence"]
```

<!-- => definition negationEquivalence : Equivalence[𝔹, 𝔹] := isomorphismEquivalence[not, not, negationInvolution, negationInvolution] -->

## Applications

A path from `"true"` to `"false"` is as good as an element of the empty type [False](). Carrying `"trueIntroduction"` along it, in the family that is [True]() at `"true"` and [False]() at `"false"`, gives an element of [False](), and from [False]() anything follows:

```wl
noPaths = TypeTheoryEnvironment["HomotopyTypeTheory", TypeTheoryDefinition[TrueFalsePathsEmpty, Typed[
    "equivalenceIntroduction"[
        p |-> Transport[b |-> InductiveRecursor[Booleans][TypeUniverse[1] &, False, True, b], p, "trueIntroduction"],
        EquivalenceProof[
            y |-> "falseElimination"[y],
            p |-> "falseElimination"[Transport[b |-> InductiveRecursor[Booleans][TypeUniverse[1] &, False, True, b], p, "trueIntroduction"]],
            y |-> "falseElimination"[y],
            y |-> "falseElimination"[y]
        ]
    ],
    Equivalence["true" == "false", False]
]]]
```

<!-- => TypeTheoryEnvironment summary box: 42 constants -->

By univalence the type of those paths is the empty type:

```wl
TypeTheoryType["equivalenceToEquality"[TrueFalsePathsEmpty], noPaths]
```

<!-- => (true == false) == False -->

## Properties and Relations

In the HoTT environment, [Equivalence]() is an inductive type with one constructor:

```wl
TypeTheoryEnvironment["HomotopyTypeTheory"][Equivalence]
```

<!-- => inductive Equivalence : Type u → Type v → Type (max u v) | equivalenceIntroduction : ∀_{A ∶ Type u} ∀_{B ∶ Type v} ∀_function∶A → B IsEquivalence[function] → Equivalence[A, B] -->

---

In the cubical environment it is a dependent sum, of a function and the contractibility of its fibers:

```wl
TypeTheoryEnvironment["Cubical"][Equivalence]
```

<!-- => definition Equivalence : Type u → Type u → Type u := (A ∶ Type u) (B ∶ Type u) ↦ Σ_f∶A → B IsEquivalence[f] -->

---

There univalence computes: transport along the path that negation gives applies negation:

```wl
WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport["equivalenceToPath"["negationEquivalence"], 0, "true"], "Cubical"]]
```

<!-- => false -->

## Possible Issues

In the HoTT environment univalence is an axiom, so transport along the path of an equivalence stops at it:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Transport[X |-> X, "equivalenceToEquality"["negationEquivalence"], "true"], "HomotopyTypeTheory"]]
```

<!-- => Equal_rec[(z ∶ Type) (q ∶ 𝔹 == z) ↦ ((X ∶ Type) ↦ X)[z], true, equivalenceToEquality[negationEquivalence]] -->

---

The two environments' equivalences differ. A cubical equivalence's proof is a function of the fibers, not a structure with an inverse as third field:

```wl
TypeTheoryType["negationEquivalence"[[2]][[3]], "Cubical"]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

The prelude has no equivalences:

```wl
TypeTheoryType[Equivalence]
```

<!-- => Failure["ElaborationFailed", ...] -->
