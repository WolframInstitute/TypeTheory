---
Template: Symbol
Name: IsContractible
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IsContractible
Keywords: [contractible, center, contraction, singleton, equivalence, contractible fibers, cubical type theory, Glue type]
SeeAlso: [Fiber, IsEquivalence, Equivalence, DependentSum, GlueType]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[IsContractible]()[*X*]</code> is the type of an element *c* of *X*, its center, with a path from *c* to every element.

## Details & Options

- [IsContractible]() is a definition, <code>[DependentSum]()[*X*, [Function]()[{*c*}, [ForAll]()[{[Typed]()[*z*, *X*]}, Path[*X*, *c*, *z*]]]]</code>; for a proof *k*, <code>*k*["first"]</code>, or <code>*k*[[1]]</code>, is the center and <code>*k*["second"]</code>, or <code>*k*[[2]]</code>, the function that gives the path from it to each element.
- A contractible type has one element up to paths: any two of its elements are joined by a path, through the center.
- In the cubical environment, [IsEquivalence]() asks every fiber of a function to be contractible. The kernel writes the same type for the fibers of the equivalences of Glue types, and transport in a Glue type uses their centers.
- It is a definition of <code>[TypeTheoryEnvironment]()["Cubical"]</code>; terms that use it name that environment.

## Basic Examples

Its definition, in the cubical environment:

```wl
TypeTheoryEnvironment["Cubical"][IsContractible]
```

<!-- => definition IsContractible : Type u → Type u := (A ∶ Type u) ↦ Σ_c∶A ∀_z∶A c ≡ z -->

---

The Booleans with a path from `"true"` are contractible: the center is `"true"` with its constant path, and the path to a pair of `x` and `p` follows `p`, with the path from `"true"` along `p` to the point it has reached:

```wl
TypeTheoryProof[IsContractible[DependentSum[Booleans, x |-> Path[Booleans, "true", x]]], "Cubical", {
    "Exact"["dependentPair"[
        "dependentPair"["true", Function[{j}, "true"]],
        w |-> Function[{i}, "dependentPair"[w[[2]][i], Function[{j}, w[[2]][Min[i, j]]]]]
    ]]
}]
```

<!-- => Proof complete -->

---

The fibers of an equivalence are contractible. `"identityEquivalence"` proves it for the fiber of the identity of the Booleans over `"true"`:

```wl
TypeTheoryProof[IsContractible[Fiber[x |-> x, "true"]], "Cubical", {"Exact"["identityEquivalence"[Booleans][[2]]["true"]]}]
```

<!-- => Proof complete -->

## Scope

What [IsContractible]() says of the Booleans, unfolded: an element `c` with a path from `c` to every Boolean. The Booleans are not contractible, as Possible Issues shows:

```wl
WeakHeadNormalForm[TypeTheoryTerm[IsContractible[Booleans], "Cubical"]]
```

<!-- => Σ_c∶𝔹 ∀_z∶𝔹 c ≡ z -->

---

The center of the fiber of the identity over `"true"` is `"true"` with the constant path:

```wl
WeakHeadNormalForm[TypeTheoryTerm["identityEquivalence"[Booleans][[2]]["true"][[1]], "Cubical"]]
```

<!-- => 〈true, (j ∶ Interval) ↦ true〉 ∶ Fiber[identityEquivalence[𝔹]〚"first"〛, true] -->

---

The proof that negation is an equivalence gives, over `"true"`, a proof that its fiber is contractible:

```wl
TypeTheoryType["negationEquivalence"[[2]]["true"], "Cubical"]
```

<!-- => IsContractible[Fiber[negationEquivalence〚"first"〛, true]] -->

## Properties and Relations

Any two elements of a contractible type are joined by a path: the path from the center to one, reversed, then the path from the center to the other:

```wl
TypeTheoryType[
    {TypedImplicit[A, TypeUniverse[1]], Typed[k, IsContractible[A]], x, y} |-> "pathTransitivity"["pathSymmetry"[k[[2]][x]], k[[2]][y]],
    "Cubical"
]
```

<!-- => ∀_{A ∶ Type} IsContractible[A] → ∀_x∶A ∀_y∶A x ≡ y -->

---

In the cubical environment, [IsEquivalence]() asks every fiber of a function to be contractible. What it says of negation:

```wl
WeakHeadNormalForm[TypeTheoryTerm[IsEquivalence["not"], "Cubical"]]
```

<!-- => ∀_y∶𝔹 IsContractible[Fiber[not, y]] -->

## Possible Issues

The Booleans are not contractible: the constant path at `"true"` goes nowhere else, so it is no path from the center `"true"` to every Boolean:

```wl
TypeTheoryType[Typed["dependentPair"["true", z |-> Function[{i}, "true"]], IsContractible[Booleans]], "Cubical"]
```

<!-- => Failure["TypeMismatch", ...] -->

---

A term without an environment is in the default environment, the prelude, which has no [IsContractible](): there it is a Wolfram Language expression, of type `Expressions`, not the proposition:

```wl
TypeTheoryType[IsContractible[Booleans]]
```

<!-- => Expressions -->
