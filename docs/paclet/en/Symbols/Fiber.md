---
Template: Symbol
Name: Fiber
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Fiber
Keywords: [fiber, homotopy fiber, preimage, equivalence, contractible fibers, cubical type theory, path, dependent pair]
SeeAlso: [IsContractible, IsEquivalence, Equivalence, DependentSum]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[Fiber]()[*f*, *y*]</code> is the type of the elements *x* with a path from *f*[*x*] to *y*: <code>[DependentSum]()[*A*, [Function]()[{*x*}, Path[*B*, *f*[*x*], *y*]]]</code>.

## Details & Options

- An element of a fiber is a pair `"dependentPair"[x, p]` of an element *x* and a path *p* from *f*[*x*] to *y*; <code>*w*["first"]</code> and <code>*w*["second"]</code> are the two parts of an element *w*, also <code>*w*[[1]]</code> and <code>*w*[[2]]</code>.
- It is the preimage of *y* up to paths. An equivalence is a function whose fibers are all contractible, [IsContractible](): over each point there is one element, up to paths.
- *A* and *B*, the types of *f*, are implicit, and in the same universe.
- It is a definition of <code>[TypeTheoryEnvironment]()["Cubical"]</code>; terms that use it name that environment.

## Basic Examples

Its definition, in the cubical environment:

```wl
TypeTheoryEnvironment["Cubical"][Fiber]
```

<!-- => definition Fiber : ∀_{A ∶ Type u} ∀_{B ∶ Type u} (A → B) → B → Type u := {A ∶ Type u} {B ∶ Type u} (f ∶ A → B) (y ∶ B) ↦ Σ_x∶A f[x] ≡ y -->

---

The fiber of negation over `"true"`: a Boolean `x` with a path from `"not"[x]` to `"true"`:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Fiber["not", "true"], "Cubical"]]
```

<!-- => Σ_x∶𝔹 !x ≡ true -->

---

`"false"` is in it: `"not"["false"]` computes to `"true"`, so the constant path at `"true"` goes from one to the other:

```wl
TypeTheoryProof[Fiber["not", "true"], "Cubical", {"Exact"["dependentPair"["false", i |-> "true"]]}]
```

<!-- => Proof complete -->

## Scope

The second field of an element is its path:

```wl
TypeTheoryType[Typed[w, Fiber["not", "true"]] |-> w[[2]], "Cubical"]
```

<!-- => ∀_w∶Fiber[not, true] !w〚"first"〛 ≡ true -->

---

A constant function has every element in its fiber over its value. Both Booleans are in the fiber of the constant function at `"true"` over `"true"`, here `"false"`, so that function is no equivalence:

```wl
TypeTheoryType[Typed["dependentPair"["false", Function[{i}, "true"]], Fiber[Typed[b, Booleans] |-> "true", "true"]], "Cubical"]
```

<!-- => Fiber[(b ∶ 𝔹) ↦ true, true] -->

---

The equivalence of negation has contractible fibers, and the center of the fiber over `"true"` pairs `"not"["true"]` with the path `"negationInvolution"["true"]` from its negation to `"true"`:

```wl
WeakHeadNormalForm[TypeTheoryTerm["negationEquivalence"[[2]]["true"][[1]], "Cubical"]]
```

<!-- => 〈!true, negationInvolution[true]〉 ∶ Fiber[negationEquivalence〚"first"〛, true] -->

Its element computes to `"false"`:

```wl
WeakHeadNormalForm[TypeTheoryTerm["negationEquivalence"[[2]]["true"][[1]][[1]], "Cubical"]]
```

<!-- => false -->

## Properties and Relations

The fiber of the identity over a point is contractible, with the point and its constant path as center:

```wl
TypeTheoryProof[IsContractible[Fiber[x |-> x, "true"]], "Cubical", {"Exact"["identityEquivalence"[Booleans][[2]]["true"]]}]
```

<!-- => Proof complete -->

---

Being an equivalence, in the cubical environment, is the contractibility of every fiber:

```wl
WeakHeadNormalForm[TypeTheoryTerm[IsEquivalence["not"], "Cubical"]]
```

<!-- => ∀_y∶𝔹 IsContractible[Fiber[not, y]] -->

## Possible Issues

The path must end at the point. `"not"["true"]` is `"false"`, so the constant path at `"true"` does not put `"true"` in the fiber of negation over `"true"`:

```wl
TypeTheoryType[Typed["dependentPair"["true", Function[{i}, "true"]], Fiber["not", "true"]], "Cubical"]
```

<!-- => Failure["TypeMismatch", ...] -->

---

The two types of the function are in the same universe, so a function from the Booleans to types, which are in the universe above, has no fiber here:

```wl
TypeTheoryType[Fiber[Typed[b, Booleans] |-> Booleans, Booleans], "Cubical"]
```

<!-- => Failure["TypeMismatch", ...] -->

---

[Fiber]() is a definition of the cubical environment only. In the HoTT environment an equivalence is a function with a left and a right inverse, and there are no fibers:

```wl
TypeTheoryType[Fiber, "HomotopyTypeTheory"]
```

<!-- => Failure["ElaborationFailed", ...] -->
