---
Template: Symbol
Name: DependentSum
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/DependentSum
Keywords: [dependent sum, sigma type, dependent pair, pair, fiber, pointed type, family of types, cubical type theory, structure]
SeeAlso: [TypeTheoryCubical, Fiber, IsContractible, Equivalence, Subtype, CartesianProductType]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[DependentSum]()[*A*, *B*]</code> is the dependent sum Σ *x* : *A*, *B*[*x*] of the cubical environment, whose elements are the pairs <code>"dependentPair"[*a*, *b*]</code> of an *a* in *A* and a *b* in *B*[*a*].

## Details & Options

- *B* is a family of types over *A*, a function from *A* to a universe, so the type of the second field depends on the first. A type that does not depend on the first field is written as a [Function]() whose body does not mention its variable.
- It is a structure: <code>*p*[[1]]</code> and <code>*p*[[2]]</code> are the fields of a pair *p*, and they compute on a pair.
- For *A* in `Type u` and *B* into `Type v`, <code>[DependentSum]()[*A*, *B*]</code> is in `Type (max u v)`.
- It is a constant of <code>[TypeTheoryEnvironment]()["Cubical"]</code>, which has no Prop: a property there is a type of paths, so a pair of an element and a path, as an element of a [Fiber](), is an element with a proof of its property. [TypeTheoryCubical]() names it, and the kernel writes the equivalences of Glue types with it, as the cubical library writes [Fiber](), [IsContractible]() and [Equivalence]().
- In the prelude, [Subtype]() pairs an element with a proof of a proposition about it, and [CartesianProductType]() is the sum of a family that does not depend.
- <code>[DependentSum]()[*A*, [Function]()[{[Typed]()[*x*, *A*]}, *B*]]</code> displays as `Σ_x∶A B`, with the binder under Σ as ∀ has it, as Lean writes `(x : A) × B`, and a pair as `〈a, b〉`.

## Basic Examples

The type of [DependentSum](), in the cubical environment:

```wl
TypeTheoryType[DependentSum, "Cubical"]
```

<!-- => ∀_A∶Type u (A → Type v) → Type (max u v) -->

---

A type with an element of it, a pointed type, here the Booleans with `"true"`:

```wl
TypeTheoryType[Typed["dependentPair"[Booleans, "true"], DependentSum[TypeUniverse[1], Typed[A, TypeUniverse[1]] |-> A]], "Cubical"]
```

<!-- => Σ_A∶Type A -->

---

A Boolean whose negation is `"false"`, with the path that shows it, an element of the fiber of `"not"` over `"false"`:

```wl
TypeTheoryType[Typed["dependentPair"["true", Function[{i}, "false"]], Fiber["not", "false"]], "Cubical"]
```

<!-- => Fiber[not, false] -->

## Scope

With a family that does not depend on the first element, the pairs are plain pairs:

```wl
TypeTheoryType[Typed["dependentPair"["true", "false"], DependentSum[Booleans, Typed[b, Booleans] |-> Booleans]], "Cubical"]
```

<!-- => Σ_b∶𝔹 𝔹 -->

---

Its second field:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Typed["dependentPair"["true", "false"], DependentSum[Booleans, Typed[b, Booleans] |-> Booleans]][[2]], "Cubical"]]
```

<!-- => false -->

---

The first field of a pointed type is the type:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Typed["dependentPair"[Booleans, "true"], DependentSum[TypeUniverse[1], Typed[A, TypeUniverse[1]] |-> A]][[1]], "Cubical"]]
```

<!-- => 𝔹 -->

---

The second field of a pointed type is in the first:

```wl
TypeTheoryType[Typed[s, DependentSum[TypeUniverse[1], Typed[A, TypeUniverse[1]] |-> A]] |-> s[[2]], "Cubical"]
```

<!-- => ∀_s∶Σ_A∶Type A s[[1]] -->

---

A family by cases: a Boolean with, for `"false"`, a Boolean, and for `"true"`, a function on Booleans; `"true"` goes with `"not"`:

```wl
TypeTheoryType[Typed["dependentPair"["true", "not"], DependentSum[Booleans, Typed[b, Booleans] |-> InductiveRecursor[Booleans][Typed[t, Booleans] |-> TypeUniverse[1], Booleans, TypeSpecifier[{Booleans} -> Booleans], b]]], "Cubical"]
```

<!-- => Σ_b∶𝔹 𝔹_rec[(t ∶ 𝔹) ↦ Type, 𝔹, 𝔹 → 𝔹, b] -->

---

The second field of that pair is a function, applied here to `"false"`:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Typed["dependentPair"["true", "not"], DependentSum[Booleans, Typed[b, Booleans] |-> InductiveRecursor[Booleans][Typed[t, Booleans] |-> TypeUniverse[1], Booleans, TypeSpecifier[{Booleans} -> Booleans], b]]][[2]]["false"], "Cubical"]]
```

<!-- => true -->

---

A pair nested to the right shows as a triple:

```wl
TypeTheoryTerm[Typed["dependentPair"["true", "dependentPair"["false", "true"]], DependentSum[Booleans, Typed[a, Booleans] |-> DependentSum[Booleans, Typed[b, Booleans] |-> Booleans]]], "Cubical"]
```

<!-- => 〈true, false, true〉 ∶ Σ_a∶𝔹 Σ_b∶𝔹 𝔹 -->

---

Pointed types are in Type 1, the universe above the types they pair:

```wl
TypeTheoryType[DependentSum[TypeUniverse[1], Typed[A, TypeUniverse[1]] |-> A], "Cubical"]
```

<!-- => Type 1 -->

## Applications

A fiber of *f* over *y* is the dependent sum of the elements *x* with a path from `f[x]` to *y*:

```wl
TypeTheoryEnvironment["Cubical"][Fiber]
```

<!-- => definition Fiber : ∀_{A ∶ Type u} ∀_{B ∶ Type u} (A → B) → B → Type u := {A ∶ Type u} {B ∶ Type u} (f ∶ A → B) (y ∶ B) ↦ Σ_x∶A f[x] ≡ y -->

---

An equivalence is the dependent sum of a function and the proof that it is an equivalence:

```wl
TypeTheoryEnvironment["Cubical"][Equivalence]
```

<!-- => definition Equivalence : Type u → Type u → Type u := (A ∶ Type u) (B ∶ Type u) ↦ Σ_f∶A → B IsEquivalence[f] -->

The first field of the equivalence of negation is negation, which computes:

```wl
WeakHeadNormalForm[TypeTheoryTerm["negationEquivalence"[[1]]["true"], "Cubical"]]
```

<!-- => false -->

## Properties and Relations

Its declaration, an inductive type with the one constructor `"dependentPair"`:

```wl
TypeTheoryEnvironment["Cubical"][DependentSum]
```

<!-- => inductive DependentSum : ∀_A∶Type u (A → Type v) → Type (max u v) | dependentPair : ∀_{A ∶ Type u} ∀_{B ∶ A → Type v} ∀_a∶A B[a] → DependentSum[A, B] -->

---

Its recursor takes a function of the two fields:

```wl
TypeTheoryType[InductiveRecursor[DependentSum], "Cubical"]
```

<!-- => ∀_{A ∶ Type u} ∀_{B ∶ A → Type v} ∀_m∶DependentSum[A, B] → Type w (∀_a∶A ∀_b∶B[a] m[〈a, b〉]) → ∀_t∶DependentSum[A, B] m[t] -->

---

In the prelude, [Subtype]() is the dependent sum of a number and a proof of a proposition about it:

```wl
TypeTheoryType[Typed["subtype"[3, "equalityReflexivity"[6]], Subtype[Typed[n, Naturals] |-> n + n == 6]]]
```

<!-- => {n ∶ ℕ // n + n == 6} -->

## Possible Issues

The prelude does not have it, so a term that uses it names the cubical environment:

```wl
TypeTheoryType[DependentSum]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

The second argument is a family, a function, not a type:

```wl
TypeTheoryType[DependentSum[Booleans, Booleans], "Cubical"]
```

<!-- => Failure["TypeMismatch", ...] -->

---

The second field has the type the family gives at the first: for `"true"`, a function, not a Boolean:

```wl
TypeTheoryType[Typed["dependentPair"["true", "true"], DependentSum[Booleans, Typed[b, Booleans] |-> InductiveRecursor[Booleans][Typed[t, Booleans] |-> TypeUniverse[1], Booleans, TypeSpecifier[{Booleans} -> Booleans], b]]], "Cubical"]
```

<!-- => Failure["TypeMismatch", ...] -->

---

The negation of `"false"` is `"true"`, so the constant path at `"false"` does not put it in the fiber over `"false"`:

```wl
TypeTheoryType[Typed["dependentPair"["false", Function[{i}, "false"]], Fiber["not", "false"]], "Cubical"]
```

<!-- => Failure["TypeMismatch", ...] -->

---

The cubical environment has no Prop, so a family cannot take its values there:

```wl
TypeTheoryType[DependentSum[Booleans, Typed[b, Booleans] |-> TypeUniverse[0]], "Cubical"]
```

<!-- => Failure["NoProp", ...] -->
