---
Template: Symbol
Name: DependentCongruence
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/DependentCongruence
Keywords: [dependent congruence, apd, path, HoTT, homotopy type theory]
SeeAlso: [Transport, EqualityCongruence, CircleInductionLoop]
RelatedGuides: [TypeTheory]
RelatedTutorials: [HomotopyTypeTheory]
---

## Usage

<code>[DependentCongruence]()[*f*, *p*]</code> is the path <code>[Transport]()[*P*, *p*, *f*[*x*]] == *f*[*y*]</code> that a dependent function *f* : <code>(*x* : *A*) -> *P*[*x*]</code> gives from a path *p* : <code>*x* == *y*</code>.

## Details & Options

- [DependentCongruence]() is a definition by path induction; on reflexivity it is reflexivity. It is what the HoTT book writes `apd f p`.
- *P* is implicit and found from the type of *f*.
- [CircleInductionLoop]() says what it gives for circle induction on [CircleLoop]().
- It is a constant of <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code>; terms that use it name that environment.

## Basic Examples

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The statement of [DependentCongruence]() in the HoTT environment:

```wl
TypeTheoryCheck[TypeTheoryTerm[DependentCongruence, hott]]
```

<!-- => ∀_{A ∶ Type u} ∀_{P ∶ A → Type v} ∀_f∶∀_z∶A P[z] ∀_{x ∶ A} ∀_{y ∶ A} ∀_p∶x == y Transport[P, p, f[x]] == f[y] -->

## Scope

On reflexivity, [DependentCongruence]() is reflexivity, by computation.

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

For the function on the circle that is `"true"` everywhere, at the reflexivity of [CircleBase]():

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[DependentCongruence[Function[{Typed[x, Circle]}, "true"], EqualityReflexivity[CircleBase]], hott],
    TypeTheoryTerm[EqualityReflexivity["true"], hott]
]
```

<!-- => True -->

## Applications

[DependentCongruence]() of the function that is `"true"` everywhere proves that carrying `"true"` around the loop of the circle gives `"true"`.

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The proof:

```wl
TypeTheoryProof[Transport[Function[{Typed[x, Circle]}, Booleans], CircleLoop, "true"] == "true", hott, {
    TypeTheoryTactic["Exact", DependentCongruence[Function[{Typed[x, Circle]}, "true"], CircleLoop]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

For a function whose values do not depend on the point, [EqualityCongruence]() gives a path between the values, and [DependentCongruence]() a path from the first value carried along the path.

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The dependent congruence of the function that is `"true"` everywhere, along the loop:

```wl
TypeTheoryCheck[TypeTheoryTerm[DependentCongruence[Function[{Typed[x, Circle]}, "true"], CircleLoop], hott]]
```

<!-- => Transport[(x∶𝕊¹) ↦ 𝔹, CircleLoop, true] == true -->

[EqualityCongruence]() of the same function along the loop:

```wl
TypeTheoryCheck[TypeTheoryTerm[EqualityCongruence[Function[{Typed[x, Circle]}, "true"], CircleLoop], hott]]
```

<!-- => true == true -->

## Possible Issues

[DependentCongruence]() is a definition of the HoTT environment. A term without an environment is in the prelude, which does not have it.

The type of [DependentCongruence](), in the prelude:

```wl
TypeTheoryCheck[TypeTheoryTerm[DependentCongruence]]
```

<!-- => Failure["ElaborationFailed", ...] -->
