---
Template: Symbol
Name: CircleInductionLoop
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/CircleInductionLoop
Keywords: [circle, loop, computation rule, higher inductive type, HoTT]
SeeAlso: [CircleInduction, DependentCongruence, CircleInductionBase]
RelatedGuides: [TypeTheory]
RelatedTutorials: [HomotopyTypeTheory]
---

## Usage

<code>[CircleInductionLoop]()[*P*, *b*, *l*]</code> proves that circle induction gives the path *l* on the loop: <code>[DependentCongruence]()[[CircleInduction]()[*P*, *b*, *l*, #] &, [CircleLoop]()] == *l*</code>.

## Details & Options

- [CircleInductionLoop]() is an axiom: on paths, a higher inductive type computes only up to a path.
- Its statement type-checks only because [CircleInductionBase]() computes: the two sides are paths between `CircleInduction[P, b, l, CircleBase]` and *b*.
- It is a constant of <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code>; terms that use it name that environment.

## Basic Examples

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The statement of [CircleInductionLoop]() in the HoTT environment:

```wl
TypeTheoryCheck[TypeTheoryTerm[CircleInductionLoop, hott]]
```

<!-- => ∀_P∶𝕊¹ → Type u ∀_b∶P[CircleBase] ∀_l∶Transport[P, CircleLoop, b] == b DependentCongruence[(x∶𝕊¹) ↦ CircleInduction[P, b, l, x], CircleLoop] == l -->

## Applications

For the constant family of Booleans, with the path that [TransportConstant]() gives, [CircleInductionLoop]() proves what circle induction gives on the loop.

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The proof:

```wl
TypeTheoryProof[DependentCongruence[Function[{Typed[x, Circle]}, CircleInduction[Function[{Typed[y, Circle]}, Booleans], "true", TransportConstant[CircleLoop, "true"], x]], CircleLoop] == TransportConstant[CircleLoop, "true"], hott, {
    TypeTheoryTactic["Exact", CircleInductionLoop[Function[{Typed[y, Circle]}, Booleans], "true", TransportConstant[CircleLoop, "true"]]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

The two sides of the statement have the same type only because circle induction computes on [CircleBase](), by the rewrite rule [CircleInductionBase]().

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

For the constant family of Booleans, the left side is a path from `CircleInduction[P, b, l, CircleBase]`, carried around the loop, to itself:

```wl
TypeTheoryCheck[TypeTheoryTerm[DependentCongruence[Function[{Typed[x, Circle]}, CircleInduction[Function[{Typed[y, Circle]}, Booleans], "true", TransportConstant[CircleLoop, "true"], x]], CircleLoop], hott]]
```

<!-- => Transport[(y∶𝕊¹) ↦ 𝔹, CircleLoop, CircleInduction[(y∶𝕊¹) ↦ 𝔹, true, TransportConstant[CircleLoop, true], CircleBase]] == CircleInduction[(y∶𝕊¹) ↦ 𝔹, true, TransportConstant[CircleLoop, true], CircleBase] -->

By computation, that is the type of the right side, a path from `"true"`, carried around the loop, to `"true"`:

```wl
DefinitionallyEqualQ[
    TypeTheoryCheck[TypeTheoryTerm[DependentCongruence[Function[{Typed[x, Circle]}, CircleInduction[Function[{Typed[y, Circle]}, Booleans], "true", TransportConstant[CircleLoop, "true"], x]], CircleLoop], hott]],
    TypeTheoryCheck[TypeTheoryTerm[TransportConstant[CircleLoop, "true"], hott]]
]
```

<!-- => True -->

## Possible Issues

On the loop, circle induction does not compute, so `"Reflexivity"` cannot prove what [CircleInductionLoop]() states.

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The statement for the constant family of Booleans, by computation:

```wl
TypeTheoryProof[DependentCongruence[Function[{Typed[x, Circle]}, CircleInduction[Function[{Typed[y, Circle]}, Booleans], "true", TransportConstant[CircleLoop, "true"], x]], CircleLoop] == TransportConstant[CircleLoop, "true"], hott, {
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Failure["NotReflexive", ...] -->
