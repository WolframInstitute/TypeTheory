---
Template: Symbol
Name: TypeTheoryCubical
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryCubical
Keywords: [cubical type theory, interval, path, transport, composition, Glue type, univalence, function extensionality, declaration, kernel, CCHM]
SeeAlso: [TypeTheoryRules, CubicalTransport, CubicalComposition, GlueType, DependentSum, TypeTheoryEnvironment]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[TypeTheoryCubical]()[*sum*]</code> declares the primitives of cubical type theory, when added to a [TypeTheoryEnvironment]() whose rules are cubical: the interval, `Interval`, with [IntervalZero](), [IntervalOne](), [IntervalMeet](), [IntervalJoin]() and [IntervalReverse](), the path types `Path[A, a, b]`, [CubicalTransport](), [CubicalComposition](), [GlueType](), [GlueIntroduction]() and [GlueElimination]().

## Details & Options

- The rules must have `"Cubical" -> True`, no Prop and no quantities, as <code>[TypeTheoryRules]()["CubicalTypeTheory"]</code> does: Prop's proof irrelevance contradicts univalence.
- *sum* is the dependent sum, declared before: a structure of the type <code>[ForAll]()[{[Typed]()[*A*, [TypeUniverse]()[*u* + 1]], [Typed]()[*B*, *A* -> [TypeUniverse]()[*v* + 1]]}, [TypeUniverse]()[[Max]()[*u* + 1, *v* + 1]]]</code> whose constructor takes *a* and *b* : *B*[*a*]. The kernel writes the type of equivalences with it, for Glue types.
- The interval is a pretype: no type of a universe, so only a function or a path may take an element of it. A function of the interval into a type is a path between its values at 0 and 1, and the kernel gives it that path type. `0` and `1` stand for the endpoints, and [Min](), [Max]() and `1 - i` for the meet, the join and the reversal.
- The kernel checks the primitives by rules of their own, and computes them as cubical type theory does; [CubicalTransport]() and [CubicalComposition]() describe the rules. Nothing about them is an axiom.
- The primitives are part of the trusted kernel. <code>[TypeTheoryEnvironment]()["Cubical"]</code> declares them with a small library, in which univalence computes.

## Basic Examples

Cubical rules, a dependent sum and the primitives:

```wl
primitives = TypeTheoryEnvironment[TypeTheoryRules["CubicalTypeTheory"], {
    TypeTheoryInductiveType[DependentSum, ForAll[{Typed[A, TypeUniverse[u + 1]], Typed[B, TypeSpecifier[{A} -> TypeUniverse[v + 1]]]}, TypeUniverse[Max[u + 1, v + 1]]], {
        "dependentPair" -> ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeSpecifier[{A} -> TypeUniverse[v + 1]]], Typed[a, A], Typed[b, B[a]]}, DependentSum[A, B]]
    }],
    TypeTheoryCubical[DependentSum]
}]
```

<!-- => TypeTheoryEnvironment summary box: 15 constants -->

The constants the declaration adds:

```wl
Drop[Keys[primitives], 3]
```

<!-- => {Interval, IntervalZero, IntervalOne, IntervalMeet, IntervalJoin, IntervalReverse, Path, CubicalTransport, CubicalComposition, GlueType, GlueIntroduction, GlueElimination} -->

The type of a path type, over a line of types, a function of the interval:

```wl
TypeTheoryType[Path, primitives]
```

<!-- => ∀_A∶Interval → Sort u A[0] → A[1] → Sort u -->

---

The cubical environment declares the primitives with a small library:

```wl
TypeTheoryEnvironment["Cubical"][Interval]
```

<!-- => TypeTheoryCubical[DependentSum] -->

## Scope

A constant function of the interval is a path, from its value to itself:

```wl
TypeTheoryType[Typed[i, Interval] |-> "true", "Cubical"]
```

<!-- => true ≡ true -->

---

A path applied to an endpoint computes to the endpoint of its type:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[{x, y, Typed[p, Path[Booleans, x, y]]} |-> p[1], "Cubical"],
    TypeTheoryTerm[{x, y, Typed[p, Path[Booleans, x, y]]} |-> y, "Cubical"]
]
```

<!-- => True -->

---

A path reversed, by the reversal `1 - i` of the interval, goes the other way:

```wl
TypeTheoryType[{x, y, Typed[p, Path[Booleans, x, y]]} |-> (Typed[i, Interval] |-> p[1 - i]), "Cubical"]
```

<!-- => ∀_x∶𝔹 ∀_y∶𝔹 x ≡ y → y ≡ x -->

---

Transport along a constant line of functions of Booleans computes, by the type:

```wl
WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport[i |-> TypeSpecifier[{Booleans} -> Booleans], 0, "not"]["true"], "Cubical"]]
```

<!-- => false -->

---

A composition is its side at 1 where a face holds:

```wl
WeakHeadNormalForm[TypeTheoryTerm[CubicalComposition[Booleans, j |-> {1 -> "true"}, "true"], "Cubical"]]
```

<!-- => true -->

---

Function extensionality is a term: a path between functions from a path at each argument, here between double negation and the identity:

```wl
TypeTheoryType["pathFunctionExtensionality"[b |-> "negationInvolution"[b]], "Cubical"]
```

<!-- => ((b ∶ 𝔹) ↦ !!b) ≡ ((b ∶ 𝔹) ↦ b) -->

---

Univalence computes: transport along the path of an equivalence applies it, here negation:

```wl
WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport["equivalenceToPath"["negationEquivalence"], 0, "true"], "Cubical"]]
```

<!-- => false -->

## Properties and Relations

The primitives add no axiom:

```wl
Information[TypeTheoryEnvironment["Cubical"], "Axioms"]
```

<!-- => {} -->

---

The cubical environment follows the rules of cubical type theory:

```wl
Information[TypeTheoryEnvironment["Cubical"], "Rules"] === TypeTheoryRules["CubicalTypeTheory"]
```

<!-- => True -->

---

The twelve constants are of their own kind, and come from one declaration:

```wl
Information[TypeTheoryEnvironment["Cubical"], "Kinds"]["Cubical"]
```

<!-- => 12 -->

---

Cubical rules, a dependent sum and the primitives:

```wl
primitives = TypeTheoryEnvironment[TypeTheoryRules["CubicalTypeTheory"], {
    TypeTheoryInductiveType[DependentSum, ForAll[{Typed[A, TypeUniverse[u + 1]], Typed[B, TypeSpecifier[{A} -> TypeUniverse[v + 1]]]}, TypeUniverse[Max[u + 1, v + 1]]], {
        "dependentPair" -> ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeSpecifier[{A} -> TypeUniverse[v + 1]]], Typed[a, A], Typed[b, B[a]]}, DependentSum[A, B]]
    }],
    TypeTheoryCubical[DependentSum]
}]
```

<!-- => TypeTheoryEnvironment summary box: 15 constants -->

[TypeTheoryCheck]() replays the declaration and compares the twelve records:

```wl
TypeTheoryCheck[primitives]
```

<!-- => Success["EnvironmentChecked", ...] -->

## Possible Issues

The rules of the prelude are not cubical:

```wl
TypeTheoryEnvironment[{TypeTheoryCubical[DependentSum]}]
```

<!-- => Failure["CubicalNotAllowed", ...] -->

---

Nor are those of Martin-Löf type theory, without the setting `"Cubical"`:

```wl
TypeTheoryEnvironment[TypeTheoryRules["MartinLofTypeTheory"], {TypeTheoryCubical[DependentSum]}]
```

<!-- => Failure["CubicalNotAllowed", ...] -->

---

The dependent sum must be declared first:

```wl
TypeTheoryEnvironment[TypeTheoryRules["CubicalTypeTheory"], {TypeTheoryCubical[DependentSum]}]
```

<!-- => Failure["SumExpected", ...] -->

---

A pair whose second type does not depend on the first is not a dependent sum:

```wl
TypeTheoryEnvironment[TypeTheoryRules["CubicalTypeTheory"], {
    TypeTheoryInductiveType[Pair, ForAll[{Typed[A, TypeUniverse[u + 1]], Typed[B, TypeUniverse[v + 1]]}, TypeUniverse[Max[u + 1, v + 1]]], {
        "pair" -> ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[v + 1]], Typed[a, A], Typed[b, B]}, Pair[A, B]]
    }],
    TypeTheoryCubical[Pair]
}]
```

<!-- => Failure["SumExpected", ...] -->

---

The interval is no type, so nothing is declared of it:

```wl
TypeTheoryEnvironment["Cubical", {TypeTheoryAxiom[IntervalPoint, Interval]}]
```

<!-- => Failure["TypeExpected", ...] -->

---

The cubical environment has the primitives already:

```wl
TypeTheoryEnvironment["Cubical", {TypeTheoryCubical[DependentSum]}]
```

<!-- => Failure["AlreadyDeclared", ...] -->
