---
Template: Symbol
Name: TypeTheoryCubical
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryCubical
Keywords: [cubical type theory, interval, path, Glue type, univalence, declaration, kernel]
SeeAlso: [TypeTheoryRules, CubicalTransport, CubicalComposition, GlueType, TypeTheoryEnvironment]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[TypeTheoryCubical]()[*sum*]</code> declares the primitives of cubical type theory, when added to a [TypeTheoryEnvironment]() whose rules are cubical: the interval, `Interval`, with [IntervalZero](), [IntervalOne](), [IntervalMeet](), [IntervalJoin]() and [IntervalReverse](), the path types `Path[A, a, b]`, [CubicalTransport](), [CubicalComposition](), [GlueType](), [GlueIntroduction]() and [GlueElimination]().

## Details & Options

- The rules must have `"Cubical" -> True`, no Prop and no quantities, as <code>[TypeTheoryRules]()["CubicalTypeTheory"]</code> does: Prop's proof irrelevance contradicts univalence.
- *sum* is the dependent sum, declared before: a structure of the type <code>[ForAll]()[{[Typed]()[*A*, [TypeUniverse]()[*u* + 1]], [Typed]()[*B*, *A* -> [TypeUniverse]()[*v* + 1]]}, [TypeUniverse]()[[Max]()[*u* + 1, *v* + 1]]]</code> whose constructor takes *a* and *b* : *B*[*a*]. The kernel writes the type of equivalences with it, for Glue types.
- The interval is a pretype: no type of a universe, so only a function or a path may take an element of it. A function of the interval is a path between its values at 0 and 1, and the kernel gives it that path type.
- The kernel checks the primitives by rules of their own, and computes them as cubical type theory does; [CubicalTransport]() and [CubicalComposition]() describe the rules. Nothing about them is an axiom.
- The primitives are part of the trusted kernel. <code>[TypeTheoryEnvironment]()["Cubical"]</code> declares them with a small library.

## Basic Examples

Cubical rules, a dependent sum and the primitives:

```wl
primitives = TypeTheoryEnvironment[TypeTheoryRules["CubicalTypeTheory"], {
    TypeTheoryInductiveType[DependentSum, ForAll[{Typed[A, TypeUniverse[u + 1]], Typed[B, TypeSpecifier[{A} -> TypeUniverse[v + 1]]]}, TypeUniverse[Max[u + 1, v + 1]]], {
        DependentPair -> ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeSpecifier[{A} -> TypeUniverse[v + 1]]], Typed[a, A], Typed[b, B[a]]}, DependentSum[A, B]]
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

## Possible Issues

The rules of the prelude are not cubical:

```wl
TypeTheoryEnvironment[{TypeTheoryCubical[DependentSum]}]
```

<!-- => Failure["CubicalNotAllowed", ...] -->
