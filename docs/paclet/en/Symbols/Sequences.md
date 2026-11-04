---
Template: Symbol
Name: Sequences
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Sequences
Keywords: [Wolfram Language, Sequence, heterogeneous list, HList, dependent type, arguments, currying]
SeeAlso: [EmptySequence, SequencePrepend, Lists, CartesianProductType]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, Elaboration]
---

## Usage

[Sequences]()[{*A*, *B*, ...}] is the type of the sequences `Sequence[a, b, ...]` of an element of *A*, then of *B*, and so on.

## Details & Options

- [Sequences]() is an inductive family of [TypeTheoryEnvironment]()["WolframLanguage"], indexed by the list of the types of its elements, as Lean's `HList`: its type gives the length of a sequence and the type of each element. It has the constructors [EmptySequence]() and [SequencePrepend](), and `Sequence[a, b, ...]` writes them, as `{a, b, ...}` writes a list.
- The types of the elements are of one universe, `TypeUniverse[u + 1]`, and the sequences a universe above, `TypeUniverse[u + 2]`.
- A Wolfram Language function is applied to a sequence: `f[a, b]` gives `f` the sequence of `a` and `b`. So a binder of a type [Sequences]()[...] takes the arguments of an application that are left as one `Sequence`, and a function of the type `Sequences[{A, B}] -> C` is applied as `f[a, b]`, another function than one of the curried type `A -> B -> C`, which is applied as `f[a][b]`.
- One argument that is a sequence already is the sequence itself, and a `Sequence` among the elements of a `Sequence` is spliced, as the Wolfram Language splices it.

## Basic Examples

A sequence of two natural numbers:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
TypeOf[TypeTheoryTerm[Sequence[1, 2], wolfram]]
```

<!-- => Sequences[{ℕ, ℕ}] -->

## Scope

A function of a sequence of two natural numbers takes its arguments as one sequence, and the type gives how many:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
firsts = TypeTheoryEnvironment[wolfram, {
    TypeTheoryDefinition[first, Function[{Typed[s, Sequences[{NonNegativeIntegers, NonNegativeIntegers}]]},
        InductiveRecursor[Sequences][
            Function[{Typed[types, Lists[TypeUniverse[1]]], Typed[t, Sequences[types]]}, NonNegativeIntegers],
            0,
            Function[{TypedImplicit[A, TypeUniverse[1]], TypedImplicit[As, Lists[TypeUniverse[1]]], Typed[x, A], Typed[xs, Sequences[As]], Typed[r, NonNegativeIntegers]}, 1],
            s
        ]
    ]]
}];
{
    DefinitionallyEqualQ[TypeTheoryTerm[first[3, 4], firsts], TypeTheoryTerm[first[Sequence[3, 4]], firsts]],
    FailureQ[TypeTheoryCheck[TypeTheoryTerm[first[3], firsts]]]
}
```

<!-- => {True, True} -->
