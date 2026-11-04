---
Template: Symbol
Name: SequencePrepend
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/SequencePrepend
Keywords: [Wolfram Language, Sequence, heterogeneous list, HList, dependent type, arguments, currying]
SeeAlso: [EmptySequence, Prepend, Sequence]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, Elaboration]
---

## Usage

[SequencePrepend]()[*x*, *s*] is the sequence of *x* and then the elements of the sequence *s*.

## Details & Options

- [SequencePrepend]() is a constructor of the sequences, in [TypeTheoryEnvironment]()["WolframLanguage"]: for *x* of the type *A* and *s* of the type `Sequence[As]`, *As* the list of the types of its elements, it has the type `Sequence[Prepend[A][As]]`.
- `Sequence[a, b]` writes `SequencePrepend[a, SequencePrepend[b, EmptySequence]]`, and shows as `[a, b]`.
- `Sequence` is a type and its elements alike. Where a type is expected, `Sequence[A, B]` is the type of the sequences of an element of *A* and then of *B*, a list of elements of different types whose type gives their number and types, as Lean's `HList`; elsewhere `Sequence[a, b]` is a sequence. One argument that is a list of types, as *As*, is the list of the types itself.
- A Wolfram Language function is applied to a sequence, so a binder of a type `Sequence[...]` takes the arguments of an application that are left as one sequence: a function of the type `Sequence[A, B] -> C` is applied as `f[a, b]`, and is another function than one of the curried type `A -> B -> C`.

## Basic Examples

A sequence of a natural number and an expression:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
TypeOf[TypeTheoryTerm[SequencePrepend[1, SequencePrepend[Typed[2, Expressions], EmptySequence]], wolfram]]
```

<!-- => Sequence[ℕ, Expressions] -->

## Scope

A function of a sequence of two natural numbers takes its arguments as one sequence, and the type gives how many:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
pairs = TypeTheoryEnvironment[wolfram, {TypeTheoryAxiom[sum, Sequence[NonNegativeIntegers, NonNegativeIntegers] -> NonNegativeIntegers]}];
{
    DefinitionallyEqualQ[TypeTheoryTerm[sum[3, 4], pairs], TypeTheoryTerm[sum[SequencePrepend[3, SequencePrepend[4, EmptySequence]]], pairs]],
    FailureQ[TypeTheoryCheck[TypeTheoryTerm[sum[3], pairs]]]
}
```

<!-- => {True, True} -->
