---
Template: Symbol
Name: SequencePrepend
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/SequencePrepend
Keywords: [Wolfram Language, Sequence, heterogeneous list, HList, dependent type, arguments, currying]
SeeAlso: [Sequences, EmptySequence]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, Elaboration]
---

## Usage

[SequencePrepend]()[*x*, *s*] is the sequence of *x* and then the elements of the sequence *s*.

## Details & Options

- [SequencePrepend]() is a constructor of [Sequences](), in [TypeTheoryEnvironment]()["WolframLanguage"]: for *x* of the type *A* and *s* of the type `Sequences[As]`, it has the type `Sequences[ListPrepend[A, As]]`.
- `Sequence[a, b]` writes `SequencePrepend[a, SequencePrepend[b, EmptySequence]]`.

## Basic Examples

A sequence of a natural number and an expression:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
TypeOf[TypeTheoryTerm[SequencePrepend[1, SequencePrepend[Typed[2, Expressions], EmptySequence]], wolfram]]
```

<!-- => Sequences[{ℕ, Expressions}] -->
