---
Template: Symbol
Name: EmptySequence
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/EmptySequence
Keywords: [Wolfram Language, Sequence, heterogeneous list, HList, dependent type, arguments, currying]
SeeAlso: [SequencePrepend, {}, Sequence]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, Elaboration]
---

## Usage

[EmptySequence]() is the sequence with no elements, of the type `Sequence[]`.

## Details & Options

- [EmptySequence]() is a constructor of the sequences, in [TypeTheoryEnvironment]()["WolframLanguage"], with [SequencePrepend](). `Sequence[]` writes it, and it shows as `[]`.

## Basic Examples

The empty sequence:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
DefinitionallyEqualQ[TypeTheoryTerm[Sequence[], wolfram], TypeTheoryTerm[EmptySequence, wolfram]]
```

<!-- => True -->
