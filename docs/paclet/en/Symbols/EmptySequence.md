---
Template: Symbol
Name: EmptySequence
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/EmptySequence
Keywords: [Wolfram Language, Sequence, heterogeneous list, HList, dependent type, arguments, currying]
SeeAlso: [Sequences, SequencePrepend]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, Elaboration]
---

## Usage

[EmptySequence]() is the sequence with no elements, of the type `Sequences[]`.

## Details & Options

- [EmptySequence]() is a constructor of [Sequences](), in [TypeTheoryEnvironment]()["WolframLanguage"]. `Sequence[]` writes it.

## Basic Examples

The empty sequence:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
DefinitionallyEqualQ[TypeTheoryTerm[Sequence[], wolfram], TypeTheoryTerm[EmptySequence, wolfram]]
```

<!-- => True -->
