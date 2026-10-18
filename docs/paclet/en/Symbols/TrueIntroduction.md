---
Template: Symbol
Name: TrueIntroduction
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TrueIntroduction
Keywords: [True, proof, constructor, prelude, logic]
SeeAlso: [FalseElimination, AndIntroduction, TypeTheoryProof, TypeTheoryEnvironment]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[TrueIntroduction]()</code> is the proof of [True]().

## Details & Options

- [True]() is an inductive proposition of the prelude, and [TrueIntroduction]() is its one constructor.
- Like every constant, [TrueIntroduction]() means something only in an environment that declares it.

## Basic Examples

[TrueIntroduction]() proves [True]():

```wl
TypeTheoryCheck[TypeTheoryTerm[TrueIntroduction]]
```

<!-- => True -->

---

Prove [True]() with a tactic:

```wl
TypeTheoryProof[True, {TypeTheoryTactic["Exact", TrueIntroduction]}]
```

<!-- => Proof complete -->

## Properties and Relations

[True]() is a proposition:

```wl
TypeTheoryCheck[TypeTheoryTerm[True], TypeTheoryTerm[TypeUniverse[0]]]
```

<!-- => Success["TypeChecked", ...] -->

## Possible Issues

The empty environment does not declare [TrueIntroduction]():

```wl
TypeTheoryCheck[TypeTheoryTerm[TrueIntroduction, TypeTheoryEnvironment[]]]
```

<!-- => Failure["ElaborationFailed", ...]: TrueIntroduction is neither a variable in scope nor a declared constant -->

---

On its own, [True]() could also be the Boolean `"true"`, so its type is ambiguous:

```wl
TypeTheoryCheck[TypeTheoryTerm[True]]
```

<!-- => Failure["Ambiguous", ...] -->
