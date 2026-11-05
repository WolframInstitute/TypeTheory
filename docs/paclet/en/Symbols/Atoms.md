---
Template: Symbol
Name: Atoms
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Atoms
Keywords: [Wolfram Language, expressions, pattern matching, Match]
SeeAlso: [Expressions, TypeTheoryEnvironment]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage]
---

## Usage

[Atoms]() is the type of the expressions of the Wolfram Language that have no parts: symbols, numbers and strings.

## Details & Options

- [Atoms]() is an inductive type of [TypeTheoryEnvironment]()["WolframLanguage"], whose atoms are data: `"symbolAtom"` of a symbol's full name, `"naturalAtom"` of a natural number, `"negativeAtom"` of *n* for the integer -(*n* + 1), `"stringAtom"` of a string, and `"otherAtom"` of the head and the [InputForm]() of any other atom, as a real number.
- `"atom"` makes an expression of an atom. A quotation, <code>[HoldForm]()[*e*]</code>, makes the atoms of *e* itself, and nothing declares them.
- The head of an atom and [SameQ]() of two atoms are definitions, which the kernel computes: two symbols are the same where their names are, and two other atoms where their values are. Two real numbers are the same where their [InputForm]() is, which [SameQ]() of the Wolfram Language relaxes by a tolerance.

## Basic Examples

An atom is an expression:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
TypeTheoryType["atom", wolfram]
```

<!-- => Atoms → Expressions -->

---

The symbol `Plus` quoted is the atom of its full name:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
DefinitionallyEqualQ[TypeTheoryTerm[HoldForm[Plus], wolfram], TypeTheoryTerm["atom"["symbolAtom"["System`Plus"]], wolfram]]
```

<!-- => True -->

## Scope

The head of an atom computes:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
{NormalForm[TypeTheoryTerm[Head[HoldForm[1]], wolfram]], NormalForm[TypeTheoryTerm[Head[HoldForm["text"]], wolfram]]}
```

<!-- => {Integer, String} -->

---

Atoms compare by computation:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
{WeakHeadNormalForm[TypeTheoryTerm[SameQ[HoldForm[f], HoldForm[f]], wolfram]], WeakHeadNormalForm[TypeTheoryTerm[SameQ[HoldForm[f], HoldForm[g]], wolfram]]}
```

<!-- => {true, false} -->
