---
Template: Symbol
Name: Strings
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Strings
Keywords: [strings, string literals, StringReverse, StringJoin, StringLength, formalization]
SeeAlso: [TypeTheoryFormalize, Expressions, Atoms]
RelatedGuides: [TypeTheory]
RelatedTutorials: [Elaboration, TheWolframLanguage]
---

## Usage

[Strings]() is the type of the strings of the Wolfram Language.

## Details & Options

- In [TypeTheoryEnvironment]()["WolframLanguage"], [Strings]() is an inductive type: a string is `"string"` of the list of its character codes, so two strings compare by computation. A string literal `"abc"` is that string where a string is expected, or where nothing decides the type, and no constant is named `abc`; where an expression is expected it is the expression.
- The string functions have signatures over [Strings](): [StringReverse]() and [ToUpperCase]() `Strings -> Strings`, [StringJoin]() `Strings -> Strings -> Strings`, [StringLength]() `Strings -> ℕ`, [StringTake]() `Strings -> ℕ -> Strings`, [StringContainsQ]() `Strings -> Strings -> Booleans`, [Characters]() `Strings -> {Strings}` and [ToString]() `Expressions -> Strings`. They are axioms, which the Wolfram Language computes.
- Where an environment has no [Strings](), [TypeTheoryFormalize]() declares it as an axiom, opaque, with each literal a definition uses a constant of it named by its [InputForm]().

## Basic Examples

A function of strings is a definition over [Strings]():

```wl
reversed[s_] := StringReverse[s];
TypeTheoryFormalize[reversed, TypeTheoryEnvironment["Integers"]]
```

<!-- => {axiom Strings : Type, axiom StringReverse : Strings → Strings, definition reversed := s ↦ StringReverse[s]} -->

---

A string literal is a string, the list of its character codes:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
{TypeTheoryType["abc", wolfram], DefinitionallyEqualQ[TypeTheoryTerm["abc", wolfram], TypeTheoryTerm["string"[{97, 98, 99}], wolfram]]}
```

<!-- => {Strings, True} -->
