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

- [Strings]() is opaque: its elements are the string literals, and what the built-ins compute from them, which the Wolfram Language computes and the kernel never does.
- A string literal `"abc"` is a constant of [Strings](), named by its [InputForm](), `"\"abc\""`, and shows as the string. In a term, `"abc"` is that constant where no constant is named `abc`, as `"true"` is.
- [Strings]() is a constant of [TypeTheoryEnvironment]()["WolframLanguage"], where a string is an expression by a coercion, and [TypeTheoryFormalize]() declares it, with each literal a definition uses, where an environment does not have it.
- The string functions have signatures over [Strings](): [StringReverse]() and [ToUpperCase]() `Strings -> Strings`, [StringJoin]() `Strings -> Strings -> Strings`, [StringLength]() `Strings -> ℕ`, [StringTake]() `Strings -> ℕ -> Strings`, [StringContainsQ]() `Strings -> Strings -> Booleans`, [Characters]() `Strings -> {Strings}` and [ToString]() `Expressions -> Strings`.

## Basic Examples

A function of strings is a definition over [Strings]():

```wl
reversed[s_] := StringReverse[s];
TypeTheoryFormalize[reversed, TypeTheoryEnvironment["Integers"]]
```

<!-- => {TypeTheoryAxiom[Strings, TypeUniverse[1]], TypeTheoryAxiom[StringReverse, Strings -> Strings, "Implementation" -> StringReverse], TypeTheoryDefinition[reversed, Function[{s}, StringReverse[s]]]} -->

---

A string literal is a constant of [Strings]():

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
TypeOf[TypeTheoryTerm["abc", TypeTheoryEnvironment[wolfram, {TypeTheoryAxiom["\"abc\"", Strings]}]]]
```

<!-- => Strings -->
