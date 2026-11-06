---
Template: Symbol
Name: Strings
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Strings
Keywords: [strings, string literals, character codes, StringReverse, StringJoin, StringLength, ToString, Characters, formalization, Wolfram Language]
SeeAlso: [TypeTheoryFormalize, Expressions, Atoms, SameQ]
RelatedGuides: [TypeTheory]
RelatedTutorials: [Elaboration, TheWolframLanguage]
---

## Usage

[Strings]() is the type of the strings of the Wolfram Language, each the list of its character codes.

## Details & Options

- In <code>[TypeTheoryEnvironment]()["WolframLanguage"]</code>, [Strings]() is an inductive type with one constructor, `"string"`, of the type `{ℕ} -> Strings`: a string is `"string"` of the list of its character codes, so two strings compare by computation.
- A string literal `"abc"` is that string where a string is expected, or where nothing decides the type, and no constant is named `"abc"`. Where an expression is expected it is the expression, the atom `"stringAtom"` of the string.
- [TypeTheoryFormalize]() declares a string function that a definition calls by its signature over [Strings](): [StringReverse]() and [ToUpperCase]() `Strings -> Strings`, [StringJoin]() `Strings -> Strings -> Strings`, [StringLength]() `Strings -> ℕ`, [Characters]() `Strings -> {Strings}` and [ToString]() `Expressions -> Strings`. They are axioms, which the Wolfram Language computes.
- Where an environment has no [Strings](), [TypeTheoryFormalize]() declares it as an axiom, opaque, with each literal a definition uses a constant of it named by its [InputForm]().

## Basic Examples

The type of [Strings]():

```wl
TypeTheoryType[Strings, "WolframLanguage"]
```

<!-- => Type -->

---

A string is made of the list of its character codes:

```wl
TypeTheoryType["string", "WolframLanguage"]
```

<!-- => {ℕ} → Strings -->

---

A string literal is a string:

```wl
TypeTheoryType["abc", "WolframLanguage"]
```

<!-- => Strings -->

---

The literal is the list of its character codes:

```wl
DefinitionallyEqualQ[TypeTheoryTerm["abc", "WolframLanguage"], TypeTheoryTerm["string"[{97, 98, 99}], "WolframLanguage"]]
```

<!-- => True -->

---

A function of strings is a definition over [Strings]():

```wl
reversed[s_] := StringReverse[s];
TypeTheoryFormalize[reversed, TypeTheoryEnvironment["WolframLanguage"]]
```

<!-- => {axiom StringReverse : Strings → Strings, definition reversed := s ↦ StringReverse[s]} -->

## Scope

The empty string is the empty list of codes:

```wl
DefinitionallyEqualQ[TypeTheoryTerm["", "WolframLanguage"], TypeTheoryTerm["string"[Typed[{}, {NonNegativeIntegers}]], "WolframLanguage"]]
```

<!-- => True -->

---

A string made of its codes shows as the string:

```wl
NormalForm[TypeTheoryTerm["string"[{97, 98}], "WolframLanguage"]]
```

<!-- => ab -->

---

The recursor of [Strings]() gives the codes back:

```wl
WeakHeadNormalForm[TypeTheoryTerm[InductiveRecursor[Strings][Typed[s, Strings] |-> {NonNegativeIntegers}, Typed[c, {NonNegativeIntegers}] |-> c, "ab"], "WolframLanguage"]]
```

<!-- => {97, 98} -->

---

Where an expression is expected, a string literal is an expression:

```wl
TypeTheoryType[Typed["abc", Expressions], "WolframLanguage"]
```

<!-- => Expressions -->

---

Its head is [String]():

```wl
NormalForm[TypeTheoryTerm[Head["abc"], "WolframLanguage"]]
```

<!-- => String -->

---

A quoted string is the atom of the string:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[HoldForm["ab"], "WolframLanguage"], TypeTheoryTerm["atom"["stringAtom"["ab"]], "WolframLanguage"]]
```

<!-- => True -->

---

Two strings with the same characters are the same:

```wl
WeakHeadNormalForm[TypeTheoryTerm[SameQ["ab", "ab"], "WolframLanguage"]]
```

<!-- => true -->

---

Two strings with other characters are not:

```wl
WeakHeadNormalForm[TypeTheoryTerm[SameQ["ab", "ac"], "WolframLanguage"]]
```

<!-- => false -->

---

A pattern with the head [String]() matches a string:

```wl
NormalForm[TypeTheoryTerm[Replace[f["a", 1], f[x_String, y_] :> {y, x}], "WolframLanguage"]]
```

<!-- => {1, "a"} -->

---

[StringJoin]() takes two strings:

```wl
joined[s_, t_] := StringJoin[s, t];
TypeTheoryFormalize[joined, TypeTheoryEnvironment["WolframLanguage"]]
```

<!-- => {axiom StringJoin : Strings → Strings → Strings, definition joined := s t ↦ s <> t} -->

---

A string literal in a definition is a string:

```wl
greeting[s_] := StringJoin["Hello, ", s];
TypeTheoryFormalize[greeting, TypeTheoryEnvironment["WolframLanguage"]]
```

<!-- => {axiom StringJoin : Strings → Strings → Strings, definition greeting := s ↦ "Hello, " <> s} -->

---

[StringLength]() gives a natural number:

```wl
lengthOf[s_] := StringLength[s];
TypeTheoryFormalize[lengthOf, TypeTheoryEnvironment["WolframLanguage"]]
```

<!-- => {axiom StringLength : Strings → ℕ, definition lengthOf := s ↦ StringLength[s]} -->

---

[Characters]() gives a list of strings:

```wl
characters[s_] := Characters[s];
TypeTheoryFormalize[characters, TypeTheoryEnvironment["WolframLanguage"]]
```

<!-- => {axiom Characters : Strings → {Strings}, definition characters := s ↦ Characters[s]} -->

---

[ToString]() takes any expression:

```wl
shown[x_] := ToString[x];
TypeTheoryFormalize[shown, TypeTheoryEnvironment["WolframLanguage"]]
```

<!-- => {axiom ToString : Expressions → Strings, definition shown := x ↦ ToString[x]} -->

## Properties and Relations

The declaration of [Strings]():

```wl
TypeTheoryEnvironment["WolframLanguage"][Strings]
```

<!-- => inductive Strings : Type | string : {ℕ} → Strings -->

---

Where the environment has no strings, [TypeTheoryFormalize]() declares [Strings]() as an axiom:

```wl
reversed[s_] := StringReverse[s];
TypeTheoryFormalize[reversed, TypeTheoryEnvironment["Integers"]]
```

<!-- => {axiom Strings : Type, axiom StringReverse : Strings → Strings, definition reversed := s ↦ StringReverse[s]} -->

---

There, a literal is a constant of its own:

```wl
greeting[s_] := StringJoin["Hello, ", s];
TypeTheoryFormalize[greeting, TypeTheoryEnvironment["Integers"]]
```

<!-- => {axiom Strings : Type, axiom StringJoin : Strings → Strings → Strings, axiom "Hello, " : Strings, definition greeting := s ↦ "Hello, " <> s} -->

## Possible Issues

In the prelude, a string is the name of a constant, and no constant is named `"abc"`:

```wl
TypeTheoryType["abc"]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

The string functions are not constants of the Wolfram Language environment; [TypeTheoryFormalize]() declares those a definition calls:

```wl
TypeTheoryType[StringReverse["ab"], "WolframLanguage"]
```

<!-- => Failure["ElaborationFailed", ...] -->
