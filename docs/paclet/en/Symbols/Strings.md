---
Template: Symbol
Name: Strings
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Strings
Keywords: [strings, string literals, character codes, string comparison, string concatenation, StringJoin, ToUpperCase, StringLength, Characters, ToString, formalization, Wolfram Language]
SeeAlso: [TypeTheoryFormalize, Expressions, Atoms, SameQ, InductiveRecursor]
RelatedGuides: [TypeTheory]
RelatedTutorials: [Elaboration, TheWolframLanguage]
---

## Usage

[Strings]() is the type of the strings of the Wolfram Language, each the list of its character codes.

## Details & Options

- In <code>[TypeTheoryEnvironment]()["WolframLanguage"]</code>, [Strings]() is an inductive type with one constructor, `"string"`, of the type `{ℕ} -> Strings`: a string is `"string"` of the list of its character codes, so two strings compare by computation.
- A string literal `"abc"` is that string where a string is expected, or where nothing decides the type, and no constant is named `"abc"`. Where an expression is expected it is the expression, the atom `"stringAtom"` of the string.
- [SameQ]() of two strings computes, and so does every match of a pattern against a string, such as a string literal on the left of a rule or `_String`.
- [TypeTheoryFormalize]() declares a string function that a definition calls by its signature over [Strings](): [StringReverse]() and [ToUpperCase]() `Strings -> Strings`, [StringJoin]() `Strings -> Strings -> Strings`, [StringLength]() `Strings -> ℕ`, [Characters]() `Strings -> {Strings}` and [ToString]() `Expressions -> Strings`. They are axioms, which the Wolfram Language computes.
- Where an environment has no [Strings](), [TypeTheoryFormalize]() declares it as an axiom, opaque, with each literal a definition uses a constant of it named by its [InputForm]().

## Basic Examples

A string is made of the list of its character codes:

```wl
TypeTheoryEnvironment["WolframLanguage"][Strings]
```

<!-- => inductive Strings : Type | string : {ℕ} → Strings -->

---

The literal `"Hi"` is the string of the codes 72 and 105:

```wl
DefinitionallyEqualQ[TypeTheoryTerm["Hi", "WolframLanguage"], TypeTheoryTerm["string"[{72, 105}], "WolframLanguage"]]
```

<!-- => True -->

---

A table of rules looks a string up, the kernel comparing it with each left side:

```wl
NormalForm[TypeTheoryTerm[Replace["green", {"red" -> 1, "green" -> 2, "blue" -> 3}], "WolframLanguage"]]
```

<!-- => 2 -->

## Scope

`_String` matches the strings among the parts of an expression:

```wl
NormalForm[TypeTheoryTerm[ReplaceAll[f[1, "a", x, "b"], s_String :> g[s]], "WolframLanguage"]]
```

<!-- => f[1, g["a"], x, g["b"]] -->

---

The recursor of [Strings]() gives the codes of a string, whose [Length]() is the length of the string:

```wl
NormalForm[TypeTheoryTerm[Length[InductiveRecursor[Strings][Typed[s, Strings] |-> {NonNegativeIntegers}, Typed[c, {NonNegativeIntegers}] |-> c, "hello"]], "WolframLanguage"]]
```

<!-- => 5 -->

---

A code put in front of the codes of a string makes a longer string:

```wl
NormalForm[TypeTheoryTerm[InductiveRecursor[Strings][Typed[s, Strings] |-> Strings, Typed[c, {NonNegativeIntegers}] |-> "string"[Prepend[c, 72]], "ello"], "WolframLanguage"]]
```

<!-- => Hello -->

---

Where an expression is expected, a string literal is the atom of the string, whose head is [String]():

```wl
NormalForm[TypeTheoryTerm[Head["abc"], "WolframLanguage"]]
```

<!-- => String -->

## Applications

Joining two strings is joining their lists of codes, a definition the kernel computes:

```wl
joining = TypeTheoryEnvironment["WolframLanguage", {TypeTheoryDefinition[JoinStrings, Function[{Typed[s, Strings], Typed[t, Strings]},
    InductiveRecursor[Strings][Typed[u, Strings] |-> Strings, Typed[c, {NonNegativeIntegers}] |->
        InductiveRecursor[Strings][Typed[v, Strings] |-> Strings, Typed[d, {NonNegativeIntegers}] |-> "string"[Join[c, d]], t], s]
]]}]
```

<!-- => TypeTheoryEnvironment summary box: 226 constants -->

It joins two literals:

```wl
NormalForm[TypeTheoryTerm[JoinStrings["Hello, ", "world"], joining]]
```

<!-- => Hello, world -->

So the equation of the joined string and the literal is proved by computation:

```wl
TypeTheoryProof[JoinStrings["Hello, ", "world"] == "Hello, world", joining, {"Reflexivity"}]
```

<!-- => Proof complete -->

The empty string joined to any string is that string, by cases on the string:

```wl
TypeTheoryProof[ForAll[{Typed[s, Strings]}, JoinStrings["", s] == s], joining, {"Introduce"[s], "Cases"[s], "Introduce"[c], "Reflexivity"}]
```

<!-- => Proof complete -->

---

A function of strings is formalized over [Strings](), the string functions it calls declared by their signatures:

```wl
shout[s_] := StringJoin[ToUpperCase[s], "!"];
TypeTheoryFormalize[shout, "WolframLanguage"]
```

<!-- => {axiom StringJoin : Strings → Strings → Strings, axiom ToUpperCase : Strings → Strings, definition shout := s ↦ ToUpperCase[s] <> "!"} -->

## Properties and Relations

Where the environment has no strings, [TypeTheoryFormalize]() declares [Strings]() as an axiom, and each literal as a constant of its own:

```wl
shout[s_] := StringJoin[ToUpperCase[s], "!"];
TypeTheoryFormalize[shout, "Integers"]
```

<!-- => {axiom Strings : Type, axiom StringJoin : Strings → Strings → Strings, axiom ToUpperCase : Strings → Strings, axiom "!" : Strings, definition shout := s ↦ ToUpperCase[s] <> "!"} -->

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

---

No instance of [Decidable]() decides an equation of strings, so `"Decide"` does not prove one:

```wl
TypeTheoryProof[Not["ab" == "ba"], "WolframLanguage", {"Decide"}]
```

<!-- => Failure["NotDecidable", ...] -->

[SameQ]() of the two strings computes, so that they differ is proved by computation:

```wl
TypeTheoryProof[SameQ["ab", "ba"] == "false", "WolframLanguage", {"Reflexivity"}]
```

<!-- => Proof complete -->
