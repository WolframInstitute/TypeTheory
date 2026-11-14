---
Template: Symbol
Name: Strings
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Strings
Keywords: [strings, string literals, character codes, string comparison, string concatenation, StringJoin, ToUpperCase, StringLength, Characters, ToString, formalization, Wolfram Language, prelude]
SeeAlso: [FromString, TypeTheoryFormalize, Expressions, Atoms, SameQ, InductiveRecursor]
RelatedGuides: [TypeTheory]
RelatedTutorials: [Elaboration, TheWolframLanguage]
---

## Usage

[Strings]() is the type of the strings of the Wolfram Language, each the list of its character codes.

## Details & Options

- [Strings]() is an inductive type of the prelude with one constructor, `"string"`, of the type `{ℕ} -> Strings`: a string is `"string"` of the list of its character codes, so two strings compare by computation.
- A string literal `"abc"` that names no constant is that string where a string is expected, or where the type is still to be decided, as an element of a list. A literal that names a constant, as `"true"` does, is the constant. Where an expression is expected, a string is the expression, the atom `"stringAtom"` of the string, by a coercion.
- A string on its own, where no type is expected, is the name of a constant; one that names none is refused, as a misspelled name would be. <code>[FromString]()["abc"]</code> is the string, even where `"abc"` names a constant, and so is <code>[Typed]()["abc", [Strings]()]</code> where it does not.
- A string that names no constant, applied to arguments, as `"abc"[1]`, is no term: it is taken for a misspelled constant.
- [SameQ]() of two strings computes, and so does every match of a pattern against a string, such as a string literal on the left of a rule or `_String`.
- [TypeTheoryFormalize]() declares a string function that a definition calls by its signature over [Strings](): [StringReverse]() and [ToUpperCase]() `Strings -> Strings`, [StringJoin]() `Strings -> Strings -> Strings`, [StringLength]() `Strings -> ℕ`, [Characters]() `Strings -> {Strings}` and [ToString]() `Expressions -> Strings`. They are axioms, which the Wolfram Language computes.
- Where an environment has no [Strings](), as the constructive environment, [TypeTheoryFormalize]() declares it as an axiom, opaque, with each literal a definition uses a constant of it named by its [InputForm]().

## Basic Examples

The strings are a type of the prelude:

```wl
TypeTheoryType[Strings]
```

<!-- => Type -->

---

A string is made of the list of its character codes:

```wl
TypeTheoryEnvironment["Prelude"][Strings]
```

<!-- => inductive Strings : Type | string : {ℕ} → Strings -->

---

A string literal is a string where a string is expected, as an element of a list:

```wl
TypeTheoryType[{"Hi", "there"}]
```

<!-- => {Strings} -->

---

[FromString]()`["Hi"]` is the string of the codes 72 and 105:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[FromString["Hi"]], TypeTheoryTerm["string"[{72, 105}]]]
```

<!-- => True -->

---

A table of rules looks a string up in the kernel, comparing it with each left side:

```wl
NormalForm[TypeTheoryTerm[Replace["green", {"red" -> 1, "green" -> 2, "blue" -> 3}]]]
```

<!-- => 2 -->

## Scope

Where an expression is expected, a string is its atom, by a coercion:

```wl
TypeTheoryEnvironment["Prelude"]["StringExpressionCoercion"]
```

<!-- => coercion StringExpressionCoercion : Strings → Expressions := (s ∶ Strings) ↦ atom[stringAtom[s]] -->

---

`_String` matches the strings among the parts of an expression:

```wl
NormalForm[TypeTheoryTerm[ReplaceAll[f[1, "a", x, "b"], s_String :> g[s]]]]
```

<!-- => f[1, g["a"], x, g["b"]] -->

---

The recursor of [Strings]() takes a function of the list of codes:

```wl
TypeTheoryType[InductiveRecursor[Strings]]
```

<!-- => ∀_m∶Strings → Sort u (∀_x∶{ℕ} m[string[x]]) → ∀_t∶Strings m[t] -->

So it gives the codes of a string, a list of natural numbers:

```wl
TypeTheoryType[InductiveRecursor[Strings][{NonNegativeIntegers} &, c |-> c, "hello"]]
```

<!-- => {ℕ} -->

Their [Length]() is the length of the string, 5, by computation:

```wl
TypeTheoryProof[Length[InductiveRecursor[Strings][{NonNegativeIntegers} &, c |-> c, "hello"]] == 5, {"Reflexivity"}]
```

<!-- => Proof complete -->

---

A code put in front of the codes of a string makes a longer string, here 72, `H`, in front of `"ello"`:

```wl
TypeTheoryProof[InductiveRecursor[Strings][Strings &, c |-> "string"[Prepend[c, 72]], "ello"] == "Hello", {"Reflexivity"}]
```

<!-- => Proof complete -->

## Applications

Joining two strings is joining their lists of codes, a definition the kernel computes:

```wl
joining = TypeTheoryEnvironment[{TypeTheoryDefinition[JoinStrings, {s, t} |->
    InductiveRecursor[Strings][Strings &, c |-> InductiveRecursor[Strings][Strings &, d |-> "string"[Join[c, d]], t], s]
]}]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

It takes two strings to a string:

```wl
TypeTheoryType[JoinStrings, joining]
```

<!-- => Strings → Strings → Strings -->

The equation of two literals joined and the literal of the whole is proved by computation:

```wl
TypeTheoryProof[JoinStrings["Hello, ", "world"] == "Hello, world", joining, {"Reflexivity"}]
```

<!-- => Proof complete -->

The empty string joined to any string is that string, by cases on the string:

```wl
TypeTheoryProof[ForAll[{s}, JoinStrings["", s] == s], joining, {"Introduce"[s], "Cases"[s], "Introduce"[c], "Reflexivity"}]
```

<!-- => Proof complete -->

---

A function of strings is formalized over [Strings](), the string functions it calls declared by their signatures:

```wl
shout[s_] := StringJoin[ToUpperCase[s], "!"];
TypeTheoryFormalize[shout]
```

<!-- => {axiom StringJoin : Strings → Strings → Strings, axiom ToUpperCase : Strings → Strings, definition shout := s ↦ ToUpperCase[s] <> "!"} -->

## Properties and Relations

[SameQ]() compares two strings, a Boolean:

```wl
TypeTheoryType[SameQ["ab", "ba"]]
```

<!-- => 𝔹 -->

---

The constructive environment has no strings, so [TypeTheoryFormalize]() declares [Strings]() there as an axiom, and each literal as a constant of its own:

```wl
shout[s_] := StringJoin[ToUpperCase[s], "!"];
TypeTheoryFormalize[shout, "Constructive"]
```

<!-- => {axiom Strings : Type, axiom StringJoin : Strings → Strings → Strings, axiom ToUpperCase : Strings → Strings, axiom "!" : Strings, definition shout := s ↦ ToUpperCase[s] <> "!"} -->

## Possible Issues

A literal that names a constant is the constant, not a string: `"true"` is the Boolean:

```wl
TypeTheoryType["true"]
```

<!-- => 𝔹 -->

So it is no string even where one is expected:

```wl
TypeTheoryType[Typed["true", Strings]]
```

<!-- => Failure["TypeMismatch", ...] -->

---

[FromString]() makes it the string:

```wl
TypeTheoryType[FromString["true"]]
```

<!-- => Strings -->

---

A string on its own that names no constant is taken for a misspelled constant, and refused:

```wl
TypeTheoryType["Hi"]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

A string applied to arguments is taken for a misspelled constant, not a string:

```wl
TypeTheoryType["abc"[1]]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

The string functions are not constants of the prelude, so a call of one is a Wolfram Language expression there, of type `Expressions`; [TypeTheoryFormalize]() declares those a definition calls:

```wl
TypeTheoryType[StringReverse["ab"]]
```

<!-- => Expressions -->

---

No instance of [Decidable]() decides an equation of strings, so `"Decide"` does not prove one:

```wl
TypeTheoryProof[Not["ab" == "ba"], {"Decide"}]
```

<!-- => Failure["NotDecidable", ...] -->

[SameQ]() of the two strings computes, so that they differ is proved by computation:

```wl
TypeTheoryProof[SameQ["ab", "ba"] == "false", {"Reflexivity"}]
```

<!-- => Proof complete -->
