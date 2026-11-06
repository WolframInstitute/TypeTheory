---
Template: Symbol
Name: Atoms
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Atoms
Keywords: [Wolfram Language, expressions, atoms, symbols, integers, strings, real numbers, AtomQ, SameQ, Head, HoldForm, pattern matching]
SeeAlso: [Expressions, Strings, Arguments, TypeTheoryEnvironment]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, PatternsAndRewriting]
---

## Usage

[Atoms]() is the type of the expressions of the Wolfram Language that have no parts, as data: symbols by their full names, integers, strings, and other atoms by their head and [InputForm]().

## Details & Options

- [Atoms]() is an inductive type of <code>[TypeTheoryEnvironment]()["WolframLanguage"]</code>, with five constructors: `"symbolAtom"` of a symbol's full name, `"naturalAtom"` of a natural number, `"negativeAtom"` of *n* for the integer -(*n* + 1), `"stringAtom"` of a string, and `"otherAtom"` of the head and the [InputForm]() of any other atom, as a real number.
- `"atom"`, of the type `Atoms -> Expressions`, makes an expression of an atom, and an atom shows as the Wolfram Language atom it stands for.
- A quotation, <code>[HoldForm]()[*e*]</code>, makes the atoms of *e* itself, and nothing declares them. Where an expression is expected, a natural number or a string is its atom by a coercion, and a symbol that names nothing stands for its own atom.
- The head of an atom is [Symbol](), [Integer]() or [String](), or the head that `"otherAtom"` was given. [AtomQ]() of an atom is `"true"`, and its [Arguments]() are the empty sequence.
- [SameQ]() of two atoms is a definition, which the kernel computes: two symbols are the same where their names are, and two other atoms where their values are. Two real numbers are the same where their [InputForm]() is, which [SameQ]() of the Wolfram Language relaxes by a tolerance.

## Basic Examples

The type of [Atoms]():

```wl
TypeTheoryType[Atoms, "WolframLanguage"]
```

<!-- => Type -->

---

An atom is an expression:

```wl
TypeTheoryType["atom", "WolframLanguage"]
```

<!-- => Atoms → Expressions -->

---

A symbol is the atom of its full name, a string:

```wl
TypeTheoryType["symbolAtom", "WolframLanguage"]
```

<!-- => Strings → Atoms -->

---

The symbol [Plus]() quoted is the atom of its full name:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[HoldForm[Plus], "WolframLanguage"], TypeTheoryTerm["atom"["symbolAtom"["System`Plus"]], "WolframLanguage"]]
```

<!-- => True -->

## Scope

A natural number is `"naturalAtom"` of it:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[HoldForm[3], "WolframLanguage"], TypeTheoryTerm["atom"["naturalAtom"[3]], "WolframLanguage"]]
```

<!-- => True -->

---

A negative integer -(*n* + 1) is `"negativeAtom"` of *n*:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[HoldForm[-3], "WolframLanguage"], TypeTheoryTerm["atom"["negativeAtom"[2]], "WolframLanguage"]]
```

<!-- => True -->

---

An atom shows as the Wolfram Language atom it stands for:

```wl
NormalForm[TypeTheoryTerm["atom"["negativeAtom"[0]], "WolframLanguage"]]
```

<!-- => -1 -->

---

A string is `"stringAtom"` of it:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[HoldForm["ab"], "WolframLanguage"], TypeTheoryTerm["atom"["stringAtom"["ab"]], "WolframLanguage"]]
```

<!-- => True -->

---

Any other atom, as a real number, is `"otherAtom"` of its head and its [InputForm]():

```wl
DefinitionallyEqualQ[TypeTheoryTerm[HoldForm[1.5], "WolframLanguage"], TypeTheoryTerm["atom"["otherAtom"["System`Real", "1.5"]], "WolframLanguage"]]
```

<!-- => True -->

---

The head of a symbol computes to [Symbol]():

```wl
NormalForm[TypeTheoryTerm[Head[HoldForm[f]], "WolframLanguage"]]
```

<!-- => Symbol -->

---

The head of a natural number is [Integer]():

```wl
NormalForm[TypeTheoryTerm[Head[HoldForm[1]], "WolframLanguage"]]
```

<!-- => Integer -->

---

The head of a negative integer is [Integer]() too:

```wl
NormalForm[TypeTheoryTerm[Head[HoldForm[-2]], "WolframLanguage"]]
```

<!-- => Integer -->

---

The head of a string is [String]():

```wl
NormalForm[TypeTheoryTerm[Head[HoldForm["text"]], "WolframLanguage"]]
```

<!-- => String -->

---

The head of another atom is the head it was given:

```wl
NormalForm[TypeTheoryTerm[Head[HoldForm[2.5]], "WolframLanguage"]]
```

<!-- => Real -->

---

Two symbols are the same where their names are:

```wl
WeakHeadNormalForm[TypeTheoryTerm[SameQ[HoldForm[f], HoldForm[f]], "WolframLanguage"]]
```

<!-- => true -->

---

Two symbols with other names are not:

```wl
WeakHeadNormalForm[TypeTheoryTerm[SameQ[HoldForm[f], HoldForm[g]], "WolframLanguage"]]
```

<!-- => false -->

---

A number and a string are other atoms:

```wl
WeakHeadNormalForm[TypeTheoryTerm[SameQ[1, "1"], "WolframLanguage"]]
```

<!-- => false -->

## Properties and Relations

The declaration of [Atoms]():

```wl
TypeTheoryEnvironment["WolframLanguage"][Atoms]
```

<!-- => inductive Atoms : Type | symbolAtom : Strings → Atoms | naturalAtom : ℕ → Atoms | negativeAtom : ℕ → Atoms | stringAtom : Strings → Atoms | otherAtom : Strings → Strings → Atoms -->

---

An atom is an atom by [AtomQ]():

```wl
WeakHeadNormalForm[TypeTheoryTerm[AtomQ[HoldForm[f]], "WolframLanguage"]]
```

<!-- => true -->

---

An atom has no arguments:

```wl
NormalForm[TypeTheoryTerm[Arguments[HoldForm[f]], "WolframLanguage"]]
```

<!-- => [] -->

---

Two real numbers with the same [InputForm]() are the same:

```wl
WeakHeadNormalForm[TypeTheoryTerm[SameQ[HoldForm[1.5], HoldForm[1.50]], "WolframLanguage"]]
```

<!-- => true -->

## Possible Issues

Two real numbers whose [InputForm]() differs are not the same atom:

```wl
WeakHeadNormalForm[TypeTheoryTerm[SameQ[HoldForm[0.3], HoldForm[0.30000000000000004]], "WolframLanguage"]]
```

<!-- => false -->

[SameQ]() of the Wolfram Language takes them as the same, within a tolerance:

```wl
SameQ[0.3, 0.30000000000000004]
```

<!-- => True -->

---

A quoted fraction is no atom: [HoldForm]() keeps the product it is written as:

```wl
NormalForm[TypeTheoryTerm[Head[HoldForm[1/2]], "WolframLanguage"]]
```

<!-- => Times -->

---

A natural number is an expression by a coercion, not an atom:

```wl
TypeTheoryType[Typed[3, Atoms], "WolframLanguage"]
```

<!-- => Failure["TypeMismatch", ...] -->
