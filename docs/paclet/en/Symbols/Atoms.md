---
Template: Symbol
Name: Atoms
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Atoms
Keywords: [Wolfram Language, expressions, atoms, symbols, contexts, integers, strings, real numbers, rationals, AtomQ, SameQ, Head, HoldForm, pattern matching]
SeeAlso: [Expressions, Strings, Arguments, TypeTheoryEnvironment]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, PatternsAndRewriting]
---

## Usage

[Atoms]() is the type of the expressions of the Wolfram Language that have no parts, as data: symbols by their full names, integers, strings, and other atoms by their head and [InputForm]().

## Details & Options

- [Atoms]() is an inductive type of <code>[TypeTheoryEnvironment]()["WolframLanguage"]</code>, with five constructors: `"symbolAtom"` of a symbol's full name, `"naturalAtom"` of a natural number, `"negativeAtom"` of *n* for the integer -(*n* + 1), `"stringAtom"` of a string, and `"otherAtom"` of the head and the [InputForm]() of any other atom, as a real or a rational number.
- `"atom"`, of the type `Atoms -> Expressions`, makes an expression of an atom, and an atom shows as the Wolfram Language atom it stands for.
- A quotation, <code>[HoldForm]()[*e*]</code>, makes the atoms of *e* itself, and nothing declares them. Where an expression is expected, a natural number or a string is its atom by a coercion, a negative integer is its atom, and a symbol that names nothing stands for its own atom.
- The head of an atom is [Symbol](), [Integer]() or [String](), or the head that `"otherAtom"` was given, so a pattern such as `_Integer` or `_Symbol` matches the atoms of that kind. [AtomQ]() of an atom is `"true"`, and its [Arguments]() are the empty sequence.
- [SameQ]() of two atoms is a definition, which the kernel computes: two symbols are the same where their full names are, and two other atoms where their values are. Two real numbers are the same where their [InputForm]() is, which [SameQ]() of the Wolfram Language relaxes by a tolerance.

## Basic Examples

The five kinds of atoms:

```wl
TypeTheoryEnvironment["WolframLanguage"][Atoms]
```

<!-- => inductive Atoms : Type | symbolAtom : Strings → Atoms | naturalAtom : ℕ → Atoms | negativeAtom : ℕ → Atoms | stringAtom : Strings → Atoms | otherAtom : Strings → Strings → Atoms -->

---

The heads of the atoms of a list, a symbol, two integers, a string and a real number:

```wl
NormalForm[TypeTheoryTerm[Map[Typed[e, Expressions] |-> Head[e], {Arguments[HoldForm[{x, 1, -2, "s", 1.5}]]}], "WolframLanguage"]]
```

<!-- => {Symbol, Integer, Integer, String, Real} -->

---

So `_Integer` picks out the integers, positive or negative:

```wl
NormalForm[TypeTheoryTerm[ReplaceList[HoldForm[{x, 1, -2, "s", 1.5}], {___, a_Integer, ___} :> a], "WolframLanguage"]]
```

<!-- => {1, -2} -->

## Scope

A symbol is the atom of its full name:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[HoldForm[Plus], "WolframLanguage"], TypeTheoryTerm["atom"["symbolAtom"["System`Plus"]], "WolframLanguage"]]
```

<!-- => True -->

---

Two symbols with one name in two contexts are different atoms:

```wl
WeakHeadNormalForm[TypeTheoryTerm[SameQ[HoldForm[x], HoldForm[Other`x]], "WolframLanguage"]]
```

<!-- => false -->

---

A negative integer -(*n* + 1) is `"negativeAtom"` of *n*:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[HoldForm[-3], "WolframLanguage"], TypeTheoryTerm["atom"["negativeAtom"[2]], "WolframLanguage"]]
```

<!-- => True -->

---

A real number is `"otherAtom"` of its head and its [InputForm]():

```wl
DefinitionallyEqualQ[TypeTheoryTerm[HoldForm[1.5], "WolframLanguage"], TypeTheoryTerm["atom"["otherAtom"["System`Real", "1.5"]], "WolframLanguage"]]
```

<!-- => True -->

---

So is a rational number, whose head is [Rational]():

```wl
NormalForm[TypeTheoryTerm[Head["atom"["otherAtom"["System`Rational", "1/2"]]], "WolframLanguage"]]
```

<!-- => Rational -->

---

A name met twice in a pattern matches the same atom twice, which [SameQ]() decides:

```wl
NormalForm[TypeTheoryTerm[ReplaceList[f[x, y, x, z], f[___, a_, ___, a_, ___] :> a], "WolframLanguage"]]
```

<!-- => {x} -->

A negative integer where an expression is expected is its atom, `"negativeAtom"` of n - 1 for -n:

```wl
NormalForm[TypeTheoryTerm[Head[Construct[f, -2]], "WolframLanguage"]]
```

<!-- => f -->

## Properties and Relations

[AtomQ]() tells the atoms of a list from the expressions with parts:

```wl
NormalForm[TypeTheoryTerm[Map[Typed[e, Expressions] |-> AtomQ[e], {Arguments[HoldForm[{x, f[x], 1, "s"}]]}], "WolframLanguage"]]
```

<!-- => {true, false, true, true} -->

---

An atom has no arguments:

```wl
NormalForm[TypeTheoryTerm[Arguments[HoldForm[x]], "WolframLanguage"]]
```

<!-- => [] -->

---

Two real numbers with the same [InputForm]() are the same atom, however they are written:

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

A quoted fraction is no atom: [HoldForm]() keeps the product it is written as, where the Wolfram Language evaluates it to a [Rational]():

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
