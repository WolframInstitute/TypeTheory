---
Template: Symbol
Name: Atoms
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Atoms
Keywords: [Wolfram Language, expressions, atoms, symbols, contexts, integers, strings, real numbers, rationals, AtomQ, SameQ, Head, Unevaluated, pattern matching, prelude]
SeeAlso: [Expressions, Strings, Arguments, TypeTheoryEnvironment]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, PatternsAndRewriting]
---

## Usage

[Atoms]() is the type of the expressions of the Wolfram Language that have no parts, as data: symbols by their full names, integers, strings, and other atoms by their head and [InputForm]().

## Details & Options

- [Atoms]() is an inductive type of the prelude, with five constructors: `"symbolAtom"` of a symbol's full name, `"naturalAtom"` of a natural number, `"negativeAtom"` of *n* for the integer -(*n* + 1), `"stringAtom"` of a string, and `"otherAtom"` of the head and the [InputForm]() of any other atom, as a real or a rational number.
- `"atom"`, of the type `Atoms -> Expressions`, makes an expression of an atom, and an atom shows as the Wolfram Language atom it stands for.
- A quotation, <code>[Unevaluated]()[*e*]</code>, makes the atoms of *e* itself, and nothing declares them. Where an expression is expected, a natural number or a string is its atom by a coercion, a negative integer is its atom, and a symbol that names nothing stands for its own atom.
- The head of an atom is [Symbol](), [Integer]() or [String](), or the head that `"otherAtom"` was given, so a pattern such as `_Integer` or `_Symbol` matches the atoms of that kind. [AtomQ]() of an atom is `"true"`, and its [Arguments]() are the empty sequence.
- [SameQ]() of two atoms is a definition, which the kernel computes: two symbols are the same where their full names are, and two other atoms where their values are. Two real numbers are the same where their [InputForm]() is, which [SameQ]() of the Wolfram Language relaxes by a tolerance.

## Basic Examples

The atoms are a type of the prelude:

```wl
TypeTheoryType[Atoms]
```

<!-- => Type -->

---

The five kinds of atoms:

```wl
TypeTheoryEnvironment["Prelude"][Atoms]
```

<!-- => inductive Atoms : Type | symbolAtom : Strings → Atoms | naturalAtom : ℕ → Atoms | negativeAtom : ℕ → Atoms | stringAtom : Strings → Atoms | otherAtom : Strings → Strings → Atoms -->

---

An atom makes an expression:

```wl
TypeTheoryType["atom"]
```

<!-- => Atoms → Expressions -->

---

`_Integer` picks out the integers among the parts of a list, positive or negative:

```wl
NormalForm[TypeTheoryTerm[ReplaceList[Unevaluated[{x, 1, -2, "s", 1.5}], {___, a_Integer, ___} :> a]]]
```

<!-- => {1, -2} -->

## Scope

A symbol is the atom of its full name, a string:

```wl
TypeTheoryType["symbolAtom"]
```

<!-- => Strings → Atoms -->

The head of a sum is the atom of the symbol [Plus]():

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Head[a + b]], TypeTheoryTerm["atom"["symbolAtom"["System`Plus"]]]]
```

<!-- => True -->

---

Two symbols with one name in two contexts are different atoms:

```wl
TypeTheoryProof[SameQ[x, Other`x] == "false", {"Reflexivity"}]
```

<!-- => Proof complete -->

---

An integer is `"naturalAtom"` or `"negativeAtom"` of a natural number:

```wl
TypeTheoryType["negativeAtom"]
```

<!-- => ℕ → Atoms -->

The integer -(*n* + 1) is `"negativeAtom"` of *n*:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[-3], TypeTheoryTerm["atom"["negativeAtom"[2]]]]
```

<!-- => True -->

---

A negative integer is an expression where one is expected:

```wl
TypeTheoryType[Typed[-2, Expressions]]
```

<!-- => Expressions -->

---

Any other atom is made of two strings, its head and its [InputForm]():

```wl
TypeTheoryType["otherAtom"]
```

<!-- => Strings → Strings → Atoms -->

So a real number is `"otherAtom"` of [Real]() and its digits:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[1.5], TypeTheoryTerm["atom"["otherAtom"["System`Real", "1.5"]]]]
```

<!-- => True -->

---

A name met twice in a pattern matches the same atom twice, which [SameQ]() decides:

```wl
NormalForm[TypeTheoryTerm[ReplaceList[f[x, y, x, z], f[___, a_, ___, a_, ___] :> a]]]
```

<!-- => {x} -->

## Properties and Relations

The head of an atom is an atom, defined by cases on the five kinds: [Symbol](), [Integer]() twice, [String](), and the head `"otherAtom"` was given:

```wl
TypeTheoryEnvironment["Prelude"]["atomHead"]
```

<!-- => definition atomHead : Atoms → Atoms := (a ∶ Atoms) ↦ (Atoms_rec)[(x ∶ Atoms) ↦ Atoms, (s ∶ Strings) ↦ symbolAtom["System`Symbol"], (n ∶ ℕ) ↦ symbolAtom["System`Integer"], (n ∶ ℕ) ↦ symbolAtom["System`Integer"], (s ∶ Strings) ↦ symbolAtom["System`String"], (h ∶ Strings) (s ∶ Strings) ↦ symbolAtom[h], a] -->

---

[AtomQ]() says whether an expression is an atom, a Boolean:

```wl
TypeTheoryType[AtomQ]
```

<!-- => Expressions → 𝔹 -->

Every atom is one, by computation:

```wl
TypeTheoryProof[ForAll[{Typed[a, Atoms]}, AtomQ["atom"[a]] == "true"], {"Introduce"[a], "Reflexivity"}]
```

<!-- => Proof complete -->

---

An atom has no arguments, whatever atom it is:

```wl
TypeTheoryProof[ForAll[{Typed[a, Atoms]}, Length[{Arguments["atom"[a]]}] == 0], {"Introduce"[a], "Reflexivity"}]
```

<!-- => Proof complete -->

---

Two real numbers with the same [InputForm]() are the same atom, however they are written:

```wl
TypeTheoryProof[SameQ[1.5, 1.50] == "true", {"Reflexivity"}]
```

<!-- => Proof complete -->

## Possible Issues

Two real numbers whose [InputForm]() differs are not the same atom:

```wl
TypeTheoryProof[SameQ[0.3, 0.30000000000000004] == "false", {"Reflexivity"}]
```

<!-- => Proof complete -->

[SameQ]() of the Wolfram Language takes them as the same, within a tolerance:

```wl
SameQ[0.3, 0.30000000000000004]
```

<!-- => True -->

---

A fraction of integers is the rational number the Wolfram Language evaluates it to, an atom:

```wl
NormalForm[TypeTheoryTerm[Head[1/2]]]
```

<!-- => Rational -->

[Unevaluated]() keeps the product it is written as, as it does in the Wolfram Language:

```wl
NormalForm[TypeTheoryTerm[Head[Unevaluated[1/2]]]]
```

<!-- => Times -->

The rational number one half is `"otherAtom"` of [Rational]() and its [InputForm]():

```wl
TypeTheoryType["otherAtom"["System`Rational", "1/2"]]
```

<!-- => Atoms -->

---

A natural number is an expression by a coercion, not an atom:

```wl
TypeTheoryType[Typed[3, Atoms]]
```

<!-- => Failure["TypeMismatch", ...] -->

---

On its own, a negative integer is its atom, an expression, as the prelude has no integers:

```wl
TypeTheoryType[-2]
```

<!-- => Expressions -->

Where the integers are declared, it is an integer:

```wl
TypeTheoryType[-2, "Integers"]
```

<!-- => ℤ -->
