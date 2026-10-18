---
Template: Symbol
Name: TypeTheoryEnvironment
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryEnvironment
Keywords: [environment, declarations, constants, prelude, kernel, theorem, axiom, definition, inductive type]
SeeAlso: [TypeTheoryTheorem, TypeTheoryAxiom, TypeTheoryDefinition, TypeTheoryInductiveType, TypeTheoryTerm, TypeTheoryCheck]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[TypeTheoryEnvironment]()[]</code> gives the environment with no constants.

<code>[TypeTheoryEnvironment]()["Prelude"]</code> gives the prelude: logic, equality and the natural numbers.

<code>[TypeTheoryEnvironment]()[{*declaration1*, *declaration2*, ...}]</code> checks the declarations in turn and gives the environment of their constants.

<code>[TypeTheoryEnvironment]()[*env*, {*declaration1*, ...}]</code> gives the environment *env* extended with the declarations.

## Details & Options

- A declaration is one of [TypeTheoryAxiom](), [TypeTheoryDefinition](), [TypeTheoryTheorem](), [TypeTheoryInductiveType]() and [TypeTheoryNaturalNumbers](). Each is checked by the kernel in the environment so far, and the result is a new environment, or a [Failure]() for the first declaration that does not check.
- An environment never changes: adding declarations gives a new one and leaves the old one as it was. <code>[Append]()[*env*, *declaration*]</code> adds one declaration.
- An environment behaves like an [Association]() of its constants. <code>*env*[*name*]</code> gives the declaration that introduced the constant *name*, and [Keys](), [Length](), [KeyExistsQ]() and [Normal]() work as for an [Association](). [Normal]() gives the declarations, written out exactly, so <code>[TypeTheoryEnvironment]()[[Normal]()[*env*]]</code> rebuilds *env*.
- <code>[Information]()[*env*, *property*]</code> gives `"Constants"`, `"Kinds"`, `"Axioms"` and `"NaturalNumbers"`.
- An environment is a handle to a store: a symbol whose definitions, its [DownValues](), hold the constants. The handle is small, so terms and proofs carry their environment with them, and a store lasts for the session.
- <code>[TypeTheoryCheck]()[*env*]</code> checks every declaration of *env* again from scratch.

## Basic Examples

The prelude:

```wl
prelude = TypeTheoryEnvironment["Prelude"]
```

<!-- => TypeTheoryEnvironment summary box: 31 constants -->

Add a theorem, proved by computation:

```wl
arithmetic = Append[prelude, TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, EqualityReflexivity[4]]]
```

<!-- => TypeTheoryEnvironment summary box: 32 constants -->

The declaration of the new constant:

```wl
arithmetic[TwoPlusTwo]
```

<!-- => theorem TwoPlusTwo : 2 + 2 == 4 -->

## Scope

An environment from declarations alone:

```wl
bits = TypeTheoryEnvironment[{
    TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}]
}];
Keys[bits]
```

<!-- => {Bit, BitZero, BitOne, InductiveRecursor[Bit]} -->

---

How many constants of each kind the prelude has:

```wl
Information[TypeTheoryEnvironment["Prelude"], "Kinds"]
```

<!-- => <|"InductiveType" -> 7, "Constructor" -> 8, "Recursor" -> 7, "Definition" -> 2, "Theorem" -> 7|> -->

---

Its natural numbers, which literals belong to:

```wl
Information[TypeTheoryEnvironment["Prelude"], "NaturalNumbers"]
```

<!-- => <|"Type" -> NonNegativeIntegers, "Zero" -> NaturalNumberZero, "Successor" -> NaturalNumberSuccessor, "Addition" -> Plus|> -->

## Properties and Relations

Adding a declaration leaves the old environment as it was:

```wl
prelude = TypeTheoryEnvironment["Prelude"];
extended = Append[prelude, TypeTheoryAxiom[Excluded, ForAll[{Typed[p, TypeUniverse[0]]}, Or[p, Not[p]]]]];
{KeyExistsQ[extended, Excluded], KeyExistsQ[prelude, Excluded]}
```

<!-- => {True, False} -->

---

[Normal]() gives the declarations to rebuild an environment from:

```wl
prelude = TypeTheoryEnvironment["Prelude"];
Keys[TypeTheoryEnvironment[Normal[prelude]]] === Keys[prelude]
```

<!-- => True -->

## Possible Issues

A name is held in a declaration, but [Keys]() and <code>*env*[*name*]</code> evaluate it, so a constant is best named by a symbol with no value. The built-in `Red` has one:

```wl
Keys[TypeTheoryEnvironment[{TypeTheoryInductiveType[Paint, TypeUniverse[1], {Red -> Paint}]}]]
```

<!-- => {Paint, RGBColor[1, 0, 0], InductiveRecursor[Paint]} -->

---

A declaration that does not check gives a [Failure]():

```wl
Append[TypeTheoryEnvironment["Prelude"], TypeTheoryTheorem[Wrong, 2 + 2 == 5, EqualityReflexivity[4]]]
```

<!-- => Failure["TypeMismatch", ...] -->
