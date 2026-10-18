---
Template: Symbol
Name: TypeTheoryEnvironment
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryEnvironment
Keywords: [environment, declarations, constants, prelude, constructive, classical, kernel, theorem, axiom, definition, inductive type]
SeeAlso: [TypeTheoryTheorem, TypeTheoryAxiom, TypeTheoryDefinition, TypeTheoryInductiveType, TypeTheoryTerm, TypeTheoryCheck]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[TypeTheoryEnvironment]()[{*declaration1*, *declaration2*, ...}]</code> checks the declarations in turn and gives the prelude extended with their constants.

<code>[TypeTheoryEnvironment]()[*env*, {*declaration1*, ...}]</code> gives the environment *env* extended with the declarations.

<code>[TypeTheoryEnvironment]()[]</code> gives the environment with no constants.

<code>[TypeTheoryEnvironment]()["Prelude"]</code> gives the prelude: classical logic, equality, the natural numbers and the Booleans.

<code>[TypeTheoryEnvironment]()["Constructive"]</code> gives the prelude without its axioms and the theorems proved from them.

## Details & Options

- A declaration is one of [TypeTheoryAxiom](), [TypeTheoryDefinition](), [TypeTheoryTheorem](), [TypeTheoryInductiveType]() and [TypeTheoryNaturalNumbers](). Each is checked by the kernel in the environment so far, and the result is a new environment, or a [Failure]() for the first declaration that does not check.
- The prelude is the environment wherever none is given: declarations without one extend it, and a [TypeTheoryTerm]() or [TypeTheoryProof]() without one is in it. <code>[TypeTheoryEnvironment]()[[TypeTheoryEnvironment]()[], {*declaration1*, ...}]</code> starts from no constants instead.
- The prelude is classical: it assumes [PropositionalExtensionality](), [FunctionExtensionality]() and [Choice](), and proves [ExcludedMiddle]() from them. The constructive environment has none of these, so other axioms can be declared on it with [TypeTheoryAxiom]().
- An environment never changes: adding declarations gives a new one and leaves the old one as it was. <code>[Append]()[*env*, *declaration*]</code> adds one declaration, and <code>[TypeTheoryEnvironment]()[*declaration*]</code> adds one to the prelude.
- An environment behaves like an [Association]() of its constants. <code>*env*[*name*]</code> gives the declaration that introduced the constant *name*, and [Keys](), [Length](), [KeyExistsQ]() and [Normal]() work as for an [Association](). [Normal]() gives all the declarations, the prelude's included, written out exactly, so <code>[TypeTheoryEnvironment]()[[TypeTheoryEnvironment]()[], [Normal]()[*env*]]</code> rebuilds *env*.
- <code>[Information]()[*env*, *property*]</code> gives `"Constants"`, `"Kinds"`, `"Axioms"` and `"NaturalNumbers"`.
- An environment is a handle to a store: a symbol whose definitions, its [DownValues](), hold the constants. The handle is small, so terms and proofs carry their environment with them, and a store lasts for the session.
- <code>[TypeTheoryCheck]()[*env*]</code> checks every declaration of *env* again from scratch.

## Basic Examples

Add a theorem to the prelude, proved by computation:

```wl
arithmetic = TypeTheoryEnvironment[{TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, EqualityReflexivity[4]]}]
```

<!-- => TypeTheoryEnvironment summary box: 110 constants -->

The declaration of the new constant:

```wl
arithmetic[TwoPlusTwo]
```

<!-- => theorem TwoPlusTwo : 2 + 2 == 4 -->

Add a definition to that environment:

```wl
doubled = Append[arithmetic, TypeTheoryDefinition[Doubled, Function[{Typed[n, NonNegativeIntegers]}, n + n]]]
```

<!-- => TypeTheoryEnvironment summary box: 111 constants -->

## Scope

An environment of only the declarations given, built on the empty environment:

```wl
bits = TypeTheoryEnvironment[TypeTheoryEnvironment[], {
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

<!-- => <|"InductiveType" -> 12, "Constructor" -> 15, "Recursor" -> 12, "Definition" -> 16, "Theorem" -> 51, "Axiom" -> 3|> -->

---

Its natural numbers, which literals belong to:

```wl
Information[TypeTheoryEnvironment["Prelude"], "NaturalNumbers"]
```

<!-- => <|"Type" -> NonNegativeIntegers, "Zero" -> NaturalNumberZero, "Successor" -> NaturalNumberSuccessor, "Addition" -> Plus|> -->

---

The constructive environment has no axioms, and no excluded middle:

```wl
constructive = TypeTheoryEnvironment["Constructive"];
{Information[constructive, "Axioms"], KeyExistsQ[constructive, ExcludedMiddle]}
```

<!-- => {{}, False} -->

## Properties and Relations

Adding a declaration leaves the old environment as it was:

```wl
arithmetic = TypeTheoryEnvironment[{TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, EqualityReflexivity[4]]}];
extended = Append[arithmetic, TypeTheoryAxiom[Origin, NonNegativeIntegers]];
{KeyExistsQ[extended, Origin], KeyExistsQ[arithmetic, Origin]}
```

<!-- => {True, False} -->

---

[Normal]() gives the declarations, which rebuild the environment on the empty one:

```wl
arithmetic = TypeTheoryEnvironment[{TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, EqualityReflexivity[4]]}];
Keys[TypeTheoryEnvironment[TypeTheoryEnvironment[], Normal[arithmetic]]] === Keys[arithmetic]
```

<!-- => True -->

## Possible Issues

A name is held in a declaration, but [Keys]() and <code>*env*[*name*]</code> evaluate it, so a constant is best named by a symbol with no value. The built-in `Red` has one:

```wl
Keys[TypeTheoryEnvironment[TypeTheoryEnvironment[], {TypeTheoryInductiveType[Paint, TypeUniverse[1], {Red -> Paint}]}]]
```

<!-- => {Paint, RGBColor[1, 0, 0], InductiveRecursor[Paint]} -->

---

The prelude has its natural numbers already, so natural numbers of your own go in an environment built on the empty one:

```wl
TypeTheoryEnvironment[{
    TypeTheoryInductiveType[Unary, TypeUniverse[1], {UnaryZero -> Unary, UnarySuccessor -> ForAll[{Typed[n, Unary]}, Unary]}],
    TypeTheoryNaturalNumbers[Unary, UnaryZero, UnarySuccessor]
}]
```

<!-- => Failure["NaturalNumbersRegistered", ...] -->

---

A declaration that does not check gives a [Failure]():

```wl
TypeTheoryEnvironment[{TypeTheoryTheorem[Wrong, 2 + 2 == 5, EqualityReflexivity[4]]}]
```

<!-- => Failure["TypeMismatch", ...] -->
