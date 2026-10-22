---
Template: Symbol
Name: TypeTheoryEnvironment
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryEnvironment
Keywords: [environment, declarations, constants, prelude, constructive, classical, kernel, theorem, axiom, definition, inductive type]
SeeAlso: [SetTypeTheoryEnvironment, TypeTheoryTheorem, TypeTheoryAxiom, TypeTheoryDefinition, TypeTheoryInductiveType, TypeTheoryRules, TypeTheoryRewriteRule, TypeTheoryTerm, TypeTheoryCheck]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[TypeTheoryEnvironment]()[{*declaration1*, *declaration2*, ...}]</code> checks the declarations in turn and gives the default environment, the prelude unless [SetTypeTheoryEnvironment]() set another, extended with their constants.

<code>[TypeTheoryEnvironment]()[*env*, {*declaration1*, ...}]</code> gives the environment *env* extended with the declarations.

<code>[TypeTheoryEnvironment]()[]</code> gives the environment with no constants.

<code>[TypeTheoryEnvironment]()["Prelude"]</code> gives the prelude: classical logic, equality, the natural numbers and the Booleans.

<code>[TypeTheoryEnvironment]()["Constructive"]</code> gives the prelude without its axioms and the theorems proved from them.

<code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code> gives homotopy type theory: paths, univalence and the circle, under rules without Prop.

<code>[TypeTheoryEnvironment]()[*rules*]</code> gives the environment with no constants that follows the [TypeTheoryRules]() *rules*, and <code>[TypeTheoryEnvironment]()[*rules*, {*declaration1*, ...}]</code> extends it.

## Details & Options

- A declaration is one of [TypeTheoryAxiom](), [TypeTheoryDefinition](), [TypeTheoryTheorem](), [TypeTheoryInductiveType](), [TypeTheoryNaturalNumbers]() and [TypeTheoryRewriteRule](). Each is checked by the kernel in the environment so far, and the result is a new environment, or a [Failure]() for the first declaration that does not check.
- The default environment, [$TypeTheoryEnvironment](), is the environment wherever none is given: declarations without one extend it, and a [TypeTheoryTerm]() or [TypeTheoryProof]() without one is in it. It is the prelude unless [SetTypeTheoryEnvironment]() set another. <code>[TypeTheoryEnvironment]()[[TypeTheoryEnvironment]()[], {*declaration1*, ...}]</code> starts from no constants instead.
- Every environment carries the rules it was started with, which say what the kernel allows and computes: the prelude follows the calculus of inductive constructions, the HoTT environment Martin-Löf type theory with rewrite rules. Environments made from one follow its rules, and <code>[Information]()[*env*, "Rules"]</code> gives them.
- The prelude is classical: it assumes [PropositionalExtensionality](), [FunctionExtensionality]() and [Choice](), and proves [ExcludedMiddle]() from them. The constructive environment has none of these, so other axioms can be declared on it with [TypeTheoryAxiom]().
- An environment never changes: adding declarations gives a new one and leaves the old one as it was. <code>[Append]()[*env*, *declaration*]</code> adds one declaration, and <code>[TypeTheoryEnvironment]()[*declaration*]</code> adds one to the default environment.
- An environment behaves like an [Association]() of its constants. <code>*env*[*name*]</code> gives the declaration that introduced the constant *name*, and [Keys](), [Length](), [KeyExistsQ]() and [Normal]() work as for an [Association](). [Normal]() gives all the declarations, the prelude's included, written out exactly, so <code>[TypeTheoryEnvironment]()[[TypeTheoryEnvironment]()[[Information]()[*env*, "Rules"]], [Normal]()[*env*]]</code> rebuilds *env* on the empty environment of its rules.
- <code>[Information]()[*env*, *property*]</code> gives `"Constants"`, `"Kinds"`, `"Axioms"`, `"RewriteRules"`, `"NaturalNumbers"` and `"Rules"`.
- An environment is a handle to a store: a symbol whose definitions, its [DownValues](), hold the constants. The handle is small, so terms and proofs carry their environment with them, and a store lasts for the session.
- <code>[TypeTheoryCheck]()[*env*]</code> checks every declaration of *env* again from scratch.

## Basic Examples

Add a theorem to the prelude, proved by computation:

```wl
arithmetic = TypeTheoryEnvironment[{TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, EqualityReflexivity[4]]}]
```

<!-- => TypeTheoryEnvironment summary box: 165 constants -->

The declaration of the new constant:

```wl
arithmetic[TwoPlusTwo]
```

<!-- => theorem TwoPlusTwo : 2 + 2 == 4 -->

Add a definition to that environment:

```wl
doubled = Append[arithmetic, TypeTheoryDefinition[Doubled, Function[{Typed[n, Naturals]}, n + n]]]
```

<!-- => TypeTheoryEnvironment summary box: 166 constants -->

## Scope

An environment of only the declarations given, built on the empty environment:

```wl
bits = TypeTheoryEnvironment[TypeTheoryEnvironment[], {
    TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}]
}]
```

<!-- => TypeTheoryEnvironment summary box: 4 constants -->

Its constants are the type, its constructors and its recursor:

```wl
Keys[bits]
```

<!-- => {Bit, BitZero, BitOne, InductiveRecursor[Bit]} -->

---

How many constants of each kind the prelude has:

```wl
Information[TypeTheoryEnvironment["Prelude"], "Kinds"]
```

<!-- => <|"InductiveType" -> 17, "Constructor" -> 24, "Recursor" -> 17, "Definition" -> 32, "Theorem" -> 71, "Axiom" -> 3|> -->

---

Its natural numbers, which literals belong to, and the operations the kernel computes on literals:

```wl
Information[TypeTheoryEnvironment["Prelude"], "NaturalNumbers"]
```

<!-- => <|"Type" -> NonNegativeIntegers, "Zero" -> NaturalNumberZero, "Successor" -> NaturalNumberSuccessor, "Operations" -> <|"Addition" -> Plus, "Subtraction" -> Subtract, "Multiplication" -> Times, "Power" -> Power, "Equal" -> "equal", "LessEqual" -> "lessEqual"|>|> -->

---

The constructive environment:

```wl
constructive = TypeTheoryEnvironment["Constructive"]
```

<!-- => TypeTheoryEnvironment summary box: 151 constants -->

It has no axioms:

```wl
Information[constructive, "Axioms"]
```

<!-- => {} -->

And no excluded middle:

```wl
KeyExistsQ[constructive, ExcludedMiddle]
```

<!-- => False -->

---

The HoTT environment follows other rules than the prelude:

```wl
Information[TypeTheoryEnvironment["HomotopyTypeTheory"], "Rules"]["Name"]
```

<!-- => "MartinLofTypeTheory" -->

## Properties and Relations

Add a theorem to the prelude:

```wl
arithmetic = TypeTheoryEnvironment[{TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, EqualityReflexivity[4]]}]
```

<!-- => TypeTheoryEnvironment summary box: 165 constants -->

Add an axiom to that environment:

```wl
extended = Append[arithmetic, TypeTheoryAxiom[Origin, Naturals]]
```

<!-- => TypeTheoryEnvironment summary box: 166 constants -->

The new environment has the axiom:

```wl
KeyExistsQ[extended, Origin]
```

<!-- => True -->

Adding a declaration leaves the old environment as it was:

```wl
KeyExistsQ[arithmetic, Origin]
```

<!-- => False -->

---

Add a theorem to the prelude:

```wl
arithmetic = TypeTheoryEnvironment[{TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, EqualityReflexivity[4]]}]
```

<!-- => TypeTheoryEnvironment summary box: 165 constants -->

[Normal]() gives the declarations, which rebuild the environment on the empty one:

```wl
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
