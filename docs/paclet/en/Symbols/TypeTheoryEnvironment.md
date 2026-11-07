---
Template: Symbol
Name: TypeTheoryEnvironment
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryEnvironment
Keywords: [environment, declarations, constants, prelude, constructive, classical, kernel, theorem, axiom, definition, inductive type, library environment, integers, rationals, homotopy type theory, cubical, saved environment, compiled kernel]
SeeAlso: [SetTypeTheoryEnvironment, $TypeTheoryEnvironment, TypeTheoryTheorem, TypeTheoryAxiom, TypeTheoryDefinition, TypeTheoryInductiveType, TypeTheoryRules, TypeTheoryRewriteRule, TypeTheoryTerm, TypeTheoryCheck, TypeTheoryTranslate]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TypeTheoryIntroduction, ThePrelude, TheIntegers]
---

## Usage

<code>[TypeTheoryEnvironment]()[{*declaration1*, *declaration2*, ...}]</code> checks the declarations in turn and gives the default environment, the prelude unless [SetTypeTheoryEnvironment]() set another, extended with their constants.

<code>[TypeTheoryEnvironment]()[*env*, {*declaration1*, ...}]</code> gives the environment *env* extended with the declarations.

<code>[TypeTheoryEnvironment]()["*name*", {*declaration1*, ...}]</code> extends the library environment called *name*.

<code>[TypeTheoryEnvironment]()[]</code> gives the environment with no constants.

<code>[TypeTheoryEnvironment]()["Prelude"]</code> gives the prelude: classical logic, equality, the natural numbers, the Booleans, and the expressions, strings and pattern matching of the Wolfram Language.

<code>[TypeTheoryEnvironment]()["Constructive"]</code> gives the prelude without its axioms, the theorems proved from them and the Wolfram Language's expressions.

<code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code> gives homotopy type theory: paths, univalence and the circle, under rules without Prop.

<code>[TypeTheoryEnvironment]()["Integers"]</code> gives the prelude with the integers, a quotient of pairs of natural numbers, and the laws of a commutative ring.

<code>[TypeTheoryEnvironment]()["Rationals"]</code> gives the integers with the rationals, a quotient of pairs of an integer and a natural number, and the laws of a field.

<code>[TypeTheoryEnvironment]()["Machine"]</code> gives the integers with the 64-bit integers of the compiler's typed entries, a subtype of the integers in [-2^63, 2^63), whose operations give `Failure["IntegerOverflow", <||>]`, the leave of a typed entry, where a result is out of range.

<code>[TypeTheoryEnvironment]()["Cubical"]</code> gives cubical type theory, with paths as functions of an interval and univalence that computes, under rules without Prop.

<code>[TypeTheoryEnvironment]()[*rules*]</code> gives the environment with no constants that follows the [TypeTheoryRules]() *rules*, and <code>[TypeTheoryEnvironment]()[*rules*, {*declaration1*, ...}]</code> extends it.

<code>[TypeTheoryEnvironment]()[[File]()["*file*.wxf"]]</code> reads the environment that <code>[Export]()["*file*.wxf", *env*]</code> saved, without checking its declarations again.

## Details & Options

- A declaration is one of [TypeTheoryAxiom](), [TypeTheoryDefinition](), [TypeTheoryTheorem](), [TypeTheoryInductiveType](), [TypeTheoryNaturalNumbers](), [TypeTheoryRewriteRule](), [TypeTheoryQuotients]() and [TypeTheoryCubical](). Each is checked by the kernel in the environment the declarations before it made, and the result is a new environment, or a [Failure]() for the first declaration that does not check, with none of them added.
- A single declaration needs no list: <code>[TypeTheoryEnvironment]()[*declaration*]</code> and <code>[TypeTheoryEnvironment]()[*env*, *declaration*]</code> add one, and so does <code>[Append]()[*env*, *declaration*]</code>.
- The library environments are named by strings: `"Prelude"`, `"Constructive"`, `"HomotopyTypeTheory"`, `"Integers"`, `"Rationals"`, `"Machine"` and `"Cubical"`, and `"WolframLanguage"` is an old name of the prelude, from when the Wolfram Language's expressions were an environment of their own. Every function that takes an environment takes its name too, as in <code>[TypeTheoryTerm]()[*term*, "Integers"]</code>, <code>[TypeTheoryProof]()[*statement*, "Integers", {...}]</code> and <code>[TypeTheoryType]()[*term*, "HomotopyTypeTheory"]</code>. Any other name gives a [Failure]() tagged `"UnknownEnvironment"` that lists the names.
- The default environment, [$TypeTheoryEnvironment](), is the environment wherever none is given: declarations without one extend it, and a [TypeTheoryTerm]() or [TypeTheoryProof]() without one is in it. It is the prelude unless [SetTypeTheoryEnvironment]() set another. <code>[TypeTheoryEnvironment]()[[TypeTheoryEnvironment]()[], {*declaration1*, ...}]</code> starts from no constants instead.
- Every environment carries the rules it was started with, which say what the kernel allows and computes: the prelude follows the calculus of inductive constructions, the HoTT environment Martin-Löf type theory with rewrite rules, and the cubical environment cubical type theory. Environments made from one follow its rules, and <code>[Information]()[*env*, "Rules"]</code> gives them.
- The prelude is classical: it assumes `"propositionalExtensionality"`, `"quotientSoundness"` and `"choice"`, and proves `"functionExtensionality"` and `"excludedMiddle"` from them. Its fourth axiom, [ExpressionEvaluate](), is the evaluation of the Wolfram Language. The constructive environment has none of these, so other axioms can be declared on it with [TypeTheoryAxiom]().
- An environment never changes: adding declarations gives a new one and leaves the old one as it was.
- An environment behaves like an [Association]() of its constants. <code>*env*[*name*]</code> gives the declaration that introduced the constant *name*, and [Keys](), [Length](), [KeyExistsQ]() and [Normal]() work as for an [Association](). [Normal]() gives all the declarations, the prelude's included, written out exactly, so <code>[TypeTheoryEnvironment]()[[TypeTheoryEnvironment]()[[Information]()[*env*, "Rules"]], [Normal]()[*env*]]</code> rebuilds *env* on the empty environment of its rules.
- <code>[Information]()[*env*, *property*]</code> gives `"Constants"`, `"Kinds"`, `"Theorems"`, `"Axioms"`, `"RewriteRules"`, `"NaturalNumbers"`, `"Rules"` and `"Provenance"`, which says whether *env* was read from a file without checking it.
- An environment is a handle to a store: a symbol whose definitions, its [DownValues](), hold the constants. The handle is small, so terms and proofs carry their environment with them, and a store lasts for the session. A library environment is built once a session, the first time it is asked for.
- <code>[TypeTheoryCheck]()[*env*]</code> checks every declaration of *env* again from scratch.
- <code>[TypeTheoryEnvironment]()[*env*, {*declaration1*, ...}, [Method]() -> "Compiled"]</code> adds the declarations without checking them, inductive types aside, and then checks them all at once with the compiled kernel (see [TypeTheoryCheck]()), which is faster for many declarations, as an import from Lean has. Where the compiled kernel cannot check them, or one does not check, the declarations are added again with each one checked, so the result is the same as without the option.
- <code>[Export]()["*file*.wxf", *env*]</code> saves *env* in a file that holds each of its terms once, and only the constants beyond the library environment it extends, such as the prelude, which it names. A file reads back in a fraction of the time its declarations take to check.
- Reading a file takes its declarations as checked, as Lean takes an `.olean` file it imports. The option `"Check" -> True` checks every declaration again with [TypeTheoryCheck]() as it reads the file. A file saved by another version of TypeTheory reads only with `"Check" -> True`.
- A file is read without evaluating anything in it, and a file that holds anything but terms and plain data, or whose terms were changed out of order, is refused.
- The library environments are read from files saved with the paclet, so loading the paclet does not check the prelude again.

## Basic Examples

Add a theorem to the prelude, proved by computation:

```wl
arithmetic = TypeTheoryEnvironment[{TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, "equalityReflexivity"[4]]}]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

The declaration of the new constant:

```wl
arithmetic[TwoPlusTwo]
```

<!-- => theorem TwoPlusTwo : 2 + 2 == 4 -->

---

A library environment by its name, here the integers:

```wl
TypeTheoryEnvironment["Integers"]
```

<!-- => TypeTheoryEnvironment summary box: 344 constants -->

---

Extend the integers by their name with a theorem, proved by the tactic `"Ring"`:

```wl
squares = TypeTheoryEnvironment["Integers", {
    TypeTheoryTheorem[SquareOfSum, TypeTheoryProof[
        ForAll[{Typed[x, Integers], Typed[y, Integers]}, (x + y)^2 == x^2 + 2 x y + y^2],
        "Integers",
        {"Introduce"[x, y], "Ring"}
    ]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 345 constants -->

The theorem it declares:

```wl
squares[SquareOfSum]
```

<!-- => theorem SquareOfSum : ∀_x∶ℤ ∀_y∶ℤ (x + y)^2 == x^2 + 2 x y + y^2 -->

---

A declaration that does not check gives a [Failure](), with the reason:

```wl
TypeTheoryEnvironment[{TypeTheoryTheorem[Wrong, 2 + 2 == 5, "equalityReflexivity"[4]]}]
```

<!-- => Failure["TypeMismatch", ...]: equalityReflexivity[4] has type 4 == 4, but the expected type is 2 + 2 == 5 -->

## Scope

### Declarations

Each declaration is checked in the environment the ones before it made, so a function can recurse on a type declared just before it. Binary trees and the number of their nodes:

```wl
trees = TypeTheoryEnvironment[{
    TypeTheoryInductiveType[BinaryTree, TypeUniverse[1], {
        BinaryLeaf -> BinaryTree,
        BinaryNode -> ForAll[{Typed[left, BinaryTree], Typed[right, BinaryTree]}, BinaryTree]
    }],
    TypeTheoryDefinition[NodeCount, tree |-> InductiveRecursor[BinaryTree][Naturals &, 1, {left, right, l, r} |-> l + r + 1, tree]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 262 constants -->

A node over a leaf and a node of two leaves has five nodes:

```wl
WeakHeadNormalForm[TypeTheoryTerm[NodeCount[BinaryNode[BinaryLeaf, BinaryNode[BinaryLeaf, BinaryLeaf]]], trees]]
```

<!-- => 5 -->

---

A single declaration needs no list. Assume a natural number about which nothing is known:

```wl
mystery = TypeTheoryEnvironment[TypeTheoryAxiom[Mystery, Naturals]]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

[Append]() adds one declaration, here a theorem about the axiom that holds by computation:

```wl
Append[mystery, TypeTheoryTheorem[MysteryPlusZero, Mystery + 0 == Mystery, "equalityReflexivity"[Mystery]]]
```

<!-- => TypeTheoryEnvironment summary box: 259 constants -->

---

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

An environment that follows other rules, Martin-Löf type theory, where a theorem may state a type:

```wl
units = TypeTheoryEnvironment[TypeTheoryRules["MartinLofTypeTheory"], {
    TypeTheoryInductiveType[Unit, TypeUniverse[1], {UnitIntroduction -> Unit}],
    TypeTheoryTheorem[UnitInhabited, Unit, UnitIntroduction]
}]
```

<!-- => TypeTheoryEnvironment summary box: 4 constants -->

The theorem states the type `Unit`:

```wl
units[UnitInhabited]
```

<!-- => theorem UnitInhabited : Unit -->

### Library environments

The constructive environment, the prelude without its axioms and the Wolfram Language's expressions:

```wl
constructive = TypeTheoryEnvironment["Constructive"]
```

<!-- => TypeTheoryEnvironment summary box: 155 constants -->

It has no axioms:

```wl
Information[constructive, "Axioms"]
```

<!-- => {} -->

---

Assume the excluded middle in the constructive environment, extended by its name:

```wl
TypeTheoryEnvironment["Constructive", {
    TypeTheoryAxiom["excludedMiddle", ForAll[{p}, Or[p, Not[p]]]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 156 constants -->

---

Homotopy type theory, with univalence and the circle:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

Its axioms:

```wl
Information[hott, "Axioms"]
```

<!-- => {univalence, Circle, circleBase, circleLoop, circleInduction, circleInductionLoop} -->

---

The rationals, which extend the integers:

```wl
TypeTheoryEnvironment["Rationals"]
```

<!-- => TypeTheoryEnvironment summary box: 423 constants -->

---

Cubical type theory, in which univalence computes:

```wl
TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

---

The old name `"WolframLanguage"` names the prelude, which has the expressions of the Wolfram Language:

```wl
TypeTheoryEnvironment["WolframLanguage"] === TypeTheoryEnvironment["Prelude"]
```

<!-- => True -->

### Information

The declaration of a constant of the prelude, the natural numbers:

```wl
TypeTheoryEnvironment["Prelude"][Naturals]
```

<!-- => inductive ℕ : Type | zero : ℕ | successor : ℕ → ℕ -->

---

How many constants of each kind the prelude has:

```wl
Information[TypeTheoryEnvironment["Prelude"], "Kinds"]
```

<!-- => <|"InductiveType" -> 27, "Constructor" -> 41, "Recursor" -> 28, "Definition" -> 81, "Quotient" -> 4, "Theorem" -> 72, "Axiom" -> 4|> -->

---

Its theorems, constants named by strings, each with its statement:

```wl
Take[Information[TypeTheoryEnvironment["Prelude"], "Theorems"], 3]
```

<!-- => <|"falseElimination" -> ∀_{a∶Prop} False ⇒ a, "andEliminationLeft" -> ∀_{a∶Prop} ∀_{b∶Prop} (a ∧ b) ⇒ a, "andEliminationRight" -> ∀_{a∶Prop} ∀_{b∶Prop} (a ∧ b) ⇒ b|> -->

---

Its natural numbers, which literals belong to, and the operations the kernel computes on literals:

```wl
Information[TypeTheoryEnvironment["Prelude"], "NaturalNumbers"]
```

<!-- => <|"Type" -> ℤ_≥0, "Zero" -> "zero", "Successor" -> "successor", "Operations" -> <|"Addition" -> Plus, "Subtraction" -> Subtract, "Multiplication" -> Times, "Power" -> Power, "Equal" -> "equal", "LessEqual" -> "lessEqual"|>|> -->

---

The rewrite rules of the HoTT environment, which make induction on the circle compute on its base point:

```wl
Information[TypeTheoryEnvironment["HomotopyTypeTheory"], "RewriteRules"]
```

<!-- => {circleInductionBase} -->

---

The HoTT environment follows other rules than the prelude:

```wl
Information[TypeTheoryEnvironment["HomotopyTypeTheory"], "Rules"]["Name"]
```

<!-- => "MartinLofTypeTheory" -->

### Saved environments

An environment with a theorem:

```wl
arithmetic = TypeTheoryEnvironment[{TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, "equalityReflexivity"[4]]}]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

Save it in a file:

```wl
file = Export[FileNameJoin[{$TemporaryDirectory, "arithmetic.wxf"}], arithmetic]
```

<!-- => File[.../arithmetic.wxf] -->

Read it back:

```wl
saved = TypeTheoryEnvironment[file]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

It has the same declarations:

```wl
Normal[saved] === Normal[arithmetic]
```

<!-- => True -->

The environment read from the file says that it was not checked:

```wl
Information[saved, "Provenance"]["Checked"]
```

<!-- => False -->

## Options

### Method

Rebuild the prelude from its declarations on the empty environment, checked at once by the compiled kernel:

```wl
TypeTheoryEnvironment[TypeTheoryEnvironment[], Normal[TypeTheoryEnvironment["Prelude"]], Method -> "Compiled"]
```

<!-- => TypeTheoryEnvironment summary box: 257 constants -->

---

A declaration that does not check gives the same [Failure]() as without the option:

```wl
TypeTheoryEnvironment["Integers", {TypeTheoryTheorem[Wrong, 2 + 2 == 5, "equalityReflexivity"[4]]}, Method -> "Compiled"]
```

<!-- => Failure["TypeMismatch", ...] -->

### Check

An environment saved in a file:

```wl
file = Export[FileNameJoin[{$TemporaryDirectory, "checked.wxf"}], TypeTheoryEnvironment[{TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, "equalityReflexivity"[4]]}]]
```

<!-- => File[.../checked.wxf] -->

`"Check" -> True` checks every declaration as it reads the file:

```wl
Information[TypeTheoryEnvironment[file, "Check" -> True], "Provenance"]["Checked"]
```

<!-- => True -->

## Properties and Relations

Add a theorem to the prelude:

```wl
arithmetic = TypeTheoryEnvironment[{TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, "equalityReflexivity"[4]]}]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

Add an axiom to that environment:

```wl
extended = Append[arithmetic, TypeTheoryAxiom[Origin, Naturals]]
```

<!-- => TypeTheoryEnvironment summary box: 259 constants -->

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

The integers extend the prelude, so every constant of the prelude is one of theirs:

```wl
SubsetQ[Keys[TypeTheoryEnvironment["Integers"]], Keys[TypeTheoryEnvironment["Prelude"]]]
```

<!-- => True -->

---

A library environment is built once a session, so its name stands for the same environment each time:

```wl
TypeTheoryEnvironment["Integers"] === TypeTheoryEnvironment["Integers"]
```

<!-- => True -->

---

Declarations without an environment extend the default one, here the integers for one computation:

```wl
Block[{$TypeTheoryEnvironment = "Integers"}, TypeTheoryEnvironment[{TypeTheoryDefinition[IntegerSquare, Typed[x, Integers] |-> x x]}]]
```

<!-- => TypeTheoryEnvironment summary box: 345 constants -->

---

Add a theorem to the prelude:

```wl
arithmetic = TypeTheoryEnvironment[{TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, "equalityReflexivity"[4]]}]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

[Normal]() gives the declarations, which rebuild the environment on the empty one:

```wl
Keys[TypeTheoryEnvironment[TypeTheoryEnvironment[], Normal[arithmetic]]] === Keys[arithmetic]
```

<!-- => True -->

[TypeTheoryCheck]() checks every declaration again from scratch:

```wl
TypeTheoryCheck[arithmetic]
```

<!-- => Success["EnvironmentChecked", ...] -->

## Possible Issues

A name of no library environment gives a [Failure]() that lists the names:

```wl
TypeTheoryEnvironment["Integer"]
```

<!-- => Failure["UnknownEnvironment", ...]: Integer is not the name of a library environment, which are {Prelude, Constructive, HomotopyTypeTheory, Integers, Rationals, Cubical, WolframLanguage}. -->

---

A constant cannot be declared twice. The prelude proves the excluded middle, so the name is taken there:

```wl
TypeTheoryEnvironment[{TypeTheoryAxiom["excludedMiddle", ForAll[{p}, Or[p, Not[p]]]]}]
```

<!-- => Failure["AlreadyDeclared", ...] -->

---

Only declarations extend an environment; a rule is not one:

```wl
TypeTheoryEnvironment[{TwoPlusTwo -> 2 + 2 == 4}]
```

<!-- => Failure["DeclarationExpected", ...] -->

---

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
