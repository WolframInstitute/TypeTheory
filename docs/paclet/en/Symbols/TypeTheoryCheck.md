---
Template: Symbol
Name: TypeTheoryCheck
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryCheck
Keywords: [type checking, kernel, type inference, environment, replay, trust, proof checking, compiled kernel, saved environment]
SeeAlso: [TypeTheoryType, TypeTheoryTerm, TypeTheoryEnvironment, DefinitionallyEqualQ, WeakHeadNormalForm, TypeTheoryTheorem, TypeTheoryTranslate]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[TypeTheoryCheck]()[*term*]</code> gives the type of the [TypeTheoryTerm]() *term* by calling <code>[TypeTheoryType]()[*term*]</code>.

<code>[TypeTheoryCheck]()[*term*, *type*]</code> gives a [Success]() if *term* has the given *type*, and a [Failure]() otherwise.

<code>[TypeTheoryCheck]()[*env*]</code> checks every declaration of the [TypeTheoryEnvironment]() *env*, or of the library environment named *env*, again from scratch and gives a [Success](), or a [Failure]() for the first declaration that does not check.

## Details & Options

- *term* and *type* are [TypeTheoryTerm]() expressions. [TypeTheoryCheck]() does not hold its arguments, so an expression of the type theory is given inside [TypeTheoryTerm](), or to [TypeTheoryType](), which holds it.
- In <code>[TypeTheoryCheck]()[*term*, *type*]</code>, a term or type without an environment takes the other's, and both without one are in the default environment, [$TypeTheoryEnvironment](). Two different environments give a [Failure]() tagged `"DifferentEnvironments"`.
- *type* is elaborated as a type first, and *term* is then elaborated against it, so the type decides what the term leaves out, such as the types of the variables of a function.
- A check that passes gives a [Success]() whose message says what was checked: the tag `"TypeChecked"` with the term and the type under `"Term"` and `"Type"`, or `"EnvironmentChecked"` with the number of constants under `"Constants"`. A check that does not pass gives a [Failure](), so <code>[FailureQ]()[[TypeTheoryCheck]()[...]]</code> tells the two apart.
- An environment's store could be changed by hand, and an environment read from a file with <code>[TypeTheoryEnvironment]()[[File]()[...]]</code> is not checked. <code>[TypeTheoryCheck]()[*env*]</code> replays every declaration on the empty environment of the same rules and compares each record with the one the replay produces, which catches a forged theorem or recursor; each part of the store made from the records, as the index of rewrite rules that computation reads, is compared with the one the replay makes, and is never read from a file. Axioms and rewrite rules are taken on trust.
- <code>[TypeTheoryCheck]()[*env*]</code> takes the option [Method](). With the default, [Automatic](), it checks the declarations with the compiled kernel, the same algorithm compiled to native code, where the paclet has a library for the platform and the compiled kernel handles *env*, and then makes every declaration again from its record without checking its terms a second time, comparing each record whole, as the kernel written in Wolfram Language does; otherwise every declaration is replayed with the kernel written in Wolfram Language. `Method -> "Symbolic"` always replays with the kernel written in Wolfram Language, and `Method -> "Compiled"` gives a [Failure]() tagged `"CompiledKernelUnavailable"` where the compiled kernel cannot check *env*.
- The compiled kernel checks environments under rules with Prop and without rewrite rules, quantities or cubical type theory, whose natural number literals are below 2^62.

## Basic Examples

A proof of `2 + 2 == 4` by computation:

```wl
TypeTheoryCheck[TypeTheoryTerm["equalityReflexivity"[4]], TypeTheoryTerm[2 + 2 == 4]]
```

<!-- => Success["TypeChecked", ...] -->

---

The type of a term, given by [TypeTheoryType]():

```wl
TypeTheoryCheck[TypeTheoryTerm["equalityReflexivity"[4]]]
```

<!-- => 4 == 4 -->

---

Check an environment again from scratch, the prelude's declarations included:

```wl
TypeTheoryCheck[TypeTheoryEnvironment[{TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, "equalityReflexivity"[4]]}]]
```

<!-- => Success["EnvironmentChecked", ...] -->

## Scope

The type checked against gives the variable of a function its type:

```wl
TypeTheoryCheck[TypeTheoryTerm[n |-> n + 1], TypeTheoryTerm[Naturals -> Naturals]]
```

<!-- => Success["TypeChecked", ...] -->

---

The type decides what an overloaded term is. Against `Prop`, [True]() is the proposition:

```wl
TypeTheoryCheck[TypeTheoryTerm[True], TypeTheoryTerm[TypeUniverse[0]]]
```

<!-- => Success["TypeChecked", ...] -->

Against [Booleans](), it is the Boolean:

```wl
TypeTheoryCheck[TypeTheoryTerm[True], TypeTheoryTerm[Booleans]]
```

<!-- => Success["TypeChecked", ...] -->

---

A theorem of the integers has the statement it is meant to have:

```wl
TypeTheoryCheck[
    TypeTheoryTerm["integerAdditionCommutativity", "Integers"],
    TypeTheoryTerm[ForAll[{Typed[a, Integers], Typed[b, Integers]}, a + b == b + a]]
]
```

<!-- => Success["TypeChecked", ...] -->

---

A type of bits:

```wl
bits = TypeTheoryEnvironment[{TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}]}]
```

<!-- => TypeTheoryEnvironment summary box: 261 constants -->

The type has no environment, so it takes the term's:

```wl
TypeTheoryCheck[TypeTheoryTerm[BitOne, bits], TypeTheoryTerm[Bit]]
```

<!-- => Success["TypeChecked", ...] -->

---

The [Success]() holds the term and the type that were checked:

```wl
checked = TypeTheoryCheck[TypeTheoryTerm["equalityReflexivity"[4]], TypeTheoryTerm[2 + 2 == 4]]
```

<!-- => Success["TypeChecked", ...] -->

```wl
checked["Type"]
```

<!-- => 2 + 2 == 4 -->

---

Check the prelude, a library environment given by its name:

```wl
checked = TypeTheoryCheck["Prelude"]
```

<!-- => Success["EnvironmentChecked", ...] -->

The number of constants that checked:

```wl
checked["Constants"]
```

<!-- => 257 -->

---

An environment under other rules is checked by its own rules, here homotopy type theory, without Prop:

```wl
TypeTheoryCheck["HomotopyTypeTheory"]
```

<!-- => Success["EnvironmentChecked", ...] -->

## Options

### Method

Check an environment with the kernel written in Wolfram Language, which gives the same answer as the compiled kernel, more slowly:

```wl
TypeTheoryCheck["Integers", Method -> "Symbolic"]
```

<!-- => Success["EnvironmentChecked", ...] -->

---

`Method -> "Compiled"` gives a [Failure]() where the compiled kernel cannot check the environment, as for rules with rewrite rules:

```wl
TypeTheoryCheck["HomotopyTypeTheory", Method -> "Compiled"]
```

<!-- => Failure["CompiledKernelUnavailable", ...] -->

## Applications

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

Read it back, which does not check its declarations:

```wl
saved = TypeTheoryEnvironment[file]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

Check them afterwards:

```wl
TypeTheoryCheck[saved]
```

<!-- => Success["EnvironmentChecked", ...] -->

## Properties and Relations

[FailureQ]() tells a check that does not pass:

```wl
FailureQ[TypeTheoryCheck[TypeTheoryTerm["equalityReflexivity"[4]], TypeTheoryTerm[2 + 2 == 5]]]
```

<!-- => True -->

---

A proof by reflexivity of an equation checks exactly when its sides are equal by computation, as [DefinitionallyEqualQ]() decides:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[2 * 3], TypeTheoryTerm[3 + 3]]
```

<!-- => True -->

```wl
TypeTheoryCheck[TypeTheoryTerm["equalityReflexivity"[6]], TypeTheoryTerm[2 * 3 == 3 + 3]]
```

<!-- => Success["TypeChecked", ...] -->

## Possible Issues

A term against a type it does not have:

```wl
TypeTheoryCheck[TypeTheoryTerm["equalityReflexivity"[4]], TypeTheoryTerm[2 + 2 == 5]]
```

<!-- => Failure["TypeMismatch", ...] -->

---

The second argument must be a type, not a term of one, here a proof:

```wl
TypeTheoryCheck[TypeTheoryTerm["equalityReflexivity"[4]], TypeTheoryTerm["equalityReflexivity"[4]]]
```

<!-- => Failure["TypeExpected", ...] -->

---

Two terms that carry different environments:

```wl
TypeTheoryCheck[TypeTheoryTerm[2, "Integers"], TypeTheoryTerm[Naturals, "Rationals"]]
```

<!-- => Failure["DifferentEnvironments", ...] -->

---

[TypeTheoryCheck]() does not hold its argument, so an expression evaluates before it is checked, here to `5`, and nothing matches:

```wl
TypeTheoryCheck[2 + 3]
```

<!-- => TypeTheoryCheck[5] -->

[TypeTheoryTerm]() keeps it a term:

```wl
TypeTheoryCheck[TypeTheoryTerm[2 + 3]]
```

<!-- => ℕ -->

---

A misspelled name of an environment gives a [Failure]():

```wl
TypeTheoryCheck["Integer"]
```

<!-- => Failure["UnknownEnvironment", ...] -->
