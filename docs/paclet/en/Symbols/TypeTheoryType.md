---
Template: Symbol
Name: TypeTheoryType
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryType
Keywords: [type, type inference, elaboration, term, type of a term, proposition, universe, held, PacletSymbol, Wolfram Language expressions]
SeeAlso: [TypeTheoryTerm, TypeTheoryCheck, TypeTheoryEnvironment, WeakHeadNormalForm, DefinitionallyEqualQ, TypeTheoryAxiomClosure]
RelatedGuides: [TypeTheory]
RelatedTutorials: [Elaboration, TypeTheoryIntroduction]
---

## Usage

<code>[TypeTheoryType]()[*term*]</code> gives the type of *term*, or a [Failure]() if it does not type-check.

<code>[TypeTheoryType]()[*term*, *env*]</code> gives the type of *term* in the [TypeTheoryEnvironment]() *env*, or in the library environment named *env*, such as `"Integers"`.

## Details & Options

- *term* is an expression of the type theory, kept unevaluated as the statement of a [TypeTheoryProof]() is, a [TypeTheoryTerm](), or a symbol whose value is a [TypeTheoryTerm]() or a finished [TypeTheoryProof]().
- [TypeTheoryType]() has the [HoldAll]() attribute, so `1 + 1 == 2` stays an equation and does not evaluate to [True](). A term computed by an expression is given with [Evaluate]().
- An expression on its own is in the default environment, [$TypeTheoryEnvironment](), the prelude unless [SetTypeTheoryEnvironment]() set another. The prelude has the expressions, strings and matches of the Wolfram Language, such as [Arguments](), [Head](), [Expressions]() and [ExpressionEvaluate]().
- In <code>[TypeTheoryType]()[*term*, *env*]</code> the term is read in *env*, also a [TypeTheoryTerm]() that carries an environment of its own. *env* is an environment or the name of a library environment, as [TypeTheoryEnvironment]() takes it; a name of none gives a [Failure]() tagged `"UnknownEnvironment"`, and an *env* that is a [Failure]() is the result.
- The type is a [TypeTheoryTerm]() in the same environment, read back into surface syntax, so it can be used as a term again.
- Elaboration fills in the implicit arguments, types and universe levels nobody wrote, and the kernel checks the term before its type is given.
- A constant on its own has its declared type, with its implicit arguments and universe parameters.
- The type of a proof is the proposition it proves, the type of a proposition is `Prop`, and the type of a type is a universe: <code>[TypeUniverse]()[*k*]</code> is in <code>[TypeUniverse]()[*k* + 1]</code>, so `Prop` is in `Type`.
- A term that does not type-check gives a [Failure]() whose tag says why: `"ElaborationFailed"` for a name that is neither a variable nor a declared constant, `"TypeMismatch"` for an argument of the wrong type, `"Ambiguous"` for a term two readings fit, and `"UnsolvedImplicitArgument"` for an implicit argument nothing decides.
- [TypeTheoryType]() takes code copied from a documentation page, where each symbol of the paclet is written `PacletSymbol[paclet, name]`.
- [TypeOf]() is the compiler's function, which gives how a value is stored, not a type of the type theory.

## Basic Examples

The type of a function from natural numbers to natural numbers:

```wl
TypeTheoryType[Typed[n, NonNegativeIntegers] |-> n + 1]
```

<!-- => ℕ → ℕ -->

---

A proof has the proposition it proves as its type:

```wl
TypeTheoryType["equalityReflexivity"[4]]
```

<!-- => 4 == 4 -->

---

An equation is a proposition; the argument is held, so `1 + 1 == 2` does not evaluate to [True]() first:

```wl
TypeTheoryType[1 + 1 == 2]
```

<!-- => Prop -->

## Scope

A universal statement is a proposition:

```wl
TypeTheoryType[ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n]]
```

<!-- => Prop -->

---

The type of a type is a universe:

```wl
TypeTheoryType[Naturals]
```

<!-- => Type -->

---

`Prop`, the universe of propositions, is in `Type`:

```wl
TypeTheoryType[TypeUniverse[0]]
```

<!-- => Type -->

---

The declared type of a constant, with its implicit arguments:

```wl
TypeTheoryType["equalitySymmetry"]
```

<!-- => ∀_{α∶Sort u} ∀_{x∶α} ∀_{y∶α} x == y ⇒ y == x -->

---

A polymorphic function, its implicit type argument filled in where it is used:

```wl
TypeTheoryType[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A]} |-> x]
```

<!-- => ∀_{A ∶ Type} A → A -->

---

A function that gives a list:

```wl
TypeTheoryType[Typed[n, Naturals] |-> {n, n + 1}]
```

<!-- => ℕ → {ℕ} -->

---

A [TypeTheoryTerm]() kept in a variable:

```wl
sum = TypeTheoryTerm[2 + 3]
```

<!-- => 2 + 3 -->

```wl
TypeTheoryType[sum]
```

<!-- => ℕ -->

---

A finished proof kept in a variable stands for its proof:

```wl
proved = TypeTheoryProof[2 + 2 == 4, {"Decide"}]
```

<!-- => Proof complete -->

```wl
TypeTheoryType[proved]
```

<!-- => 2 + 2 == 4 -->

---

A type of bits:

```wl
bits = TypeTheoryEnvironment[{TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}]}]
```

<!-- => TypeTheoryEnvironment summary box: 234 constants -->

The type of one of its constructors, in that environment, given as the second argument:

```wl
TypeTheoryType[BitOne, bits]
```

<!-- => Bit -->

---

A difference of integers, in the library environment of the integers, given by its name:

```wl
TypeTheoryType[Typed[2, Integers] - 3, "Integers"]
```

<!-- => ℤ -->

---

The prelude has the expressions of the Wolfram Language: the arguments of an expression are a sequence of expressions:

```wl
TypeTheoryType[Arguments]
```

<!-- => Expressions → Expressions... -->

---

Code copied from a documentation page writes the paclet's symbols with `PacletSymbol`, which [TypeTheoryType]() reads as the symbols:

```wl
TypeTheoryType[Typed[n, PacletSymbol["WolframInstitute/TypeTheory", "Naturals"]] |-> n]
```

<!-- => ℕ → ℕ -->

## Properties and Relations

The type of a term:

```wl
type = TypeTheoryType[2 + 3]
```

<!-- => ℕ -->

The type is a [TypeTheoryTerm]() itself, whose type is a universe:

```wl
TypeTheoryType[type]
```

<!-- => Type -->

---

<code>[TypeTheoryCheck]()[*term*, *type*]</code> checks a term against a type that is given:

```wl
TypeTheoryCheck[TypeTheoryTerm["equalityReflexivity"[4]], TypeTheoryTerm[2 + 2 == 4]]
```

<!-- => Success["TypeChecked", ...] -->

---

[TypeOf]() gives the compiler's type, how a value is stored:

```wl
TypeOf[2 + 3]
```

<!-- => TypeSpecifier["Integer64"] -->

[TypeTheoryType]() gives the type of the term of the type theory:

```wl
TypeTheoryType[2 + 3]
```

<!-- => ℕ -->

## Possible Issues

A term that does not type-check gives a [Failure]():

```wl
TypeTheoryType[1 + True]
```

<!-- => Failure["TypeMismatch", ...] -->

---

A name that is neither a variable nor a declared constant:

```wl
TypeTheoryType[undeclaredThing]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

On its own, [True]() could be the proposition or the Boolean:

```wl
TypeTheoryType[True]
```

<!-- => Failure["Ambiguous", ...] -->

[Typed]() says which it is:

```wl
TypeTheoryType[Typed[True, Booleans]]
```

<!-- => 𝔹 -->

---

The empty list has no element that gives its element type:

```wl
TypeTheoryType[{}]
```

<!-- => Failure["UnsolvedImplicitArgument", ...] -->

[Typed]() gives it:

```wl
TypeTheoryType[Typed[{}, {Naturals}]]
```

<!-- => {ℕ} -->

---

The argument is held, so a term computed by an expression is a term of its own, here of the function [Last](), which no environment declares:

```wl
terms = {TypeTheoryTerm[2 + 3], TypeTheoryTerm[1 + 1 == 2]};
TypeTheoryType[Last[terms]]
```

<!-- => Failure["ElaborationFailed", ...] -->

[Evaluate]() computes the term first:

```wl
TypeTheoryType[Evaluate[Last[terms]]]
```

<!-- => Prop -->

---

A symbol whose value is not a [TypeTheoryTerm]() is a name, not the value:

```wl
increment = Typed[n, Naturals] |-> n + 1;
TypeTheoryType[increment]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

Literals are natural numbers, also in the integers, so the difference of two is a natural number, cut off at 0:

```wl
TypeTheoryType[2 - 3, "Integers"]
```

<!-- => ℕ -->

---

A misspelled name of an environment gives a [Failure]():

```wl
TypeTheoryType[2 + 3, "Integer"]
```

<!-- => Failure["UnknownEnvironment", ...] -->
