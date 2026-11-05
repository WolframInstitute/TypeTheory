---
Template: Symbol
Name: TypeTheoryType
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryType
Keywords: [type, type inference, elaboration, term, type of a term, proposition]
SeeAlso: [TypeTheoryTerm, TypeTheoryCheck, TypeTheoryEnvironment, WeakHeadNormalForm, DefinitionallyEqualQ]
RelatedGuides: [TypeTheory]
RelatedTutorials: [Elaboration, TypeTheoryIntroduction]
---

## Usage

<code>[TypeTheoryType]()[*term*]</code> gives the type of *term*, or a [Failure]() if it does not type-check.

<code>[TypeTheoryType]()[*term*, *env*]</code> gives the type of *term* in the [TypeTheoryEnvironment]() *env*.

## Details & Options

- *term* is an expression of the type theory, kept unevaluated as the statement of a [TypeTheoryProof]() is, or a [TypeTheoryTerm](), written out or kept in a symbol, which carries its own environment.
- An expression on its own is in the default environment, [$TypeTheoryEnvironment](), the prelude unless [SetTypeTheoryEnvironment]() set another.
- The type is a [TypeTheoryTerm]() in the same environment, read back into surface syntax, so it can be used as a term again.
- Elaboration fills in the implicit arguments, types and universe levels nobody wrote, and the kernel checks the term before its type is given.
- A constant on its own has its declared type, with its implicit arguments and universe parameters.
- The type of a proof is the proposition it proves, and the type of a proposition is `Prop`.
- [TypeTheoryType]() takes code copied from a documentation page, where each symbol is written `PacletSymbol[paclet, name]`.
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

## Scope

A proposition is a type whose type is `Prop`; the expression is not evaluated, so `n + 0 == n` stays a statement:

```wl
TypeTheoryType[ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n]]
```

<!-- => Prop -->

---

The type of a term in an environment given as the second argument:

```wl
bits = TypeTheoryEnvironment[{TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}]}];
TypeTheoryType[BitOne, bits]
```

<!-- => Bit -->

---

The declared type of a constant, with its implicit arguments:

```wl
TypeTheoryType["equalitySymmetry"]
```

<!-- => ∀_{α∶Sort u} ∀_{x∶α} ∀_{y∶α} x == y ⇒ y == x -->

---

A [TypeTheoryTerm]() kept in a variable carries its environment:

```wl
sum = TypeTheoryTerm[2 + 3];
TypeTheoryType[sum]
```

<!-- => ℕ -->

## Properties and Relations

<code>[TypeTheoryCheck]()[*term*, *type*]</code> checks a term against a type that is given:

```wl
TypeTheoryCheck[TypeTheoryTerm["equalityReflexivity"[4]], TypeTheoryTerm[2 + 2 == 4]]
```

<!-- => Success["TypeChecked", ...] -->

## Possible Issues

A term that does not type-check gives a [Failure]():

```wl
TypeTheoryType[1 + True]
```

<!-- => Failure[...] -->

---

The argument is held, so a term computed by an expression is given with [Evaluate]():

```wl
terms = {TypeTheoryTerm[2 + 3], TypeTheoryTerm[1 + 1 == 2]};
TypeTheoryType[Evaluate[Last[terms]]]
```

<!-- => Prop -->
