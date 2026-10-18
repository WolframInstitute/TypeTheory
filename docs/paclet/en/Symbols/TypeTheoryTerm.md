---
Template: Symbol
Name: TypeTheoryTerm
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryTerm
Keywords: [term, type, surface syntax, Function, Typed, ForAll, Implies, dependent type, held]
SeeAlso: [TypeTheoryEnvironment, TypeTheoryCheck, TypeUniverse, WeakHeadNormalForm, DefinitionallyEqualQ]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[TypeTheoryTerm]()[*term*, *env*]</code> represents a term of the type theory in the [TypeTheoryEnvironment]() *env*, written with built-in symbols such as [Function](), [Typed](), [ForAll](), [Implies](), [Equal]() and [Plus](), and kept unevaluated.

<code>[TypeTheoryTerm]()[*term*]</code> is a term in the prelude, the environment of logic, equality and the natural numbers.

## Details & Options

- [TypeTheoryTerm]() has the [HoldFirst]() attribute. It has to: on its own, <code>[ForAll]()[[Typed]()[x, A], B]</code> evaluates to `B`, and `n + 0 == n` to [True](). The environment is evaluated.
- A term without an environment is in the prelude, except beside a term that has one, as in <code>[TypeTheoryCheck]()[*term*, *type*]</code>, where it takes that term's.
- <code>[TypeOf]()[[TypeTheoryTerm]()[*term*, *env*]]</code> gives the type of *term*, and <code>[TypeOf]()[[TypeTheoryTerm]()[*term*], *env*]</code> gives its type in *env*. [TypeOf]() holds its argument, so give it a [TypeTheoryTerm]() written out, or use [TypeTheoryCheck]().
- The surface language:

| Surface term | Meaning |
|---|---|
| <code>[Function]()[{[Typed]()[x, A], ...}, b]</code> | a function |
| <code>[ForAll]()[{[Typed]()[x, A], ...}, B]</code> | a dependent function type, or a universal statement |
| <code>[Implies]()[A, B]</code>, <code>[TypeSpecifier]()[{A, ...} -> B]</code>, `A -> B` | a function type whose result does not depend on the argument |
| <code>[Annotation]()[[Typed]()[x, A], "Implicit"]</code> | an implicit binder, filled in by elaboration (also `"StrictImplicit"`, `"InstanceImplicit"`) |
| <code>[Exists]()[{[Typed]()[x, A]}, p]</code> | an existential statement |
| <code>[Typed]()[e, A]</code> | `e`, checked against `A` |
| <code>[With]()[{x = v}, b]</code> | `b` with `x` standing for `v` |
| <code>[TypeUniverse]()[*level*]</code> | a universe |
| `f[a, b]` | application, curried, with implicit arguments filled in |
| <code>[Construct]()[f, a, b]</code> | application with every argument given, implicit ones included |
| <code>[Subscript]()[c, *level*, ...]</code> | the constant `c` at explicit universe levels |
| `t[[i]]` | field `i` of `t`, whose type is a structure |
| `0`, `1`, `2`, ... | natural number literals |
| <code>[RightTee]()[{[Typed]()[x, A], ...}, B]</code> | a goal: hypotheses and a conclusion, read as [ForAll]() |

- Any other symbol or string is a bound variable or a declared constant. A symbol whose value is a [TypeTheoryTerm]() stands for that term, and one whose value is a finished [TypeTheoryProof]() stands for its proof.
- In a notebook a term shows in mathematical notation, with the term itself behind the display.

## Basic Examples

A term and its type:

```wl
TypeOf[TypeTheoryTerm[2 + 3]]
```

<!-- => ℕ -->

---

A universal statement, kept unevaluated:

```wl
statement = TypeTheoryTerm[ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n]]
```

<!-- => ∀_n∶ℕ n + 0 == n -->

It is a proposition. [TypeTheoryCheck]() gives the type of a term held in a variable:

```wl
TypeTheoryCheck[statement]
```

<!-- => Prop -->

## Scope

A polymorphic function with an implicit type argument:

```wl
TypeOf[TypeTheoryTerm[Function[{Annotation[Typed[A, TypeUniverse[1]], "Implicit"], Typed[x, A]}, x]]]
```

<!-- => ∀_{A ∶ Type} A → A -->

---

Implicit arguments are filled in; [Construct]() gives them explicitly:

```wl
TypeOf[TypeTheoryTerm[Construct[EqualityReflexivity, NonNegativeIntegers, 3]]]
```

<!-- => 3 == 3 -->

---

A term that holds another, spliced in:

```wl
equation = TypeTheoryTerm[1 + 1 == 2];
TypeOf[TypeTheoryTerm[Implies[equation, equation]]]
```

<!-- => Prop -->

## Properties and Relations

A term in an environment of its own, here the empty one, [TypeTheoryEnvironment]()[], which declares no constants:

```wl
TypeOf[TypeTheoryTerm[2 + 3, TypeTheoryEnvironment[]]]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

[TypeOf]() also takes the environment as its second argument, as it takes a type environment for compiled types:

```wl
bits = TypeTheoryEnvironment[{TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}]}];
TypeOf[TypeTheoryTerm[BitOne], bits]
```

<!-- => Bit -->

## Possible Issues

[TypeOf]() holds its argument, so it does not see the term a variable holds; [TypeTheoryCheck]() evaluates its argument:

```wl
term = TypeTheoryTerm[2 + 3];
TypeTheoryCheck[term]
```

<!-- => ℕ -->
