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

<code>[TypeTheoryTerm]()[*term*]</code> is a term in the empty environment.

## Details & Options

- [TypeTheoryTerm]() has the [HoldFirst]() attribute. It has to: on its own, <code>[ForAll]()[[Typed]()[x, A], B]</code> evaluates to `B`, and `n + 0 == n` to [True](). The environment is evaluated.
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

A term in the prelude, and its type:

```wl
prelude = TypeTheoryEnvironment["Prelude"];
TypeOf[TypeTheoryTerm[2 + 3, prelude]]
```

<!-- => ℕ -->

---

A universal statement, kept unevaluated:

```wl
prelude = TypeTheoryEnvironment["Prelude"];
statement = TypeTheoryTerm[ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n], prelude]
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
prelude = TypeTheoryEnvironment["Prelude"];
TypeOf[TypeTheoryTerm[Construct[EqualityReflexivity, NonNegativeIntegers, 3], prelude]]
```

<!-- => 3 == 3 -->

---

A term that holds another, spliced in:

```wl
prelude = TypeTheoryEnvironment["Prelude"];
equation = TypeTheoryTerm[1 + 1 == 2];
TypeOf[TypeTheoryTerm[Implies[equation, equation], prelude]]
```

<!-- => Prop -->

## Properties and Relations

A term without an environment is read in the empty environment, where no constant is declared:

```wl
TypeOf[TypeTheoryTerm[2 + 3]]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

[TypeOf]() takes an environment as its second argument, as it takes a type environment for compiled types:

```wl
TypeOf[TypeTheoryTerm[2 + 3], TypeTheoryEnvironment["Prelude"]]
```

<!-- => ℕ -->

## Possible Issues

[TypeOf]() holds its argument, so it does not see the term a variable holds; [TypeTheoryCheck]() evaluates its argument:

```wl
prelude = TypeTheoryEnvironment["Prelude"];
term = TypeTheoryTerm[2 + 3, prelude];
TypeTheoryCheck[term]
```

<!-- => ℕ -->
