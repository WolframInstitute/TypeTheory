---
Template: Symbol
Name: TypeTheoryTerm
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryTerm
Keywords: [term, type, surface syntax, Function, Typed, ForAll, Implies, dependent type, held, Booleans, overloading, ambiguous]
SeeAlso: [TypeTheoryEnvironment, TypeTheoryCheck, TypeUniverse, WeakHeadNormalForm, DefinitionallyEqualQ]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[TypeTheoryTerm]()[*term*, *env*]</code> represents a term of the type theory in the [TypeTheoryEnvironment]() *env*, written with built-in symbols such as [Function](), [Typed](), [ForAll](), [Implies](), [Equal]() and [Plus](), and kept unevaluated.

<code>[TypeTheoryTerm]()[*term*]</code> is a term in the default environment, [$TypeTheoryEnvironment](), the prelude unless [SetTypeTheoryEnvironment]() set another.

## Details & Options

- [TypeTheoryTerm]() has the [HoldFirst]() attribute. It has to: on its own, <code>[ForAll]()[[Typed]()[x, A], B]</code> evaluates to `B`, and `n + 0 == n` to [True](). The environment is evaluated.
- A term without an environment is in the default environment, except beside a term that has one, as in <code>[TypeTheoryCheck]()[*term*, *type*]</code>, where it takes that term's.
- <code>[TypeTheoryType]()[[TypeTheoryTerm]()[*term*, *env*]]</code> gives the type of *term*, and <code>[TypeTheoryType]()[[TypeTheoryTerm]()[*term*], *env*]</code> gives its type in *env*.
- The surface language:

| Surface term | Meaning |
|---|---|
| <code>[Function]()[{[Typed]()[x, A], ...}, b]</code> | a function |
| <code>[ForAll]()[{[Typed]()[x, A], ...}, B]</code> | a dependent function type, or a universal statement |
| <code>[Implies]()[A, B]</code>, <code>[TypeSpecifier]()[{A, ...} -> B]</code>, `A -> B` | a function type whose result does not depend on the argument |
| <code>[TypedImplicit]()[x, A]</code> | an implicit binder, filled in by elaboration; <code>[Annotation]()[[Typed]()[x, A], *kind*]</code> with `"StrictImplicit"` or `"InstanceImplicit"` gives the other kinds |
| <code>[Exists]()[{[Typed]()[x, A]}, p]</code> | an existential statement |
| <code>[ForAll]()[x, *condition*, B]</code>, <code>[Exists]()[x, *condition*, p]</code> | <code>[ForAll]()[x, [Implies]()[*condition*, B]]</code> and <code>[Exists]()[x, *condition* && p]</code>, as the Wolfram Language reads them |
| <code>[Typed]()[e, A]</code> | `e`, checked against `A` |
| <code>[With]()[{x = v}, b]</code> | `b` with `x` standing for `v` |
| <code>[TypeUniverse]()[*level*]</code> | a universe |
| `f[a, b]` | application, curried, with implicit arguments filled in |
| <code>[Construct]()[f, a, b]</code> | application with every argument given, implicit ones included |
| <code>[Subscript]()[c, *level*, ...]</code> | the constant `c` at explicit universe levels |
| `t[[i]]` | field `i` of `t`, whose type is a structure |
| `0`, `1`, `2`, ... | natural number literals |
| `{a, b, ...}` | the list <code>[Prepend]()[a][[Prepend]()[b][... {}]]</code>, which is <code>[Prepend]()[[Prepend]()[..., b], a]</code>, in an environment with [List]() |
| <code>[RightTee]()[{[Typed]()[x, A], ...}, B]</code> | a goal: hypotheses and a conclusion, read as [ForAll]() |

- A binder written as a bare symbol, <code>[ForAll]()[{n}, n + 0 == n]</code> or <code>[ForAll]()[n, n + 0 == n]</code>, takes the type its body gives it, as Lean leaves a binder's type to unification; a binder whose type nothing decides gives a [Failure]() asking for <code>[Typed]()[x, *type*]</code>.
- Any other symbol or string is a bound variable or a declared constant. A symbol whose value is a [TypeTheoryTerm]() stands for that term, and one whose value is a finished [TypeTheoryProof]() stands for its proof.
- [True](), [False](), [Not](), [And]() and [Or](), and so `!`, `&&` and `||`, stand for the propositions or, in an environment that declares the Booleans, for its constants `"true"`, `"false"`, `"not"`, `"and"` and `"or"`, as the type allows: a proposition where a type or Prop is expected, a Boolean where [Booleans]() is. Elsewhere the arguments decide, or how the term is used. A term that nothing decides is ambiguous, and <code>[Typed]()[*e*, [TypeUniverse]()[0]]</code> or <code>[Typed]()[*e*, [Booleans]()]</code> says which it is, as the string `"true"` or `"not"` does for a Boolean.
- In a notebook a term shows in mathematical notation, with the term itself behind the display.
- A constant shows as its symbol or string, applied to its arguments that are not implicit. TypeTheory builds that expression, with its parts already shown, and gives it to [MakeBoxes](), so [MakeBoxes]() definitions give a constant a notation and [Format]() definitions give its symbol a display, in terms, declarations and proofs alike.
- <code>[Information]()[*term*, "AxiomClosure"]</code> gives the axioms *term* rests on, as [TypeTheoryAxiomClosure]() does, <code>[Information]()[*term*, "Holes"]</code> the holes it rests on, <code>[Information]()[*term*, "Constants"]</code> the constants its type and value mention, and <code>[Information]()[*term*, "Annotation"]</code> the annotation of a hole.

## Basic Examples

A term and its type:

```wl
TypeTheoryType[2 + 3]
```

<!-- => ℕ -->

---

A universal statement, kept unevaluated:

```wl
statement = TypeTheoryTerm[ForAll[{Typed[n, Naturals]}, n + 0 == n]]
```

<!-- => ∀_n∶ℕ n + 0 == n -->

It is a proposition. [TypeTheoryType]() gives the type of a term, here one held in a variable:

```wl
TypeTheoryType[statement]
```

<!-- => Prop -->

## Scope

A polymorphic function with an implicit type argument:

```wl
TypeTheoryType[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A]} |-> x]
```

<!-- => ∀_{A ∶ Type} A → A -->

---

Implicit arguments are filled in; [Construct]() gives them explicitly:

```wl
TypeTheoryType[Construct["equalityReflexivity", Naturals, 3]]
```

<!-- => 3 == 3 -->

---

A term:

```wl
equation = TypeTheoryTerm[1 + 1 == 2]
```

<!-- => 1 + 1 == 2 -->

A term that holds another, spliced in:

```wl
TypeTheoryType[Implies[equation, equation]]
```

<!-- => Prop -->

---

Where a Boolean is expected, `&&` and [True]() are Booleans:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Typed[True && False, Booleans]]]
```

<!-- => false -->

## Properties and Relations

A term in an environment of its own, here the empty one, [TypeTheoryEnvironment]()[], which declares no constants:

```wl
TypeTheoryType[2 + 3, TypeTheoryEnvironment[]]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

A type of bits:

```wl
bits = TypeTheoryEnvironment[{TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}]}]
```

<!-- => TypeTheoryEnvironment summary box: 173 constants -->

[TypeTheoryType]() also takes the environment as its second argument:

```wl
TypeTheoryType[BitOne, bits]
```

<!-- => Bit -->

## Possible Issues

On its own, [True]() could be the proposition or the Boolean, so its type is ambiguous:

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

Define doubling:

```wl
doubled = TypeTheoryEnvironment[TypeTheoryDefinition[Double, Typed[n, Naturals] |-> n + n]]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

[Format]() evaluates the arguments of what it formats, so a bound variable whose symbol has a value shows that value:

```wl
Format[Double[a_]] := CenterDot[2, a];
k = 7;
TypeTheoryTerm[Typed[k, Naturals] |-> Double[k], doubled]
```

<!-- => (k ∶ ℕ) ↦ 2·7 -->

---

Define doubling:

```wl
doubled = TypeTheoryEnvironment[TypeTheoryDefinition[Double, Typed[n, Naturals] |-> n + n]]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

[MakeBoxes]() holds them, so a notation for a constant applied to arguments is a definition of [MakeBoxes]():

```wl
MakeBoxes[Double[a_], form_] := MakeBoxes[CenterDot[2, a], form];
k = 7;
TypeTheoryTerm[Typed[k, Naturals] |-> Double[k], doubled]
```

<!-- => (k ∶ ℕ) ↦ 2·k -->
