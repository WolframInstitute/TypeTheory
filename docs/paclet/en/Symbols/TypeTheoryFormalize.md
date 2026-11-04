---
Template: Symbol
Name: TypeTheoryFormalize
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryFormalize
Keywords: [formalization, Wolfram Language definitions, DownValues, implementation, compiler, built-in signatures]
SeeAlso: [TypeTheoryDefinition, TypeTheoryAxiom, TypeTheoryEnvironment, TypeOf]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[TypeTheoryFormalize]()[*symbol*]</code> gives the declarations that make the Wolfram Language function *symbol* a constant of the default environment: a definition read off its definitions where they translate, typed by elaboration, and otherwise an axiom that *symbol* computes.

<code>[TypeTheoryFormalize]()[*symbol*, *environment*]</code> makes the declarations for *environment*.

## Details & Options

- The definitions are read by the compiler of the WolframKernel project, from the paclet Wolfram/KernelCompiler, which TypeTheory loads when it first formalizes a symbol. Where it is missing, [TypeTheoryFormalize]() gives a [Failure]() that names how to install it.
- A symbol is a [TypeTheoryDefinition]() where it has one definition, its arguments bound by plain patterns or by `_Integer` and `_Rational`, and its body arithmetic, list literals, calls of built-ins that have a signature, and calls of other symbols, formalized first and declared before it.
- Two definitions by structural recursion on a list, `f[{}]` and `f[{x_, rest___}]`, whose body calls `f` only on `{rest}`, are a definition by the recursor of [Lists](). Its result type is the type of the empty case, or the one `"Type"` gives as `Lists[a] -> b`, and its elements are of any type where they can be.
- Two definitions by recursion on a natural number, `f[0]` and `f[n_]`, whose body calls `f` only on `n - 1`, perhaps with `n_Integer` and the condition `n > 0`, are a definition by the recursor of the natural numbers, of the type its zero case gives the result, or the one `"Type"` gives. Other arguments, passed on unchanged in the recursive call as in `power[x_, 0] = 1; power[x_, n_] := x power[x, n - 1]`, are arguments of the definition outside the recursion.
- Definitions each but the last with a condition, `f[x_ /; c] := a`, and [If]() in a body, are [If]() by the decision of the condition, a [Decidable]() instance that elaboration finds, declared as a definition by the recursor of [Decidable]() where the environment has no [If]().
- A type that `"Type"` gives decides the arguments, also where the heads of the patterns, as `_Integer`, would give them another.
- Otherwise it is a [TypeTheoryAxiom]() with `"Implementation" -> symbol`: the Wolfram Language computes it, and the kernel never does.
- The option `"Type" -> type` gives the type the constant must have: a definition is checked against it, and an axiom takes it. Without it, an axiom's type is `"Expressions" -> ... -> "Expressions"`, one `"Expressions"` for each argument, `"Expressions"` being the type of any Wolfram Language expression.
- A built-in that a body calls is declared by its signature, where the environment does not declare it already: precise where the built-in allows, as [Simplify]() with the type ∀ A, A → A, and over `"Expressions"` otherwise, as [D](). The numbers of the environment go into `"Expressions"` by coercions. No equation about a built-in is assumed.
- The result is a list of declarations, to extend an environment with: <code>[TypeTheoryEnvironment]()[*environment*, [TypeTheoryFormalize]()[*symbol*, *environment*]]</code>.

## Basic Examples

A Wolfram Language function on integers translates, and elaboration types it:

```wl
square[x_Integer] := x^2 + 1;
TypeTheoryFormalize[square, TypeTheoryEnvironment["Integers"]]
```

<!-- => {TypeTheoryDefinition[square, Function[{Typed[x, Integers]}, x^2 + 1]]} -->

## Scope

A function that calls another is formalized after it:

```wl
square[x_Integer] := x^2 + 1;
next[x_Integer] := square[x] + 1;
integers = TypeTheoryEnvironment["Integers"];
formalized = TypeTheoryEnvironment[integers, TypeTheoryFormalize[next, integers]]
```

<!-- => TypeTheoryEnvironment summary box -->

```wl
TypeOf[TypeTheoryTerm[next, formalized]]
```

<!-- => ℤ → ℤ -->

---

A built-in with a signature is declared with it:

```wl
simplified[x_Integer] := Simplify[x + 1];
TypeTheoryFormalize[simplified, TypeTheoryEnvironment["Integers"]][[All, 1]]
```

<!-- => {Simplify, simplified} -->

---

Structural recursion on a list is a definition by the recursor of lists, which computes:

```wl
size[{}] = 0;
size[{x_, rest___}] := 1 + size[{rest}];
integers = TypeTheoryEnvironment["Integers"];
sized = TypeTheoryEnvironment[integers, TypeTheoryFormalize[size, integers]];
{TypeOf[TypeTheoryTerm[size, sized]], WeakHeadNormalForm[TypeTheoryTerm[size[{4, 5, 6}], sized]]}
```

<!-- => {∀_{α∶Type u} List α → ℕ, 3} -->

---

A factorial is a definition by the recursor of the natural numbers, which computes:

```wl
fact[0] = 1;
fact[n_] := n fact[n - 1];
prelude = TypeTheoryEnvironment["Prelude"];
facts = TypeTheoryEnvironment[prelude, TypeTheoryFormalize[fact, prelude]];
{TypeOf[TypeTheoryTerm[fact, facts]], WeakHeadNormalForm[TypeTheoryTerm[fact[5], facts]]}
```

<!-- => {ℕ → ℕ, 120} -->

---

A condition is If by the decision of the condition, which computes:

```wl
clamp[x_Integer] := If[x <= 3, x, 3];
prelude = TypeTheoryEnvironment["Prelude"];
clamped = TypeTheoryEnvironment[prelude, TypeTheoryFormalize[clamp, prelude, "Type" -> NonNegativeIntegers -> NonNegativeIntegers]];
{WeakHeadNormalForm[TypeTheoryTerm[clamp[5], clamped]], WeakHeadNormalForm[TypeTheoryTerm[clamp[2], clamped]]}
```

<!-- => {3, 2} -->

## Options

### Type

A function that does not translate is an axiom of the type given, which it computes:

```wl
reversed[s_] := StringReverse[s];
TypeTheoryFormalize[reversed, "Type" -> Integers -> Integers]
```

<!-- => {TypeTheoryAxiom[reversed, Integers -> Integers, "Implementation" -> reversed]} -->

## Possible Issues

Without a type, a function that does not translate takes `"Expressions"` for each argument:

```wl
reversed[s_] := StringReverse[s];
Last[TypeTheoryFormalize[reversed, TypeTheoryEnvironment["Integers"]]]
```

<!-- => TypeTheoryAxiom[reversed, "Expressions" -> "Expressions", "Implementation" -> reversed] -->
