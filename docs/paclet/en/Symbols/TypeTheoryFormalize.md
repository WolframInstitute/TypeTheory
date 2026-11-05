---
Template: Symbol
Name: TypeTheoryFormalize
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryFormalize
Keywords: [formalization, Wolfram Language definitions, DownValues, implementation, compiler, built-in signatures, rules, pattern matching, Match]
SeeAlso: [TypeTheoryDefinition, TypeTheoryAxiom, TypeTheoryEnvironment, TypeTheoryType, MatchFirst, Expressions]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[TypeTheoryFormalize]()[*symbol*]</code> gives the declarations that make the Wolfram Language function *symbol* a constant of the default environment: a definition read off its definitions where they translate, typed by elaboration, and otherwise an axiom that *symbol* computes.

<code>[TypeTheoryFormalize]()[*symbol*, *environment*]</code> makes the declarations for *environment*.

<code>[TypeTheoryFormalize]()[*symbol*, *environment*, "Meaning" -> "Rules"]</code> gives the rules of *symbol* instead, a definition of type `Expressions -> Option[Expressions]` in [TypeTheoryEnvironment]()["WolframLanguage"].

## Details & Options

- The definitions are read by the compiler of the WolframKernel project, from the paclet Wolfram/KernelCompiler, which TypeTheory loads when it first formalizes a symbol. Where it is missing, [TypeTheoryFormalize]() gives a [Failure]() that names how to install it.
- A symbol is a [TypeTheoryDefinition]() where it has one definition, its arguments bound by plain patterns or by `_Integer` and `_Rational`, and its body arithmetic, list literals, calls of built-ins that have a signature, and calls of other symbols, formalized first and declared before it.
- Two definitions by structural recursion on a list, `f[{}]` and `f[{x_, rest___}]`, whose body calls `f` only on `{rest}`, are a definition by the recursor of [List](). Its result type is the type of the empty case, or the one `"Type"` gives as `{a} -> b`, and its elements are of any type where they can be.
- Two definitions by recursion on a natural number, `f[0]` and `f[n_]`, whose body calls `f` only on `n - 1`, perhaps with `n_Integer` and the condition `n > 0`, are a definition by the recursor of the natural numbers, of the type its zero case gives the result, or the one `"Type"` gives. Other arguments, passed on unchanged in the recursive call as in `power[x_, 0] = 1; power[x_, n_] := x power[x, n - 1]`, are arguments of the definition outside the recursion.
- Definitions each but the last with a condition, `f[x_ /; c] := a`, and [If]() in a body, are [If]() by the decision of the condition, a [Decidable]() instance that elaboration finds, declared as a definition by the recursor of [Decidable]() where the environment has no [If]().
- A type that `"Type"` gives decides the arguments, also where the heads of the patterns, as `_Integer`, would give them another.
- Otherwise it is a [TypeTheoryAxiom]() with `"Implementation" -> symbol`: the Wolfram Language computes it, and the kernel never does.
- The option `"Type" -> type` gives the type the constant must have: a definition is checked against it, and an axiom takes it. Without it, an axiom's type is `Expressions -> ... -> Expressions`, one [Expressions]() for each argument, [Expressions]() being the type of any Wolfram Language expression: an axiom where the environment lacks it, and the inductive type of expressions in [TypeTheoryEnvironment]()["WolframLanguage"].
- The strings are [Strings](), declared where a definition needs them: [StringReverse]() has the signature `Strings -> Strings`, [StringLength]() `Strings -> ℕ`, [StringJoin]() `Strings -> Strings -> Strings`, and a string literal `"abc"` is a constant of [Strings](), named by its [InputForm]() and declared with the definition that uses it.
- A built-in that a body calls is declared by its signature, where the environment does not declare it already: precise where the built-in allows, as [Simplify]() with the type ∀ A, A → A, and over [Expressions]() otherwise, as [D](). The numbers of the environment go into [Expressions]() by coercions. No equation about a built-in is assumed.
- The option `"Meaning"` is `"Function"`, the default, for a constant that is the function *symbol* computes, or `"Rules"` for its rules, its [DownValues](), as a rewriting of expressions: the definition named `"DownValues[symbol]"` gives the expression that an expression rewrites to by the first rule that matches it, and `"none"` where none does and the expression stays as it is.
- The rules are [MatchFirst]() of the [MatchSum]() of the matches of the rules, in the order the Wolfram Language tries them. The left side of each rule is translated from its pattern: the lengths and parts of the expression by [Length](), [Arguments]() and [MatchPart](), its heads and literals by [SameQ](), sequences by every split, an [Orderless]() head by every order, alternatives by [MatchSum](), exceptions by [MatchQ](), and conditions by [SameQ]() of their [ExpressionValue]() and `True`. The right side is quoted as it is, its pattern variables the parts they match: the rules give one step of evaluation. The tutorial *Patterns and Rewriting* goes through every pattern.
- The atoms of the rules are data of the type [Atoms](), which nothing declares, so the kernel computes every test but a condition or a pattern test, which only the Wolfram Language evaluates.
- [KeyValuePattern]() does not translate, as an [Association]() is an atom, and gives a [Failure]().
- The result is a list of declarations, to extend an environment with: <code>[TypeTheoryEnvironment]()[*environment*, [TypeTheoryFormalize]()[*symbol*, *environment*]]</code>.

## Basic Examples

A Wolfram Language function on integers translates, and elaboration types it:

```wl
square[x_Integer] := x^2 + 1;
TypeTheoryFormalize[square, TypeTheoryEnvironment["Integers"]]
```

<!-- => {definition square := (x ∶ ℤ) ↦ x^2 + 1} -->

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
TypeTheoryType[next, formalized]
```

<!-- => ℤ → ℤ -->

---

A function of strings is a definition over [Strings](), and a string literal a constant of it:

```wl
greeting[s_] := StringJoin["Hello, ", s];
integers = TypeTheoryEnvironment["Integers"];
greeted = TypeTheoryEnvironment[integers, TypeTheoryFormalize[greeting, integers]];
TypeTheoryType[greeting, greeted]
```

<!-- => Strings → Strings -->

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
{TypeTheoryType[size, sized], WeakHeadNormalForm[TypeTheoryTerm[size[{4, 5, 6}], sized]]}
```

<!-- => {∀_{elementType∶Type u} {elementType} → ℕ, 3} -->

---

A factorial is a definition by the recursor of the natural numbers, which computes:

```wl
fact[0] = 1;
fact[n_] := n fact[n - 1];
prelude = TypeTheoryEnvironment["Prelude"];
facts = TypeTheoryEnvironment[prelude, TypeTheoryFormalize[fact, prelude]];
{TypeTheoryType[fact, facts], WeakHeadNormalForm[TypeTheoryTerm[fact[5], facts]]}
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
styled[x_] := Style[x, Bold];
TypeTheoryFormalize[styled, "Type" -> Integers -> Integers]
```

<!-- => {axiom styled : ℤ → ℤ} -->

### Meaning

The rules of a function, a rewriting of expressions:

```wl
listed[x_, y_, z___] := {x, y, z};
wolfram = TypeTheoryEnvironment["WolframLanguage"];
rules = TypeTheoryFormalize[listed, wolfram, "Meaning" -> "Rules"]
```

<!-- => {definition DownValues[listed] : Expressions → Option[Expressions] := (expression ∶ Expressions) ↦ MatchFirst[...]} -->

The kernel computes them: an expression with two arguments or more rewrites to the list of them, and one with fewer stays as it is:

```wl
listing = TypeTheoryEnvironment[wolfram, rules];
{
    DefinitionallyEqualQ[TypeTheoryTerm["DownValues[listed]"[listed[1, 2]], listing], TypeTheoryTerm["some"[HoldForm[{1, 2}]], listing]],
    DefinitionallyEqualQ[TypeTheoryTerm["DownValues[listed]"[listed[1]], listing], TypeTheoryTerm[Typed["none", Option[Expressions]], listing]]
}
```

<!-- => {True, True} -->

## Possible Issues

Without a type, a function that does not translate takes [Expressions]() for each argument:

```wl
styled[x_] := Style[x, Bold];
Last[TypeTheoryFormalize[styled, TypeTheoryEnvironment["Integers"]]]
```

<!-- => axiom styled : Expressions → Expressions -->
