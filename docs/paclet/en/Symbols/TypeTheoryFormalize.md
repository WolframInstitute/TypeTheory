---
Template: Symbol
Name: TypeTheoryFormalize
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryFormalize
Keywords: [formalization, Wolfram Language definitions, DownValues, implementation, compiler, built-in signatures, rules, pattern matching, Match, recursion, axiom, Expressions]
SeeAlso: [TypeTheoryDefinition, TypeTheoryAxiom, TypeTheoryEnvironment, TypeTheoryType, MatchFirst, Expressions, Strings, TypeTheoryAxiomClosure]
RelatedGuides: [TypeTheory]
RelatedTutorials: [Elaboration, TheWolframLanguage, PatternsAndRewriting]
---

## Usage

<code>[TypeTheoryFormalize]()[*symbol*]</code> gives the declarations that make the Wolfram Language function *symbol* a constant of the default environment: a definition read off its definitions where they translate, typed by elaboration, and otherwise an axiom that *symbol* computes.

<code>[TypeTheoryFormalize]()[*symbol*, *environment*]</code> makes the declarations for *environment*, an environment or the name of a library environment, such as `"Integers"`.

<code>[TypeTheoryFormalize]()[*symbol*, *environment*, "Meaning" -> "Rules"]</code> gives the rules of *symbol* instead, a definition of type `Expressions -> Option[Expressions]`, in an environment with the Wolfram Language's expressions, as the prelude.

## Details & Options

- The definitions are read by the compiler of the WolframKernel project, from the paclet Wolfram/KernelCompiler, which TypeTheory loads when it first formalizes a symbol. Where it is missing, [TypeTheoryFormalize]() gives a [Failure]() tagged `"KernelCompilerMissing"` that names how to install it.
- [TypeTheoryFormalize]() has the [HoldAll]() attribute: *symbol* is a symbol with [DownValues](), which are read and never evaluated.
- A symbol is a [TypeTheoryDefinition]() where it has one definition, its arguments bound by plain patterns or by `_Integer` and `_Rational`, and its body arithmetic, list literals, string literals, calls of built-ins that have a signature, and calls of other symbols, formalized first and declared before it. Its arguments are the variables of the body; any other symbol in the body, as `t` in `D[y, t]`, has no counterpart, and the function is an axiom.
- Two definitions by structural recursion on a list, `f[{}]` and `f[{x_, rest___}]`, whose body calls `f` only on `{rest}`, are a definition by the recursor of [List](). Its result type is the type of the empty case, or the one `"Type"` gives as `{a} -> b`, and its elements are of any type where they can be.
- Two definitions by recursion on a natural number, `f[0]` and `f[n_]`, whose body calls `f` only on `n - 1`, perhaps with `n_Integer` and the condition `n > 0`, are a definition by the recursor of the natural numbers, of the type its zero case gives the result, or the one `"Type"` gives. Other arguments, passed on unchanged in the recursive call as in `power[x_, 0] = 1; power[x_, n_] := x power[x, n - 1]`, are arguments of the definition outside the recursion.
- Definitions each but the last with a condition, `f[x_ /; c] := a`, and [If]() in a body, are [If]() by the decision of the condition, a [Decidable]() instance that elaboration finds. [If]() is a definition of the prelude by the recursor of [Decidable](), and is declared with the definition where the environment has no [If](), as the constructive one.
- A type that `"Type"` gives decides the arguments, also where the heads of the patterns, as `_Integer`, would give them another.
- Otherwise it is a [TypeTheoryAxiom]() with `"Implementation" -> symbol`: the Wolfram Language computes it, and the kernel never does. A function that calls itself through another function is an axiom, and so is a function whose definitions take different numbers of arguments, which needs `"Type"`.
- The option `"Type" -> type` gives the type the constant must have: a definition is checked against it, and where none checks, the axiom takes it. Without it, an axiom's type is `Expressions -> ... -> Expressions`, one [Expressions]() for each argument, [Expressions]() being the type of any Wolfram Language expression: the inductive type of expressions of the prelude, and an axiom, declared with the coercions of the environment's numbers into it, where the environment lacks it, as the constructive environment does.
- The strings are [Strings](): [StringReverse]() has the signature `Strings -> Strings`, [StringLength]() `Strings -> ℕ` and [StringJoin]() `Strings -> Strings -> Strings`. In the prelude, which has [Strings](), a string literal is the string it is. Where the environment has no [Strings](), as the constructive one, [Strings]() is declared as an axiom where a definition needs it, and a string literal `"abc"` is a constant of it, named by its [InputForm]() and declared with the definition that uses it.
- A built-in that a body calls is declared by its signature, where the environment does not declare it already: precise where the built-in allows, as [Simplify]() with the type ∀ A, A → A, and over [Expressions]() otherwise, as [D]() with `Expressions -> Expressions -> Expressions` and [Sqrt]() with `Expressions -> Expressions`. The numbers of the environment go into [Expressions]() by coercions. No equation about a built-in is assumed.
- The option `"Meaning"` is `"Function"`, the default, for a constant that is the function *symbol* computes, or `"Rules"` for its rules, its [DownValues](), as a rewriting of expressions: the definition named `"DownValues[symbol]"` gives the expression that an expression rewrites to by the first rule that matches it, and `"none"` where none does and the expression stays as it is. The rules are terms of an environment with the Wolfram Language's expressions and matches, the prelude or one that extends it, as the integers do; another, such as the constructive environment, gives a [Failure]() tagged `"RulesEnvironment"`.
- The rules are [MatchFirst]() of the [MatchSum]() of the matches of the rules, in the order the Wolfram Language tries them. The left side of each rule is translated from its pattern: the lengths and parts of the expression by [Length](), [Arguments]() and [MatchPart](), its heads and literals by [SameQ](), sequences by every split, an [Orderless]() head by every order, alternatives by [MatchSum](), exceptions by [MatchQ](), and conditions by [SameQ]() of their [ExpressionEvaluate]() and `True`. The right side is quoted as it is, its pattern variables the parts they match, whatever it calls: the rules give one step of evaluation. The tutorial *Patterns and Rewriting* goes through every pattern.
- The atoms of the rules are data of the type [Atoms](), which nothing declares, so the kernel computes every test but a condition or a pattern test, which only the Wolfram Language evaluates.
- [KeyValuePattern]() does not translate, as an [Association]() is an atom, and gives a [Failure]() tagged `"Untranslatable"`.
- The result is a list of declarations, to extend an environment with: <code>[TypeTheoryEnvironment]()[*environment*, [TypeTheoryFormalize]()[*symbol*, *environment*]]</code>.

## Basic Examples

A Wolfram Language function on integers translates, and elaboration types it:

```wl
square[x_Integer] := x^2 + 1;
TypeTheoryFormalize[square, "Integers"]
```

<!-- => {definition square := (x ∶ ℤ) ↦ x^2 + 1} -->

---

A function whose arguments are not typed by their patterns is typed by elaboration, here in the prelude:

```wl
twice[x_] := 2 x;
TypeTheoryFormalize[twice]
```

<!-- => {definition twice := x ↦ 2 x} -->

---

A function that does not translate, because [Style]() has no signature, is an axiom that the Wolfram Language computes:

```wl
styled[x_] := Style[x, Bold];
TypeTheoryFormalize[styled]
```

<!-- => {axiom styled : Expressions → Expressions} -->

## Scope

A function formalized:

```wl
twice[x_] := 2 x;
doubling = TypeTheoryEnvironment[TypeTheoryFormalize[twice]]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

Its type:

```wl
TypeTheoryType[twice, doubling]
```

<!-- => ℕ → ℕ -->

The kernel computes it:

```wl
WeakHeadNormalForm[TypeTheoryTerm[twice[21], doubling]]
```

<!-- => 42 -->

---

A function that calls another is formalized after it:

```wl
square[x_Integer] := x^2 + 1;
next[x_Integer] := square[x] + 1;
TypeTheoryFormalize[next, "Integers"]
```

<!-- => {definition square := (x ∶ ℤ) ↦ x^2 + 1, definition next := (x ∶ ℤ) ↦ square[x] + 1} -->

```wl
formalized = TypeTheoryEnvironment["Integers", TypeTheoryFormalize[next, "Integers"]]
```

<!-- => TypeTheoryEnvironment summary box: 334 constants -->

```wl
TypeTheoryType[next, formalized]
```

<!-- => ℤ → ℤ -->

---

A function of strings is a definition over [Strings](). The constructive environment has no strings, so [Strings]() is declared with it, and a string literal is a constant of it:

```wl
greeting[s_] := StringJoin["Hello, ", s];
TypeTheoryFormalize[greeting, "Constructive"]
```

<!-- => {axiom Strings : Type, axiom StringJoin : Strings → Strings → Strings, axiom "Hello, " : Strings, definition greeting := s ↦ "Hello, " <> s} -->

```wl
TypeTheoryType[greeting, TypeTheoryEnvironment["Constructive", TypeTheoryFormalize[greeting, "Constructive"]]]
```

<!-- => Strings → Strings -->

---

The prelude has the strings already, and the literal is the string it is:

```wl
greeting[s_] := StringJoin["Hello, ", s];
TypeTheoryFormalize[greeting]
```

<!-- => {axiom StringJoin : Strings → Strings → Strings, definition greeting := s ↦ "Hello, " <> s} -->

---

A built-in with a precise signature is declared with it:

```wl
simplified[x_Integer] := Simplify[x + 1];
TypeTheoryFormalize[simplified, "Integers"]
```

<!-- => {axiom Simplify : ∀_{A∶Type u} A → A, definition simplified := (x ∶ ℤ) ↦ Simplify[x + 1]} -->

---

A built-in that takes any expression has a signature over [Expressions]():

```wl
derivative[y_, x_] := D[y, x];
TypeTheoryFormalize[derivative]
```

<!-- => {axiom D : Expressions → Expressions → Expressions, definition derivative := y x ↦ ∂_x y} -->

---

Structural recursion on a list is a definition by the recursor of lists:

```wl
size[{}] = 0;
size[{x_, rest___}] := 1 + size[{rest}];
sized = TypeTheoryEnvironment[TypeTheoryFormalize[size]]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

Its elements are of any type:

```wl
TypeTheoryType[size, sized]
```

<!-- => ∀_{elementType∶Type u} {elementType} → ℕ -->

It computes:

```wl
WeakHeadNormalForm[TypeTheoryTerm[size[{4, 5, 6}], sized]]
```

<!-- => 3 -->

---

A factorial is a definition by the recursor of the natural numbers:

```wl
fact[0] = 1;
fact[n_] := n fact[n - 1];
facts = TypeTheoryEnvironment[TypeTheoryFormalize[fact]]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

```wl
TypeTheoryType[fact, facts]
```

<!-- => ℕ → ℕ -->

```wl
WeakHeadNormalForm[TypeTheoryTerm[fact[5], facts]]
```

<!-- => 120 -->

---

An argument passed on unchanged in the recursive call is an argument outside the recursion:

```wl
power[x_, 0] = 1;
power[x_, n_] := x power[x, n - 1];
powers = TypeTheoryEnvironment[TypeTheoryFormalize[power]]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

```wl
TypeTheoryType[power, powers]
```

<!-- => ℕ → ℕ → ℕ -->

```wl
WeakHeadNormalForm[TypeTheoryTerm[power[2, 10], powers]]
```

<!-- => 1024 -->

---

[If]() is the decision of its condition, a definition of the prelude:

```wl
clamp[x_Integer] := If[x <= 3, x, 3];
TypeTheoryFormalize[clamp, "Type" -> NonNegativeIntegers -> NonNegativeIntegers]
```

<!-- => {definition clamp : ℕ → ℕ := x ↦ If[x <= 3, x, 3]} -->

The constructive environment has no [If](), so it is declared with the definition:

```wl
clamp[x_Integer] := If[x <= 3, x, 3];
TypeTheoryFormalize[clamp, "Constructive", "Type" -> NonNegativeIntegers -> NonNegativeIntegers]
```

<!-- => {definition If := {A∶Type u} (condition∶Prop) [decision∶Decidable[condition]] (a∶A) (b∶A) ↦ (Decidable_rec)[(d∶Decidable[condition]) ↦ A, (h∶¬condition) ↦ b, (h∶condition) ↦ a, decision], definition clamp : ℕ → ℕ := x ↦ If[x <= 3, x, 3]} -->

The kernel computes the decision:

```wl
clamped = TypeTheoryEnvironment[TypeTheoryFormalize[clamp, "Type" -> NonNegativeIntegers -> NonNegativeIntegers]]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

```wl
WeakHeadNormalForm[TypeTheoryTerm[clamp[5], clamped]]
```

<!-- => 3 -->

```wl
WeakHeadNormalForm[TypeTheoryTerm[clamp[2], clamped]]
```

<!-- => 2 -->

## Options

### Type

A function that does not translate is an axiom of the type given, which it computes:

```wl
styled[x_] := Style[x, Bold];
TypeTheoryFormalize[styled, "Type" -> Integers -> Integers]
```

<!-- => {axiom styled : ℤ → ℤ} -->

---

A definition is checked against the type given, which decides its arguments over the head of their pattern:

```wl
square[x_Integer] := x^2 + 1;
TypeTheoryFormalize[square, "Type" -> NonNegativeIntegers -> NonNegativeIntegers]
```

<!-- => {definition square : ℕ → ℕ := x ↦ x^2 + 1} -->

---

A type of the list recursion's elements and result:

```wl
size[{}] = 0;
size[{x_, rest___}] := 1 + size[{rest}];
TypeTheoryFormalize[size, "Type" -> {NonNegativeIntegers} -> NonNegativeIntegers]
```

<!-- => {definition size : {ℕ} → ℕ := (listArgument∶{ℕ}) ↦ List_rec[(list∶{ℕ}) ↦ ℕ, 0, (x∶ℕ) (rest∶{ℕ}) (recursionResult∶ℕ) ↦ 1 + recursionResult, listArgument]} -->

---

Definitions with different numbers of arguments are an axiom of the type given:

```wl
norm[x_] := Abs[x];
norm[x_, y_] := Sqrt[x^2 + y^2];
TypeTheoryFormalize[norm, "Type" -> Expressions -> Expressions]
```

<!-- => {axiom norm : Expressions → Expressions} -->

### Meaning

The rules of a function, a rewriting of expressions:

```wl
listed[x_, y_, z___] := {x, y, z};
rules = TypeTheoryFormalize[listed, "Meaning" -> "Rules"]
```

<!-- => {definition DownValues[listed] : Expressions → Option[Expressions] := (expression ∶ Expressions) ↦ MatchFirst[...]} -->

The kernel computes them: an expression with two arguments or more rewrites to the list of them:

```wl
listing = TypeTheoryEnvironment[rules];
NormalForm[TypeTheoryTerm["DownValues[listed]"[listed[1, 2]], listing]]
```

<!-- => some[{1, 2}] -->

And one with fewer stays as it is:

```wl
NormalForm[TypeTheoryTerm["DownValues[listed]"[listed[1]], listing]]
```

<!-- => none -->

The same, by [DefinitionallyEqualQ]():

```wl
DefinitionallyEqualQ[TypeTheoryTerm["DownValues[listed]"[listed[1, 2]], listing], TypeTheoryTerm["some"[Unevaluated[{1, 2}]], listing]]
```

<!-- => True -->

---

The rules translate whatever the right side calls, quoted as it is:

```wl
slope[y_] := D[y, t];
TypeTheoryFormalize[slope, "Meaning" -> "Rules"]
```

<!-- => {definition DownValues[slope] : Expressions → Option[Expressions] := (expression ∶ Expressions) ↦ MatchFirst[MatchPart[expression, 1, (y ∶ Expressions) ↦ MatchValue[∂_t y]] /; ¬AtomQ[expression] ∧ Decide[Length[{Arguments[expression]}] == 1]]} -->

## Properties and Relations

The declarations extend an environment:

```wl
square[x_Integer] := x^2 + 1;
TypeTheoryEnvironment["Integers", TypeTheoryFormalize[square, "Integers"]]
```

<!-- => TypeTheoryEnvironment summary box: 333 constants -->

---

An axiom names the function that computes it:

```wl
styled[x_] := Style[x, Bold];
styling = TypeTheoryEnvironment[TypeTheoryFormalize[styled, "Type" -> NonNegativeIntegers -> NonNegativeIntegers]]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

```wl
Information[TypeTheoryTerm[styled, styling], "Implementation"]
```

<!-- => styled -->

It is an axiom the terms that use it rest on:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[styled[2], styling]]
```

<!-- => <|styled -> "Signature"|> -->

---

A definition rests on the signatures of the built-ins it calls:

```wl
derivative[y_, x_] := D[y, x];
differentiating = TypeTheoryEnvironment[TypeTheoryFormalize[derivative]]
```

<!-- => TypeTheoryEnvironment summary box: 259 constants -->

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[derivative, differentiating]]
```

<!-- => <|D -> "Signature"|> -->

## Possible Issues

Without a type, a function that does not translate takes [Expressions]() for each argument, and where the environment has no [Expressions](), as the constructive one, it is declared with it, with a coercion of the natural numbers into it:

```wl
styled[x_] := Style[x, Bold];
TypeTheoryFormalize[styled, "Constructive"]
```

<!-- => {axiom Expressions : Type, axiom expressionOfNatural : ℕ → Expressions, coercion ExpressionOfNaturalCoercion := (n ∶ ℕ) ↦ expressionOfNatural[n], axiom styled : Expressions → Expressions} -->

---

A symbol in the body that is not an argument, here `t`, has no counterpart, so the function is an axiom, even where [D]() has a signature:

```wl
slope[y_] := D[y, t];
TypeTheoryFormalize[slope]
```

<!-- => {axiom slope : Expressions → Expressions} -->

The variable as an argument translates:

```wl
derivative[y_, x_] := D[y, x];
TypeTheoryFormalize[derivative]
```

<!-- => {axiom D : Expressions → Expressions → Expressions, definition derivative := y x ↦ ∂_x y} -->

---

A type the definitions do not have is the type of an axiom, which the kernel takes on trust:

```wl
square[x_Integer] := x^2 + 1;
TypeTheoryFormalize[square, "Integers", "Type" -> Booleans -> Booleans]
```

<!-- => {axiom square : 𝔹 → 𝔹} -->

---

A function that calls itself through another function is an axiom:

```wl
evenQ[n_] := If[n == 0, True, oddQ[n - 1]];
oddQ[n_] := If[n == 0, False, evenQ[n - 1]];
TypeTheoryFormalize[evenQ]
```

<!-- => {axiom evenQ : Expressions → Expressions} -->

---

Definitions that take different numbers of arguments need a type:

```wl
norm[x_] := Abs[x];
norm[x_, y_] := Sqrt[x^2 + y^2];
TypeTheoryFormalize[norm]
```

<!-- => Failure["Unformalizable", ...] -->

---

The rules are terms of the Wolfram Language's expressions and matches, which the constructive environment does not have:

```wl
listed[x_, y_, z___] := {x, y, z};
TypeTheoryFormalize[listed, "Constructive", "Meaning" -> "Rules"]
```

<!-- => Failure["RulesEnvironment", ...] -->

---

[KeyValuePattern]() has no counterpart among the matches:

```wl
valueOf[KeyValuePattern[{"a" -> x_}]] := x;
TypeTheoryFormalize[valueOf, "Meaning" -> "Rules"]
```

<!-- => Failure["Untranslatable", ...] -->

---

`"Meaning"` is `"Function"` or `"Rules"`:

```wl
listed[x_, y_, z___] := {x, y, z};
TypeTheoryFormalize[listed, "Meaning" -> "Values"]
```

<!-- => Failure["InvalidOption", ...] -->

---

The function is given as its symbol; a string is left as it is:

```wl
TypeTheoryFormalize["square"]
```

<!-- => TypeTheoryFormalize["square"] -->
