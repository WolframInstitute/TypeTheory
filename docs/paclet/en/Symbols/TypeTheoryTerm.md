---
Template: Symbol
Name: TypeTheoryTerm
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryTerm
Keywords: [term, type, surface syntax, Function, Typed, ForAll, Implies, Exists, dependent type, held, Booleans, overloading, ambiguous, implicit argument, PacletSymbol, notation]
SeeAlso: [TypeTheoryType, TypeTheoryEnvironment, TypeTheoryCheck, TypeUniverse, TypedImplicit, WeakHeadNormalForm, NormalForm, DefinitionallyEqualQ, TypeTheoryAxiomClosure, TypeTheoryExpression]
RelatedGuides: [TypeTheory]
RelatedTutorials: [Elaboration, TypeTheoryIntroduction]
---

## Usage

<code>[TypeTheoryTerm]()[*term*, *env*]</code> represents a term of the type theory in the [TypeTheoryEnvironment]() *env*, or in the library environment named *env*, written with built-in symbols such as [Function](), [Typed](), [ForAll](), [Implies](), [Equal]() and [Plus](), and kept unevaluated.

<code>[TypeTheoryTerm]()[*term*]</code> is a term in the default environment, [$TypeTheoryEnvironment](), the prelude unless [SetTypeTheoryEnvironment]() set another.

## Details & Options

- [TypeTheoryTerm]() has the attributes [HoldFirst]() and [SequenceHold](). It has to: on its own, <code>[ForAll]()[[Typed]()[x, A], B]</code> evaluates to `B`, and `1 + 1 == 2` to [True](). The environment is evaluated: an environment, or the name of a library environment, such as `"Integers"`. A name of none gives a [Failure]() tagged `"UnknownEnvironment"`, and so does an environment that is that [Failure]().
- A term without an environment is in the default environment, except beside a term that has one, as in <code>[TypeTheoryCheck]()[*term*, *type*]</code>, where it takes that term's. The prelude has the expressions, strings and matches of the Wolfram Language, such as [Arguments]() and [Head]().
- <code>[TypeTheoryType]()[[TypeTheoryTerm]()[*term*, *env*]]</code> gives the type of *term*, and <code>[TypeTheoryType]()[[TypeTheoryTerm]()[*term*], *env*]</code> gives its type in *env*.
- The surface language:

| Surface term | Meaning |
|---|---|
| <code>[Function]()[{[Typed]()[x, A], ...}, b]</code> | a function |
| <code>[Function]()[b]</code>, `b &` | a function of its slots `#1`, `#2`, ..., taking as many arguments as the type expected takes, and at least the highest slot |
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
- Any other symbol or string is a bound variable or a declared constant. A symbol whose value is a [TypeTheoryTerm]() stands for that term, and one whose value is a finished [TypeTheoryProof]() stands for its proof; a symbol with any other value is a name.
- [True](), [False](), [Not](), [And]() and [Or](), and so `!`, `&&` and `||`, stand for the propositions or, in an environment that declares the Booleans, for its constants `"true"`, `"false"`, `"not"`, `"and"` and `"or"`, as the type allows: a proposition where a type or Prop is expected, a Boolean where [Booleans]() is. Elsewhere the arguments decide, or how the term is used. A term that nothing decides is ambiguous, and <code>[Typed]()[*e*, [TypeUniverse]()[0]]</code> or <code>[Typed]()[*e*, [Booleans]()]</code> says which it is, as the string `"true"` or `"not"` does for a Boolean.
- A term copied from a documentation page writes each symbol of the paclet as `PacletSymbol[paclet, name]`; the term stores the symbol it names.
- In a notebook a term shows in mathematical notation, with the term itself behind the display.
- In a notebook every part of a term that has a type shows it on mouseover, as Lean's infoview does: a variable the type its binder gives, a constant its declared type, a number, a string or a symbol of an expression its own, and an operator the type of the constant it stands for, ℕ → ℕ → ℕ for `+` of natural numbers, and `Expressions` for `-` in `n x^(n - 1)` with *n* an expression. A function of System, as [Replace]() or [AtomQ](), shows its type on its name and brackets, and `↦` the type of its function. Elaboration decides what an operator stands for, so a term that does not elaborate on its own shows the types of its variables and constants only. The display is the same with the types or without them.
- A constant shows as its symbol or string, applied to its arguments that are not implicit. TypeTheory builds that expression, with its parts already shown, and gives it to [MakeBoxes](), so [MakeBoxes]() definitions give a constant a notation and [Format]() definitions give its symbol a display, in terms, declarations and proofs alike.
- <code>[Information]()[*term*, "AxiomClosure"]</code> gives the axioms *term* rests on, as [TypeTheoryAxiomClosure]() does, <code>[Information]()[*term*, "Holes"]</code> the holes it rests on, <code>[Information]()[*term*, "Constants"]</code> the constants its type and value mention, <code>[Information]()[*term*, "Annotation"]</code> the annotation of a hole, <code>[Information]()[*term*, "ProofTree"]</code> its derivation, as [TypeTheoryProofTree]() gives it, <code>[Information]()[*term*, "Implementation"]</code> the function that computes an axiom, and <code>[Information]()[*term*, "Expression"]</code> the expression of the Wolfram Language it is written as, as [TypeTheoryExpression]() gives it.

## Basic Examples

An equation evaluates on its own:

```wl
1 + 1 == 2
```

<!-- => True -->

In a term it stays an equation:

```wl
TypeTheoryTerm[1 + 1 == 2]
```

<!-- => 1 + 1 == 2 -->

---

A term and its type:

```wl
TypeTheoryType[TypeTheoryTerm[2 + 3]]
```

<!-- => ℕ -->

---

A universal statement:

```wl
statement = TypeTheoryTerm[ForAll[{n}, n + 0 == n]]
```

<!-- => ∀_n n + 0 == n -->

It is a proposition. [TypeTheoryType]() gives the type of a term, here one held in a variable:

```wl
TypeTheoryType[statement]
```

<!-- => Prop -->

## Scope

A function of two arguments:

```wl
TypeTheoryTerm[{m, n} |-> m + n]
```

<!-- => m n ↦ m + n -->

---

The type of the polymorphic identity, a dependent function type, whose result mentions its argument:

```wl
TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[1]]}, A -> A]]
```

<!-- => ∀_A∶Type A → A -->

---

An implication, here in the symmetry of equality:

```wl
TypeTheoryTerm[ForAll[{Typed[m, Naturals], Typed[n, Naturals]}, Implies[m == n, n == m]]]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ m == n ⇒ n == m -->

---

The type of a function of two natural numbers, by [TypeSpecifier]():

```wl
TypeTheoryTerm[TypeSpecifier[{Naturals, Naturals} -> Naturals]]
```

<!-- => ℕ → ℕ → ℕ -->

---

The type of a predicate on the natural numbers, by an arrow:

```wl
TypeTheoryTerm[Naturals -> Booleans]
```

<!-- => ℕ → 𝔹 -->

---

Reflexivity for every type, whose implicit binder shows in braces:

```wl
TypeTheoryTerm[ForAll[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A]}, x == x]]
```

<!-- => ∀_{A∶Type} ∀_x∶A x == x -->

---

The same with a strict implicit binder, Lean's ⦃A⦄:

```wl
TypeTheoryTerm[ForAll[{Annotation[Typed[A, TypeUniverse[1]], "StrictImplicit"], Typed[x, A]}, x == x]]
```

<!-- => ∀_⦃A∶Type⦄ ∀_x∶A x == x -->

---

An existential statement, that 3 has a predecessor:

```wl
TypeTheoryTerm[Exists[{n}, n + 1 == 3]]
```

<!-- => ∃_n n + 1 == 3 -->

---

A quantifier with a condition, as the Wolfram Language writes one:

```wl
TypeTheoryTerm[ForAll[n, n > 0, n >= 1]]
```

<!-- => ∀_n,n > 0 n >= 1 -->

---

A proof checked against the statement it proves:

```wl
TypeTheoryTerm[Typed["equalityReflexivity"[4], 2 + 2 == 4]]
```

<!-- => equalityReflexivity[4] ∶ 2 + 2 == 4 -->

---

A local definition of squaring, used twice:

```wl
local = TypeTheoryTerm[With[{square = n |-> n n}, square[3] + square[4]]]
```

<!-- => With[{square = n ↦ n n}, square[3] + square[4]] -->

It computes:

```wl
WeakHeadNormalForm[local]
```

<!-- => 25 -->

---

Implicit arguments are filled in; [Construct]() gives them explicitly:

```wl
TypeTheoryType[Construct["equalityReflexivity", Naturals, 3]]
```

<!-- => 3 == 3 -->

---

[Subscript]() gives a constant's universe level, here the level of [Naturals]():

```wl
TypeTheoryType[Construct[Subscript["equalityReflexivity", 1], Naturals, 3]]
```

<!-- => 3 == 3 -->

---

A field of a pair:

```wl
TypeTheoryType[Typed[p, CartesianProductType[Naturals, Booleans]] |-> p[[1]]]
```

<!-- => ℕ × 𝔹 → ℕ -->

---

A list literal is the list [Prepend]() builds:

```wl
NormalForm[TypeTheoryTerm[Prepend[{2, 3}, 1]]]
```

<!-- => {1, 2, 3} -->

---

A goal, its hypotheses before ⊢:

```wl
TypeTheoryTerm[RightTee[{Typed[n, Naturals]}, n + 0 == n]]
```

<!-- => n ∶ ℕ ⊢ n + 0 == n -->

It is read as a universal statement:

```wl
TypeTheoryType[RightTee[{Typed[n, Naturals]}, n + 0 == n]]
```

<!-- => Prop -->

---

A binder without a type takes the type its body gives it:

```wl
TypeTheoryType[ForAll[{n}, n + 0 == n]]
```

<!-- => Prop -->

---

Where a Boolean is expected, `&&` and [True]() are Booleans:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Typed[True && False, Booleans]]]
```

<!-- => false -->

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

A finished proof:

```wl
proved = TypeTheoryProof[2 + 2 == 4, {"Decide"}]
```

<!-- => Proof complete -->

A term that uses it:

```wl
TypeTheoryType["equalitySymmetry"[proved]]
```

<!-- => 4 == 2 + 2 -->

---

A term in a library environment, given by its name:

```wl
difference = TypeTheoryTerm[Typed[2, Integers] - 3, "Integers"]
```

<!-- => (2 ∶ ℤ) - 3 -->

```wl
TypeTheoryType[difference]
```

<!-- => ℤ -->

---

Each `PacletSymbol` of code copied from a documentation page is stored as the symbol it names:

```wl
TypeTheoryTerm[Typed[n, PacletSymbol["WolframInstitute/TypeTheory", "Naturals"]] |-> n]
```

<!-- => (n ∶ ℕ) ↦ n -->

## Properties and Relations

The attributes that keep a term unevaluated:

```wl
Attributes[TypeTheoryTerm]
```

<!-- => {HoldFirst, SequenceHold} -->

---

A term in an environment of its own, here the empty one, <code>[TypeTheoryEnvironment]()[]</code>, which declares no constants:

```wl
TypeTheoryType[2 + 3, TypeTheoryEnvironment[]]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

A type of bits:

```wl
bits = TypeTheoryEnvironment[{TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}]}]
```

<!-- => TypeTheoryEnvironment summary box: 261 constants -->

A term in it:

```wl
TypeTheoryType[TypeTheoryTerm[BitOne, bits]]
```

<!-- => Bit -->

[TypeTheoryType]() also takes the environment as its second argument:

```wl
TypeTheoryType[BitOne, bits]
```

<!-- => Bit -->

---

The properties [Information]() gives of a term:

```wl
Information[TypeTheoryTerm[2 + 3], "Properties"]
```

<!-- => {"AxiomClosure", "Holes", "Constants", "Annotation", "ProofTree", "Implementation", "Expression"} -->

---

The constants a term and its type mention:

```wl
Information[TypeTheoryTerm[2 + 3], "Constants"]
```

<!-- => {Plus, ℤ_≥0} -->

---

The axioms a term rests on, as [TypeTheoryAxiomClosure]() gives them:

```wl
Information[TypeTheoryTerm["excludedMiddle"], "AxiomClosure"]
```

<!-- => <|"choice" -> "Signature", "quotientSoundness" -> "Proposition", "propositionalExtensionality" -> "Proposition"|> -->

---

The derivation of a proof of propositional logic, as [TypeTheoryProofTree]() gives it:

```wl
Information[TypeTheoryTerm[{Typed[a, TypeUniverse[0]], Typed[x, a]} |-> x], "ProofTree"]
```

<!-- => a / (a ⇒ a) →I -->

---

A theorem left as a hole:

```wl
later = TypeTheoryEnvironment[{TypeTheoryTheorem[Later, ForAll[{k}, k + 0 == k], TypeTheoryHole["by induction"]]}]
```

<!-- => TypeTheoryEnvironment summary box: 259 constants -->

The holes it rests on:

```wl
Information[TypeTheoryTerm[Later, later], "Holes"]
```

<!-- => <|Later -> {<|"Hole" -> TypeTheoryHole[Later, 1], "Statement" -> ∀_k∶ℕ k + 0 == k, "Annotation" -> <|"Citation" -> "by induction"|>|>}|> -->

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

A binder whose type nothing decides needs [Typed]():

```wl
TypeTheoryType[ForAll[{x}, x == x]]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

A symbol whose value is a bare [Function](), not a [TypeTheoryTerm](), is a name, which no environment declares:

```wl
increment = n |-> n + 1;
TypeTheoryType[increment[2]]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

A misspelled name of an environment gives a [Failure]():

```wl
TypeTheoryTerm[2 + 3, "Prelud"]
```

<!-- => Failure["UnknownEnvironment", ...] -->

---

Define doubling:

```wl
doubled = TypeTheoryEnvironment[TypeTheoryDefinition[Double, n |-> n + n]]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

[Format]() evaluates the arguments of what it formats, so a bound variable whose symbol has a value shows that value:

```wl
Format[Double[a_]] := CenterDot[2, a];
k = 7;
TypeTheoryTerm[k |-> Double[k], doubled]
```

<!-- => k ↦ 2·7 -->

---

Define doubling:

```wl
doubled = TypeTheoryEnvironment[TypeTheoryDefinition[Double, n |-> n + n]]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

[MakeBoxes]() holds them, so a notation for a constant applied to arguments is a definition of [MakeBoxes]():

```wl
MakeBoxes[Double[a_], form_] := MakeBoxes[CenterDot[2, a], form];
k = 7;
TypeTheoryTerm[k |-> Double[k], doubled]
```

<!-- => k ↦ 2·k -->
