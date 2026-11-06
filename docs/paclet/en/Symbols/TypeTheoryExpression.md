---
Template: Symbol
Name: TypeTheoryExpression
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryExpression
Keywords: [Wolfram Language, expression, reading, as written, normal form, value, agreement, typed definition, integers, rationals, function, ToExpression, Expression property]
SeeAlso: [NormalForm, TypeTheoryTerm, TypeTheoryFormalize, Expressions, ExpressionEvaluate, TypeTheoryType]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, Elaboration]
---

## Usage

<code>[TypeTheoryExpression]()[*term*]</code> gives the expression of the Wolfram Language that the [TypeTheoryTerm]() *term* is, as it is written.

<code>[TypeTheoryExpression]()[*term*, *h*]</code> wraps the expression in *h* before it evaluates.

## Details & Options

- [TypeTheoryExpression]() reads *term* as it is written, without reducing it: its constants are the symbols that name them, and the type theory's own notation is read as the Wolfram Language writes it. The expression evaluates in the Wolfram Language.
- An ascription, <code>[Typed]()[*e*, *T*]</code> or <code>[TypeHint]()[*e*, *T*]</code>, is *e*. A function is a [Function]() of its explicit arguments: its implicit binders are left out, and so are the types of the others.
- A constructor is the data the Wolfram Language writes: `"true"` and `"false"` are [True]() and [False](), `"none"` is `Missing["NotAvailable"]`, a value of `A | B` or of <code>[Option]()[*A*]</code> is the value in it, and a pair is a list of two. <code>[Decide]()[*p*]</code> is *p*, <code>[Arguments]()[*e*]</code> is `Sequence @@ e`, and <code>[FromString]()[*s*]</code> of the strings is *s*.
- [Unevaluated]() around the whole of *term* is the expression itself. Inside, it stays, as the Wolfram Language passes the argument on unevaluated.
- <code>[TypeTheoryExpression]()[[NormalForm]()[*term*]]</code> reads the value the kernel computes, in which a class of the integers or the rationals is its number. Where every constant in *term* is defined as the Wolfram Language defines it, as the prelude defines [Plus](), [Map]() and [Lookup](), and as [TypeTheoryFormalize]() reads a definition of the Wolfram Language, the reading evaluates to the reading of the value.
- A constant of your own reads as the symbol that names it, which the Wolfram Language evaluates by its own definitions, if it has any.
- Where something in *term* is the type theory's only, a proof, a recursor or a constant named by a string, [TypeTheoryExpression]() gives `Failure["NoExpression", ...]`. It does not check *term*: [TypeTheoryType]() does.
- <code>[TypeTheoryExpression]()[*term*, *h*]</code> wraps the expression in *h* before it evaluates, as <code>[ToExpression]()[*s*, *form*, *h*]</code> does: [HoldForm]() shows it as it is written.
- <code>[Information]()[*term*, "Expression"]</code> is <code>[TypeTheoryExpression]()[*term*]</code>.

## Basic Examples

A term is the expression it is written as, here a map of a pure function over a list:

```wl
TypeTheoryExpression[TypeTheoryTerm[Map[n |-> n^2, {1, 2, 3}]], HoldForm]
```

<!-- => Function[n, n^2] /@ {1, 2, 3} -->

Without a wrapper, it evaluates in the Wolfram Language:

```wl
TypeTheoryExpression[TypeTheoryTerm[Map[n |-> n^2, {1, 2, 3}]]]
```

<!-- => {1, 4, 9} -->

---

A function is a [Function]() of the Wolfram Language, without the types of its arguments:

```wl
weighted = TypeTheoryExpression[TypeTheoryTerm[{a, b} |-> a + 2 b]]
```

<!-- => Function[{a, b}, a + 2 b] -->

```wl
weighted[3, 4]
```

<!-- => 11 -->

---

The value the kernel computes is read from the normal form, here the factorial of 20:

```wl
factorials = TypeTheoryEnvironment[{TypeTheoryDefinition[FactorialOf, n |-> InductiveRecursor[Naturals][Naturals &, 1, (#1 + 1) #2 &, n]]}]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

```wl
TypeTheoryExpression[NormalForm[TypeTheoryTerm[FactorialOf[20], factorials]]]
```

<!-- => 2432902008176640000 -->

## Scope

An ascription is left out, so an integer of the type theory is the integer the Wolfram Language computes with:

```wl
TypeTheoryExpression[TypeTheoryTerm[Typed[-3, Integers] + 1, "Integers"], HoldForm]
```

<!-- => -3 + 1 -->

---

A decision is the proposition it decides, which the Wolfram Language evaluates to a Boolean:

```wl
TypeTheoryExpression[TypeTheoryTerm[Decide[2 <= 3]], HoldForm]
```

<!-- => 2 <= 3 -->

---

No value of an [Option]() is the [Missing]() the Wolfram Language gives:

```wl
TypeTheoryExpression[TypeTheoryTerm[Typed["none", Option[Naturals]]]]
```

<!-- => Missing["NotAvailable"] -->

---

A rewriting is the Wolfram Language's own, with its rules as they are written:

```wl
TypeTheoryExpression[TypeTheoryTerm[ReplaceRepeated[log[a b c], log[x_ y_] :> log[x] + log[y]]], HoldForm]
```

<!-- => log[a b c] //. log[x_ y_] :> log[x] + log[y] -->

---

The arguments of an expression are a [Sequence](), spliced into the list around them:

```wl
TypeTheoryExpression[TypeTheoryTerm[{Arguments[f[1, 2, 3]]}]]
```

<!-- => {1, 2, 3} -->

## Options

A wrapper is put around the expression before it evaluates. A quoted sum is the sum, which evaluates without one:

```wl
TypeTheoryExpression[TypeTheoryTerm[Unevaluated[1 + 2]]]
```

<!-- => 3 -->

[HoldComplete]() keeps it as it is written:

```wl
TypeTheoryExpression[TypeTheoryTerm[Unevaluated[1 + 2]], HoldComplete]
```

<!-- => HoldComplete[1 + 2] -->

## Properties and Relations

A definition of the Wolfram Language that [TypeTheoryFormalize]() reads computes in the kernel what it computes in the Wolfram Language:

```wl
square[x_Integer] := x^2 + 1;
squares = TypeTheoryEnvironment[TypeTheoryFormalize[square]]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

So the reading of a term, which the Wolfram Language evaluates, is the reading of its value, which the kernel computes:

```wl
fifth = TypeTheoryTerm[square[5], squares];
{TypeTheoryExpression[fifth], TypeTheoryExpression[NormalForm[fifth]]}
```

<!-- => {26, 26} -->

---

The class of pairs the kernel computes for an integer reads as the integer:

```wl
TypeTheoryExpression[NormalForm[TypeTheoryTerm[Typed[-3, Integers] + 1, "Integers"]]]
```

<!-- => -2 -->

---

The property `"Expression"` of a term is its reading:

```wl
Information[TypeTheoryTerm[Join[{1, 2}, {3}]], "Expression"]
```

<!-- => {1, 2, 3} -->

## Possible Issues

A constant of your own is a symbol the Wolfram Language has no definition of, so the reading and the value differ:

```wl
doubling = TypeTheoryEnvironment[{TypeTheoryDefinition[Doubled, n |-> 2 n]}]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

```wl
doubled = TypeTheoryTerm[Doubled[21], doubling];
{TypeTheoryExpression[doubled], TypeTheoryExpression[NormalForm[doubled]]}
```

<!-- => {Doubled[21], 42} -->

---

A proof has no reading as an expression:

```wl
TypeTheoryExpression[TypeTheoryTerm["equalityReflexivity"[2]]]
```

<!-- => Failure["NoExpression", ...] -->

---

The reading does not check the term. `Length[3]` is no term, as 3 is no list, but the Wolfram Language evaluates it:

```wl
TypeTheoryExpression[TypeTheoryTerm[Length[3]]]
```

<!-- => 0 -->

[TypeTheoryType]() checks it:

```wl
TypeTheoryType[Length[3]]
```

<!-- => Failure["TypeMismatch", ...] -->
