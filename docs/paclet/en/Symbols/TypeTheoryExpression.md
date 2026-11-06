---
Template: Symbol
Name: TypeTheoryExpression
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryExpression
Keywords: [Wolfram Language, expression, reading, value, read back, normal form, data, integers, rationals, function, ToExpression, Expression property]
SeeAlso: [NormalForm, TypeTheoryTerm, TypeTheoryFormalize, Expressions, ExpressionEvaluate, TypeTheoryType]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, Elaboration]
---

## Usage

<code>[TypeTheoryExpression]()[*term*]</code> gives the expression of the Wolfram Language that the value of the [TypeTheoryTerm]() *term* stands for.

<code>[TypeTheoryExpression]()[*term*, *h*]</code> wraps the expression in *h* before it evaluates.

## Details & Options

- [TypeTheoryExpression]() reads the normal form of *term*, as [NormalForm]() computes it in the kernel, and gives its data as the Wolfram Language writes them, so a value computed in the type theory can be used in the Wolfram Language.
- A natural number is an integer, a class of the integers an integer and a class of the rationals a rational. A string, a list and an association are themselves, a Boolean is [True]() or [False](), and a quoted expression, of the type [Expressions](), is the expression.
- A value of `A | B` is the value in it, a value of <code>[Option]()[*A*]</code> is the value or `Missing["NotAvailable"]`, a pair is a list of two, and a sequence is a [Sequence](), spliced into what is around it.
- A function is a [Function]() of its explicit arguments: its implicit binders are left out, and so are the types of the others. The normal form of a function unfolds its arithmetic into recursors, so a function is read from its term as written, where its normal form has no reading and every constant in it is a System symbol, which the prelude defines as the Wolfram Language does.
- Where something in the value is the type theory's only, a proof, a recursor, a constant named by a string or a constant of your own, [TypeTheoryExpression]() gives `Failure["NoExpression", ...]`.
- <code>[TypeTheoryExpression]()[*term*, *h*]</code> wraps the expression in *h* before it evaluates, as <code>[ToExpression]()[*s*, *form*, *h*]</code> does: [HoldComplete]() keeps it unevaluated.
- <code>[Information]()[*term*, "Expression"]</code> is <code>[TypeTheoryExpression]()[*term*]</code>.

## Basic Examples

A list computed in the kernel is a list of the Wolfram Language:

```wl
TypeTheoryExpression[TypeTheoryTerm[Map[n |-> n^2, {1, 2, 3}]]]
```

<!-- => {1, 4, 9} -->

---

A function is a [Function]() of the Wolfram Language, which takes its arguments as the type theory's did:

```wl
weighted = TypeTheoryExpression[TypeTheoryTerm[{a, b} |-> a + 2 b]]
```

<!-- => Function[{a, b}, a + 2 b] -->

```wl
weighted[3, 4]
```

<!-- => 11 -->

---

An integer is a class of pairs of natural numbers, and reads as the integer it stands for:

```wl
TypeTheoryExpression[TypeTheoryTerm[Typed[-3, Integers] + 1, "Integers"]]
```

<!-- => -2 -->

## Scope

A class of the rationals is a rational:

```wl
TypeTheoryExpression[TypeTheoryTerm[1/2 + 1/3, "Rationals"]]
```

<!-- => 5/6 -->

---

A decision is a Boolean:

```wl
TypeTheoryExpression[TypeTheoryTerm[Decide[2 <= 3]]]
```

<!-- => True -->

---

A lookup of a key that an association does not have is the [Missing]() the Wolfram Language gives:

```wl
TypeTheoryExpression[TypeTheoryTerm[Lookup[<|"a" -> 1, "b" -> 2|>, "c"]]]
```

<!-- => Missing["KeyAbsent", "c"] -->

---

A rewriting computed in the kernel is the expression it gives, which then evaluates as any expression of the Wolfram Language does:

```wl
TypeTheoryExpression[TypeTheoryTerm[ReplaceRepeated[log[a b c], log[x_ y_] :> log[x] + log[y]]]]
```

<!-- => log[a] + log[b] + log[c] -->

---

A sequence is a [Sequence](), spliced into the list around it:

```wl
{TypeTheoryExpression[TypeTheoryTerm[Arguments[f[1, 2, 3]]]]}
```

<!-- => {1, 2, 3} -->

---

A constant of your own reads where its value is data:

```wl
doubling = TypeTheoryEnvironment[{TypeTheoryDefinition[Doubled, n |-> 2 n]}]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

```wl
TypeTheoryExpression[TypeTheoryTerm[Doubled[21], doubling]]
```

<!-- => 42 -->

## Options

A wrapper is put around the expression before it evaluates. Without one, a quoted sum evaluates:

```wl
TypeTheoryExpression[TypeTheoryTerm[Unevaluated[1 + 2]]]
```

<!-- => 3 -->

[HoldComplete]() keeps it as the kernel built it:

```wl
TypeTheoryExpression[TypeTheoryTerm[Unevaluated[1 + 2]], HoldComplete]
```

<!-- => HoldComplete[1 + 2] -->

---

[HoldForm]() shows how the rewriting grouped the sum, which [Plus]() flattens once it evaluates:

```wl
TypeTheoryExpression[TypeTheoryTerm[ReplaceRepeated[log[a b c], log[x_ y_] :> log[x] + log[y]]], HoldForm]
```

<!-- => log[a] + (log[b] + log[c]) -->

## Properties and Relations

The property `"Expression"` of a term is its reading:

```wl
Information[TypeTheoryTerm[Join[{1, 2}, {3}]], "Expression"]
```

<!-- => {1, 2, 3} -->

---

A term of squares:

```wl
squares = TypeTheoryTerm[Map[n |-> n^2, {1, 2, 3}]]
```

<!-- => (n ↦ n^2) /@ {1, 2, 3} -->

[NormalForm]() gives its value as a term of the type theory, which is no list of the Wolfram Language, and [TypeTheoryExpression]() gives the list:

```wl
{NormalForm[squares] === {1, 4, 9}, TypeTheoryExpression[squares] === {1, 4, 9}}
```

<!-- => {False, True} -->

## Possible Issues

A proof has no reading as an expression:

```wl
TypeTheoryExpression[TypeTheoryTerm["equalityReflexivity"[2]]]
```

<!-- => Failure["NoExpression", ...] -->

---

A function that calls a constant of your own has no reading: its normal form unfolds the arithmetic into recursors, and the Wolfram Language has no such constant:

```wl
doubling = TypeTheoryEnvironment[{TypeTheoryDefinition[Doubled, n |-> 2 n]}]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

```wl
TypeTheoryExpression[TypeTheoryTerm[m |-> Doubled[m] + 1, doubling]]
```

<!-- => Failure["NoExpression", ...] -->

---

The reading is of the value, so [HoldComplete]() holds what the kernel computed, not the term as it is written:

```wl
TypeTheoryExpression[TypeTheoryTerm[{1 + 1, 2}], HoldComplete]
```

<!-- => HoldComplete[{2, 2}] -->
