---
Template: TechNote
Name: TheWolframLanguage
Title: The Wolfram Language
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/tutorial/TheWolframLanguage
Keywords: [Wolfram Language, expressions, sums, Alternatives, Failure, Enclose, Confirm, errors, Sequence, List, heterogeneous list, currying, pattern matching, Match, MatchValue, MatchSum, MatchPart, monad, nondeterminism, Option, Wolfram/Patterns, Match IR, DownValues, rules, rewriting]
RelatedGuides: [TypeTheory]
RelatedTutorials: [PatternsAndRewriting, Elaboration, ThePrelude, TypeTheoryIntroduction]
---

The prelude declares the expressions of the Wolfram Language as an inductive type, and the monad of pattern matching, so every term, proof and query can use them without naming an environment; <code>[TypeTheoryEnvironment]()["WolframLanguage"]</code> is the prelude by the name it had when they were an environment of their own. A pattern is a function from expressions to its matches, and a definition is the first match of its rules, so a Wolfram Language function has a meaning in the type theory: a total function, whose value is an [Option]() that is none where no rule matches and the expression stays as it is.

## Expressions

An expression is an atom, a symbol, a number or a string, which has no parts, or a head applied to a sequence of expressions, its arguments, [Construct]()`[h, a, b]`, which is `h[a, b]`. An atom is data, of the type [Atoms](): a symbol by its full name, an integer, a string, the list of its character codes, or any other atom by its head and its [InputForm](). So [Head](), [Arguments](), [AtomQ]() and [SameQ]() are definitions, which the kernel computes, and only [ExpressionEvaluate](), the expression an expression evaluates to, is an axiom that the Wolfram Language computes. A natural number is an expression where one is expected:

```wl
TypeTheoryType[Construct[7, 1, 2]]
```

<!-- => Expressions -->

An expression is written as the Wolfram Language holds one, `HoldForm[e]`, and shows so: its symbols, numbers and strings are their atoms, which nothing declares, and its variables in scope the expressions they stand for, a sequence of expressions among its arguments spliced in, as is `Sequence @@ l` of a list. [Construct]() and `"atom"` build what it stands for:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{Typed[x, Expressions], Typed[rest, Expressions...]}, HoldForm[{x, rest}]][1, 2, 3]],
    TypeTheoryTerm[Construct["atom"["symbolAtom"["System`List"]], 1, 2, 3]]
]
```

<!-- => True -->

[Arguments]() gives the sequence of an expression's arguments, so that [Construct]()`[Head[e], Arguments[e]]` is *e*, and `{Arguments[e]}` is their list:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[{Arguments[Construct[7, 1, 2]]}], TypeTheoryTerm[Typed[{1, 2}, {Expressions}]]]
```

<!-- => True -->

## Sequences

A Wolfram Language function is applied to a sequence of arguments: `f[a, b]` gives `f` the sequence of `a` and `b`, and the curried `f[a][b]` gives `f` the sequence of `a`, then gives its value the sequence of `b`. `Sequence[a, b]` is that sequence, and `Sequence[A, B]` its type, for `a` of the type `A` and `b` of the type `B`: a list of elements of different types, whose type gives its length and the type of each element, as Lean's `HList`. `Sequence`, as `List`, is a type and its elements alike: where a type is expected it is the type, elsewhere a sequence, and in a term on its own, its elements decide, types making the type. A sequence shows in brackets, `[a, b]`. It is `"sequencePrepend"` over `"emptySequence"`, as a list is [Prepend]() over `{}`, and a `Sequence` among its elements is spliced, as the Wolfram Language splices it:

```wl
{TypeTheoryType[Sequence[1, Typed[2, Expressions]]], DefinitionallyEqualQ[TypeTheoryTerm[Sequence[1, Sequence[2, 3]]], TypeTheoryTerm[Sequence[1, 2, 3]]]}
```

<!-- => {[ℕ, Expressions], True} -->

A binder of a type [Sequence]()[...] takes the arguments of an application that are left as one `Sequence`, so a function of the type `Sequence[A, B] -> C` is applied as the Wolfram Language applies one, `f[a, b]`, and is another function than one of the curried type `A -> B -> C`, applied as `f[a][b]`. The type gives how many arguments it takes:

```wl
pairs = TypeTheoryEnvironment[{
    TypeTheoryAxiom[sum, Sequence[NonNegativeIntegers, NonNegativeIntegers] -> NonNegativeIntegers],
    TypeTheoryAxiom[curried, NonNegativeIntegers -> NonNegativeIntegers -> NonNegativeIntegers]
}];
{
    DefinitionallyEqualQ[TypeTheoryTerm[sum[1, 2], pairs], TypeTheoryTerm[sum[Sequence[1, 2]], pairs]],
    FailureQ[TypeTheoryType[sum[1], pairs]],
    TypeTheoryType[curried[1], pairs]
}
```

<!-- => {True, True, ℕ → ℕ} -->

A sequence of any number of elements of one type `A` is of the type `A...`, as the pattern `p...` takes any number of expressions. It is written held, `Unevaluated[a, b, ...]`, as the Wolfram Language holds the arguments it passes on, shows in brackets, `[a, b, ...]`, as every sequence does, and [Prepend]() puts an element in front of one, as it does in the Wolfram Language; a sequence among the elements is spliced in, as are `Sequence @@ l` and `Unevaluated @@ l` of a list `l`:

```wl
{
    NormalForm[TypeTheoryTerm[Prepend[Unevaluated[1, 2, 3], 0]]],
    NormalForm[TypeTheoryTerm[Unevaluated[Unevaluated[1, 2], 3, Unevaluated @@ {4, 5}]]]
}
```

<!-- => {[0, 1, 2, 3], [1, 2, 3, 4, 5]} -->

The last explicit binder of a function, if its type is `A...`, takes the arguments that are left as one sequence, so [Construct](), of the type `Expressions -> Expressions... -> Expressions`, is applied to a head and its arguments, as in the Wolfram Language:

```wl
{TypeTheoryType[Construct], NormalForm[TypeTheoryTerm[Construct[f, 1, Unevaluated[2, 3]]]]}
```

<!-- => {Expressions → Expressions... → Expressions, f[1, 2, 3]} -->

## Sums and Failures

`A | B` is the type of a value of `A` or of `B`, as the pattern `_A | _B` matches either: the sum [DisjointUnionType]()`[A, B]`. Where a sum is expected, a value of either side is one, injected with no tag, as a Wolfram Language function returns a number or a string; a string, or a symbol that names nothing, is a value of the first side that takes it:

```wl
TypeTheoryType[Typed[n, NonNegativeIntegers] |-> Typed[If[n == 0, "zero", n], NonNegativeIntegers | Strings]]
```

<!-- => ℕ → (ℕ | Strings) -->

A Wolfram Language function that cannot give a value gives a [Failure](): `Failure[tag, details]`, its tag a string and its details an expression, as an association of what went wrong:

```wl
TypeTheoryType[Failure["DivideByZero", <|"Numerator" -> 7|>]]
```

<!-- => Failure -->

So a computation that may fail has a value of `A | Failure`, and [If]() picks the branch by the decision of its condition:

```wl
TypeTheoryType[Typed[n, NonNegativeIntegers] |-> Typed[If[n == 0, Failure["Zero", <|"Value" -> n|>], n - 1], NonNegativeIntegers | Failure]]
```

<!-- => ℕ → (ℕ | Failure) -->

`A | Failure` is a monad, as [Option]() is: `"confirmBind"` continues a value with the function it is given and passes a failure on:

```wl
TypeTheoryType["confirmBind"]
```

<!-- => ∀_{A ∶ Type u} ∀_{B ∶ Type v} (A | Failure) → (A → (B | Failure)) → (B | Failure) -->

[Enclose]() and [Confirm]() are written with it, as the Wolfram Language writes a computation that stops at the first failure: `Enclose[body]` binds each `Confirm[e]` of *body*, in the order the Wolfram Language evaluates them, and has the type `A | Failure` for *body* of the type `A`:

```wl
TypeTheoryType[Function[{Typed[a, NonNegativeIntegers | Failure], Typed[b, NonNegativeIntegers | Failure]}, Enclose[Confirm[a] * Confirm[b]]]]
```

<!-- => (ℕ | Failure) → (ℕ | Failure) → (ℕ | Failure) -->

Of two failures, the first confirmed is the one it gives:

```wl
NormalForm[TypeTheoryTerm[Function[{Typed[a, NonNegativeIntegers | Failure], Typed[b, NonNegativeIntegers | Failure]}, Enclose[Confirm[a] * Confirm[b]]][Failure["First", 1], Failure["Second", 2]]]]
```

<!-- => right[Failure["First", 1]] -->

A [Confirm]() outside an [Enclose]() has nowhere to give its failure, and is refused:

```wl
TypeTheoryType[Typed[x, NonNegativeIntegers | Failure] |-> Confirm[x] + 1]
```

<!-- => Failure["ElaborationFailed", ...]: Confirm[x] is outside an Enclose -->

## The Monad of Matches

[Match]()`[A]` is the list of the results of a match, in the order they are tried: none, one, or several, as a pattern with an [Orderless]() head or a sequence matches in several ways. Its constants follow the match objects of the prototype paclet Wolfram/Patterns and the Match IR that the compiler of the WolframKernel project built from them. A result is one value, and every match with several results is a sum:

| | Wolfram/Patterns | the Match IR | in the type theory |
|---|---|---|---|
| one result | `MatchValues` | `Values` | [MatchValue]()` : A -> Match[A]` |
| one result of several values | `MatchValues` | `Values` | [MatchValue]()`[Sequence[a, b]] : Match[Sequence[A, B]]` |
| no result | | `Sum[]` | `{}` |
| alternatives, in order | `MatchSum` | `Sum` | [MatchSum]()` : Match[A] -> Match[A] -> Match[A]` |
| parts in turn | `MatchProduct` | `Product` | [MatchBind]()` : Match[A] -> (A -> Match[B]) -> Match[B]` |
| a match at a position | `MatchPart` | `Part` | [MatchPart]()` : Expressions -> ℕ -> (Expressions -> Match[A]) -> Match[A]` |
| a condition | | `Guard` | [Condition]()` : Match[A] -> Booleans -> Match[A]` |
| whether it matches | | | [MatchQ]()` : Match[A] -> Booleans` |
| the rule applied | the first result | the leftmost result | [MatchFirst]()` : Match[A] -> Option[A]` |

These are the operations of the monad of lists, the monad of nondeterminism, with its alternatives in order: [MatchValue]() is its unit and [MatchBind]() its bind.

The alternatives keep their order, so the first result is the left one, as the Wolfram Language applies the first rule that matches:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[MatchFirst[MatchSum[MatchValue[1], MatchValue[2]]]], TypeTheoryTerm["some"[1]]]
```

<!-- => True -->

A match with no result gives none, the expression left as it is:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[MatchFirst[Typed[{}, Match[NonNegativeIntegers]]]], TypeTheoryTerm[Typed["none", Option[NonNegativeIntegers]]]]
```

<!-- => True -->

A result holds one value; a sequence of values is one value, a result of the type of sequences:

```wl
TypeTheoryType[MatchValue[Sequence[1, "true"]]]
```

<!-- => Match[[ℕ, 𝔹]] -->

[MatchPart]() matches at the part of an expression at a position, its head at 0, with no result out of range, where [Part]() fails:

```wl
{
    DefinitionallyEqualQ[TypeTheoryTerm[MatchPart[Construct[7, 1, 2], 2, MatchValue]], TypeTheoryTerm[MatchValue[Typed[2, Expressions]]]],
    DefinitionallyEqualQ[TypeTheoryTerm[MatchPart[Construct[7, 1], 5, MatchValue]], TypeTheoryTerm[Typed[{}, Match[Expressions]]]]
}
```

<!-- => {True, True} -->

## The Rules of a Symbol

The rules of a symbol, its [DownValues](), are a definition of type `Expressions -> Option[Expressions]`, which [TypeTheoryFormalize]() reads with `"Meaning" -> "Rules"`: the expression that an expression rewrites to by the first rule that matches it, and none where no rule does. The left side of each rule is translated from its pattern, every pattern the Wolfram Language has but [KeyValuePattern](), as the tutorial *Patterns and Rewriting* shows construct by construct. The right side is quoted as it is, its pattern variables the parts they match, a sequence variable the sequence of its expressions, `Unevaluated @@ l`, shown `[Sequence @@ l]`, of the type `Expressions...`, spliced where it stands: the rules give one step of evaluation, and the Wolfram Language evaluates the result further. A function whose third argument is a sequence:

```wl
listed[x_, y_, z___] := {x, y, z};
rules = TypeTheoryFormalize[listed, "Meaning" -> "Rules"]
```

<!-- => {definition DownValues[listed] : Expressions → Option[Expressions] := (expression ∶ Expressions) ↦ MatchFirst[...]} -->

Lengths, parts, sequences, heads and atoms are all definitions, so the kernel computes the rewriting. An expression with two arguments or more rewrites to the list of them, and one with fewer stays as it is; `listed` names nothing in the environment, so where an expression is expected it stands for itself:

```wl
listing = TypeTheoryEnvironment[rules];
{
    DefinitionallyEqualQ[TypeTheoryTerm["DownValues[listed]"[listed[1, 2, 3]], listing], TypeTheoryTerm["some"[HoldForm[{1, 2, 3}]], listing]],
    DefinitionallyEqualQ[TypeTheoryTerm["DownValues[listed]"[listed[1]], listing], TypeTheoryTerm[Typed["none", Option[Expressions]], listing]]
}
```

<!-- => {True, True} -->

A condition or a pattern test is [SameQ]() of the [ExpressionEvaluate]() of an expression and `True`, which only the Wolfram Language evaluates, so a rule with one computes in the kernel up to its test.
