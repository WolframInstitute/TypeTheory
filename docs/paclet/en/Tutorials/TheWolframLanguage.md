---
Template: TechNote
Name: TheWolframLanguage
Title: The Wolfram Language
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/tutorial/TheWolframLanguage
Keywords: [Wolfram Language, expressions, Sequence, List, heterogeneous list, currying, pattern matching, Match, MatchValue, MatchSum, MatchPart, monad, nondeterminism, Option, Wolfram/Patterns, Match IR, DownValues, rules, rewriting]
RelatedGuides: [TypeTheory]
RelatedTutorials: [Elaboration, ThePrelude, TypeTheoryIntroduction]
---

[TypeTheoryEnvironment]()["WolframLanguage"] is the prelude with the expressions of the Wolfram Language as an inductive type, and with the monad of pattern matching. A pattern is a function from expressions to its matches, and a definition is the first match of its rules, so a Wolfram Language function has a meaning in the type theory: a total function, whose value is an [Option]() that is none where no rule matches and the expression stays as it is.

## Expressions

An expression is an atom, a symbol, a number or a string, which has no parts, or a head applied to a list of expressions, its arguments. The atoms are opaque, and [SameQ]() and [Head]() of an atom are axioms that the Wolfram Language computes, as is [ExpressionValue](), the expression an expression evaluates to. [Head](), [Arguments]() and [AtomQ]() are definitions, which the kernel computes. A natural number is an expression where one is expected:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
TypeTheoryType["normal"[7, {1, 2}], wolfram]
```

<!-- => Expressions -->

An expression is written as the Wolfram Language holds one, `HoldForm[e]`, and shows so: its symbols are their atoms, declared as constants named by their full names, its natural numbers and strings theirs, and its variables in scope the expressions they stand for, a list of expressions among its arguments joined in, as `Sequence @@ l` is. `"normal"` and `"atom"` build what it stands for:

```wl
quoting = TypeTheoryEnvironment[wolfram, {TypeTheoryAxiom["System`List", Atoms, "Implementation" -> List]}];
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{Typed[x, Expressions], Typed[rest, {Expressions}]}, HoldForm[{x, rest}]][1, {2, 3}], quoting],
    TypeTheoryTerm["normal"["atom"["System`List"], {1, 2, 3}], quoting]
]
```

<!-- => True -->

[Arguments]() gives the list of an expression's arguments:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Arguments["normal"[7, {1, 2}]], wolfram], TypeTheoryTerm[Typed[{1, 2}, {Expressions}], wolfram]]
```

<!-- => True -->

## Sequences

A Wolfram Language function is applied to a sequence of arguments: `f[a, b]` gives `f` the sequence of `a` and `b`, and the curried `f[a][b]` gives `f` the sequence of `a`, then gives its value the sequence of `b`. `Sequence[a, b]` is that sequence, and `Sequence[A, B]` its type, for `a` of the type `A` and `b` of the type `B`: a list of elements of different types, whose type gives its length and the type of each element, as Lean's `HList`. `Sequence`, as `List`, is a type and its elements alike: where a type is expected it is the type, elsewhere a sequence, and in a term on its own, its elements decide, types making the type. A sequence shows in brackets, `[a, b]`. It is `"sequencePrepend"` over `"emptySequence"`, as a list is [Prepend]() over `{}`, and a `Sequence` among its elements is spliced, as the Wolfram Language splices it:

```wl
{TypeTheoryType[Sequence[1, Typed[2, Expressions]], wolfram], DefinitionallyEqualQ[TypeTheoryTerm[Sequence[1, Sequence[2, 3]], wolfram], TypeTheoryTerm[Sequence[1, 2, 3], wolfram]]}
```

<!-- => {[ℕ, Expressions], True} -->

A binder of a type [Sequence]()[...] takes the arguments of an application that are left as one `Sequence`, so a function of the type `Sequence[A, B] -> C` is applied as the Wolfram Language applies one, `f[a, b]`, and is another function than one of the curried type `A -> B -> C`, applied as `f[a][b]`. The type gives how many arguments it takes:

```wl
pairs = TypeTheoryEnvironment[wolfram, {
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
DefinitionallyEqualQ[TypeTheoryTerm[MatchFirst[MatchSum[MatchValue[1], MatchValue[2]]], wolfram], TypeTheoryTerm["some"[1], wolfram]]
```

<!-- => True -->

A match with no result gives none, the expression left as it is:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[MatchFirst[Typed[{}, Match[NonNegativeIntegers]]], wolfram], TypeTheoryTerm[Typed["none", Option[NonNegativeIntegers]], wolfram]]
```

<!-- => True -->

A result holds one value; a sequence of values is one value, a result of the type of sequences:

```wl
TypeTheoryType[MatchValue[Sequence[1, "true"]], wolfram]
```

<!-- => Match[[ℕ, 𝔹]] -->

[MatchPart]() matches at the part of an expression at a position, its head at 0, with no result out of range, where [Part]() fails:

```wl
{
    DefinitionallyEqualQ[TypeTheoryTerm[MatchPart["normal"[7, {1, 2}], 2, MatchValue], wolfram], TypeTheoryTerm[MatchValue[Typed[2, Expressions]], wolfram]],
    DefinitionallyEqualQ[TypeTheoryTerm[MatchPart["normal"[7, {1}], 5, MatchValue], wolfram], TypeTheoryTerm[Typed[{}, Match[Expressions]], wolfram]]
}
```

<!-- => {True, True} -->

## The Rules of a Symbol

The rules of a symbol, its [DownValues](), are a definition of type `Expressions -> Option[Expressions]`, which [TypeTheoryFormalize]() reads with `"Meaning" -> "Rules"`: the expression that an expression rewrites to by the first rule that matches it, and none where no rule does. The left side of each rule is read from the match program the compiler writes for it, an instruction at a time:

| the match program | the match |
|---|---|
| `Length[p, n]`, `MinLength[p, n]` | [Condition]() on the [Length]() of the [Arguments]() of the part at `p` |
| `HeadIs[p, h]`, `Same[p, e]` | [Condition]() on [SameQ]() of its [Head]() and `h`, or of it and `e` |
| `Bind[x, p]` | `MatchPart` at each position on the way to `p`, the part named `x` |
| `Join[x, p]` | [Condition]() on [SameQ]() of the part and `x`: a name repeated |
| `BindSequence[x, p, i, j]` | the arguments from position `i` to the `j`-th from the end, by [Drop]() |
| `AnyOf`, `NoneOf` | [Condition]() on [MatchQ]() of the matches of the alternatives |
| `Guard[test]` | [Condition]() on [SameQ]() of the [ExpressionValue]() of `test` and `True` |

The right side is quoted as it is, its pattern variables the parts they match: the rules give one step of evaluation, and the Wolfram Language evaluates the result further. A function whose third argument is a sequence:

```wl
listed[x_, y_, z___] := {x, y, z};
rules = TypeTheoryFormalize[listed, wolfram, "Meaning" -> "Rules"]
```

<!-- => {axiom System`List : Atoms, definition DownValues[listed] : Expressions → Option[Expressions] := (expression ∶ Expressions) ↦ MatchFirst[...]} -->

Lengths, parts and sequences are definitions, so the kernel computes the rewriting. An expression with two arguments or more rewrites to the list of them, and one with fewer stays as it is:

```wl
listing = TypeTheoryEnvironment[wolfram, rules];
{
    DefinitionallyEqualQ[TypeTheoryTerm["DownValues[listed]"["normal"[0, {1, 2, 3}]], listing], TypeTheoryTerm["some"["normal"["atom"["System`List"], {1, 2, 3}]], listing]],
    DefinitionallyEqualQ[TypeTheoryTerm["DownValues[listed]"["normal"[0, {1}]], listing], TypeTheoryTerm[Typed["none", Option[Expressions]], listing]]
}
```

<!-- => {True, True} -->

A test of a head, a literal or a condition is [SameQ]() of atoms, which the Wolfram Language computes and the kernel does not. A pattern that needs a search, as `f[x__, y__]` or an [Orderless]() head, is one the compiler leaves to the evaluator, and its rules do not translate yet.
