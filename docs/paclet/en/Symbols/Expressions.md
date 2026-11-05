---
Template: Symbol
Name: Expressions
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Expressions
Keywords: [Wolfram Language, expressions, pattern matching, Match]
SeeAlso: [Atoms, Arguments]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage]
---

## Usage

[Expressions]() is the type of the expressions of the Wolfram Language: an atom, `"atom"`[*a*], or a head applied to the sequence of its arguments, [Construct]()[*h*, *a*, *b*, ...], which is *h*[*a*, *b*, ...].

## Details & Options

- [Expressions]() is an inductive type of [TypeTheoryEnvironment]()["WolframLanguage"], nested: [Construct]() takes the arguments of an expression as one sequence, of the type `Expressions...`, so `Construct : Expressions -> Expressions... -> Expressions`.
- `A...` is the type of the sequences of any number of elements of `A`, as the pattern `p...` takes any number of expressions. A sequence is written held, `Unevaluated[a, b, ...]`, as the Wolfram Language holds the arguments it passes on; a sequence among its elements is spliced in, as are `Sequence @@ l` and `Unevaluated @@ l` of a list `l`, and [Prepend]()`[s, x]` puts `x` in front of a sequence `s`.
- The last explicit binder of a function, if its type is `A...`, takes the arguments that are left as one sequence, each an `A` or a sequence spliced in, as the Wolfram Language gives a function its arguments: `Construct[h, a, b]` gives `h` the sequence of `a` and `b`, and `Construct[h]` the empty one, `h[]`.
- [Construct]() of a term that is no expression applies it, as [Construct]() does in the Wolfram Language.
- The Wolfram Language strips [Unevaluated]() from an argument of a function with rules, even one that holds its arguments, so a sequence on its own is written inside a term: `TypeTheoryTerm[Unevaluated[1, 2], wolfram]`, or `Typed[Unevaluated[1, 2], NonNegativeIntegers...]`.
- Where an expression is expected, a term evaluates as in the Wolfram Language: a symbol that names nothing stands for itself, a head that names nothing applied to arguments is that expression, `{a, b}` is the expression `List[a, b]`, and a natural number or a string is its atom, by a coercion; a constant computes, and [HoldForm]() keeps it from computing.
- [TypeTheoryFormalize]() types a built-in it has no precise signature for over [Expressions]().

## Basic Examples

An expression with head 7 and arguments 1 and 2:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
TypeTheoryType[Construct[7, 1, 2], wolfram]
```

<!-- => Expressions -->

The type of [Construct](), whose arguments are a sequence:

```wl
TypeTheoryType[Construct, wolfram]
```

<!-- => Expressions → Expressions... → Expressions -->

## Scope

A sequence is written held, `Unevaluated[a, b, ...]`, and [Prepend]() puts an element in front of one, as in the Wolfram Language:

```wl
NormalForm[TypeTheoryTerm[Prepend[Unevaluated[1, 2, 3], 0], wolfram]]
```

<!-- => Unevaluated[0, 1, 2, 3] -->

Its type is `A...`, the type of the sequences of any number of elements of `A`:

```wl
TypeTheoryType[TypeTheoryTerm[Unevaluated[1, 2], wolfram]]
```

<!-- => ℕ... -->

A sequence among the arguments of [Construct]() is spliced in, and with none it builds `h[]`:

```wl
{
    NormalForm[TypeTheoryTerm[Construct[f, Unevaluated[1, 2], 3], wolfram]],
    NormalForm[TypeTheoryTerm[Construct[f], wolfram]]
}
```

<!-- => {f[1, 2, 3], f[]} -->

A variable of the type `Expressions...` is spliced where it stands among the arguments, so a function of a sequence is applied to the arguments themselves:

```wl
NormalForm[TypeTheoryTerm[Function[{Typed[s, Expressions...]}, Construct[g, 0, s]][1, 2], wolfram]]
```

<!-- => g[0, 1, 2] -->
