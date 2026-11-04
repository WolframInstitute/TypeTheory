---
Template: TechNote
Name: TheWolframLanguage
Title: The Wolfram Language
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/tutorial/TheWolframLanguage
Keywords: [Wolfram Language, expressions, pattern matching, Match, monad, nondeterminism, Option, Match IR]
RelatedGuides: [TypeTheory]
RelatedTutorials: [Elaboration, ThePrelude, TypeTheoryIntroduction]
---

[TypeTheoryEnvironment]()["WolframLanguage"] is the prelude with the expressions of the Wolfram Language as an inductive type, and with the monad of pattern matching. A pattern is a function from expressions to its matches, and a definition is the first match of its rules, so a Wolfram Language function has a meaning in the type theory: a total function, whose value is an [Option]() that is none where no rule matches and the expression stays as it is.

## Expressions

An expression is an atom, a symbol, a number or a string, which has no parts, or a head applied to a list of expressions. The atoms are opaque, and [SameQ]() and [Head]() on them are axioms that the Wolfram Language computes:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"]
```

<!-- => TypeTheoryEnvironment summary box -->

```wl
wolfram["Expressions"]
```

<!-- => TypeTheoryInductiveType["Expressions", Type, {"expressionAtom" -> "Atoms" -> "Expressions", "expressionNormal" -> "Expressions" -> List "Expressions" -> "Expressions"}] -->

`"matchPart"` gives the part of an expression at a position, its head at 0, as [Part]() does, with no result out of range where [Part]() fails:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm["matchPart"["expressionNormal"["expressionAtom"["atomOfNatural"[7]], {"expressionAtom"["atomOfNatural"[1]], "expressionAtom"["atomOfNatural"[2]]}], 2], wolfram],
    TypeTheoryTerm["matchPure"["expressionAtom"["atomOfNatural"[2]]], wolfram]
]
```

<!-- => True -->

## The Monad of Matches

`"Match"[A]` is the list of the results of a match, in the order they are tried: none, one, or several, as a pattern with an [Orderless]() head or a sequence matches in several ways. Its operations are those of the monad of lists, the monad of nondeterminism:

| | the Match IR of the WolframKernel compiler | in the type theory |
|---|---|---|
| one result | `Values` | `"matchPure"` |
| no result | `Sum[]` | `"matchFailure"` |
| alternatives, in order | `Sum` | `"matchAlternative"` |
| parts matched in turn | `Product` | `"matchBind"` |
| a condition | `Guard` | `"matchGuard"` |
| the rule applied | the leftmost result | `"matchFirst"`, an [Option]() |

The alternatives keep their order, so the first result is the left one, as the Wolfram Language applies the first rule that matches:

```wl
DefinitionallyEqualQ[TypeTheoryTerm["matchFirst"["matchAlternative"["matchPure"[1], "matchPure"[2]]], wolfram], TypeTheoryTerm[OptionSome[1], wolfram]]
```

<!-- => True -->

A match with no result gives none, the expression left as it is:

```wl
DefinitionallyEqualQ[TypeTheoryTerm["matchFirst"[Typed["matchFailure", "Match"[NonNegativeIntegers]]], wolfram], TypeTheoryTerm[Typed[OptionNone, Option[NonNegativeIntegers]], wolfram]]
```

<!-- => True -->

`"matchBind"` continues each result with another match, as the parts of a pattern are matched in turn:

```wl
DefinitionallyEqualQ[TypeTheoryTerm["matchBind"[{1, 2}, Function[{Typed[x, NonNegativeIntegers]}, {x, x}]], wolfram], TypeTheoryTerm[{1, 1, 2, 2}, wolfram]]
```

<!-- => True -->
