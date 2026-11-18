---
Template: TechNote
Name: WolframLanguageTheorems
Title: Wolfram Language Theorems
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/tutorial/WolframLanguageTheorems
Keywords: [theorems, universal statements, Wolfram Language, expressions, Replace, SameQ, If, Booleans, associations, Lookup, Enclose, Confirm, DownValues, proof by cases]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, PatternsAndRewriting, ThePrelude, ProgramsAndProofs]
---

An evaluation checks one input. A theorem says what a piece of Wolfram Language code does for every input: every expression, every Boolean, every key of an association. The prelude holds the Wolfram Language's expressions, Booleans, failures, associations and matches as definitions, so such statements can be written with [ForAll]() and proved, and the kernel checks each proof. Some follow by computation alone, even with unknowns in them; most need an argument, a split into cases or a lemma, which tactics build and the kernel checks again.

## What Computation Decides

A statement about every value can still be decided by computing, where the part that is unknown is never looked at. [Head]() of an application is its head, whatever the head and the arguments are:

```wl
TypeTheoryProof[ForAll[{Typed[h, Expressions], Typed[s, Expressions...]}, Head[Construct[h, s]] == h], {"Introduce"[h, s], "Reflexivity"}]
```

<!-- => Proof complete -->

A rule whose pattern is a head and plain blanks matches by the shape of the expression alone, so [Replace]() computes on any two arguments:

```wl
TypeTheoryProof[ForAll[{Typed[a, Expressions], Typed[b, Expressions]}, Replace[f[a, b], f[x_, y_] :> {y, x}] == {b, a}], {"Introduce"[a, b], "Reflexivity"}]
```

<!-- => Proof complete -->

## Splitting on a Boolean

A test on an unknown expression does not compute: whether `e` is an integer depends on `e`. [If]() takes the Boolean the test gives, as the Wolfram Language writes it, so the statement that a list of rules applies the first one that matches is

```wl
TypeTheoryProof[ForAll[{Typed[e, Expressions]}, Replace[e, {x_Integer :> "integer", y_ :> "other"}] == If[Head[e] === Integer, "integer", "other"]], Automatic]
```

<!-- => Failure["NoProofFound", ...] -->

No tactic of the [Automatic]() portfolio proves it, since every one of them waits for `Head[e] === Integer` to compute. The proof splits on it: [Replace]() is the first result of the matches, and a pattern's test is a [Condition]() on the Boolean, so `"Change"` writes the goal with the test showing, `"Cases"` splits on its two values, and each case computes:

```wl
order = TypeTheoryProof[ForAll[{Typed[e, Expressions]}, Replace[e, {x_Integer :> "integer", y_ :> "other"}] == If[Head[e] === Integer, "integer", "other"]], {
    "Introduce"[e],
    "Change"[InductiveRecursor[Option][Typed[o, Option[Expressions]] |-> Expressions, e, Typed[r, Expressions] |-> r,
        MatchFirst[MatchSum[Condition[MatchValue["integer"], Head[e] === Integer], MatchValue["other"]]]] == If[Head[e] === Integer, "integer", "other"]],
    "Cases"[Head[e] === Integer],
    "Reflexivity",
    "Reflexivity"
}]
```

<!-- => Proof complete -->

The proof uses no axiom: the cases of a Boolean and computation are all it needs.

```wl
TypeTheoryAxiomClosure[order]
```

<!-- => <||> -->

A Boolean where a proposition is expected, as the condition of [If](), is the proposition that it is true, which the equality of Booleans decides; the display marks it with an arrow, `If[↑(Head[e] === Integer), ...]`.

## Booleans by Cases

A statement about every Boolean is proved by its two cases. De Morgan's law for the Boolean connectives, [Not](), [And]() and [Or](), takes four:

```wl
TypeTheoryProof[ForAll[{Typed[a, Booleans], Typed[b, Booleans]}, Not[a && b] == (Not[a] || Not[b])],
    {"Introduce"[a, b], "Cases"[a], "Cases"[b], "Reflexivity", "Reflexivity", "Cases"[b], "Reflexivity", "Reflexivity"}]
```

<!-- => Proof complete -->

An [If]() whose branches are the same is its branch, whatever the condition:

```wl
TypeTheoryProof[ForAll[{Typed[c, Booleans], Typed[x, Expressions]}, If[c, x, x] == x], {"Introduce"[c, x], "Cases"[c], "Reflexivity", "Reflexivity"}]
```

<!-- => Proof complete -->

## Failures

A computation that may fail has a value of `A | Failure`, and [Enclose]() and [Confirm]() pass a failure on. `Enclose[Confirm[x]]` is `x` for every such value, a number or a [Failure](), by the cases of the sum:

```wl
TypeTheoryProof[ForAll[{Typed[x, NonNegativeIntegers | Failure]}, Enclose[Confirm[x]] == x], {"Introduce"[x], "Cases"[x], "Introduce"[n], "Reflexivity", "Introduce"[failure], "Reflexivity"}]
```

<!-- => Proof complete -->

## Decisions and SameQ

The prelude proves that a decision that is true proves its proposition, `"decideSoundness"`. The converse, that a proposition proved is decided true, is a theorem of a few lines: a decision is either a proof or a refutation, and a refutation of a proved proposition gives anything.

```wl
decisions = TypeTheoryEnvironment[{
    TypeTheoryTheorem["decideCompleteness", ForAll[{TypedImplicit[p, TypeUniverse[0]], Annotation[Typed[d, Decidable[p]], "InstanceImplicit"]}, Implies[p, Decide[p] == True]],
        TypeTheoryProof[ForAll[{TypedImplicit[p, TypeUniverse[0]], Annotation[Typed[d, Decidable[p]], "InstanceImplicit"]}, Implies[p, Decide[p] == True]],
            {"Introduce"[p, d, proof], "Cases"[d], "Introduce"[refuted], "Apply"["falseElimination"], "Exact"[refuted[proof]], "Introduce"[proved], "Reflexivity"}]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 260 constants -->

[SameQ]() compares two natural numbers by deciding their equality, so every natural number is the same as itself, by the theorem applied to the reflexivity of equality:

```wl
TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, SameQ[n, n] == True], decisions, {"Introduce"[n], "Exact"["decideCompleteness"["equalityReflexivity"[n]]]}]
```

<!-- => Proof complete -->

And two natural numbers that are [SameQ]() are equal, by `"decideSoundness"`:

```wl
TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers], Typed[m, NonNegativeIntegers]}, Implies[SameQ[n, m] == True, n == m]], decisions, {"Introduce"[n, m, same], "Exact"["decideSoundness"[same]]}]
```

<!-- => Proof complete -->

## Associations

An association compares keys by [SameQ]() of the expressions they are, so a key that is a variable is found only once its comparison with itself is known. With that fact as a hypothesis, `"RewriteRepeated"` unfolds [Lookup]() and the insertion, and the lookup of the key gives its value:

```wl
TypeTheoryProof[ForAll[{Typed[k, NonNegativeIntegers], Typed[v, Strings]}, Lookup[<|k -> v|>, k] == "left"[v]], decisions, {
    "Introduce"[k, v],
    "Have"[same, SameQ["quote"[k], "quote"[k]] == True],
    "Exact"["decideCompleteness"["equalityReflexivity"[k]]],
    "RewriteRepeated"["associationLookup", "associationInsert", same]
}]
```

<!-- => Proof complete -->

## The Rules of a Symbol

[TypeTheoryFormalize]() reads the rules of a function, its [DownValues](), as a definition: the first rule that matches, as the Wolfram Language tries them, or none:

```wl
paired[x_, y_] := {y, x};
paired[x_] := {x};
pairing = TypeTheoryEnvironment[TypeTheoryFormalize[paired, "Meaning" -> "Rules"]]
```

<!-- => TypeTheoryEnvironment summary box: 260 constants -->

Which rule applies is then a theorem about every call of that shape. Two arguments take the first rule:

```wl
TypeTheoryProof[ForAll[{Typed[a, Expressions], Typed[b, Expressions]}, "DownValues[paired]"[paired[a, b]] == "some"[{b, a}]], pairing, {"Introduce"[a, b], "Reflexivity"}]
```

<!-- => Proof complete -->

and three arguments match no rule, so `paired[a, b, c]` stays as it is:

```wl
TypeTheoryProof[ForAll[{Typed[a, Expressions], Typed[b, Expressions], Typed[c, Expressions]}, "DownValues[paired]"[paired[a, b, c]] == Typed["none", Option[Expressions]]], pairing, {"Introduce"[a, b, c], "Reflexivity"}]
```

<!-- => Proof complete -->

## Where the Tactics Stop

A statement is written inside [TypeTheoryProof](), which holds it. Outside, the Wolfram Language evaluates it first: `e` is a symbol, so its head is [Symbol]() and the test is already `False`:

```wl
Head[e] === Integer
```

<!-- => False -->

A false statement is not proved. [ReplaceAll]() rewrites inside `a` as well, so where `a` is itself `g[c]`, the result is not `f[a, a]`:

```wl
TypeTheoryProof[ForAll[{Typed[a, Expressions]}, ReplaceAll[f[a, g[a]], g[y_] :> y] == f[a, a]], Automatic]
```

<!-- => Failure["NoProofFound", ...] -->

An expression is an atom or an application whose arguments are a sequence of expressions, two types defined together, and `"Cases"` and `"Induction"` do not split such a type yet, so a statement about every expression that needs its two forms is out of their reach for now:

```wl
TypeTheoryProof[ForAll[{Typed[e, Expressions]}, Implies[AtomQ[e] == False, Construct[Head[e], Arguments[e]] == e]], {"Introduce"[e], "Cases"[e]}]
```

<!-- => Failure["MutualInduction", ...] -->
