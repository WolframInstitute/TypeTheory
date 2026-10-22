---
Template: TechNote
Name: RulesAndComputation
Title: Rules and Computation
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/tutorial/RulesAndComputation
Keywords: [rules, computation, axiom, rewrite rule, definitional equality, Prop, proof irrelevance, quotient, Martin-Löf, calculus of inductive constructions]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TypeTheoryIntroduction, HomotopyTypeTheory, ThePrelude]
---

A type theory has two parts. Its rules say what the kernel allows and what it computes; its declarations say what an environment assumes. [TypeTheoryRules]() holds the rules as a value, and every [TypeTheoryEnvironment]() carries the rules it was started with. This tutorial shows how each kind of constant computes, what the rules change, and how a [TypeTheoryRewriteRule]() makes an axiom compute, as some axioms do in Lean's kernel and in homotopy type theory.

## Rules and Declarations

The prelude follows the calculus of inductive constructions, the rules of Lean's kernel:

```wl
Information[TypeTheoryEnvironment[], "Rules"]["Name"]
```

<!-- => "CalculusOfInductiveConstructions" -->

Those rules have a universe of propositions, Prop, and no rewrite rules:

```wl
{TypeTheoryRules["CalculusOfInductiveConstructions"]["Prop"], TypeTheoryRules["CalculusOfInductiveConstructions"]["RewriteRules"]}
```

<!-- => {True, False} -->

Martin-Löf type theory has no Prop:

```wl
TypeTheoryRules["MartinLofTypeTheory"]["Prop"]
```

<!-- => False -->

## How Constants Compute

Under any rules, a definition unfolds to its value. Here is the prelude with a definition:

```wl
double = TypeTheoryEnvironment[{TypeTheoryDefinition[Double, Function[{Typed[n, Naturals]}, n + n]]}]
```

<!-- => TypeTheoryEnvironment summary box: 165 constants -->

`Double[4]` unfolds and computes:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Double[4], double]]
```

<!-- => 8 -->

A recursor applied to a constructor takes the case for that constructor, here the second case, for `true`:

```wl
WeakHeadNormalForm[TypeTheoryTerm[InductiveRecursor[Booleans][Function[{Typed[b, Booleans]}, Naturals], 0, 1, True]]]
```

<!-- => 1 -->

The arithmetic of the natural numbers computes on literals with the Wolfram Language's own integers, as Lean's kernel computes on its literals with GMP. [TypeTheoryNaturalNumbers]() registers the operations, which the kernel trusts:

```wl
WeakHeadNormalForm[TypeTheoryTerm[123456789 * 987654321 + 2^64]]
```

<!-- => 18568676704822186885 -->

An axiom never unfolds: it has no value.

```wl
mystery = TypeTheoryEnvironment[{TypeTheoryAxiom[Mystery, Naturals]}]
```

<!-- => TypeTheoryEnvironment summary box: 165 constants -->

Addition recurses on its second argument, so `Mystery + 0` computes, but `0 + Mystery` stops at the recursor, waiting for a constructor the axiom never gives:

```wl
{WeakHeadNormalForm[TypeTheoryTerm[Mystery + 0, mystery]], WeakHeadNormalForm[TypeTheoryTerm[0 + Mystery, mystery]]}
```

<!-- => {Mystery, ℕ_rec[(t∶ℕ) ↦ ℕ, 0, (k∶ℕ) (r∶ℕ) ↦ r + 1, Mystery]} -->

A theorem never unfolds either: what it states is all that is used of it.

## What Prop Changes

With Prop, any two proofs of a proposition are equal by computation, so reflexivity proves them equal:

```wl
TypeTheoryCheck[
    TypeTheoryTerm[Function[{Typed[p, 2 + 2 == 4], Typed[q, 2 + 2 == 4]}, EqualityReflexivity[p]]],
    TypeTheoryTerm[ForAll[{Typed[p, 2 + 2 == 4], Typed[q, 2 + 2 == 4]}, p == q]]
]
```

<!-- => Success["TypeChecked", ...] -->

The HoTT environment follows Martin-Löf type theory:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

There, two paths from the base point of the circle to itself are not equal by computation:

```wl
TypeTheoryCheck[
    TypeTheoryTerm[Function[{Typed[p, CircleBase == CircleBase], Typed[q, CircleBase == CircleBase]}, EqualityReflexivity[p]], hott],
    TypeTheoryTerm[ForAll[{Typed[p, CircleBase == CircleBase], Typed[q, CircleBase == CircleBase]}, p == q], hott]
]
```

<!-- => Failure["TypeMismatch", ...] -->

Prop is also impredicative: a statement about every proposition is a proposition.

```wl
TypeTheoryCheck[TypeTheoryTerm[ForAll[{Typed[p, TypeUniverse[0]]}, p]]]
```

<!-- => Prop -->

Without Prop every universe is predicative, and a statement about every type lives in a higher universe:

```wl
TypeTheoryCheck[TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[1]]}, A], hott]]
```

<!-- => Type 1 -->

Proof irrelevance, with an equality in Prop eliminating into any type, is what makes univalence contradict the prelude's rules, as the tutorial *Homotopy Type Theory* shows.

## Axioms That Compute

Lean's kernel has quotient types built in. Their constructor and lift are constants with no definition, and the kernel adds one computation rule: lifting a function to the quotient and applying it to a class gives the function's value. In TypeTheory the quotient is declared with axioms, and the rule with a [TypeTheoryRewriteRule](), which needs rules that allow rewrite rules.

The axioms, as Lean states them:

```wl
quotientDeclarations = {
    TypeTheoryAxiom[QuotientType, ForAll[{TypedImplicit[A, TypeUniverse[u]], Typed[r, TypeSpecifier[{A, A} -> TypeUniverse[0]]]}, TypeUniverse[u]]],
    TypeTheoryAxiom[QuotientClass, ForAll[{TypedImplicit[A, TypeUniverse[u]], Typed[r, TypeSpecifier[{A, A} -> TypeUniverse[0]]], Typed[a, A]}, QuotientType[r]]],
    TypeTheoryAxiom[QuotientLift, ForAll[
        {TypedImplicit[A, TypeUniverse[u]], TypedImplicit[r, TypeSpecifier[{A, A} -> TypeUniverse[0]]], TypedImplicit[B, TypeUniverse[v]],
            Typed[f, TypeSpecifier[{A} -> B]], Typed[h, ForAll[{Typed[a, A], Typed[b, A]}, Implies[r[a, b], f[a] == f[b]]]], Typed[q, QuotientType[r]]},
        B
    ]],
    TypeTheoryAxiom[QuotientSound, ForAll[
        {TypedImplicit[A, TypeUniverse[u]], TypedImplicit[r, TypeSpecifier[{A, A} -> TypeUniverse[0]]], TypedImplicit[a, A], TypedImplicit[b, A]},
        Implies[r[a, b], QuotientClass[r, a] == QuotientClass[r, b]]
    ]]
};
```

The computation rule:

```wl
liftClass = TypeTheoryRewriteRule[QuotientLiftClass, ForAll[
    {Typed[A, TypeUniverse[u]], Typed[r, TypeSpecifier[{A, A} -> TypeUniverse[0]]], Typed[B, TypeUniverse[v]],
        Typed[f, TypeSpecifier[{A} -> B]], Typed[h, ForAll[{Typed[a, A], Typed[b, A]}, Implies[r[a, b], f[a] == f[b]]]], Typed[a, A]},
    QuotientLift[f, h, QuotientClass[r, a]] -> f[a]
]];
```

The prelude's rules allow no rewrite rules, so the declarations of the prelude, read back with [Normal](), rebuild it under the same rules with rewrite rules allowed:

```wl
rewriting = TypeTheoryEnvironment[TypeTheoryRules["CalculusOfInductiveConstructions", "RewriteRules" -> True], Normal[TypeTheoryEnvironment["Prelude"]]]
```

<!-- => TypeTheoryEnvironment summary box: 164 constants -->

There the quotient is declared with its rule:

```wl
quotient = TypeTheoryEnvironment[rewriting, Append[quotientDeclarations, liftClass]]
```

<!-- => TypeTheoryEnvironment summary box: 169 constants -->

The rule, as declared:

```wl
quotient[QuotientLiftClass]
```

<!-- => rewrite QuotientLiftClass : ∀_A∶Sort u ∀_r∶A → A → Prop ∀_B∶Sort v ∀_f∶A → B ∀_h∶∀_a∶A ∀_b∶A r[a, b] ⇒ f[a] == f[b] ∀_a∶A QuotientLift[f, h, QuotientClass[r, a]] ⟶ f[a] -->

Negation respects equality of Booleans, so it lifts to the quotient by equality. The relation:

```wl
same = TypeTheoryTerm[Function[{Typed[a, Booleans], Typed[b, Booleans]}, a == b], quotient]
```

<!-- => (a∶𝔹) (b∶𝔹) ↦ a == b -->

And the proof that negation respects it:

```wl
respects = TypeTheoryTerm[Function[{Typed[a, Booleans], Typed[b, Booleans], Typed[e, a == b]}, EqualityCongruence[Not, e]], quotient]
```

<!-- => (a∶𝔹) (b∶𝔹) (e∶a == b) ↦ EqualityCongruence[Not, e] -->

On a class the lift computes. [Not]() and [True]() stand for the Booleans' negation and truth here, since the types say so:

```wl
WeakHeadNormalForm[TypeTheoryTerm[QuotientLift[Not, respects, QuotientClass[same, True]], quotient]]
```

<!-- => false -->

The same axioms on the prelude, with no rule, declare the quotient as well:

```wl
stuck = TypeTheoryEnvironment[quotientDeclarations]
```

<!-- => TypeTheoryEnvironment summary box: 168 constants -->

But the lift is stuck:

```wl
WeakHeadNormalForm[TypeTheoryTerm[QuotientLift[Not, respects, QuotientClass[same, True]], stuck]]
```

<!-- => QuotientLift[not, (a∶𝔹) (b∶𝔹) (e∶a == b) ↦ EqualityCongruence[not, e], QuotientClass[(a∶𝔹) (b∶𝔹) ↦ a == b, true]] -->

And the prelude's rules refuse the rule:

```wl
TypeTheoryEnvironment[Append[quotientDeclarations, liftClass]]
```

<!-- => Failure["RewriteRulesNotAllowed", ...] -->

## Computation Up to a Path

A computation rule that is an axiom, an equation the kernel does not use by itself, holds only up to a proof: a term that needs it to have its type does not check. Homotopy type theory has both kinds. Induction on the circle computes on its base point by a rewrite rule, and on its loop only up to a path, by the axiom [CircleInductionLoop]():

```wl
Information[hott, "RewriteRules"]
```

<!-- => {CircleInductionBase} -->

Univalence is an axiom too, and what carrying along the path of an equivalence gives is the theorem [UnivalenceComputation](), not a computation. Cubical type theory makes it one, with rules that TypeTheory does not have yet.

## Rewrite Rules Are Trusted

A rewrite rule is assumed, like an axiom, and the kernel does not check that rules agree with each other. Here two rules for `Flip` overlap: on `BitZero`, the first gives `BitOne`, while the second makes `Flip` the identity:

```wl
flips = TypeTheoryEnvironment[rewriting, {
    TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}],
    TypeTheoryAxiom[Flip, TypeSpecifier[{Bit} -> Bit]],
    TypeTheoryRewriteRule[FlipZero, Flip[BitZero] -> BitOne],
    TypeTheoryRewriteRule[FlipAny, ForAll[{Typed[b, Bit]}, Flip[b] -> b]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 171 constants -->

By the first rule, `Flip[BitZero]` computes to `BitOne`:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Flip[BitZero], flips]]
```

<!-- => BitOne -->

By the second, `Flip` is the identity:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Function[{Typed[b, Bit]}, Flip[b]], flips], TypeTheoryTerm[Function[{Typed[b, Bit]}, b], flips]]
```

<!-- => True -->

So the kernel accepts a proof that two different constructors are equal, from which anything follows:

```wl
confused = TypeTheoryEnvironment[flips, {TypeTheoryTheorem[
    Confusion,
    BitOne == BitZero,
    EqualityCongruence[
        Function[{Typed[g, TypeSpecifier[{Bit} -> Bit]]}, g[BitZero]],
        Typed[EqualityReflexivity[Function[{Typed[b, Bit]}, b]], Function[{Typed[b, Bit]}, Flip[b]] == Function[{Typed[b, Bit]}, b]]
    ]
]}]
```

<!-- => TypeTheoryEnvironment summary box: 172 constants -->

The theorem it declares:

```wl
confused[Confusion]
```

<!-- => theorem Confusion : BitOne == BitZero -->

Rules that do not overlap and always terminate, such as the quotient's and the circle's, keep the theory consistent, as long as the axioms they compute with are consistent.

## Summary

| | The prelude's rules | The same with rewrite rules allowed | Martin-Löf rules, as in the HoTT environment | Lean's kernel |
| --- | --- | --- | --- | --- |
| a definition, a recursor on a constructor | computes | computes | computes | computes |
| two proofs of a proposition | equal by computation | equal by computation | no Prop: two paths need not be equal | equal by computation |
| an axiom | stuck | computes by its rewrite rules | computes by its rewrite rules, where the rules allow them | stuck, except the quotient's built-in rule |
