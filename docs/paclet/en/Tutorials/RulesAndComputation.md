---
Template: TechNote
Name: RulesAndComputation
Title: Rules and Computation
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/tutorial/RulesAndComputation
Keywords: [rules, computation, axiom, rewrite rule, definitional equality, Prop, proof irrelevance, quotient, Martin-Löf, calculus of inductive constructions]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TypeTheoryIntroduction, Paradoxes, HomotopyTypeTheory, ThePrelude]
---

A type theory has two parts. Its rules say what the kernel allows and what it computes; its declarations say what an environment assumes. [TypeTheoryRules]() holds the rules as a value, and every [TypeTheoryEnvironment]() carries the rules it was started with. This tutorial shows how each kind of constant computes, what the rules change, and how a [TypeTheoryRewriteRule]() makes an axiom compute, as the lift of a quotient does and as paths do in homotopy type theory.

## Rules and Declarations

The prelude follows the calculus of inductive constructions:

```wl
Information[TypeTheoryEnvironment[], "Rules"]["Name"]
```

<!-- => "CalculusOfInductiveConstructions" -->

Those rules have a universe of propositions, Prop, quotient types, no rewrite rules and no quantities:

```wl
TypeTheoryRules["CalculusOfInductiveConstructions"] /@ {"Prop", "Quotients", "RewriteRules", "Quantities", "Cubical"}
```

<!-- => {True, True, False, False, False} -->

Without quotient types, they are the rules of Rocq's kernel. With quantities, a binder may say that the code that runs uses its variable at most once, or never; the tutorial *Erased and Affine Variables* has them. Cubical rules have the interval and paths of cubical type theory, in which univalence computes; the tutorial *Cubical Type Theory* has them.

Martin-Löf type theory has no Prop:

```wl
TypeTheoryRules["MartinLofTypeTheory"]["Prop"]
```

<!-- => False -->

## How Constants Compute

Under any rules, a definition unfolds to its value. Here is the prelude with a definition:

```wl
double = TypeTheoryEnvironment[{TypeTheoryDefinition[Double, n |-> n + n]}]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

`Double[4]` unfolds and computes:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Double[4], double]]
```

<!-- => 8 -->

A recursor applied to a constructor takes the case for that constructor, here the second case, for `true`:

```wl
WeakHeadNormalForm[TypeTheoryTerm[InductiveRecursor[Booleans][Naturals &, 0, 1, True]]]
```

<!-- => 1 -->

The arithmetic of the natural numbers computes on literals with the Wolfram Language's own integers. [TypeTheoryNaturalNumbers]() registers the operations, which the kernel trusts:

```wl
WeakHeadNormalForm[TypeTheoryTerm[123456789 * 987654321 + 2^64]]
```

<!-- => 18568676704822186885 -->

The quotient types compute too: lifting a function to the classes of a relation and applying the lift to a class gives the function's value. Here the classes are those of the relation that relates any two numbers, and the constant function 7 respects it:

```wl
WeakHeadNormalForm[TypeTheoryTerm[QuotientLift[
    7 &,
    {a, b, e} |-> "equalityReflexivity"[7],
    QuotientIntroduction[True &, 5]
]]]
```

<!-- => 7 -->

An axiom never unfolds: it has no value.

```wl
mystery = TypeTheoryEnvironment[{TypeTheoryAxiom[Mystery, Naturals]}]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

Addition recurses on its second argument, so `Mystery + 0` computes, but `0 + Mystery` stays as it is, waiting for a constructor the axiom never gives. The kernel reduces the addition by its two defining equations, `t + 0 == t` and `t + (s + 1) == (t + s) + 1`, so a stuck sum stays a sum rather than unfolding into its recursor:

```wl
{WeakHeadNormalForm[TypeTheoryTerm[Mystery + 0, mystery]], WeakHeadNormalForm[TypeTheoryTerm[0 + Mystery, mystery]]}
```

<!-- => {Mystery, 0 + Mystery} -->

A theorem never unfolds either: what it states is all that is used of it.

## What Prop Changes

With Prop, any two proofs of a proposition are equal by computation, so reflexivity proves them equal:

```wl
TypeTheoryCheck[
    TypeTheoryTerm[{p, q} |-> "equalityReflexivity"[p]],
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
    TypeTheoryTerm[{p, q} |-> "equalityReflexivity"[p], hott],
    TypeTheoryTerm[ForAll[{Typed[p, "circleBase" == "circleBase"], Typed[q, "circleBase" == "circleBase"]}, p == q], hott]
]
```

<!-- => Failure["TypeMismatch", ...] -->

Prop is also impredicative: a statement about every proposition is a proposition.

```wl
TypeTheoryType[ForAll[{Typed[p, TypeUniverse[0]]}, p]]
```

<!-- => Prop -->

Without Prop every universe is predicative, and a statement about every type lives in a higher universe:

```wl
TypeTheoryType[ForAll[{Typed[A, TypeUniverse[1]]}, A], hott]
```

<!-- => Type 1 -->

As pure type systems, the two rules differ in one place. Both have a sort `Sort u` for every level `u`, the axioms `Sort u : Sort (u + 1)`, and products by the rule `(Sort u, Sort v, Sort (imax u v))`: a function type is in the larger universe of its domain and its codomain, except that one into Prop is in Prop, as [ImpredicativeMaximum]() says. Without Prop no level is 0, and `imax` is `max`. Neither rule is cumulative: a type in `Type` is not one in `Type 1`, and `Type 1` does not take the natural numbers:

```wl
TypeTheoryType[Typed[Naturals, TypeUniverse[2]]]
```

<!-- => Failure["TypeMismatch", ...] -->

Proof irrelevance, with an equality in Prop eliminating into any type, is what makes univalence contradict the prelude's rules, as the tutorial *Homotopy Type Theory* shows.

## Axioms That Compute

The kernel has quotient types built in. Their constructor and lift are constants with no definition, and the kernel adds one computation rule: lifting a function to the quotient and applying it to a class gives the function's value, as the prelude's [QuotientLift]() does above. Rules without quotient types, as Rocq's kernel has, can still have them, with axioms for the constants and a [TypeTheoryRewriteRule]() for the rule, which needs rules that allow rewrite rules.

The axioms of the quotient types, under names of their own:

```wl
quotientDeclarations = {
    TypeTheoryAxiom[Classes, ForAll[{TypedImplicit[A, TypeUniverse[u]], Typed[r, TypeSpecifier[{A, A} -> TypeUniverse[0]]]}, TypeUniverse[u]]],
    TypeTheoryAxiom[ClassOf, ForAll[{TypedImplicit[A, TypeUniverse[u]], Typed[r, TypeSpecifier[{A, A} -> TypeUniverse[0]]], Typed[a, A]}, Classes[r]]],
    TypeTheoryAxiom[ClassLift, ForAll[
        {TypedImplicit[A, TypeUniverse[u]], TypedImplicit[r, TypeSpecifier[{A, A} -> TypeUniverse[0]]], TypedImplicit[B, TypeUniverse[v]],
            Typed[f, TypeSpecifier[{A} -> B]], Typed[h, ForAll[{a, b}, Implies[r[a, b], f[a] == f[b]]]], Typed[q, Classes[r]]},
        B
    ]],
    TypeTheoryAxiom[ClassSoundness, ForAll[
        {TypedImplicit[A, TypeUniverse[u]], TypedImplicit[r, TypeSpecifier[{A, A} -> TypeUniverse[0]]], TypedImplicit[a, A], TypedImplicit[b, A]},
        Implies[r[a, b], ClassOf[r, a] == ClassOf[r, b]]
    ]]
};
```

The computation rule:

```wl
liftClass = TypeTheoryRewriteRule[ClassLiftComputes, ForAll[
    {Typed[A, TypeUniverse[u]], Typed[r, TypeSpecifier[{A, A} -> TypeUniverse[0]]], Typed[B, TypeUniverse[v]],
        Typed[f, TypeSpecifier[{A} -> B]], Typed[h, ForAll[{a, b}, Implies[r[a, b], f[a] == f[b]]]], Typed[a, A]},
    ClassLift[f, h, ClassOf[r, a]] -> f[a]
]];
```

The prelude's rules allow no rewrite rules, so the declarations of the prelude, read back with [Normal](), rebuild it under the same rules with rewrite rules allowed:

```wl
rewriting = TypeTheoryEnvironment[TypeTheoryRules["CalculusOfInductiveConstructions", "RewriteRules" -> True], Normal[TypeTheoryEnvironment["Prelude"]]]
```

<!-- => TypeTheoryEnvironment summary box: 257 constants -->

There the quotient is declared with its rule:

```wl
quotient = TypeTheoryEnvironment[rewriting, Append[quotientDeclarations, liftClass]]
```

<!-- => TypeTheoryEnvironment summary box: 262 constants -->

The rule, as declared:

```wl
quotient[ClassLiftComputes]
```

<!-- => rewrite ClassLiftComputes : ∀_A∶Sort u ∀_r∶A → A → Prop ∀_B∶Sort v ∀_f∶A → B ∀_h∶∀_a∶A ∀_b∶A r[a, b] ⇒ f[a] == f[b] ∀_a∶A ClassLift[f, h, ClassOf[r, a]] ⟶ f[a] -->

Negation respects equality of Booleans, so it lifts to the quotient by equality. The relation:

```wl
same = TypeTheoryTerm[{Typed[a, Booleans], Typed[b, Booleans]} |-> a == b, quotient]
```

<!-- => (a∶𝔹) (b∶𝔹) ↦ a == b -->

And the proof that negation respects it:

```wl
respects = TypeTheoryTerm[{Typed[a, Booleans], Typed[b, Booleans], Typed[e, a == b]} |-> "equalityCongruence"[Not, e], quotient]
```

<!-- => (a∶𝔹) (b∶𝔹) (e∶a == b) ↦ equalityCongruence[Not, e] -->

On a class the lift computes. [Not]() and [True]() stand for the Booleans' negation and truth here, since the types say so:

```wl
WeakHeadNormalForm[TypeTheoryTerm[ClassLift[Not, respects, ClassOf[same, True]], quotient]]
```

<!-- => false -->

The prelude's quotient types compute the same way without a rewrite rule, by the kernel's own rule:

```wl
WeakHeadNormalForm[TypeTheoryTerm[QuotientLift[Not, respects, QuotientIntroduction[same, True]], quotient]]
```

<!-- => false -->

The same axioms on the prelude, with no rule, declare the quotient as well:

```wl
stuck = TypeTheoryEnvironment[quotientDeclarations]
```

<!-- => TypeTheoryEnvironment summary box: 261 constants -->

But the lift is stuck:

```wl
WeakHeadNormalForm[TypeTheoryTerm[ClassLift[Not, respects, ClassOf[same, True]], stuck]]
```

<!-- => ClassLift[not, (a∶𝔹) (b∶𝔹) (e∶a == b) ↦ equalityCongruence[not, e], ClassOf[(a∶𝔹) (b∶𝔹) ↦ a == b, true]] -->

And the prelude's rules refuse the rule:

```wl
TypeTheoryEnvironment[Append[quotientDeclarations, liftClass]]
```

<!-- => Failure["RewriteRulesNotAllowed", ...] -->

## Computation Up to a Path

A computation rule that is an axiom, an equation the kernel does not use by itself, holds only up to a proof: a term that needs it to have its type does not check. Homotopy type theory has both kinds. Induction on the circle computes on its base point by a rewrite rule, and on its loop only up to a path, by the axiom `"circleInductionLoop"`:

```wl
Information[hott, "RewriteRules"]
```

<!-- => {circleInductionBase} -->

Univalence is an axiom too, and what carrying along the path of an equivalence gives is the theorem `"univalenceComputation"`, not a computation. Cubical type theory makes it one: in <code>[TypeTheoryEnvironment]()["Cubical"]</code>, transport along `"equivalenceToPath"` applies the equivalence by computation, as the tutorial *Cubical Type Theory* shows.

## Rewrite Rules Are Trusted

A rewrite rule is assumed, like an axiom, and the kernel does not check that rules agree with each other. Here two rules for `Flip` overlap: on `BitZero`, the first gives `BitOne`, while the second makes `Flip` the identity:

```wl
flips = TypeTheoryEnvironment[rewriting, {
    TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}],
    TypeTheoryAxiom[Flip, TypeSpecifier[{Bit} -> Bit]],
    TypeTheoryRewriteRule[FlipZero, Flip[BitZero] -> BitOne],
    TypeTheoryRewriteRule[FlipAny, ForAll[{b}, Flip[b] -> b]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 264 constants -->

By the first rule, `Flip[BitZero]` computes to `BitOne`:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Flip[BitZero], flips]]
```

<!-- => BitOne -->

By the second, `Flip` is the identity:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[b |-> Flip[b], flips], TypeTheoryTerm[Typed[b, Bit] |-> b, flips]]
```

<!-- => True -->

So the kernel accepts a proof that two different constructors are equal, from which anything follows:

```wl
confused = TypeTheoryEnvironment[flips, {TypeTheoryTheorem[
    Confusion,
    BitOne == BitZero,
    "equalityCongruence"[
        Function[{Typed[g, TypeSpecifier[{Bit} -> Bit]]}, g[BitZero]],
        Typed["equalityReflexivity"[b |-> b], (b |-> Flip[b]) == (b |-> b)]
    ]
]}]
```

<!-- => TypeTheoryEnvironment summary box: 265 constants -->

The theorem it declares:

```wl
confused[Confusion]
```

<!-- => theorem Confusion : BitOne == BitZero -->

Rules that do not overlap and always terminate, such as the quotient's and the circle's, keep the theory consistent, as long as the axioms they compute with are consistent.

## Translations Between Rules

[TypeTheoryTranslate]() moves the declarations of an environment to other rules, whose kernel checks each of them again, and leaves out those that do not check, with whatever mentions them. Where the rules lose Prop, Prop becomes Type, the lowest universe of types. The constructive prelude in Martin-Löf type theory:

```wl
martinLof = TypeTheoryTranslate[TypeTheoryEnvironment["Constructive"], TypeTheoryRules["MartinLofTypeTheory"]]
```

<!-- => Success["Translated", ...] -->

All of it checks there but the quotient types, which those rules do not have:

```wl
Keys[martinLof["Failures"]]
```

<!-- => {QuotientType} -->

The laws of arithmetic hold there, proved as in the prelude:

```wl
TypeTheoryType["additionCommutativity", martinLof["Environment"]]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ m + n == n + m -->

Axioms stay behind unless asked for, since an axiom about propositions need not hold of types. Propositional extensionality, kept, does not check there; if every type counted as a proposition it would be inconsistent:

```wl
First @ TypeTheoryTranslate[TypeTheoryEnvironment["Prelude"], TypeTheoryRules["MartinLofTypeTheory"], "Axioms" -> True]["Failures"]["propositionalExtensionality"]
```

<!-- => "TypeMismatch" -->

The other way, homotopy type theory, univalence and the circle included, goes to the calculus of inductive constructions with rewrite rules, where its theorems, which state types, become definitions:

```wl
TypeTheoryTranslate[TypeTheoryEnvironment["HomotopyTypeTheory"], TypeTheoryRules["CalculusOfInductiveConstructions", "RewriteRules" -> True], "Axioms" -> True]
```

<!-- => Success["Translated", ...] -->

## Summary

| | The prelude's rules | The same with rewrite rules allowed | Martin-Löf rules, as in the HoTT environment |
| --- | --- | --- | --- |
| a definition, a recursor on a constructor | computes | computes | computes |
| two proofs of a proposition | equal by computation | equal by computation | no Prop: two paths need not be equal |
| an axiom | stuck | computes by its rewrite rules | computes by its rewrite rules, where the rules allow them |
| a quotient's lift on a class | computes | computes | no quotient types |
