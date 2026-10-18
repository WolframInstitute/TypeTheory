---
Template: TechNote
Name: HomotopyTypeTheory
Title: Homotopy Type Theory
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/tutorial/HomotopyTypeTheory
Keywords: [HoTT, homotopy type theory, univalence, paths, equivalence, circle, higher inductive type, rewrite rules, Martin-Löf, rules]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TypeTheoryIntroduction, RulesAndComputation, ThePrelude]
---

<code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code> is homotopy type theory as the HoTT book presents it: an equality is a path, equivalent types are equal by univalence, and the circle is a higher inductive type. It follows other rules than the prelude, given by [TypeTheoryRules](). This tutorial says why, and then goes through the environment.

## The Rules

The HoTT environment follows Martin-Löf type theory, with rewrite rules allowed:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"];
Information[hott, "Rules"]["Name"]
```

<!-- => "MartinLofTypeTheory" -->

Those rules have no Prop:

```wl
Information[hott, "Rules"]["Prop"]
```

<!-- => False -->

The prelude's rules have a universe of propositions in which any two proofs of a proposition are equal, and a proposition with one proof, such as an equality, eliminates into any type. Univalence contradicts that. A path maps into an equality in Prop, so carrying an element along a path agrees with carrying it along a proof of that equality, which leaves it where it is; univalence makes carrying along the path of an equivalence apply that equivalence, which may move it. So the HoTT rules refuse an equality in Prop:

```wl
TypeTheoryEnvironment[hott, {TypeTheoryInductiveType[
    StrictEqual,
    ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[x, A], Typed[y, A]}, TypeUniverse[0]],
    {StrictEqualReflexivity -> ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[x, A]}, StrictEqual[x, x]]}
]}]
```

<!-- => Failure["NoProp", ...] -->

Without Prop, every universe is `Type u`, written <code>[TypeUniverse]()[u + 1]</code>, and a theorem may state any type.

## Propositions as Types

[True](), [False]() and [Not]() are types here: [True]() has the one element [TrueIntroduction](), [False]() has none, and <code>[Not]()[*a*]</code> is a function into [False](). From [False](), anything follows:

```wl
TypeTheoryCheck[TypeTheoryTerm[FalseElimination, hott]]
```

<!-- => ∀_{a ∶ Type u} False → a -->

As in the prelude, [True](), [False]() and [Not]() also stand for the Booleans where a Boolean is expected.

## Paths

[Equal]() is the type of paths: `x == y` has an element for each path from `x` to `y`, and lives in a universe of types:

```wl
TypeTheoryCheck[TypeTheoryTerm[Equal, hott]]
```

<!-- => ∀_{A ∶ Type u} A → A → Type u -->

Its recursor is path induction: to prove something of every path from `x`, it is enough to prove it of reflexivity.

```wl
TypeTheoryCheck[TypeTheoryTerm[InductiveRecursor[Equal], hott]]
```

<!-- => ∀_{A ∶ Type u} ∀_{x ∶ A} ∀_m∶∀_y∶A x == y → Type v m[x, EqualityReflexivity[x]] → ∀_{y ∶ A} ∀_t∶x == y m[y, t] -->

The inverse, concatenation and congruence of paths, [EqualitySymmetry](), [EqualityTransitivity]() and [EqualityCongruence](), are definitions by path induction, and so are [Transport]() and [DependentCongruence](). They compute on reflexivity: carrying an element along reflexivity leaves it as it is.

```wl
WeakHeadNormalForm[TypeTheoryTerm[Transport[Function[{Typed[b, Booleans]}, Booleans], EqualityReflexivity[True], False], hott]]
```

<!-- => false -->

## Equivalences and Univalence

An equivalence is a function with a left inverse and a right inverse, each with its path: [IsEquivalence]() and [Equivalence](). Negation is one, from the Booleans to themselves:

```wl
TypeOf[TypeTheoryTerm[NegationEquivalence, hott]]
```

<!-- => Equivalence[𝔹, 𝔹] -->

A path between types gives an equivalence, [EqualityToEquivalence](), with the identity for reflexivity. [Univalence]() is the axiom that this map is itself an equivalence:

```wl
TypeTheoryCheck[TypeTheoryTerm[Univalence, hott]]
```

<!-- => ∀_A∶Type u ∀_B∶Type u IsEquivalence[(p∶A == B) ↦ EqualityToEquivalence[p]] -->

Its right inverse, [EquivalenceToEquality](), gives a path for each equivalence, and [UnivalenceComputation]() says that carrying along that path is the equivalence:

```wl
TypeTheoryCheck[TypeTheoryTerm[UnivalenceComputation, hott]]
```

<!-- => ∀_{A ∶ Type u} ∀_{B ∶ Type u} ∀_e∶Equivalence[A, B] EqualityToEquivalence[EquivalenceToEquality[e]] == e -->

## The Universe Is Not a Set

A type is a set when any two paths between the same elements are equal, [IsSet](). Under the prelude's rules every type is one. Here the universe is not:

```wl
TypeTheoryCheck[TypeTheoryTerm[UniverseNotSet, hott]]
```

<!-- => ¬IsSet[Type] -->

The proof is the HoTT book's. If any two paths between types were equal, the path that negation gives through univalence would be reflexivity, so carrying `true` along it would give `true`. By [UnivalenceComputation]() it gives what negation does, `false`, and a path from `false` to `true` carries the element of [True]() to an element of [False]().

## The Circle

The circle is a higher inductive type: a point [CircleBase](), a path [CircleLoop]() from it to itself, and an induction principle, [CircleInduction](). All three are axioms. The HoTT book makes induction compute on the point, which an axiom cannot do, so the rewrite rule [CircleInductionBase]() does it:

```wl
hott[CircleInductionBase]
```

<!-- => rewrite CircleInductionBase : ∀_P∶𝕊¹ → Type u ∀_b∶P[CircleBase] ∀_l∶Transport[P, CircleLoop, b] == b CircleInduction[P, b, l, CircleBase] ⟶ b -->

So induction on the base point computes:

```wl
WeakHeadNormalForm[TypeTheoryTerm[CircleInduction[Function[{Typed[x, Circle]}, Booleans], True, TransportConstant[CircleLoop, True], CircleBase], hott]]
```

<!-- => true -->

On the loop, induction gives its path only up to a path, by the axiom [CircleInductionLoop](). Its two sides are paths between `CircleInduction[P, b, l, CircleBase]` and `b`, so the statement type-checks only because the rewrite rule computes:

```wl
TypeTheoryCheck[TypeTheoryTerm[CircleInductionLoop, hott]]
```

<!-- => ∀_P∶𝕊¹ → Type u ∀_b∶P[CircleBase] ∀_l∶Transport[P, CircleLoop, b] == b DependentCongruence[(x∶𝕊¹) ↦ CircleInduction[P, b, l, x], CircleLoop] == l -->

## Rules of Your Own

The rules are a value, and <code>[TypeTheoryEnvironment]()[*rules*]</code> starts an environment with no constants that follows them. These are the rules of the HoTT environment:

```wl
TypeTheoryEnvironment[TypeTheoryRules["MartinLofTypeTheory", "RewriteRules" -> True]] === TypeTheoryEnvironment[Information[hott, "Rules"]]
```

<!-- => True -->

Declarations then build a theory of one's own on them, with [TypeTheoryRewriteRule]() for computation that an axiom alone does not have.

## What It Does Not Have Yet

Univalence is an axiom here, so a path it gives does not compute; cubical type theory, where it does, needs a kernel of its own. Higher inductive types come one at a time, as axioms with rewrite rules, and truncations and quotients are not here yet.
