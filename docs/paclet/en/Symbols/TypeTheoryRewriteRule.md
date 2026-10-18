---
Template: Symbol
Name: TypeTheoryRewriteRule
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryRewriteRule
Keywords: [rewrite rule, computation, axiom, definitional equality, higher inductive type]
SeeAlso: [TypeTheoryRules, TypeTheoryAxiom, TypeTheoryEnvironment, CircleInductionBase]
RelatedGuides: [TypeTheory]
RelatedTutorials: [RulesAndComputation, HomotopyTypeTheory]
---

## Usage

<code>[TypeTheoryRewriteRule]()[*name*, [ForAll]()[{[Typed]()[*x*, *A*], ...}, *lhs* -> *rhs*]]</code> declares that *lhs* computes to *rhs* for every *x*, ..., when added to a [TypeTheoryEnvironment]() whose rules allow rewrite rules.

<code>[TypeTheoryRewriteRule]()[*name*, *lhs* -> *rhs*]</code> declares a rule without variables.

## Details & Options

- *lhs* must be an axiom applied to arguments, each a variable of the rule, a term without the rule's variables, or a constant applied to such arguments. Every variable occurs in *lhs*, and every universe parameter is a universe level of the axiom. *rhs* must have the type of *lhs*.
- An axiom whose arguments match the left side of one of its rules reduces to the right side, the first rule that matches first; definitional equality then uses the rule too.
- Like an axiom, a rewrite rule is trusted: rules that overlap or loop can make the theory inconsistent or computation endless. <code>[Information]()[*env*, "RewriteRules"]</code> lists them, and [TypeTheoryCheck]() replays them like any declaration.
- A rewrite rule is not a term, and its name cannot be used as one.
- Rewrite rules need rules with `"RewriteRules" -> True`, as <code>[TypeTheoryRules]()["MartinLofTypeTheory", "RewriteRules" -> True]</code>. In the HoTT environment, [CircleInductionBase]() makes circle induction compute on the base point.
- The option `"UniverseParameters" -> {u, ...}` lists the universe parameters.

## Basic Examples

An axiom that computes:

```wl
bits = TypeTheoryEnvironment[TypeTheoryRules["MartinLofTypeTheory", "RewriteRules" -> True], {
    TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}],
    TypeTheoryAxiom[Flip, TypeSpecifier[{Bit} -> Bit]],
    TypeTheoryRewriteRule[FlipZero, Flip[BitZero] -> BitOne],
    TypeTheoryRewriteRule[FlipOne, Flip[BitOne] -> BitZero]
}];
WeakHeadNormalForm[TypeTheoryTerm[Flip[Flip[BitZero]], bits]]
```

<!-- => BitZero -->

## Scope

A rule with variables:

```wl
bits = TypeTheoryEnvironment[TypeTheoryRules["MartinLofTypeTheory", "RewriteRules" -> True], {
    TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}],
    TypeTheoryAxiom[Flip, TypeSpecifier[{Bit} -> Bit]],
    TypeTheoryRewriteRule[FlipZero, Flip[BitZero] -> BitOne],
    TypeTheoryRewriteRule[FlipOne, Flip[BitOne] -> BitZero]
}];
twice = TypeTheoryEnvironment[bits, {
    TypeTheoryAxiom[Twice, TypeSpecifier[{TypeSpecifier[{Bit} -> Bit], Bit} -> Bit]],
    TypeTheoryRewriteRule[TwiceRule, ForAll[{Typed[h, TypeSpecifier[{Bit} -> Bit]], Typed[x, Bit]}, Twice[h, x] -> h[h[x]]]]
}];
WeakHeadNormalForm[TypeTheoryTerm[Twice[Flip, BitOne], twice]]
```

<!-- => BitOne -->

An axiom applied to a variable matches no rule, and stays:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Function[{Typed[b, Bit]}, Flip[b]], twice]]
```

<!-- => (b∶Bit) ↦ Flip[b] -->

## Properties and Relations

The rewrite rules of an environment:

```wl
bits = TypeTheoryEnvironment[TypeTheoryRules["MartinLofTypeTheory", "RewriteRules" -> True], {
    TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}],
    TypeTheoryAxiom[Flip, TypeSpecifier[{Bit} -> Bit]],
    TypeTheoryRewriteRule[FlipZero, Flip[BitZero] -> BitOne],
    TypeTheoryRewriteRule[FlipOne, Flip[BitOne] -> BitZero]
}];
Information[bits, "RewriteRules"]
```

<!-- => {FlipZero, FlipOne} -->

The declaration of one:

```wl
bits[FlipZero]
```

<!-- => rewrite FlipZero : Flip[BitZero] ⟶ BitOne -->

## Possible Issues

The rules of the prelude do not allow rewrite rules:

```wl
TypeTheoryEnvironment[{TypeTheoryAxiom[Mystery, Naturals], TypeTheoryRewriteRule[MysteryZero, Mystery -> 0]}]
```

<!-- => Failure["RewriteRulesNotAllowed", ...] -->

---

The left side must be an axiom applied to arguments:

```wl
bits = TypeTheoryEnvironment[TypeTheoryRules["MartinLofTypeTheory", "RewriteRules" -> True], {
    TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}],
    TypeTheoryAxiom[Flip, TypeSpecifier[{Bit} -> Bit]],
    TypeTheoryRewriteRule[FlipZero, Flip[BitZero] -> BitOne],
    TypeTheoryRewriteRule[FlipOne, Flip[BitOne] -> BitZero]
}];
TypeTheoryEnvironment[bits, {TypeTheoryRewriteRule[ZeroOne, BitZero -> BitOne]}]
```

<!-- => Failure["RewriteRuleHead", ...] -->

A rewrite rule is not a term:

```wl
TypeTheoryCheck[TypeTheoryTerm[FlipZero, bits]]
```

<!-- => Failure["ElaborationFailed", ...] -->
