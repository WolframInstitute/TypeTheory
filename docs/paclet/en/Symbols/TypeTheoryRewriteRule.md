---
Template: Symbol
Name: TypeTheoryRewriteRule
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryRewriteRule
Keywords: [rewrite rule, computation, axiom, definitional equality, higher inductive type, homotopy type theory, circle, trusted, confluence]
SeeAlso: [TypeTheoryRules, TypeTheoryAxiom, TypeTheoryEnvironment, WeakHeadNormalForm, DefinitionallyEqualQ, TypeTheoryAxiomClosure]
RelatedGuides: [TypeTheory]
RelatedTutorials: [RulesAndComputation, HomotopyTypeTheory]
---

## Usage

<code>[TypeTheoryRewriteRule]()[*name*, [ForAll]()[{[Typed]()[*x*, *A*], ...}, *lhs* -> *rhs*]]</code> declares that *lhs* computes to *rhs* for every *x*, ..., when added to a [TypeTheoryEnvironment]() whose rules allow rewrite rules.

<code>[TypeTheoryRewriteRule]()[*name*, *lhs* -> *rhs*]</code> declares a rule without variables.

## Details & Options

- *lhs* must be an axiom applied to arguments, each a variable of the rule, a term without the rule's variables, or a constant applied to such arguments. Every variable occurs in *lhs*, and every universe parameter is a universe level of the axiom. *rhs* must have the type of *lhs*.
- An axiom whose arguments match the left side of one of its rules reduces to the right side, the first rule that matches first; definitional equality then uses the rule too, so an equation that the rule makes hold by computation is proved by reflexivity.
- Like an axiom, a rewrite rule is trusted: rules that overlap or loop can make the theory inconsistent or computation endless. <code>[Information]()[*env*, "RewriteRules"]</code> lists them, [TypeTheoryAxiomClosure]() lists those a term rests on, and [TypeTheoryCheck]() replays them like any declaration.
- A rewrite rule is not a term, and its name cannot be used as one.
- Rewrite rules need rules with `"RewriteRules" -> True`, as <code>[TypeTheoryRules]()["MartinLofTypeTheory", "RewriteRules" -> True]</code>, which the HoTT environment follows: <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory", {...}]</code> takes rewrite rules. There `"circleInductionBase"` makes circle induction compute on the base point.
- The option `"UniverseParameters" -> {u, ...}` lists the universe parameters.

## Basic Examples

An axiom that flips bits, and computes by two rewrite rules, in the HoTT environment:

```wl
bits = TypeTheoryEnvironment["HomotopyTypeTheory", {
    TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}],
    TypeTheoryAxiom[Flip, TypeSpecifier[{Bit} -> Bit]],
    TypeTheoryRewriteRule[FlipZero, Flip[BitZero] -> BitOne],
    TypeTheoryRewriteRule[FlipOne, Flip[BitOne] -> BitZero]
}]
```

<!-- => TypeTheoryEnvironment summary box: 48 constants -->

Flipping twice gives back the bit:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Flip[Flip[BitZero]], bits]]
```

<!-- => BitZero -->

The declaration of a rule:

```wl
bits[FlipZero]
```

<!-- => rewrite FlipZero : Flip[BitZero] ⟶ BitOne -->

---

Without rules, the axiom does not compute:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Flip[BitZero], TypeTheoryEnvironment["HomotopyTypeTheory", {
    TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}],
    TypeTheoryAxiom[Flip, TypeSpecifier[{Bit} -> Bit]]
}]]]
```

<!-- => Flip[BitZero] -->

## Scope

A rule with variables, for an axiom that applies a function twice:

```wl
twice = TypeTheoryEnvironment["HomotopyTypeTheory", {
    TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}],
    TypeTheoryAxiom[Flip, TypeSpecifier[{Bit} -> Bit]],
    TypeTheoryRewriteRule[FlipZero, Flip[BitZero] -> BitOne],
    TypeTheoryRewriteRule[FlipOne, Flip[BitOne] -> BitZero],
    TypeTheoryAxiom[Twice, TypeSpecifier[{TypeSpecifier[{Bit} -> Bit], Bit} -> Bit]],
    TypeTheoryRewriteRule[TwiceRule, ForAll[{Typed[h, TypeSpecifier[{Bit} -> Bit]], Typed[x, Bit]}, Twice[h, x] -> h[h[x]]]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 50 constants -->

The rule matches any function and bit:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Twice[Flip, BitOne], twice]]
```

<!-- => BitOne -->

Even a variable, so the two functions are equal by computation:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Typed[b, Bit] |-> Twice[Flip, b], twice], TypeTheoryTerm[Typed[b, Bit] |-> Flip[Flip[b]], twice]]
```

<!-- => True -->

The declaration of the rule, with its variables:

```wl
twice[TwiceRule]
```

<!-- => rewrite TwiceRule : ∀_h∶Bit → Bit ∀_x∶Bit Twice[h, x] ⟶ h[h[x]] -->

---

Bits, with an axiom that flips them by two rewrite rules:

```wl
bits = TypeTheoryEnvironment["HomotopyTypeTheory", {
    TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}],
    TypeTheoryAxiom[Flip, TypeSpecifier[{Bit} -> Bit]],
    TypeTheoryRewriteRule[FlipZero, Flip[BitZero] -> BitOne],
    TypeTheoryRewriteRule[FlipOne, Flip[BitOne] -> BitZero]
}]
```

<!-- => TypeTheoryEnvironment summary box: 48 constants -->

An equation that the rules make hold by computation is proved by reflexivity, here for each bit:

```wl
TypeTheoryProof[ForAll[{Typed[b, Bit]}, Flip[Flip[b]] == b], bits, {"Introduce"[b], "Induction"[b], "Reflexivity", "Reflexivity"}]
```

<!-- => Proof complete -->

---

A rule for a universe-polymorphic axiom, whose type is a variable of the rule:

```wl
wrapped = TypeTheoryEnvironment["HomotopyTypeTheory", {
    TypeTheoryAxiom[Wrap, ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, TypeSpecifier[{A} -> A]]],
    TypeTheoryRewriteRule[WrapRule, ForAll[{Typed[A, TypeUniverse[u + 1]], Typed[x, A]}, Wrap[x] -> x]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 43 constants -->

It computes at every type, here the Booleans:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Wrap["true"], wrapped]]
```

<!-- => true -->

---

The rule of the HoTT environment that makes induction on the circle compute on its base point:

```wl
TypeTheoryEnvironment["HomotopyTypeTheory"]["circleInductionBase"]
```

<!-- => rewrite circleInductionBase : ∀_P∶𝕊¹ → Type u ∀_b∶P[circleBase] ∀_l∶Transport[P, circleLoop, b] == b circleInduction[P, b, l, circleBase] ⟶ b -->

So induction on the base point computes:

```wl
WeakHeadNormalForm[TypeTheoryTerm["circleInduction"[Typed[x, Circle] |-> Booleans, True, "transportConstant"["circleLoop", True], "circleBase"], "HomotopyTypeTheory"]]
```

<!-- => true -->

---

The prelude's own rules with rewrite rules allowed, the prelude's declarations rebuilt under them:

```wl
rewriting = TypeTheoryEnvironment[TypeTheoryRules["CalculusOfInductiveConstructions", "RewriteRules" -> True], Normal[TypeTheoryEnvironment["Prelude"]]]
```

<!-- => TypeTheoryEnvironment summary box: 169 constants -->

There an axiom on the natural numbers may compute:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Mystery + 1, TypeTheoryEnvironment[rewriting, {
    TypeTheoryAxiom[Mystery, Naturals],
    TypeTheoryRewriteRule[MysteryValue, Mystery -> 41]
}]]]
```

<!-- => 42 -->

## Applications

Addition as an axiom that computes by rewrite rules, on the second argument, as a recursor does:

```wl
adding = TypeTheoryEnvironment["HomotopyTypeTheory", {
    TypeTheoryInductiveType[Unary, TypeUniverse[1], {UnaryZero -> Unary, UnarySuccessor -> ForAll[{Typed[n, Unary]}, Unary]}],
    TypeTheoryAxiom[UnaryAddition, TypeSpecifier[{Unary, Unary} -> Unary]],
    TypeTheoryRewriteRule[AdditionZero, ForAll[{Typed[m, Unary]}, UnaryAddition[m, UnaryZero] -> m]],
    TypeTheoryRewriteRule[AdditionSuccessor, ForAll[{Typed[m, Unary], Typed[n, Unary]}, UnaryAddition[m, UnarySuccessor[n]] -> UnarySuccessor[UnaryAddition[m, n]]]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 48 constants -->

One and two make three:

```wl
NormalForm[TypeTheoryTerm[UnaryAddition[UnarySuccessor[UnaryZero], UnarySuccessor[UnarySuccessor[UnaryZero]]], adding]]
```

<!-- => UnarySuccessor[UnarySuccessor[UnarySuccessor[UnaryZero]]] -->

On a variable second argument nothing matches, so `0 + n == n` does not hold by computation:

```wl
TypeTheoryProof[ForAll[{Typed[n, Unary]}, UnaryAddition[UnaryZero, n] == n], adding, {"Introduce"[n], "Reflexivity"}]
```

<!-- => Failure["NotReflexive", ...] -->

A third rule, which a recursor cannot give, makes it compute:

```wl
zeroLeft = Append[adding, TypeTheoryRewriteRule[ZeroAddition, ForAll[{Typed[n, Unary]}, UnaryAddition[UnaryZero, n] -> n]]]
```

<!-- => TypeTheoryEnvironment summary box: 49 constants -->

Now reflexivity proves it:

```wl
TypeTheoryProof[ForAll[{Typed[n, Unary]}, UnaryAddition[UnaryZero, n] == n], zeroLeft, {"Introduce"[n], "Reflexivity"}]
```

<!-- => Proof complete -->

## Properties and Relations

Bits, with an axiom that flips them by two rewrite rules:

```wl
bits = TypeTheoryEnvironment["HomotopyTypeTheory", {
    TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}],
    TypeTheoryAxiom[Flip, TypeSpecifier[{Bit} -> Bit]],
    TypeTheoryRewriteRule[FlipZero, Flip[BitZero] -> BitOne],
    TypeTheoryRewriteRule[FlipOne, Flip[BitOne] -> BitZero]
}]
```

<!-- => TypeTheoryEnvironment summary box: 48 constants -->

The rewrite rules of the environment, the circle's first:

```wl
Information[bits, "RewriteRules"]
```

<!-- => {circleInductionBase, FlipZero, FlipOne} -->

A term that computes by the rules rests on them, as on axioms:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[Flip[BitZero], bits]]
```

<!-- => <|Flip -> "Signature", FlipZero -> "RewriteRule", FlipOne -> "RewriteRule"|> -->

[TypeTheoryCheck]() replays the rules with the other declarations:

```wl
TypeTheoryCheck[bits]
```

<!-- => Success["EnvironmentChecked", ...] -->

---

Two rules that both match `Flip[BitZero]`:

```wl
first = TypeTheoryEnvironment["HomotopyTypeTheory", {
    TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}],
    TypeTheoryAxiom[Flip, TypeSpecifier[{Bit} -> Bit]],
    TypeTheoryRewriteRule[FlipZero, Flip[BitZero] -> BitOne],
    TypeTheoryRewriteRule[FlipAny, ForAll[{Typed[b, Bit]}, Flip[b] -> b]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 48 constants -->

The first declared applies:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Flip[BitZero], first]]
```

<!-- => BitOne -->

## Possible Issues

The rules of the prelude do not allow rewrite rules:

```wl
TypeTheoryEnvironment[{TypeTheoryAxiom[Mystery, Naturals], TypeTheoryRewriteRule[MysteryZero, Mystery -> 0]}]
```

<!-- => Failure["RewriteRulesNotAllowed", ...] -->

---

The left side must be an axiom applied to arguments, not a constructor:

```wl
TypeTheoryEnvironment["HomotopyTypeTheory", {
    TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}],
    TypeTheoryRewriteRule[ZeroOne, BitZero -> BitOne]
}]
```

<!-- => Failure["RewriteRuleHead", ...] -->

---

Every variable of a rule must occur in its left side:

```wl
TypeTheoryEnvironment["HomotopyTypeTheory", {
    TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}],
    TypeTheoryAxiom[Flip, TypeSpecifier[{Bit} -> Bit]],
    TypeTheoryRewriteRule[FlipAll, ForAll[{Typed[b, Bit], Typed[c, Bit]}, Flip[b] -> c]]
}]
```

<!-- => Failure["RewriteRuleVariable", ...] -->

---

The right side must have the type of the left side:

```wl
TypeTheoryEnvironment["HomotopyTypeTheory", {
    TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}],
    TypeTheoryAxiom[Flip, TypeSpecifier[{Bit} -> Bit]],
    TypeTheoryRewriteRule[FlipType, Flip[BitZero] -> Bit]
}]
```

<!-- => Failure["TypeMismatch", ...] -->

---

An axiom with a rewrite rule:

```wl
bits = TypeTheoryEnvironment["HomotopyTypeTheory", {
    TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}],
    TypeTheoryAxiom[Flip, TypeSpecifier[{Bit} -> Bit]],
    TypeTheoryRewriteRule[FlipZero, Flip[BitZero] -> BitOne]
}]
```

<!-- => TypeTheoryEnvironment summary box: 47 constants -->

The rule is not a term:

```wl
TypeTheoryType[FlipZero, bits]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

The kernel does not check that rules agree. Here two overlap: on `BitZero`, the first gives `BitOne`, while the second makes `Flip` the identity:

```wl
flips = TypeTheoryEnvironment["HomotopyTypeTheory", {
    TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}],
    TypeTheoryAxiom[Flip, TypeSpecifier[{Bit} -> Bit]],
    TypeTheoryRewriteRule[FlipZero, Flip[BitZero] -> BitOne],
    TypeTheoryRewriteRule[FlipAny, ForAll[{Typed[b, Bit]}, Flip[b] -> b]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 48 constants -->

So the kernel accepts a proof that two different constructors are equal:

```wl
confused = TypeTheoryEnvironment[flips, {TypeTheoryTheorem[
    Confusion,
    BitOne == BitZero,
    "equalityCongruence"[
        Function[{Typed[g, TypeSpecifier[{Bit} -> Bit]]}, g[BitZero]],
        Typed["equalityReflexivity"[Typed[b, Bit] |-> b], Function[{Typed[b, Bit]}, Flip[b]] == Function[{Typed[b, Bit]}, b]]
    ]
]}]
```

<!-- => TypeTheoryEnvironment summary box: 49 constants -->

The theorem it declares:

```wl
confused[Confusion]
```

<!-- => theorem Confusion : BitOne == BitZero -->
