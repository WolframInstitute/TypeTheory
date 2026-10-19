---
Template: Symbol
Name: CircleInductionBase
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/CircleInductionBase
Keywords: [circle, rewrite rule, computation, higher inductive type, HoTT]
SeeAlso: [CircleInduction, TypeTheoryRewriteRule, CircleInductionLoop]
RelatedGuides: [TypeTheory]
RelatedTutorials: [HomotopyTypeTheory]
---

## Usage

[CircleInductionBase]() is the rewrite rule <code>[CircleInduction]()[*P*, *b*, *l*, [CircleBase]()] -> *b*</code> of the HoTT environment.

## Details & Options

- The HoTT book makes induction on a higher inductive type compute on its points; an axiom cannot, so a [TypeTheoryRewriteRule]() does, under rules that allow rewrite rules.
- A rewrite rule is not a term; <code>*env*[[CircleInductionBase]()]</code> gives its declaration.
- It is a constant of <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code>; terms that use it name that environment.

## Basic Examples

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The declaration of the rule:

```wl
hott[CircleInductionBase]
```

<!-- => rewrite CircleInductionBase : ∀_P∶𝕊¹ → Type u ∀_b∶P[CircleBase] ∀_l∶Transport[P, CircleLoop, b] == b CircleInduction[P, b, l, CircleBase] ⟶ b -->

---

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The rewrite rules of the HoTT environment:

```wl
Information[hott, "RewriteRules"]
```

<!-- => {CircleInductionBase} -->
