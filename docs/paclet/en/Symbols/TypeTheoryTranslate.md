---
Template: Symbol
Name: TypeTheoryTranslate
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryTranslate
Keywords: [translation, rules, Martin-Löf type theory, calculus of inductive constructions, Prop, universes, environment, kernel]
SeeAlso: [TypeTheoryRules, TypeTheoryEnvironment, TypeTheoryCheck]
RelatedGuides: [TypeTheory]
RelatedTutorials: [RulesAndComputation, Quantities]
---

## Usage

<code>[TypeTheoryTranslate]()[*environment*, *rules*]</code> translates the declarations of *environment* to the [TypeTheoryRules]() *rules*, whose kernel checks them again, and gives a [Success]() whose `"Environment"` is the environment of *rules* with each declaration that checks there, and whose `"Failures"` gives the failure of each declaration left out.

## Details & Options

- A translation is trusted no more than any declaration: the declarations are replayed in order on the empty environment of *rules*, and its kernel checks each of them, as [TypeTheoryCheck]() replays an environment on its own rules.
- A declaration that fails to check is left out, and so is every declaration that mentions it.
- Where *rules* have no Prop, as Martin-Löf type theory, Prop becomes the lowest universe of types, Type, and the other universes stay: a universe level *l* becomes `max(l, 1)`.
- A recursor's motive goes into <code>[TypeUniverse]()[*u*]</code> with Prop and into <code>[TypeUniverse]()[*u* + 1]</code> without it, so the level a recursor is applied at moves with it; an inductive proposition, such as [Exists](), lives in the universe of its largest field.
- What needs Prop's impredicativity or proof irrelevance fails to check in rules without Prop, and the quotient types need rules with quotients.
- Where *rules* gain Prop, a theorem, which states a type in rules without it, becomes a definition.
- Where *rules* lose quantities, every binder loses its quantity; where they gain them, the kernel gives the constructors and recursors theirs, and every binder written without one keeps the quantity [Infinity]().
- The option `"Axioms" -> True` keeps the axioms. They are left out by default, since an axiom that holds of propositions need not hold of types: propositional extensionality, for one, is inconsistent when every type counts as a proposition.

## Basic Examples

The constructive prelude in Martin-Löf type theory:

```wl
translated = TypeTheoryTranslate[TypeTheoryEnvironment["Constructive"], TypeTheoryRules["MartinLofTypeTheory"]]
```

<!-- => Success["Translated", ...] -->

Only the quotient types are left out, since those rules have none:

```wl
Keys[translated["Failures"]]
```

<!-- => {QuotientType} -->

The translated environment:

```wl
translated["Environment"]
```

<!-- => TypeTheoryEnvironment summary box: 151 constants -->

[True]() is a type there:

```wl
translated["Environment"][True]
```

<!-- => inductive True : Type; | TrueIntroduction : True -->

## Scope

Terms and proofs work in the translated environment as in any other:

```wl
TypeTheoryProof[2 + 2 == 4, TypeTheoryTranslate[TypeTheoryEnvironment["Constructive"], TypeTheoryRules["MartinLofTypeTheory"]]["Environment"], {TypeTheoryTactic["Decide"]}]
```

<!-- => Proof complete -->

---

Homotopy type theory, univalence and the circle included, in the calculus of inductive constructions with rewrite rules:

```wl
TypeTheoryTranslate[
    TypeTheoryEnvironment["HomotopyTypeTheory"],
    TypeTheoryRules["CalculusOfInductiveConstructions", "RewriteRules" -> True],
    "Axioms" -> True
]
```

<!-- => Success["Translated", ...] -->

## Possible Issues

A proposition about all propositions is a proposition only by impredicativity, which Martin-Löf type theory does not have:

```wl
impredicative = TypeTheoryEnvironment[{TypeTheoryDefinition[Everything, Typed[ForAll[{Typed[p, TypeUniverse[0]]}, Implies[p, p]], TypeUniverse[0]]]}]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

```wl
TypeTheoryTranslate[impredicative, TypeTheoryRules["MartinLofTypeTheory"]]["Failures"][Everything]
```

<!-- => Failure["TypeMismatch", ...] -->
