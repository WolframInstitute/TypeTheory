---
Template: Symbol
Name: TypeTheoryTranslate
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryTranslate
Keywords: [translation, rules, Martin-Löf type theory, calculus of inductive constructions, Prop, universes, environment, kernel, impredicativity, axioms, rewrite rules]
SeeAlso: [TypeTheoryRules, TypeTheoryEnvironment, TypeTheoryCheck, TypeTheoryAxiom, TypeUniverse]
RelatedGuides: [TypeTheory]
RelatedTutorials: [RulesAndComputation, Quantities]
---

## Usage

<code>[TypeTheoryTranslate]()[*environment*, *rules*]</code> translates the declarations of *environment*, an environment or the name of a library environment, to the [TypeTheoryRules]() *rules*, whose kernel checks them again, and gives a [Success]() whose `"Environment"` is the environment of *rules* with each declaration that checks there, and whose `"Failures"` gives the failure of each declaration left out.

## Details & Options

- A translation is trusted no more than any declaration: the declarations are replayed in order on the empty environment of *rules*, and its kernel checks each of them, as [TypeTheoryCheck]() replays an environment on its own rules.
- A declaration that fails to check is left out, and so is every declaration that mentions it. `"Failures"` is an [Association]() from the name of each declaration left out to its [Failure](), whose tag says why: `"AxiomLeftOut"` for an axiom, `"QuotientsNotAllowed"` for the quotient types in rules without them, or the failure of the kernel, as `"TypeMismatch"`.
- The [Success]() has the tag `"Translated"`, and its message says how many of the declarations translate.
- Where *rules* have no Prop, as Martin-Löf type theory, Prop becomes the lowest universe of types, Type, and the other universes stay: a universe level *l* becomes `max(l, 1)`.
- A recursor's motive goes into <code>[TypeUniverse]()[*u*]</code> with Prop and into <code>[TypeUniverse]()[*u* + 1]</code> without it, so the level a recursor is applied at moves with it; an inductive proposition, such as [Exists](), lives in the universe of its largest field.
- What needs Prop's impredicativity or proof irrelevance fails to check in rules without Prop, and the quotient types need rules with quotients.
- Where *rules* gain Prop, a theorem, which states a type in rules without it, becomes a definition.
- Where *rules* lose quantities, every binder loses its quantity; where they gain them, the kernel gives the constructors and recursors theirs, and every binder written without one keeps the quantity [Infinity]().
- The option `"Axioms" -> True` keeps the axioms. They are left out by default, since an axiom that holds of propositions need not hold of types: propositional extensionality, for one, is inconsistent when every type counts as a proposition.
- *environment* is a [TypeTheoryEnvironment]() or the name of a library environment, such as `"Constructive"`, and *rules* a [TypeTheoryRules]() object; with rules given otherwise [TypeTheoryTranslate]() stays unevaluated.

## Basic Examples

The constructive prelude in Martin-Löf type theory:

```wl
translated = TypeTheoryTranslate["Constructive", TypeTheoryRules["MartinLofTypeTheory"]]
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

<!-- => inductive True : Type | trueIntroduction : True -->

---

Why the quotient types are left out:

```wl
TypeTheoryTranslate["Constructive", TypeTheoryRules["MartinLofTypeTheory"]]["Failures"][QuotientType]
```

<!-- => Failure["QuotientsNotAllowed", ...] -->

## Scope

The constructive prelude in Martin-Löf type theory:

```wl
martinLof = TypeTheoryTranslate["Constructive", TypeTheoryRules["MartinLofTypeTheory"]]["Environment"]
```

<!-- => TypeTheoryEnvironment summary box: 151 constants -->

The laws of arithmetic hold there, proved as in the prelude:

```wl
TypeTheoryType["additionCommutativity", martinLof]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ m + n == n + m -->

An equation is a type there:

```wl
TypeTheoryType[1 == 1, martinLof]
```

<!-- => Type -->

[Exists]() lives in the universe of its largest field, at least `Type`:

```wl
TypeTheoryType[Exists, martinLof]
```

<!-- => ∀_{α∶Sort (max 1 u)} (α → Type) → Sort (max 1 u) -->

Terms and proofs work there as in any other environment:

```wl
TypeTheoryProof[2 + 2 == 4, martinLof, {"Decide"}]
```

<!-- => Proof complete -->

---

An inductive type of one's own translates with the rest:

```wl
bits = TypeTheoryEnvironment["Constructive", {TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}]}]
```

<!-- => TypeTheoryEnvironment summary box: 159 constants -->

```wl
TypeTheoryTranslate[bits, TypeTheoryRules["MartinLofTypeTheory"]]["Environment"][Bit]
```

<!-- => inductive Bit : Type | BitZero : Bit | BitOne : Bit -->

---

The classical prelude loses its axioms, and every declaration that mentions them:

```wl
Keys[TypeTheoryTranslate["Prelude", TypeTheoryRules["MartinLofTypeTheory"]]["Failures"]]
```

<!-- => {QuotientType, "propositionalExtensionality", "quotientSoundness", "functionExtensionality", "choice", ChosenWitness, "chosenWitnessProperty", "excludedMiddle", "doubleNegationElimination", ExpressionEvaluate} -->

---

A translation to the same rules leaves out the axioms too:

```wl
TypeTheoryTranslate["Prelude", TypeTheoryRules["CalculusOfInductiveConstructions"]]
```

<!-- => Success["Translated", ...] -->

---

Homotopy type theory, univalence and the circle included, in the calculus of inductive constructions with rewrite rules:

```wl
homotopy = TypeTheoryTranslate[
    "HomotopyTypeTheory",
    TypeTheoryRules["CalculusOfInductiveConstructions", "RewriteRules" -> True],
    "Axioms" -> True
]
```

<!-- => Success["Translated", ...] -->

All of it translates:

```wl
homotopy["Failures"]
```

<!-- => <||> -->

Its two theorems, which state types, are definitions there:

```wl
Information[homotopy["Environment"], "Kinds"]
```

<!-- => <|"InductiveType" -> 6, "Constructor" -> 6, "Recursor" -> 6, "Definition" -> 16, "Axiom" -> 6, "RewriteRule" -> 1|> -->

## Options

### Axioms

By default an axiom is left out:

```wl
TypeTheoryTranslate["Prelude", TypeTheoryRules["MartinLofTypeTheory"]]["Failures"]["propositionalExtensionality"]
```

<!-- => Failure["AxiomLeftOut", ...] -->

---

`"Axioms" -> True` keeps the axioms where they check, as in rules of the same kind:

```wl
TypeTheoryTranslate["Prelude", TypeTheoryRules["CalculusOfInductiveConstructions"], "Axioms" -> True]["Failures"]
```

<!-- => <||> -->

---

Propositional extensionality, kept, does not check in Martin-Löf type theory, where it would say that any two equivalent types are equal:

```wl
TypeTheoryTranslate["Prelude", TypeTheoryRules["MartinLofTypeTheory"], "Axioms" -> True]["Failures"]["propositionalExtensionality"]
```

<!-- => Failure["TypeMismatch", ...] -->

## Properties and Relations

The constructive prelude in Martin-Löf type theory:

```wl
martinLof = TypeTheoryTranslate["Constructive", TypeTheoryRules["MartinLofTypeTheory"]]["Environment"]
```

<!-- => TypeTheoryEnvironment summary box: 151 constants -->

It follows the rules it was translated to:

```wl
Information[martinLof, "Rules"]["Name"]
```

<!-- => "MartinLofTypeTheory" -->

Its declarations check again, as any environment's do:

```wl
TypeTheoryCheck[martinLof]
```

<!-- => Success["EnvironmentChecked", ...] -->

## Possible Issues

A proposition about all propositions is a proposition only by impredicativity, which Martin-Löf type theory does not have:

```wl
impredicative = TypeTheoryEnvironment[{TypeTheoryDefinition[Everything, Typed[ForAll[{Typed[p, TypeUniverse[0]]}, Implies[p, p]], TypeUniverse[0]]]}]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

```wl
TypeTheoryTranslate[impredicative, TypeTheoryRules["MartinLofTypeTheory"]]["Failures"][Everything]
```

<!-- => Failure["TypeMismatch", ...] -->

---

There is no Prop in rules without it:

```wl
martinLof = TypeTheoryTranslate["Constructive", TypeTheoryRules["MartinLofTypeTheory"]]["Environment"]
```

<!-- => TypeTheoryEnvironment summary box: 151 constants -->

```wl
TypeTheoryType[TypeUniverse[0], martinLof]
```

<!-- => Failure["NoProp", ...] -->

---

The rules are a [TypeTheoryRules]() object, not their name:

```wl
TypeTheoryTranslate["Constructive", "MartinLofTypeTheory"]
```

<!-- => TypeTheoryTranslate[TypeTheoryEnvironment summary box: 155 constants, "MartinLofTypeTheory"] -->
