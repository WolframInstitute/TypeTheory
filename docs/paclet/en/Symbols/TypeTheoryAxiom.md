---
Template: Symbol
Name: TypeTheoryAxiom
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryAxiom
Keywords: [axiom, declaration, assumption, excluded middle, classical logic, constructive, environment]
SeeAlso: [TypeTheoryEnvironment, TypeTheoryDefinition, TypeTheoryTheorem, TypeTheoryInductiveType, Choice, ExcludedMiddle]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[TypeTheoryAxiom]()[*name*, *type*]</code> declares *name* as an axiom of the given *type*, when added to a [TypeTheoryEnvironment]().

## Details & Options

- A declaration is inert until it is added to an environment with <code>[TypeTheoryEnvironment]()[*env*, {*declaration*}]</code> or <code>[Append]()[*env*, *declaration*]</code>, which check that *type* is a type.
- An axiom is assumed, not proved. <code>[Information]()[*env*, "Axioms"]</code> lists the axioms of an environment.
- The prelude assumes [PropositionalExtensionality](), [FunctionExtensionality]() and [Choice](). <code>[TypeTheoryEnvironment]()["Constructive"]</code> is the prelude without them and the theorems proved from them, a start for other axioms.
- The option `"UniverseParameters" -> {u, ...}` lists the universe parameters; [Automatic]() takes the symbols and strings in universe levels, in the order they appear.

## Basic Examples

The prelude assumes three axioms:

```wl
Information[TypeTheoryEnvironment["Prelude"], "Axioms"]
```

<!-- => {PropositionalExtensionality, QuotientSoundness, Choice} -->

---

Assume the excluded middle in the constructive environment, which has no axioms:

```wl
excludedMiddle = TypeTheoryEnvironment[TypeTheoryEnvironment["Constructive"], {
    TypeTheoryAxiom[ExcludedMiddle, ForAll[{Typed[p, TypeUniverse[0]]}, Or[p, Not[p]]]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 156 constants -->

Applied to a proposition, the axiom proves it or its negation:

```wl
TypeOf[TypeTheoryTerm[ExcludedMiddle[True], excludedMiddle]]
```

<!-- => True ∨ ¬True -->

That environment's axioms:

```wl
Information[excludedMiddle, "Axioms"]
```

<!-- => {ExcludedMiddle} -->

## Scope

Assume a function on the natural numbers:

```wl
measured = TypeTheoryEnvironment[TypeTheoryAxiom[Measure, TypeSpecifier[{Naturals} -> Naturals]]]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

[Format]() gives an axiom's symbol a display, which its declaration and every term use:

```wl
Format[Measure] := "\[Mu]";
measured[Measure]
```

<!-- => axiom μ : ℕ → ℕ -->

And a term that uses it:

```wl
TypeTheoryTerm[Function[{Typed[n, Naturals]}, Measure[Measure[n]]], measured]
```

<!-- => (n ∶ ℕ) ↦ μ[μ[n]] -->

## Possible Issues

An axiom's type must be a type:

```wl
TypeTheoryEnvironment[TypeTheoryAxiom[Five, 5]]
```

<!-- => Failure["TypeExpected", ...] -->

---

The prelude proves the excluded middle from its axioms, so the name is taken there:

```wl
TypeTheoryEnvironment[TypeTheoryAxiom[ExcludedMiddle, ForAll[{Typed[p, TypeUniverse[0]]}, Or[p, Not[p]]]]]
```

<!-- => Failure["AlreadyDeclared", ...] -->
