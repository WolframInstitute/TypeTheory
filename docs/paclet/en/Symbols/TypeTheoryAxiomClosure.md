---
Template: Symbol
Name: TypeTheoryAxiomClosure
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryAxiomClosure
Keywords: [axioms, dependencies, print axioms, trust, signature, rewrite rule, closure]
SeeAlso: [TypeTheoryAxiom, TypeTheoryCheck, TypeTheoryTerm, TypeTheoryEnvironment, TypeTheoryRewriteRule]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[TypeTheoryAxiomClosure]()[*term*]</code> gives the axioms the [TypeTheoryTerm]() *term* rests on, as <code><\|*axiom* -> *kind*, ...\|></code>.

## Details & Options

- The closure follows every constant *term* mentions, then the constants in the type and value of each of those, as Lean's `#print axioms` does. A constructor or recursor leads to its inductive type, and an inductive type to its constructors.
- An axiom is `"Proposition"` when its type is a proposition, such as [PropositionalExtensionality](), and `"Signature"` otherwise: an axiom of a type, such as a constant of [NonNegativeIntegers]() or a type of its own, which a theorem holds for whatever it stands for, as for a variable. [Choice](), whose value is an element of a type, is a signature by this rule.
- A rewrite rule of a constant the closure reaches is listed as `"RewriteRule"`: the kernel computes with it, so it is trusted as an axiom is.
- A theorem that rests on no axiom has the closure <code><\|\|></code>.
- <code>[Information]()[*term*, "AxiomClosure"]</code> gives the same, and <code>[Information]()[*term*, "Constants"]</code> gives the constants the type and the value of *term* mention, those of a constant's declaration for a constant.

## Basic Examples

Excluded middle rests on the three axioms Lean's proof of it uses:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[ExcludedMiddle]]
```

<!-- => <|Choice -> Signature, QuotientSoundness -> Proposition, PropositionalExtensionality -> Proposition|> -->

---

A theorem proved by computation rests on none:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[EqualitySymmetry]]
```

<!-- => <||> -->

## Scope

An environment with an axiom of a type and an axiom of a proposition:

```wl
signed = TypeTheoryEnvironment[{TypeTheoryAxiom[Origin, Naturals], TypeTheoryAxiom[OriginPositive, 0 < Origin]}]
```

<!-- => TypeTheoryEnvironment summary box: 171 constants -->

A term with the constant `Origin` rests on it as a signature:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[Origin + 1, signed]]
```

<!-- => <|Origin -> Signature|> -->

The axiom about `Origin` is a proposition, and its statement mentions `Origin`:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[OriginPositive, signed]]
```

<!-- => <|OriginPositive -> Proposition, Origin -> Signature|> -->

---

Homotopy type theory's circle is given by axioms, and its induction principle computes on the base point by a rewrite rule:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[CircleInduction, TypeTheoryEnvironment["HomotopyTypeTheory"]]]
```

<!-- => <|CircleInduction -> Signature, Circle -> Signature, CircleBase -> Signature, CircleLoop -> Signature, CircleInductionBase -> RewriteRule|> -->

## Properties and Relations

[Information]() gives the same closure:

```wl
Information[TypeTheoryTerm[ExcludedMiddle], "AxiomClosure"] === TypeTheoryAxiomClosure[TypeTheoryTerm[ExcludedMiddle]]
```

<!-- => True -->

---

The constants a statement mentions; its type, Prop, mentions none:

```wl
Information[TypeTheoryTerm[ForAll[{Typed[n, Naturals]}, n + 0 == n]], "Constants"]
```

<!-- => {NonNegativeIntegers, Equal, Plus} -->

---

The constants of a theorem are those of its statement and its proof, the closure's first step:

```wl
Information[TypeTheoryTerm[TwoPlusTwo, TypeTheoryEnvironment[{TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, EqualityReflexivity[4]]}]], "Constants"]
```

<!-- => {Equal, NonNegativeIntegers, Plus, EqualityReflexivity} -->

---

Every constant of the rationals rests on Lean's three axioms at most:

```wl
With[{rationals = TypeTheoryEnvironment["Rationals"]},
    Union @@ Map[Function[name, Keys[TypeTheoryAxiomClosure[TypeTheoryTerm[name, rationals]]]], Keys[rationals]]
]
```

<!-- => {Choice, PropositionalExtensionality, QuotientSoundness} -->

## Possible Issues

The closure of a constant includes the axioms its proof uses, not only its statement's: the statement of excluded middle mentions no axiom.

```wl
TypeTheoryAxiomClosure[TypeOf[TypeTheoryTerm[ExcludedMiddle]]]
```

<!-- => <||> -->
