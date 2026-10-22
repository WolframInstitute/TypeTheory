---
Template: Symbol
Name: TypeTheoryQuotients
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryQuotients
Keywords: [quotient, quotient type, Quot, Lean, kernel, declaration, environment, trusted]
SeeAlso: [QuotientType, QuotientIntroduction, QuotientLift, QuotientInduction, QuotientSoundness, TypeTheoryRules]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude, RulesAndComputation]
---

## Usage

<code>[TypeTheoryQuotients]()[]</code> declares the quotient types of Lean's kernel, [QuotientType](), [QuotientIntroduction](), [QuotientLift]() and [QuotientInduction](), when added to a [TypeTheoryEnvironment]().

<code>[TypeTheoryQuotients]()[*equality*, {*type*, *introduction*, *lift*, *induction*}]</code> declares them under the given names, with the inductive type *equality* as the equality their types mention.

## Details & Options

- The kernel writes the four types itself, as Lean's kernel does for `Quot`, `Quot.mk`, `Quot.lift` and `Quot.ind`, and adds two computation rules: <code>[QuotientLift]()[*f*, *h*, [QuotientIntroduction]()[*r*, *a*]]</code> is *f*[*a*], and <code>[QuotientInduction]()[*premise*, [QuotientIntroduction]()[*r*, *a*]]</code> is *premise*[*a*].
- The rules of the environment must have quotients, the setting `"Quotients"` of [TypeTheoryRules](), and Prop: the calculus of inductive constructions has them, Martin-Löf type theory does not.
- The equality must be the identity type: an inductive type with one universe parameter, of the type <code>[ForAll]()[{[TypedImplicit]()[α, [TypeUniverse]()[u]]}, α -> α -> Prop]</code>, with one constructor of the type <code>[ForAll]()[{[TypedImplicit]()[α, [TypeUniverse]()[u]], [Typed]()[x, α]}, x == x]</code>. The type of the lift mentions it, and with another equality a lift could tell apart elements that the quotient identifies.
- That the classes of related elements are equal is an axiom, Lean's `Quot.sound`, which the prelude declares as [QuotientSoundness]().
- The prelude declares the quotient types; LeanLink declares Lean's own with <code>[TypeTheoryQuotients]()["Eq", {"Quot", "Quot.mk", "Quot.lift", "Quot.ind"}]</code>.
- The four constants come from one declaration: [Normal]() gives it once, and <code>[TypeTheoryCheck]()[*env*]</code> replays it and compares the four records with those it gives.

## Basic Examples

The prelude has the quotient types:

```wl
TypeTheoryEnvironment["Prelude"][QuotientLift]
```

<!-- => TypeTheoryQuotients[] -->

---

An environment from nothing but an equality, with the quotient types:

```wl
quotients = TypeTheoryEnvironment[TypeTheoryEnvironment[], {
    TypeTheoryInductiveType[Equal, ForAll[{TypedImplicit[A, TypeUniverse[u]], Typed[x, A], Typed[y, A]}, TypeUniverse[0]], {
        EqualityReflexivity -> ForAll[{TypedImplicit[A, TypeUniverse[u]], Typed[x, A]}, x == x]
    }],
    TypeTheoryQuotients[]
}]
```

<!-- => TypeTheoryEnvironment summary box: 7 constants -->

Its constants:

```wl
Keys[quotients]
```

<!-- => {Equal, EqualityReflexivity, InductiveRecursor[Equal], QuotientType, QuotientIntroduction, QuotientLift, QuotientInduction} -->

## Possible Issues

Martin-Löf type theory has no quotient types:

```wl
TypeTheoryEnvironment[TypeTheoryEnvironment[TypeTheoryRules["MartinLofTypeTheory"]], {TypeTheoryQuotients[]}]
```

<!-- => Failure["QuotientsNotAllowed", ...] -->

---

Without the equality their types mention, there are none:

```wl
TypeTheoryEnvironment[TypeTheoryEnvironment[], {TypeTheoryQuotients[]}]
```

<!-- => Failure["EqualityExpected", ...] -->
