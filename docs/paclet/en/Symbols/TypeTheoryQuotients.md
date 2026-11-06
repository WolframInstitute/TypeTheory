---
Template: Symbol
Name: TypeTheoryQuotients
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryQuotients
Keywords: [quotient, quotient type, Quot, Lean, kernel, declaration, environment, trusted, equivalence classes, lift, parity, integers]
SeeAlso: [QuotientType, QuotientIntroduction, QuotientLift, QuotientInduction, TypeTheoryRules, TypeTheoryEnvironment]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude, RulesAndComputation, TheIntegers]
---

## Usage

<code>[TypeTheoryQuotients]()[]</code> declares the quotient types of Lean's kernel, [QuotientType](), [QuotientIntroduction](), [QuotientLift]() and [QuotientInduction](), when added to a [TypeTheoryEnvironment]().

<code>[TypeTheoryQuotients]()[*equality*, {*type*, *introduction*, *lift*, *induction*}]</code> declares them under the given names, with the inductive type *equality* as the equality their types mention.

## Details & Options

- The kernel writes the four types itself, as Lean's kernel does for `Quot`, `Quot.mk`, `Quot.lift` and `Quot.ind`, and adds two computation rules: <code>[QuotientLift]()[*f*, *h*, [QuotientIntroduction]()[*r*, *a*]]</code> is *f*[*a*], and <code>[QuotientInduction]()[*premise*, [QuotientIntroduction]()[*r*, *a*]]</code> is *premise*[*a*].
- <code>[QuotientType]()[*r*]</code> is the type of the classes of the relation *r*, <code>[QuotientIntroduction]()[*r*, *a*]</code> the class of *a*, and <code>[QuotientLift]()[*f*, *h*, *q*]</code> applies *f* to the class *q*, given a proof *h* that *f* gives related elements the same value.
- The rules of the environment must have quotients, the setting `"Quotients"` of [TypeTheoryRules](), and Prop: the calculus of inductive constructions has them, Martin-Löf type theory does not.
- The equality must be the identity type: an inductive type with one universe parameter, of the type <code>[ForAll]()[{[TypedImplicit]()[α, [TypeUniverse]()[u]]}, α -> α -> Prop]</code>, with one constructor of the type <code>[ForAll]()[{[TypedImplicit]()[α, [TypeUniverse]()[u]], [Typed]()[x, α]}, x == x]</code>. The type of the lift mentions it, and with another equality a lift could tell apart elements that the quotient identifies.
- That the classes of related elements are equal is an axiom, Lean's `Quot.sound`, which the prelude declares as `"quotientSoundness"`. Without it, two classes are equal only if they are equal by computation.
- The prelude declares the quotient types, and the integers and the rationals are quotients; LeanLink declares Lean's own with <code>[TypeTheoryQuotients]()["Eq", {"Quot", "Quot.mk", "Quot.lift", "Quot.ind"}]</code>.
- The four constants come from one declaration: [Normal]() gives it once, and <code>[TypeTheoryCheck]()[*env*]</code> replays it and compares the four records with those it gives.

## Basic Examples

The prelude has the quotient types, from one declaration:

```wl
TypeTheoryEnvironment["Prelude"][QuotientLift]
```

<!-- => TypeTheoryQuotients[] -->

---

The type of the lift, which takes a function and a proof that it respects the relation:

```wl
TypeTheoryType[QuotientLift]
```

<!-- => ∀_{α∶Sort u} ∀_{r∶α → α → Prop} ∀_{β∶Sort v} ∀_f∶α → β (∀_a∶α ∀_b∶α r[a, b] ⇒ f[a] == f[b]) → QuotientType[r] → β -->

---

A lift applied to a class computes to the function's value. Here the classes are those of the relation that relates any two numbers, and the constant function 7 respects it:

```wl
WeakHeadNormalForm[TypeTheoryTerm[QuotientLift[
    Function[{Typed[k, Naturals]}, 7],
    Function[{Typed[a, Naturals], Typed[b, Naturals], Typed[e, True]}, "equalityReflexivity"[7]],
    QuotientIntroduction[Typed[{Typed[m, Naturals], Typed[n, Naturals]} |-> True, TypeSpecifier[{Naturals, Naturals} -> TypeUniverse[0]]], 5]
]]]
```

<!-- => 7 -->

## Scope

An environment from nothing but an equality, with the quotient types:

```wl
quotients = TypeTheoryEnvironment[TypeTheoryEnvironment[], {
    TypeTheoryInductiveType[Equal, ForAll[{TypedImplicit[A, TypeUniverse[u]], Typed[x, A], Typed[y, A]}, TypeUniverse[0]], {
        "equalityReflexivity" -> ForAll[{TypedImplicit[A, TypeUniverse[u]], Typed[x, A]}, x == x]
    }],
    TypeTheoryQuotients[]
}]
```

<!-- => TypeTheoryEnvironment summary box: 7 constants -->

Its constants:

```wl
Keys[quotients]
```

<!-- => {Equal, equalityReflexivity, InductiveRecursor[Equal], QuotientType, QuotientIntroduction, QuotientLift, QuotientInduction} -->

---

The quotient types under names of their own:

```wl
classes = TypeTheoryEnvironment[TypeTheoryEnvironment[], {
    TypeTheoryInductiveType[Equal, ForAll[{TypedImplicit[A, TypeUniverse[u]], Typed[x, A], Typed[y, A]}, TypeUniverse[0]], {
        "equalityReflexivity" -> ForAll[{TypedImplicit[A, TypeUniverse[u]], Typed[x, A]}, x == x]
    }],
    TypeTheoryQuotients[Equal, {Classes, ClassOf, ClassLift, ClassInduction}]
}]
```

<!-- => TypeTheoryEnvironment summary box: 7 constants -->

The lift's type names the type of classes as it was given:

```wl
TypeTheoryType[ClassLift, classes]
```

<!-- => ∀_{α∶Sort u} ∀_{r∶α → α → Prop} ∀_{β∶Sort v} ∀_f∶α → β (∀_a∶α ∀_b∶α r[a, b] ⇒ f[a] == f[b]) → Classes[r] → β -->

The declaration of each of the four:

```wl
classes[ClassLift]
```

<!-- => TypeTheoryQuotients[Equal, {Classes, ClassOf, ClassLift, ClassInduction}] -->

## Applications

The natural numbers up to parity: a number's parity, true for an odd number, the relation of having the same parity, and the parity of a class, lifted from that of its numbers:

```wl
parity = TypeTheoryEnvironment[{
    TypeTheoryDefinition[Parity, Typed[
        Typed[n, Naturals] |-> InductiveRecursor[Naturals][Typed[k, Naturals] |-> Booleans, "false", {Typed[k, Naturals], Typed[r, Booleans]} |-> "not"[r], n],
        TypeSpecifier[{Naturals} -> Booleans]
    ]],
    TypeTheoryDefinition[SameParity, Typed[{Typed[m, Naturals], Typed[n, Naturals]} |-> Parity[m] == Parity[n], TypeSpecifier[{Naturals, Naturals} -> TypeUniverse[0]]]],
    TypeTheoryDefinition[ParityOfClass, Typed[
        Typed[c, QuotientType[SameParity]] |-> QuotientLift[Parity, {Typed[a, Naturals], Typed[b, Naturals], Typed[e, SameParity[a, b]]} |-> e, c],
        TypeSpecifier[{QuotientType[SameParity]} -> Booleans]
    ]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 172 constants -->

The class of 7 is odd:

```wl
WeakHeadNormalForm[TypeTheoryTerm[ParityOfClass[QuotientIntroduction[SameParity, 7]], parity]]
```

<!-- => true -->

The classes of 1 and 3 are not equal by computation:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[QuotientIntroduction[SameParity, 1], parity], TypeTheoryTerm[QuotientIntroduction[SameParity, 3], parity]]
```

<!-- => False -->

They are equal by `"quotientSoundness"`, since 1 and 3 have the same parity by computation:

```wl
TypeTheoryProof[QuotientIntroduction[SameParity, 1] == QuotientIntroduction[SameParity, 3], parity, {"Apply"["quotientSoundness"], "Reflexivity"}]
```

<!-- => Proof complete -->

---

The integers of <code>[TypeTheoryEnvironment]()["Integers"]</code> are a quotient of pairs of natural numbers:

```wl
TypeTheoryEnvironment["Integers"][Integers]
```

<!-- => definition ℤ : Type := QuotientType[integerRelation] -->

## Properties and Relations

That the classes of related elements are equal is an axiom of the prelude, not part of the declaration:

```wl
TypeTheoryEnvironment["Prelude"]["quotientSoundness"]
```

<!-- => axiom quotientSoundness : ∀_{α∶Sort u} ∀_{r∶α → α → Prop} ∀_{a∶α} ∀_{b∶α} r[a, b] ⇒ QuotientIntroduction[r, a] == QuotientIntroduction[r, b] -->

---

The four constants are of their own kind:

```wl
Information[TypeTheoryEnvironment["Prelude"], "Kinds"]["Quotient"]
```

<!-- => 4 -->

---

An environment with the quotient types:

```wl
quotients = TypeTheoryEnvironment[TypeTheoryEnvironment[], {
    TypeTheoryInductiveType[Equal, ForAll[{TypedImplicit[A, TypeUniverse[u]], Typed[x, A], Typed[y, A]}, TypeUniverse[0]], {
        "equalityReflexivity" -> ForAll[{TypedImplicit[A, TypeUniverse[u]], Typed[x, A]}, x == x]
    }],
    TypeTheoryQuotients[]
}]
```

<!-- => TypeTheoryEnvironment summary box: 7 constants -->

[Normal]() gives the four as one declaration:

```wl
Last[Normal[quotients]]
```

<!-- => TypeTheoryQuotients[] -->

[TypeTheoryCheck]() replays it and compares the four records:

```wl
TypeTheoryCheck[quotients]
```

<!-- => Success["EnvironmentChecked", ...] -->

## Possible Issues

Martin-Löf type theory has no quotient types:

```wl
TypeTheoryEnvironment[TypeTheoryRules["MartinLofTypeTheory"], {TypeTheoryQuotients[]}]
```

<!-- => Failure["QuotientsNotAllowed", ...] -->

---

Without the equality their types mention, there are none:

```wl
TypeTheoryEnvironment[TypeTheoryEnvironment[], {TypeTheoryQuotients[]}]
```

<!-- => Failure["EqualityExpected", ...] -->

---

An equality with a second constructor, which would make any two elements equal, is not the identity type:

```wl
TypeTheoryEnvironment[TypeTheoryEnvironment[], {
    TypeTheoryInductiveType[Equal, ForAll[{TypedImplicit[A, TypeUniverse[u]], Typed[x, A], Typed[y, A]}, TypeUniverse[0]], {
        "equalityReflexivity" -> ForAll[{TypedImplicit[A, TypeUniverse[u]], Typed[x, A]}, x == x],
        "equalityAnything" -> ForAll[{TypedImplicit[A, TypeUniverse[u]], Typed[x, A], Typed[y, A]}, x == y]
    }],
    TypeTheoryQuotients[]
}]
```

<!-- => Failure["EqualityExpected", ...] -->

---

The prelude has the quotient types already:

```wl
TypeTheoryEnvironment[{TypeTheoryQuotients[]}]
```

<!-- => Failure["AlreadyDeclared", ...] -->
