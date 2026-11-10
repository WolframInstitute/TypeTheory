---
Template: Symbol
Name: QuotientType
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/QuotientType
Keywords: [quotient, quotient type, equivalence class, classes, prelude, integers, rationals, parity, quotientSoundness, function extensionality]
SeeAlso: [QuotientIntroduction, QuotientLift, QuotientInduction, TypeTheoryQuotients, Integers, Rationals]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude, RulesAndComputation, TheIntegers]
---

## Usage

<code>[QuotientType]()[*r*]</code> is the type of the classes of the relation *r* on a type α.

## Details & Options

- [QuotientType]() is a constant of the kernel, declared by [TypeTheoryQuotients]() in the prelude.
- α is an implicit argument, found from the type of *r*, which is `α -> α -> Prop`. Any relation will do, not only an equivalence: two elements have equal classes when the equivalence relation that *r* generates relates them.
- <code>[QuotientType]()[*r*]</code> lives in the universe of α: a quotient of a type is a type, and a quotient of the proofs of a proposition is a proposition.
- Its elements are classes. [QuotientIntroduction]() makes the class of an element, [QuotientLift]() takes a function on elements that respects *r* to a function on classes, [QuotientInduction]() proves a property of every class, and the axiom `"quotientSoundness"` makes the classes of related elements equal. Two classes are equal by computation only when their elements are.
- The integers of <code>[TypeTheoryEnvironment]()["Integers"]</code> are <code>[QuotientType]()["integerRelation"]</code>, the pairs of natural numbers with the same difference, and the rationals of <code>[TypeTheoryEnvironment]()["Rationals"]</code> are a quotient of pairs of an integer and a natural number. The prelude proves `"functionExtensionality"` with the quotient of functions by being equal at every point.
- Quotients need rules with Prop and the setting `"Quotients"` of [TypeTheoryRules](): the HoTT and the cubical environments have none.

## Basic Examples

The type of [QuotientType]():

```wl
TypeTheoryType[QuotientType]
```

<!-- => ∀_{α ∶ Sort u} (α → α → Prop) → Sort u -->

---

The natural numbers up to parity: a number's parity, true for an odd number, and the relation of having the same parity:

```wl
parity = TypeTheoryEnvironment[{
    TypeTheoryDefinition[Parity, n |-> InductiveRecursor[Naturals][Booleans &, "false", {k, r} |-> "not"[r], n]],
    TypeTheoryDefinition[SameParity, {m, n} |-> Parity[m] == Parity[n]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 259 constants -->

Their quotient, the two classes of even and odd numbers, is a type:

```wl
TypeTheoryType[QuotientType[SameParity], parity]
```

<!-- => Type -->

The class of 7 is one of its elements:

```wl
TypeTheoryType[QuotientIntroduction[SameParity, 7], parity]
```

<!-- => QuotientType[SameParity] -->

---

The integers are the quotient of pairs of natural numbers by a relation:

```wl
TypeTheoryEnvironment["Integers"][Integers]
```

<!-- => definition ℤ : Type := QuotientType[integerRelation] -->

The relation: (a, b) and (c, d), standing for a - b and c - d, are related when a + d == c + b:

```wl
TypeTheoryEnvironment["Integers"]["integerRelation"]
```

<!-- => definition integerRelation : ℕ × ℕ → ℕ × ℕ → Prop := (p ∶ ℕ × ℕ) (q ∶ ℕ × ℕ) ↦ p〚"first"〛 + q〚"second"〛 == q〚"first"〛 + p〚"second"〛 -->

## Scope

The rationals are a quotient too:

```wl
TypeTheoryEnvironment["Rationals"][Rationals]
```

<!-- => definition ℚ : Type := QuotientType[rationalRelation] -->

---

Functions up to being equal at every point, the quotient with which the prelude proves function extensionality:

```wl
TypeTheoryType[QuotientType[{Typed[f, TypeSpecifier[{Naturals} -> Naturals]], Typed[g, TypeSpecifier[{Naturals} -> Naturals]]} |-> ForAll[{n}, f[n] == g[n]]]]
```

<!-- => Type -->

---

Any relation will do. Relating each number to the next makes 2 and 3 one class, by `"quotientSoundness"` and the computation of 2 + 1:

```wl
TypeTheoryProof[
    QuotientIntroduction[{m, n} |-> m + 1 == n, 2] == QuotientIntroduction[{m, n} |-> m + 1 == n, 3],
    {"Apply"["quotientSoundness"], "Reflexivity"}
]
```

<!-- => Proof complete -->

---

A quotient is in the universe of its type, so a quotient of the proofs of a proposition is a proposition:

```wl
TypeTheoryType[QuotientType[{Typed[h, True], Typed[k, True]} |-> True]]
```

<!-- => Prop -->

## Applications

Function extensionality, which the prelude proves from the quotient of functions: two functions equal at every point have one class, and applying a class to a point is a lift:

```wl
TypeTheoryType["functionExtensionality"]
```

<!-- => ∀_{α ∶ Sort u} ∀_{β ∶ α → Sort v} ∀_{f ∶ ∀_x∶α β[x]} ∀_{g ∶ ∀_x∶α β[x]} (∀_x∶α f[x] == g[x]) ⇒ f == g -->

---

Two pairs with the same difference, (2, 5) and (0, 3), are one integer: `"quotientSoundness"` leaves the relation of the pairs, 2 + 3 == 0 + 5, which holds by computation:

```wl
TypeTheoryProof[QuotientIntroduction["integerRelation", "pair"[2, 5]] == QuotientIntroduction["integerRelation", "pair"[0, 3]], "Integers", {"Apply"["quotientSoundness"], "Reflexivity"}]
```

<!-- => Proof complete -->

## Properties and Relations

The four quotient constants come from one declaration of the prelude:

```wl
TypeTheoryEnvironment["Prelude"][QuotientType]
```

<!-- => TypeTheoryQuotients[] -->

---

The integers are their quotient by computation:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Integers, "Integers"], TypeTheoryTerm[QuotientType["integerRelation"], "Integers"]]
```

<!-- => True -->

---

Quotient types are a setting of the rules, which the prelude's rules, the calculus of inductive constructions, have:

```wl
Information[TypeTheoryEnvironment["Prelude"], "Rules"]["Quotients"]
```

<!-- => True -->

## Possible Issues

[QuotientType]() takes a relation, not the type it is on:

```wl
TypeTheoryType[QuotientType[Naturals]]
```

<!-- => Failure["TypeMismatch", ...] -->

---

The relation gives propositions. A Boolean test is refused; its equation with another Boolean, as `Parity[m] == Parity[n]` above, is a proposition:

```wl
TypeTheoryType[QuotientType[{Typed[m, Naturals], Typed[n, Naturals]} |-> Decide[m == n]]]
```

<!-- => Failure["TypeMismatch", ...] -->

---

The HoTT environment has no Prop, and its rules have no quotient types:

```wl
TypeTheoryEnvironment["HomotopyTypeTheory", TypeTheoryQuotients[]]
```

<!-- => Failure["QuotientsNotAllowed", ...] -->
