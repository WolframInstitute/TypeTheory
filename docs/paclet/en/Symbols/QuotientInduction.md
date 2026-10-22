---
Template: Symbol
Name: QuotientInduction
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/QuotientInduction
Keywords: [quotient, induction, classes, Quot.ind, Lean, prelude]
SeeAlso: [QuotientType, QuotientIntroduction, QuotientLift, TypeTheoryQuotients]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude, RulesAndComputation]
---

## Usage

<code>[QuotientInduction]()[*premise*, *q*]</code> proves *P*[*q*] for the class *q* from a proof *premise* of <code>*P*[[QuotientIntroduction]()[*r*, *a*]]</code> for every *a*.

## Details & Options

- [QuotientInduction]() is a constant of the kernel, declared by [TypeTheoryQuotients]() in the prelude, as Lean's `Quot.ind`.
- The type α, the relation *r* and the property *P*, a proposition about classes, are implicit arguments. Elaboration rarely finds *P* from the premise, so <code>[Construct]()[[QuotientInduction](), α, *r*, *P*, *premise*]</code> gives it.
- It computes on a class: <code>[QuotientInduction]()[*premise*, [QuotientIntroduction]()[*r*, *a*]]</code> is *premise*[*a*].

## Basic Examples

The type of [QuotientInduction]():

```wl
TypeTheoryCheck[TypeTheoryTerm[QuotientInduction]]
```

<!-- => ∀_{α ∶ Sort u} ∀_{r ∶ α → α → Prop} ∀_{β ∶ QuotientType[r] → Prop} (∀_a∶α β[QuotientIntroduction[r, a]]) ⇒ ∀_q∶QuotientType[r] β[q] -->

---

The quotient of the natural numbers by equality:

```wl
equal = TypeTheoryTerm[Typed[Function[{Typed[m, Naturals], Typed[n, Naturals]}, m == n], TypeSpecifier[{Naturals, Naturals} -> TypeUniverse[0]]]]
```

<!-- => (m ∶ ℕ) (n ∶ ℕ) ↦ m == n ∶ ℕ → ℕ → Prop -->

Every class equals itself, from every element's class doing so:

```wl
TypeTheoryCheck[TypeTheoryTerm[Construct[QuotientInduction, Naturals, equal, Function[{Typed[q, QuotientType[equal]]}, q == q], Function[{Typed[a, Naturals]}, EqualityReflexivity[QuotientIntroduction[equal, a]]]]]]
```

<!-- => ∀_q∶QuotientType[(m ∶ ℕ) (n ∶ ℕ) ↦ m == n] q == q -->
