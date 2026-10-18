---
Template: Symbol
Name: ExistsIntroduction
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/ExistsIntroduction
Keywords: [Exists, existential, witness, proof, constructor, prelude, logic]
SeeAlso: [EqualityReflexivity, TypeTheoryCheck, TypeTheoryTerm]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[ExistsIntroduction]()[*w*, *h*]</code> proves <code>[Exists]()[*p*]</code> from a witness *w* and a proof *h* of <code>*p*[*w*]</code>.

## Details & Options

- [Exists]() is an inductive proposition of the prelude whose parameter is a predicate, and [ExistsIntroduction]() is its one constructor.
- <code>[Exists]()[{[Typed]()[*x*, *A*]}, *body*]</code> is <code>[Exists]()[[Function]()[{[Typed]()[*x*, *A*]}, *body*]]</code>.
- The type of the witness, its universe level and the predicate are implicit arguments. The predicate is found from the type the proof is expected to have.
- A proof of an existential statement eliminates only into propositions: the witness cannot be taken back out.

## Basic Examples

The type of [ExistsIntroduction]():

```wl
TypeTheoryCheck[TypeTheoryTerm[ExistsIntroduction]]
```

<!-- => ∀_{α ∶ Sort u} ∀_{P ∶ α → Prop} ∀_w∶α P[w] ⇒ Exists[P] -->

---

There is a number that doubles to 4:

```wl
TypeTheoryCheck[
    TypeTheoryTerm[ExistsIntroduction[2, EqualityReflexivity[4]]],
    TypeTheoryTerm[Exists[{Typed[n, NonNegativeIntegers]}, n + n == 4]]
]
```

<!-- => True -->

## Scope

[Typed]() gives the expected type inside the term:

```wl
TypeTheoryCheck[TypeTheoryTerm[
    Typed[ExistsIntroduction[2, EqualityReflexivity[4]], Exists[{Typed[n, NonNegativeIntegers]}, n + n == 4]]
]]
```

<!-- => ∃_n∶ℕ n + n == 4 -->
