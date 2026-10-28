---
Template: Symbol
Name: DoubleNegationElimination
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/DoubleNegationElimination
Keywords: [double negation, classical logic, negation, prelude]
SeeAlso: [ExcludedMiddle, Not, FalseElimination]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[DoubleNegationElimination]()[*p*]</code> proves <code>[Implies]()[[Not]()[[Not]()[*p*]], *p*]</code>.

## Details & Options

- [DoubleNegationElimination]() is a theorem of the prelude, proved by cases on <code>[ExcludedMiddle]()[*p*]</code>.
- Its argument *p* is explicit.
- The constructive environment, <code>[TypeTheoryEnvironment]()["Constructive"]</code>, does not have it.

## Basic Examples

The statement of [DoubleNegationElimination]():

```wl
TypeTheoryCheck[TypeTheoryTerm[DoubleNegationElimination]]
```

<!-- => ∀_p∶Prop (¬¬p) ⇒ p -->

---

From the double negation of `1 == 1`, `1 == 1`:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[h, Not[Not[1 == 1]]]}, DoubleNegationElimination[1 == 1][h]]]]
```

<!-- => (¬¬1 == 1) ⇒ 1 == 1 -->

## Applications

A proof by contradiction: `"Apply"` with <code>[DoubleNegationElimination]()[*q*]</code> turns the goal *q* into `¬¬q`, and `"Introduce"` assumes `¬q`, leaving [False]() to prove:

```wl
proof = TypeTheoryProof[ForAll[{Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]]}, Implies[Implies[Not[q], Not[p]], Implies[p, q]]], {
    TypeTheoryTactic["Introduce", p, q, h, hp],
    TypeTheoryTactic["Apply", DoubleNegationElimination[q]],
    TypeTheoryTactic["Introduce", hnq]
}]
```

<!-- => Proof, 1 goal: p ∶ Prop, q ∶ Prop, h ∶ (¬q) ⇒ ¬p, hp ∶ p, hnq ∶ ¬q ⊢ False -->

`h` turns `hnq` into a refutation of `hp`:

```wl
TypeTheoryTactic["Exact", h[hnq][hp]][proof]
```

<!-- => Proof complete -->

## Properties and Relations

It is proved by cases on [ExcludedMiddle](), whose recursor takes a case for each side:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[p, TypeUniverse[0]], Typed[h, Not[Not[p]]]},
    InductiveRecursor[Or][Function[{Typed[t, p || Not[p]]}, p], Function[{Typed[k, p]}, k], Function[{Typed[k, Not[p]]}, FalseElimination[h[k]]], ExcludedMiddle[p]]
]]]
```

<!-- => ∀_p∶Prop (¬¬p) ⇒ p -->

---

The converse, from *p* to `¬¬p`, needs no axiom: it is proved in the constructive environment:

```wl
TypeTheoryProof[ForAll[{Typed[p, TypeUniverse[0]]}, Implies[p, Not[Not[p]]]], TypeTheoryEnvironment["Constructive"], {
    TypeTheoryTactic["Introduce", p, hp, hnp],
    TypeTheoryTactic["Exact", hnp[hp]]
}]
```

<!-- => Proof complete -->

## Possible Issues

The constructive environment does not have it:

```wl
TypeTheoryCheck[TypeTheoryTerm[DoubleNegationElimination, TypeTheoryEnvironment["Constructive"]]]
```

<!-- => Failure["ElaborationFailed", ...] -->
