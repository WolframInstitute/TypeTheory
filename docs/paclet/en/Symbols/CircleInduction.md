---
Template: Symbol
Name: CircleInduction
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/CircleInduction
Keywords: [circle, induction, higher inductive type, rewrite rule, HoTT]
SeeAlso: [CircleInductionBase, CircleInductionLoop, CircleBase, CircleLoop]
RelatedGuides: [TypeTheory]
RelatedTutorials: [HomotopyTypeTheory]
---

## Usage

<code>[CircleInduction]()[*P*, *b*, *l*, *x*]</code> gives an element of <code>*P*[*x*]</code> for every point *x* of the circle, from *b* : <code>*P*[[CircleBase]()]</code> and a path *l* : <code>[Transport]()[*P*, [CircleLoop](), *b*] == *b*</code>.

## Details & Options

- [CircleInduction]() is an axiom. On [CircleBase]() it computes to *b*, by the rewrite rule [CircleInductionBase](); on [CircleLoop]() it gives *l* up to a path, by the axiom [CircleInductionLoop]().
- It is a constant of <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code>; terms that use it name that environment.

## Basic Examples

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The statement of [CircleInduction]() in the HoTT environment:

```wl
TypeTheoryCheck[TypeTheoryTerm[CircleInduction, hott]]
```

<!-- => ∀_P∶𝕊¹ → Type u ∀_b∶P[CircleBase] Transport[P, CircleLoop, b] == b → ∀_x∶𝕊¹ P[x] -->

---

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

On the base point it computes, here into a constant family:

```wl
WeakHeadNormalForm[TypeTheoryTerm[CircleInduction[Function[{Typed[x, Circle]}, Booleans], True, TransportConstant[CircleLoop, True], CircleBase], hott]]
```

<!-- => true -->
