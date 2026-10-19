---
Template: Symbol
Name: DependentCongruence
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/DependentCongruence
Keywords: [dependent congruence, apd, path, HoTT, homotopy type theory]
SeeAlso: [Transport, EqualityCongruence, CircleInductionLoop]
RelatedGuides: [TypeTheory]
RelatedTutorials: [HomotopyTypeTheory]
---

## Usage

<code>[DependentCongruence]()[*f*, *p*]</code> is the path <code>[Transport]()[*P*, *p*, *f*[*x*]] == *f*[*y*]</code> that a dependent function *f* : <code>(*x* : *A*) -> *P*[*x*]</code> gives from a path *p* : <code>*x* == *y*</code>.

## Details & Options

- [DependentCongruence]() is a definition by path induction; on reflexivity it is reflexivity. It is what the HoTT book writes `apd f p`.
- *P* is implicit and found from the type of *f*.
- [CircleInductionLoop]() says what it gives for circle induction on [CircleLoop]().
- It is a constant of <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code>; terms that use it name that environment.

## Basic Examples

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The statement of [DependentCongruence]() in the HoTT environment:

```wl
TypeTheoryCheck[TypeTheoryTerm[DependentCongruence, hott]]
```

<!-- => ∀_{A ∶ Type u} ∀_{P ∶ A → Type v} ∀_f∶∀_z∶A P[z] ∀_{x ∶ A} ∀_{y ∶ A} ∀_p∶x == y Transport[P, p, f[x]] == f[y] -->
