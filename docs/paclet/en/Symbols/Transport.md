---
Template: Symbol
Name: Transport
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Transport
Keywords: [transport, path, HoTT, homotopy type theory, substitution]
SeeAlso: [DependentCongruence, TransportConstant, EqualityCongruence, EqualitySubstitution]
RelatedGuides: [TypeTheory]
RelatedTutorials: [HomotopyTypeTheory]
---

## Usage

<code>[Transport]()[*P*, *p*, *b*]</code> carries *b*, an element of <code>*P*[*x*]</code>, along the path *p* : <code>*x* == *y*</code> to an element of <code>*P*[*y*]</code>.

## Details & Options

- [Transport]() is a definition by path induction, the recursor of [Equal](), so it computes when *p* is reflexivity.
- The family *P* is explicit; *x*, *y* and the type are implicit.
- It is a constant of <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code>; terms that use it name that environment.

## Basic Examples

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The statement of [Transport]() in the HoTT environment:

```wl
TypeTheoryCheck[TypeTheoryTerm[Transport, hott]]
```

<!-- => ∀_{A ∶ Type u} ∀_P∶A → Type v ∀_{x ∶ A} ∀_{y ∶ A} x == y → P[x] → P[y] -->

---

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

Along reflexivity, transport leaves an element as it is:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Transport[Function[{Typed[b, Booleans]}, Booleans], EqualityReflexivity[True], False], hott]]
```

<!-- => false -->
