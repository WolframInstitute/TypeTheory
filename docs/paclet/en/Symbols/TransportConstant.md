---
Template: Symbol
Name: TransportConstant
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TransportConstant
Keywords: [transport, constant family, path, HoTT]
SeeAlso: [Transport, CircleInduction]
RelatedGuides: [TypeTheory]
RelatedTutorials: [HomotopyTypeTheory]
---

## Usage

<code>[TransportConstant]()[*p*, *b*]</code> is the path <code>[Transport]()[[Function]()[{*x*}, *B*], *p*, *b*] == *b*</code>: transport in a constant family leaves *b* where it is.

## Details & Options

- [TransportConstant]() is a definition by path induction.
- It gives the path that circle induction into a constant family needs, as in the example of [CircleInduction]().
- It is a constant of <code>[TypeTheoryEnvironment]()["HomotopyTypeTheory"]</code>; terms that use it name that environment.

## Basic Examples

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

The statement of [TransportConstant]() in the HoTT environment:

```wl
TypeTheoryCheck[TypeTheoryTerm[TransportConstant, hott]]
```

<!-- => ∀_{A ∶ Type u} ∀_{B ∶ Type v} ∀_{x ∶ A} ∀_{y ∶ A} ∀_p∶x == y ∀_b∶B Transport[(w∶A) ↦ B, p, b] == b -->

---

The homotopy type theory environment:

```wl
hott = TypeTheoryEnvironment["HomotopyTypeTheory"]
```

<!-- => TypeTheoryEnvironment summary box: 41 constants -->

Around the loop of the circle:

```wl
TypeTheoryCheck[TypeTheoryTerm[TransportConstant[CircleLoop, "true"], hott]]
```

<!-- => Transport[(w∶𝕊¹) ↦ 𝔹, CircleLoop, true] == true -->
