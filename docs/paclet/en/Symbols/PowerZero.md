---
Template: Symbol
Name: PowerZero
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/PowerZero
Keywords: [power, zero, prelude, natural numbers]
SeeAlso: [PowerSuccessor, PowerOne, Power]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[PowerZero]()[*m*]</code> proves <code>*m*^0 == 1</code>.

## Details & Options

- [PowerZero]() is a theorem of the prelude that holds by computation: [Power]() recurses on its second argument.

## Basic Examples

The statement of [PowerZero]():

```wl
TypeTheoryCheck[TypeTheoryTerm[PowerZero]]
```

<!-- => ∀_m∶ℕ m^0 == 1 -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[PowerZero[5]]]
```

<!-- => 5^0 == 1 -->

## Scope

The tactic `"Reflexivity"` proves it for a variable *m*, since `m^0` computes to 1:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals]}, m^0 == 1], {
    TypeTheoryTactic["Introduce", m],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Proof complete -->

---

The tactic `"Rewrite"` with it, then with [MultiplicationOneRight](), removes a factor `m^0`:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals], Typed[n, Naturals]}, n * m^0 == n], {
    TypeTheoryTactic["Introduce", m, n],
    TypeTheoryTactic["Rewrite", PowerZero[m]],
    TypeTheoryTactic["Rewrite", MultiplicationOneRight[n]]
}]
```

<!-- => Proof complete -->

## Possible Issues

It holds at 0 too, so `0^0` is 1 here, while the Wolfram Language's own [Power]() gives [Indeterminate]():

```wl
TypeTheoryCheck[TypeTheoryTerm[PowerZero[0]]]
```

<!-- => 0^0 == 1 -->
