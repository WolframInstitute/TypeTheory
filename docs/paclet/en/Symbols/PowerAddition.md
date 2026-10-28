---
Template: Symbol
Name: PowerAddition
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/PowerAddition
Keywords: [power, addition, prelude, natural numbers]
SeeAlso: [PowerSuccessor, MultiplicationAssociativity, Power]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[PowerAddition]()[*m*, *a*, *b*]</code> proves <code>*m*^(*a* + *b*) == *m*^*a* * *m*^*b*</code>.

## Details & Options

- [PowerAddition]() is a theorem of the prelude, proved by induction on *b* with [MultiplicationAssociativity]().

## Basic Examples

The statement of [PowerAddition]():

```wl
TypeTheoryCheck[TypeTheoryTerm[PowerAddition]]
```

<!-- => ∀_m∶ℕ ∀_a∶ℕ ∀_b∶ℕ m^(a + b) == m^a m^b -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[PowerAddition[2, 3, 4]]]
```

<!-- => 2^(3 + 4) == 2^3 2^4 -->

## Scope

In a proof, an instance with a literal exponent splits off a square:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals], Typed[a, Naturals]}, m^(a + 2) == m^a * m^2], {
    TypeTheoryTactic["Introduce", m, a],
    TypeTheoryTactic["Exact", PowerAddition[m, a, 2]]
}]
```

<!-- => Proof complete -->

---

The tactic `"Rewrite"` with it, then with [MultiplicationCommutativity](), puts the factors in the other order:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals], Typed[a, Naturals], Typed[b, Naturals]}, m^(a + b) == m^b * m^a], {
    TypeTheoryTactic["Introduce", m, a, b],
    TypeTheoryTactic["Rewrite", PowerAddition[m, a, b]],
    TypeTheoryTactic["Rewrite", MultiplicationCommutativity[m^a, m^b]]
}]
```

<!-- => Proof complete -->

## Possible Issues

The tactic `"Ring"` takes a power by a variable as an atom, so it does not prove the law:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals], Typed[a, Naturals], Typed[b, Naturals]}, m^(a + b) == m^a * m^b], {
    TypeTheoryTactic["Introduce", m, a, b],
    TypeTheoryTactic["Ring"]
}]
```

<!-- => Failure["NotRingEquation", ...] -->
