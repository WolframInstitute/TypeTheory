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
