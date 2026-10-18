---
Template: Symbol
Name: Naturals
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Naturals
Keywords: [natural numbers, NonNegativeIntegers, Nat, alias, prelude]
SeeAlso: [NaturalNumberZero, NaturalNumberSuccessor, InductiveRecursor, TypeTheoryNaturalNumbers, TypeTheoryTerm]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TypeTheoryIntroduction, ThePrelude]
---

## Usage

[Naturals]() is [NonNegativeIntegers](), the natural numbers of the prelude, by a shorter name.

## Details & Options

- [Naturals]() evaluates to [NonNegativeIntegers](). Held in a term, it stands for the same constant: a symbol whose value is a declared constant stands for that constant.
- <code>[InductiveRecursor]()[[Naturals]()]</code> is the recursor of the natural numbers.
- [Naturals]() shows as ℕ, and terms and declarations read back with [NonNegativeIntegers](), the name of the constant.
- A symbol of your own given a declared constant as its value stands for it the same way, unless a binder of the same name is in scope. [True]() and the other names overloaded by type are left to their own rules.

## Basic Examples

[Naturals]() is [NonNegativeIntegers]():

```wl
Naturals
```

<!-- => NonNegativeIntegers -->

---

The successor function on the natural numbers:

```wl
TypeOf[TypeTheoryTerm[Function[{Typed[n, Naturals]}, n + 1]]]
```

<!-- => ℕ → ℕ -->

## Scope

The recursor of the natural numbers:

```wl
TypeTheoryCheck[TypeTheoryTerm[InductiveRecursor[Naturals]]]
```

<!-- => ∀_m∶ℕ → Sort u m[0] → (∀_n∶ℕ m[n] → m[n + 1]) → ∀_t∶ℕ m[t] -->

---

A proof by induction over the natural numbers:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, 0 + n == n], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Induction", n],
    TypeTheoryTactic["Reflexivity"],
    TypeTheoryTactic["Introduce", k, ih],
    TypeTheoryTactic["Exact", EqualityCongruence[NaturalNumberSuccessor, ih]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

A symbol of your own whose value is a constant stands for it too:

```wl
Counting = NonNegativeIntegers;
TypeOf[TypeTheoryTerm[Function[{Typed[k, Counting]}, k]]]
```

<!-- => ℕ → ℕ -->

## Possible Issues

A binder named [Naturals]() is a variable of its own:

```wl
TypeOf[TypeTheoryTerm[Function[{Typed[Naturals, TypeUniverse[1]], Typed[x, Naturals]}, x]]]
```

<!-- => ∀_Naturals∶Type Naturals → Naturals -->
