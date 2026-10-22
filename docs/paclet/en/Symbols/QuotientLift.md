---
Template: Symbol
Name: QuotientLift
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/QuotientLift
Keywords: [quotient, lift, function on classes, Quot.lift, Lean, computation, prelude]
SeeAlso: [QuotientType, QuotientIntroduction, QuotientInduction, TypeTheoryQuotients]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude, RulesAndComputation]
---

## Usage

<code>[QuotientLift]()[*f*, *h*, *q*]</code> applies the function *f* to the class *q*, given a proof *h* that <code>*f*[*a*] == *f*[*b*]</code> whenever <code>*r*[*a*, *b*]</code>.

## Details & Options

- [QuotientLift]() is a constant of the kernel, declared by [TypeTheoryQuotients]() in the prelude, as Lean's `Quot.lift`.
- The type α, the relation *r* and the codomain of *f* are implicit arguments.
- It computes on a class: <code>[QuotientLift]()[*f*, *h*, [QuotientIntroduction]()[*r*, *a*]]</code> is *f*[*a*]. This is one of the two computation rules of quotients.
- *h* is what makes the lift well defined: two related elements, whose classes are equal by [QuotientSoundness](), give the same value.

## Basic Examples

The type of [QuotientLift]():

```wl
TypeTheoryCheck[TypeTheoryTerm[QuotientLift]]
```

<!-- => ∀_{α ∶ Sort u} ∀_{r ∶ α → α → Prop} ∀_{β ∶ Sort v} ∀_f∶α → β (∀_a∶α ∀_b∶α r[a, b] ⇒ f[a] == f[b]) → QuotientType[r] → β -->

---

The quotient of the natural numbers by equality:

```wl
equal = TypeTheoryTerm[Typed[Function[{Typed[m, Naturals], Typed[n, Naturals]}, m == n], TypeSpecifier[{Naturals, Naturals} -> TypeUniverse[0]]]]
```

<!-- => (m ∶ ℕ) (n ∶ ℕ) ↦ m == n ∶ ℕ → ℕ → Prop -->

The successor respects equality, so it lifts to the classes, and computes on one:

```wl
WeakHeadNormalForm[TypeTheoryTerm[QuotientLift[
    Function[{Typed[k, Naturals]}, k + 1],
    Function[{Typed[a, Naturals], Typed[b, Naturals], Typed[e, a == b]}, EqualityCongruence[Function[{Typed[k, Naturals]}, k + 1], e]],
    QuotientIntroduction[equal, 5]
]]]
```

<!-- => 6 -->

## Possible Issues

A function lifts only with a proof that it respects the relation:

```wl
equal = TypeTheoryTerm[Typed[Function[{Typed[m, Naturals], Typed[n, Naturals]}, m == n], TypeSpecifier[{Naturals, Naturals} -> TypeUniverse[0]]]]
```

<!-- => (m ∶ ℕ) (n ∶ ℕ) ↦ m == n ∶ ℕ → ℕ → Prop -->

A wrong proof is refused:

```wl
TypeTheoryCheck[TypeTheoryTerm[QuotientLift[Function[{Typed[k, Naturals]}, 7], Function[{Typed[a, Naturals], Typed[b, Naturals], Typed[e, a == b]}, EqualityReflexivity[a]], QuotientIntroduction[equal, 5]]]]
```

<!-- => Failure["TypeMismatch", ...] -->
