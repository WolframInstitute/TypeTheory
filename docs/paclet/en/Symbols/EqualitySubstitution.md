---
Template: Symbol
Name: EqualitySubstitution
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/EqualitySubstitution
Keywords: [equality, substitution, rewriting, theorem, prelude]
SeeAlso: [EqualityReflexivity, EqualitySymmetry, EqualityTransitivity, EqualityCongruence]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[EqualitySubstitution]()[*h*, *p*]</code> proves <code>*P*[*y*]</code> from a proof *h* of <code>*x* == *y*</code> and a proof *p* of <code>*P*[*x*]</code>.

## Details & Options

- [EqualitySubstitution]() is a theorem of the prelude, <code>[TypeTheoryEnvironment]()["Prelude"]</code>, proved with the recursor of [Equal](): it rewrites with an equation.
- The type of *x* and *y*, its universe level, the predicate *P*, and *x* and *y* are implicit arguments. *P* is found from the type the proof is expected to have, by abstracting *y* from it; [Construct]() gives it explicitly.

## Basic Examples

The type of [EqualitySubstitution]():

```wl
TypeTheoryCheck[TypeTheoryTerm[EqualitySubstitution, TypeTheoryEnvironment["Prelude"]]]
```

<!-- => ∀_{α ∶ Sort u} ∀_{P ∶ α → Prop} ∀_{x ∶ α} ∀_{y ∶ α} x == y ⇒ P[x] ⇒ P[y] -->

---

Rewrite `x` to `y` in a statement:

```wl
TypeTheoryCheck[TypeTheoryTerm[
    Function[{Typed[x, NonNegativeIntegers], Typed[y, NonNegativeIntegers], Typed[h, x == y], Typed[p, x + 0 == x]}, Typed[EqualitySubstitution[h, p], y + 0 == y]],
    TypeTheoryEnvironment["Prelude"]
]]
```

<!-- => ∀_x∶ℕ ∀_y∶ℕ x == y ⇒ x + 0 == x ⇒ y + 0 == y -->

## Scope

Give the predicate explicitly with [Construct]():

```wl
TypeTheoryCheck[TypeTheoryTerm[
    Function[{Typed[x, NonNegativeIntegers], Typed[y, NonNegativeIntegers], Typed[h, x == y], Typed[p, x + 0 == x]},
        Construct[EqualitySubstitution, NonNegativeIntegers, Function[{Typed[t, NonNegativeIntegers]}, t + 0 == t], x, y, h, p]
    ],
    TypeTheoryEnvironment["Prelude"]
]]
```

<!-- => ∀_x∶ℕ ∀_y∶ℕ x == y ⇒ x + 0 == x ⇒ y + 0 == y -->
