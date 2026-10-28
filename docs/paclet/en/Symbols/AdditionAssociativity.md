---
Template: Symbol
Name: AdditionAssociativity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/AdditionAssociativity
Keywords: [addition, associativity, prelude, natural numbers]
SeeAlso: [AdditionCommutativity, MultiplicationAssociativity, AdditionSuccessorRight]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[AdditionAssociativity]()[*a*, *b*, *c*]</code> proves <code>*a* + *b* + *c* == *a* + (*b* + *c*)</code>.

## Details & Options

- [AdditionAssociativity]() is a theorem of the prelude, proved by induction on *c*.
- `a + b + c` is read from the left, as `(a + b) + c`.

## Basic Examples

The statement of [AdditionAssociativity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[AdditionAssociativity]]
```

<!-- => ∀_a∶ℕ ∀_b∶ℕ ∀_c∶ℕ a + b + c == a + (b + c) -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[AdditionAssociativity[1, 2, 3]]]
```

<!-- => 1 + 2 + 3 == 1 + (2 + 3) -->

## Scope

The tactic `"Rewrite"` regroups `a + b + c` inside a longer sum, and the goal closes:

```wl
TypeTheoryProof[ForAll[{Typed[a, Naturals], Typed[b, Naturals], Typed[c, Naturals], Typed[d, Naturals]}, a + b + c + d == a + (b + c) + d], {
    TypeTheoryTactic["Introduce", a, b, c, d],
    TypeTheoryTactic["Rewrite", AdditionAssociativity[a, b, c]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

The tactic `"Ring"` proves the same statement without naming the law:

```wl
TypeTheoryProof[ForAll[{Typed[a, Naturals], Typed[b, Naturals], Typed[c, Naturals]}, a + b + c == a + (b + c)], {
    TypeTheoryTactic["Introduce", a, b, c],
    TypeTheoryTactic["Ring"]
}]
```

<!-- => Proof complete -->

---

The integers have the same law, [IntegerAdditionAssociativity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerAdditionAssociativity, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ ∀_y∶ℤ ∀_z∶ℤ x + y + z == x + (y + z) -->

## Possible Issues

The tactic `"Reflexivity"` does not prove it for a variable *c*, since addition recurses on its second argument:

```wl
TypeTheoryProof[ForAll[{Typed[a, Naturals], Typed[b, Naturals], Typed[c, Naturals]}, a + b + c == a + (b + c)], {
    TypeTheoryTactic["Introduce", a, b, c],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Failure["NotReflexive", ...] -->

With a literal *c*, the two sides compute to the same term:

```wl
TypeTheoryProof[ForAll[{Typed[a, Naturals], Typed[b, Naturals]}, a + b + 2 == a + (b + 2)], {
    TypeTheoryTactic["Introduce", a, b],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Proof complete -->
