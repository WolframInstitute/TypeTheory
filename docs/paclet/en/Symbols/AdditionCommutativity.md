---
Template: Symbol
Name: AdditionCommutativity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/AdditionCommutativity
Keywords: [addition, commutativity, prelude, natural numbers]
SeeAlso: [AdditionAssociativity, MultiplicationCommutativity, AdditionZeroLeft]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[AdditionCommutativity]()[*m*, *n*]</code> proves <code>*m* + *n* == *n* + *m*</code>.

## Details & Options

- [AdditionCommutativity]() is a theorem of the prelude, proved by induction on *n* from [AdditionZeroLeft]() and [AdditionSuccessorLeft]().

## Basic Examples

The statement of [AdditionCommutativity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[AdditionCommutativity]]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ m + n == n + m -->

---

So `x + 1` and `1 + x` are equal:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Naturals]}, AdditionCommutativity[x, 1]]]]
```

<!-- => ∀_x∶ℕ x + 1 == 1 + x -->

## Scope

The tactic `"Apply"` finds *m* and *n* from the goal:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals]}, x + 1 == 1 + x], {
    TypeTheoryTactic["Introduce", x],
    TypeTheoryTactic["Apply", AdditionCommutativity]
}]
```

<!-- => Proof complete -->

## Applications

With [FunctionExtensionality](), adding 1 on the right and adding 1 on the left are the same function:

```wl
TypeTheoryCheck[TypeTheoryTerm[FunctionExtensionality[Function[{Typed[n, Naturals]}, AdditionCommutativity[n, 1]]]]]
```

<!-- => ((n ∶ ℕ) ↦ n + 1) == ((n ∶ ℕ) ↦ 1 + n) -->

## Properties and Relations

The integers have the same law, [IntegerAdditionCommutativity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerAdditionCommutativity, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ ∀_y∶ℤ x + y == y + x -->

## Possible Issues

Without arguments, `"Rewrite"` swaps the first sum it finds, here `x + y`, and the goal stays open:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals], Typed[z, Naturals]}, x + y + z == z + (x + y)], {
    TypeTheoryTactic["Introduce", x, y, z],
    TypeTheoryTactic["Rewrite", AdditionCommutativity]
}]
```

<!-- => Proof, 1 goal: x ∶ ℕ, y ∶ ℕ, z ∶ ℕ ⊢ y + x + z == z + (y + x) -->

The arguments choose the sum to swap, `(x + y) + z`:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals], Typed[z, Naturals]}, x + y + z == z + (x + y)], {
    TypeTheoryTactic["Introduce", x, y, z],
    TypeTheoryTactic["Rewrite", AdditionCommutativity[x + y, z]]
}]
```

<!-- => Proof complete -->
