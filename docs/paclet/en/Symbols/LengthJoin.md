---
Template: Symbol
Name: LengthJoin
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/LengthJoin
Keywords: [list, length, join, addition, prelude]
SeeAlso: [LengthReverse, LengthMap, Lists]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[LengthJoin]()[*a*, *b*]</code> proves <code>[Length]()[[Join]()[*a*, *b*]] == [Length]()[*a*] + [Length]()[*b*]</code>.

## Details & Options

- [LengthJoin]() is a theorem of the prelude, proved by recursion on *a*, from [AdditionZeroLeft]() and [AdditionSuccessorLeft]().

## Basic Examples

The statement of [LengthJoin]():

```wl
TypeTheoryCheck[TypeTheoryTerm[LengthJoin]]
```

<!-- => ∀_{α ∶ Type u} ∀_a∶Lists[α] ∀_b∶Lists[α] Length[Join[a, b]] == Length[a] + Length[b] -->

---

For lists of natural numbers:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[a, Lists[Naturals]], Typed[b, Lists[Naturals]]}, LengthJoin[a, b]]]]
```

<!-- => ∀_a∶Lists[ℕ] ∀_b∶Lists[ℕ] Length[Join[a, b]] == Length[a] + Length[b] -->

## Scope

The tactic `"Simplify"` rewrites with it and other laws until the goal closes:

```wl
TypeTheoryProof[ForAll[{Typed[a, Lists[Naturals]], Typed[b, Lists[Naturals]]}, Length[Reverse[Join[a, b]]] == Length[b] + Length[a]], {
	TypeTheoryTactic["Introduce", a, b],
	TypeTheoryTactic["Simplify", {LengthReverse, LengthJoin, AdditionCommutativity}]
}]
```

<!-- => Proof complete -->
