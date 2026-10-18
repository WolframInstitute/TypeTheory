---
Template: Symbol
Name: FalseElimination
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/FalseElimination
Keywords: [False, absurdity, ex falso, elimination, theorem, prelude, logic]
SeeAlso: [TrueIntroduction, TypeTheoryProof, TypeTheoryTactic]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[FalseElimination]()[*h*]</code> proves any proposition from a proof *h* of [False]().

## Details & Options

- [False]() is the inductive proposition of the prelude with no constructors. [FalseElimination]() is a theorem, proved with its recursor.
- The proposition proved is an implicit argument, found from the type the proof is expected to have.
- <code>[Not]()[*p*]</code> is defined as <code>[Implies]()[*p*, [False]()]</code>, so a proof of <code>[Not]()[*p*]</code> applied to a proof of *p* is a proof of [False]().

## Basic Examples

The type of [FalseElimination]():

```wl
TypeTheoryCheck[TypeTheoryTerm[FalseElimination, TypeTheoryEnvironment["Prelude"]]]
```

<!-- => ∀_{a ∶ Prop} False ⇒ a -->

---

From [False](), even `2 + 2 == 5` follows:

```wl
TypeTheoryProof[Implies[False, 2 + 2 == 5], TypeTheoryEnvironment["Prelude"], {
    TypeTheoryTactic["Introduce", h],
    TypeTheoryTactic["Exact", FalseElimination[h]]
}]
```

<!-- => Proof complete -->

## Scope

A proposition and its negation prove anything:

```wl
TypeTheoryProof[ForAll[{Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]]}, Implies[p, Implies[Not[p], q]]], TypeTheoryEnvironment["Prelude"], {
    TypeTheoryTactic["Introduce", p, q, hp, hnp],
    TypeTheoryTactic["Exact", FalseElimination[hnp[hp]]]
}]
```

<!-- => Proof complete -->
