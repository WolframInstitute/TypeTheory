---
Template: Symbol
Name: AndEliminationRight
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/AndEliminationRight
Keywords: [And, conjunction, elimination, theorem, prelude, logic]
SeeAlso: [AndEliminationLeft, AndIntroduction, TypeTheoryProof]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[AndEliminationRight]()[*h*]</code> proves *b* from a proof *h* of <code>[And]()[*a*, *b*]</code>.

## Details & Options

- [AndEliminationRight]() is a theorem of the prelude, proved with the recursor of [And]().
- *a* and *b* are implicit arguments, found from the type of *h*.
- <code>[AndEliminationRight]()[*h*]</code> proves what the field `h[[2]]` proves.

## Basic Examples

The type of [AndEliminationRight]():

```wl
TypeTheoryCheck[TypeTheoryTerm[AndEliminationRight]]
```

<!-- => ∀_{a ∶ Prop} ∀_{b ∶ Prop} (a ∧ b) ⇒ b -->

---

Use it on a hypothesis:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[h, And[True, 1 == 1]]}, AndEliminationRight[h]]]]
```

<!-- => (True ∧ 1 == 1) ⇒ 1 == 1 -->
