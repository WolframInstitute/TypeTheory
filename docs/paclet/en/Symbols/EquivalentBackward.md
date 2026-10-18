---
Template: Symbol
Name: EquivalentBackward
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/EquivalentBackward
Keywords: [equivalent, backward, prelude, logic]
SeeAlso: [EquivalentForward, EquivalentIntroduction, EquivalentSymmetry]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[EquivalentBackward]()[*h*]</code> proves <code>[Implies]()[*b*, *a*]</code> from a proof *h* of <code>[Equivalent]()[*a*, *b*]</code>.

## Details & Options

- [EquivalentBackward]() is a theorem of the prelude, the second field of the proof: `h[[2]]`.
- *a* and *b* are implicit arguments, found from the type of *h*.

## Basic Examples

The statement of [EquivalentBackward]():

```wl
TypeTheoryCheck[TypeTheoryTerm[EquivalentBackward]]
```

<!-- => ∀_{a∶Prop} ∀_{b∶Prop} (a ⧦ b) ⇒ b ⇒ a -->

---

From a proof of <code>[Equivalent]()[[True](), 1 == 1]</code>, a proof of [True]():

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[h, Equivalent[True, 1 == 1]]}, EquivalentBackward[h][EqualityReflexivity[1]]]]]
```

<!-- => (True ⧦ 1 == 1) ⇒ True -->
