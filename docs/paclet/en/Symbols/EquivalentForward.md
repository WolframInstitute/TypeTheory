---
Template: Symbol
Name: EquivalentForward
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/EquivalentForward
Keywords: [equivalent, forward, prelude, logic]
SeeAlso: [EquivalentBackward, EquivalentIntroduction, EquivalentSymmetry]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[EquivalentForward]()[*h*]</code> proves <code>[Implies]()[*a*, *b*]</code> from a proof *h* of <code>[Equivalent]()[*a*, *b*]</code>.

## Details & Options

- [EquivalentForward]() is a theorem of the prelude, the first field of the proof: `h[[1]]`.
- *a* and *b* are implicit arguments, found from the type of *h*.

## Basic Examples

The statement of [EquivalentForward]():

```wl
TypeTheoryCheck[TypeTheoryTerm[EquivalentForward]]
```

<!-- => ∀_{a∶Prop} ∀_{b∶Prop} (a ⧦ b) ⇒ a ⇒ b -->

---

From a proof of <code>[Equivalent]()[[True](), 1 == 1]</code>, a proof of `1 == 1`:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[h, Equivalent[True, 1 == 1]]}, EquivalentForward[h][TrueIntroduction]]]]
```

<!-- => (True ⧦ 1 == 1) ⇒ 1 == 1 -->
