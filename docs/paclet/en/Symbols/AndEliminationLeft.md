---
Template: Symbol
Name: AndEliminationLeft
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/AndEliminationLeft
Keywords: [And, conjunction, elimination, theorem, prelude, logic]
SeeAlso: [AndEliminationRight, AndIntroduction, TypeTheoryProof]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[AndEliminationLeft]()[*h*]</code> proves *a* from a proof *h* of <code>[And]()[*a*, *b*]</code>.

## Details & Options

- [AndEliminationLeft]() is a theorem of the prelude, <code>[TypeTheoryEnvironment]()["Prelude"]</code>, proved with the recursor of [And]().
- *a* and *b* are implicit arguments, found from the type of *h*.
- <code>[AndEliminationLeft]()[*h*]</code> proves what the field `h[[1]]` proves.

## Basic Examples

The type of [AndEliminationLeft]():

```wl
TypeTheoryCheck[TypeTheoryTerm[AndEliminationLeft, TypeTheoryEnvironment["Prelude"]]]
```

<!-- => ∀_{a ∶ Prop} ∀_{b ∶ Prop} (a && b) ⇒ a -->

---

Conjunction is commutative:

```wl
proof = TypeTheoryProof[ForAll[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]]}, Implies[And[a, b], And[b, a]]], TypeTheoryEnvironment["Prelude"], {
    TypeTheoryTactic["Introduce", a, b, h],
    TypeTheoryTactic["Exact", AndIntroduction[AndEliminationRight[h], AndEliminationLeft[h]]]
}]
```

<!-- => Proof complete -->

The proof term:

```wl
proof["Term"]
```

<!-- => (a ∶ Prop) (b ∶ Prop) (h ∶ a && b) ↦ AndIntroduction[AndEliminationRight[h], AndEliminationLeft[h]] -->
