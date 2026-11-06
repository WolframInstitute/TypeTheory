---
Template: Symbol
Name: Nonempty
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Nonempty
Keywords: [nonempty, inhabited, element, choice, prelude, classical logic, axiom of choice, proof irrelevance, large elimination]
SeeAlso: [Exists, Subtype, ChosenWitness, Decidable]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[Nonempty]()[*a*]</code> is the proposition that the type *a* has an element.

## Details & Options

- [Nonempty]() is an inductive proposition of the prelude, with the one constructor `"nonempty"`, which takes an element of *a*, as Lean's `Nonempty`.
- A proof of <code>[Nonempty]()[*a*]</code> says that *a* has an element without giving one to compute with: any two proofs of it are equal, whatever elements they were made with. `"Cases"` takes a proof apart only to prove a proposition.
- The axiom `"choice"` takes a proof of <code>[Nonempty]()[*a*]</code> to an element of *a*, which does not compute. [ChosenWitness]() chooses a witness of an existential statement with it.
- *a* may be in any universe, a proposition among them.

## Basic Examples

The type of [Nonempty]():

```wl
TypeTheoryType[Nonempty]
```

<!-- => Sort u → Prop -->

---

The natural numbers are not empty, since 0 is one:

```wl
TypeTheoryType["nonempty"[0]]
```

<!-- => Nonempty[ℕ] -->

---

The constructor takes an element of any type:

```wl
TypeTheoryType["nonempty"]
```

<!-- => ∀_{α∶Sort u} α → Nonempty[α] -->

## Scope

The type may be a proposition: a proof of [True]() shows that [True]() has a proof:

```wl
TypeTheoryType["nonempty"["trueIntroduction"]]
```

<!-- => Nonempty[True] -->

---

A function is an element of a function type:

```wl
TypeTheoryType["nonempty"[Typed[n, Naturals] |-> n + 1]]
```

<!-- => Nonempty[ℕ → ℕ] -->

---

The universe of types has the natural numbers as an element:

```wl
TypeTheoryType["nonempty"[Naturals]]
```

<!-- => Nonempty[Type] -->

---

An element of a [Subtype]() shows that some number has the property, here that its double is 6:

```wl
TypeTheoryType[Typed["nonempty"["subtype"[3, "equalityReflexivity"[6]]], Nonempty[Subtype[Typed[n, Naturals] |-> n + n == 6]]]]
```

<!-- => Nonempty[{n ∶ ℕ // n + n == 6}] -->

## Applications

An element of a type gives a pair: `"Cases"` takes a proof of [Nonempty]() apart, which it may, since the goal is a proposition:

```wl
proof = TypeTheoryProof[ForAll[{Typed[A, TypeUniverse[1]], Typed[h, Nonempty[A]]}, Nonempty[CartesianProductType[A, A]]], {
    "Introduce"[A, h],
    "Cases"[h],
    "Introduce"[x]
}]
```

<!-- => Proof, 1 goal: A ∶ Type, x ∶ A ⊢ Nonempty[A × A] -->

The pair of the element with itself:

```wl
TypeTheoryTactic["Exact", "nonempty"["pair"[x, x]]][proof]
```

<!-- => Proof complete -->

---

A function into a nonempty type exists, the constant function of an element:

```wl
TypeTheoryProof[ForAll[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]], Typed[h, Nonempty[B]]}, Nonempty[TypeSpecifier[{A} -> B]]], {
    "Introduce"[A, B, h],
    "Cases"[h],
    "Introduce"[b],
    "Exact"["nonempty"[Typed[a, A] |-> b]]
}]
```

<!-- => Proof complete -->

---

A proof of an existential statement gives an element of the type of its witness:

```wl
TypeTheoryProof[ForAll[{Typed[h, Exists[Typed[n, Naturals] |-> n + n == 6]]}, Nonempty[Naturals]], {
    "Introduce"[h],
    "Cases"[h],
    "Introduce"[w, hw],
    "Exact"["nonempty"[w]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

Any two proofs of [Nonempty]() are equal, here those made with 0 and with 5:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Typed["nonempty"[0], Nonempty[Naturals]]], TypeTheoryTerm[Typed["nonempty"[5], Nonempty[Naturals]]]]
```

<!-- => True -->

---

`"choice"` takes a proof of [Nonempty]() to an element:

```wl
TypeTheoryType[Typed[h, Nonempty[Naturals]] |-> "choice"[h]]
```

<!-- => Nonempty[ℕ] → ℕ -->

---

Since the proofs are equal, the element `"choice"` gives does not depend on the element a proof was made with:

```wl
DefinitionallyEqualQ[TypeTheoryTerm["choice"["nonempty"[0]]], TypeTheoryTerm["choice"["nonempty"[5]]]]
```

<!-- => True -->

---

A proposition with no proof is empty: from a proof that [False]() has a proof, [False]() follows:

```wl
TypeTheoryProof[Implies[Nonempty[False], False], {
    "Introduce"[h],
    "Cases"[h],
    "Introduce"[x],
    "Exact"[x]
}]
```

<!-- => Proof complete -->

## Possible Issues

A proof of [Nonempty]() can be taken apart only to prove a proposition, not to compute data such as a natural number; `"choice"` gives an element instead:

```wl
TypeTheoryProof[ForAll[{Typed[h, Nonempty[Naturals]]}, Naturals], {"Introduce"[h], "Cases"[h]}]
```

<!-- => Failure["LargeElimination", ...] -->

---

`"choice"` is an axiom and does not compute, so the element it chooses from a proof made with 3 is not 3 by computation:

```wl
TypeTheoryProof["choice"["nonempty"[3]] == 3, {"Reflexivity"}]
```

<!-- => Failure["NotReflexive", ...] -->
