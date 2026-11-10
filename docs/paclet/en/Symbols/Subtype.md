---
Template: Symbol
Name: Subtype
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Subtype
Keywords: [subtype, property, element, proof, refinement type, dependent pair, structure, proof irrelevance, prelude, classical logic]
SeeAlso: [ChosenWitness, Exists, Nonempty, DependentSum, CartesianProductType]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[Subtype]()[*P*]</code> is the type of the elements *x* of a type that come with a proof of <code>*P*[*x*]</code>.

## Details & Options

- [Subtype]() is an inductive type of the prelude, with the one constructor `"subtype"`. The type of the elements is an implicit argument, found from the type of *P*.
- A value `s` of <code>[Subtype]()[*P*]</code> is a structure of two parts: `s["element"]` is the element and `s["proof"]` the proof of its property. `s[[1]]` and `s[[2]]` are the same parts by their indices. The kernel checks the proof against the element: `"subtype"[x, h]` is in <code>[Subtype]()[*P*]</code> only if `h` proves <code>*P*[*x*]</code>.
- The element also goes by the name of the predicate's variable: for `s` of the type `Subtype[n |-> 2 <= n]`, `s["n"]` is `s["element"]`. Where the subtype is a definition whose predicate is one too, the element shows by that name, as `n["integer"]` for a machine integer `n` of <code>[TypeTheoryEnvironment]()["Machine"]</code>.
- The parts' own names come first: where the predicate's variable is itself called `proof`, `s["proof"]` is the proof, and the element is `s["element"]`.
- A name is how a part is written and shown, and no part of the term: the term is the part by its index. An output shows a named part in the brackets of a part, `s〚element〛`.
- Any two proofs of a proposition are equal, so two values with the same element are equal by computation, whatever proofs they hold.
- A value of a [Subtype]() is data, and its element computes. An element of the proposition <code>[Exists]()[*P*]</code> is a proof, which cannot be taken apart to compute its witness; [ChosenWitness]() chooses one, through a [Subtype]().
- For elements in `Sort u`, <code>[Subtype]()[*P*]</code> is in `Sort (max 1 u)`: it is a type of data even when its elements are proofs.
- [Subtype]() is declared with the prelude's classical declarations, with [ChosenWitness](), so <code>[TypeTheoryEnvironment]()["Constructive"]</code> does not have it.
- <code>[Subtype]()[[Function]()[{[Typed]()[*x*, *A*]}, *p*]]</code> displays as `{x ∶ A // p}`.

## Basic Examples

The type of [Subtype]():

```wl
TypeTheoryType[Subtype]
```

<!-- => ∀_{α ∶ Sort u} (α → Prop) → Sort (max 1 u) -->

---

The number 4 with a proof that it is at least 2, by computing the decision of `2 <= 4`:

```wl
TypeTheoryType[Typed["subtype"[4, "decideSoundness"["equalityReflexivity"["true"]]], Subtype[n |-> 2 <= n]]]
```

<!-- => {n ∶ ℕ // 2 <= n} -->

---

The proof of a value is of the property of its element:

```wl
TypeTheoryType[Typed[s, Subtype[n |-> 2 <= n]] |-> s["proof"]]
```

<!-- => ∀_s∶{n∶ℕ // 2 <= n} 2 <= s〚"element"〛 -->

## Scope

The element computes:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Typed["subtype"[4, "lessEqualStep"["lessEqualStep"["lessEqualReflexivity"]]], Subtype[n |-> 2 <= n]]["element"]]]
```

<!-- => 4 -->

---

The element is a number, so arithmetic applies to it:

```wl
TypeTheoryType[Typed[s, Subtype[n |-> 2 <= n]] |-> s["element"] + 1]
```

<!-- => {n ∶ ℕ // 2 <= n} → ℕ -->

---

The element by the name of the predicate's variable, and by its index, is the same term:

```wl
TypeTheoryProof[ForAll[{Typed[s, Subtype[n |-> 2 <= n]]}, s["n"] == s["element"] && s[[1]] == s["element"]], {
    "Introduce"[s], "Constructor", "Reflexivity", "Reflexivity"
}]
```

<!-- => Proof complete -->

---

The property of an element proves others, here that it is at least 1, with `"lessEqualTransitivity"`:

```wl
TypeTheoryProof[ForAll[{Typed[s, Subtype[n |-> 2 <= n]]}, 1 <= s["element"]], {
    "Introduce"[s],
    "Exact"["lessEqualTransitivity"["lessEqualStep"["lessEqualReflexivity"], s["proof"]]]
}]
```

<!-- => Proof complete -->

---

A subtype of types, those that have an element:

```wl
TypeTheoryType[Subtype[Typed[A, TypeUniverse[1]] |-> Nonempty[A]]]
```

<!-- => Type 1 -->

---

A subtype of the proofs of a proposition is still a type of data:

```wl
TypeTheoryType[Subtype[Typed[h, True] |-> True]]
```

<!-- => Type -->

---

An option of an element of a subtype, here the number 3 with the proof that its double is 6:

```wl
TypeTheoryType[Typed["some"["subtype"[3, "equalityReflexivity"[6]]], Option[Subtype[n |-> n + n == 6]]]]
```

<!-- => Option[{n ∶ ℕ // n + n == 6}] -->

## Applications

The even numbers, each made with its half as the witness of its property:

```wl
evens = TypeTheoryEnvironment[{TypeTheoryDefinition[EvenNumber, Typed[
    j |-> "subtype"[j + j, "existsIntroduction"[j, "equalityReflexivity"[j + j]]],
    TypeSpecifier[{Naturals} -> Subtype[n |-> Exists[{k}, k + k == n]]]
]]}]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

The even number of 3 is 6:

```wl
WeakHeadNormalForm[TypeTheoryTerm[EvenNumber[3]["element"], evens]]
```

<!-- => 6 -->

It comes with the proof that it is even:

```wl
TypeTheoryType[EvenNumber[3]["proof"], evens]
```

<!-- => ∃_k∶ℕ k + k == EvenNumber[3]〚"element"〛 -->

## Properties and Relations

Two elements with the same number are equal, whatever their proofs, here one by steps of the order and one by computation:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Typed["subtype"[4, "lessEqualStep"["lessEqualStep"["lessEqualReflexivity"]]], Subtype[n |-> 2 <= n]]],
    TypeTheoryTerm[Typed["subtype"[4, "decideSoundness"["equalityReflexivity"["true"]]], Subtype[n |-> 2 <= n]]]
]
```

<!-- => True -->

---

A value is its two parts, by computation:

```wl
TypeTheoryProof[ForAll[{Typed[s, Subtype[n |-> 2 <= n]]}, s == "subtype"[s["element"], s["proof"]]], {"Introduce"[s], "Reflexivity"}]
```

<!-- => Proof complete -->

---

A subtype is data, in `Type`:

```wl
TypeTheoryType[Subtype[n |-> 2 <= n]]
```

<!-- => Type -->

The existence of such a number is a proposition, in Prop:

```wl
TypeTheoryType[Exists[n |-> 2 <= n]]
```

<!-- => Prop -->

---

[ChosenWitness]() takes the first field of a [Subtype]() that `"choice"` chooses:

```wl
TypeTheoryEnvironment["Prelude"][ChosenWitness]
```

<!-- => definition ChosenWitness : ∀_{α∶Sort u} ∀_{P∶α → Prop} Exists[P] → α := {α∶Sort u} {P∶α → Prop} (h∶Exists[P]) ↦ choice[Exists_rec[(t∶Exists[P]) ↦ Nonempty[Subtype[P]], (w∶α) (k∶P[w]) ↦ nonempty[subtype[w, k]], h]]〚"element"〛 -->

## Possible Issues

A value of a subtype is not its element: [Plus]() takes `s["element"]`, not `s`:

```wl
TypeTheoryType[Typed[s, Subtype[n |-> 2 <= n]] |-> s + 1]
```

<!-- => Failure["TypeMismatch", ...] -->

---

A proof of the property of another number is rejected: the decision of `2 <= 1` computes to `"false"`:

```wl
TypeTheoryType[Typed["subtype"[1, "decideSoundness"["equalityReflexivity"["true"]]], Subtype[n |-> 2 <= n]]]
```

<!-- => Failure["TypeMismatch", ...] -->

---

A proof of an existential statement eliminates only into propositions, so it does not give an element of a [Subtype](); [ChosenWitness]() chooses one instead:

```wl
TypeTheoryType[Typed[h, Exists[n |-> n + n == 6]] |-> InductiveRecursor[Exists][Subtype[n |-> n + n == 6] &, {w, k} |-> "subtype"[w, k], h]]
```

<!-- => Failure["TypeMismatch", ...] -->

---

The constructive environment does not have [Subtype]():

```wl
TypeTheoryType[Subtype, "Constructive"]
```

<!-- => Failure["ElaborationFailed", ...] -->
