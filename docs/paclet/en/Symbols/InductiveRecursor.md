---
Template: Symbol
Name: InductiveRecursor
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/InductiveRecursor
Keywords: [recursor, induction, recursion, eliminator, inductive type, motive]
SeeAlso: [TypeTheoryInductiveType, TypeTheoryTactic, WeakHeadNormalForm]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[InductiveRecursor]()[*type*]</code> is the recursor of the inductive type *type*, generated when the type is declared.

<code>[InductiveRecursor]()[*type*, *k*]</code> is the recursor on the *k*th container that *type*, or a type declared with it, is nested in.

## Details & Options

- Its arguments are the type's parameters (implicit), a motive, one minor premise per constructor, the indices (implicit) and the term to eliminate. For types declared together, or nested in containers, there is a motive for each type and container, and a minor premise for each of their constructors, as in Lean.
- A minor premise takes the constructor's fields and an induction hypothesis for each recursive field; applied to a constructor, the recursor reduces to its minor premise.
- The recursor is how definitions recurse and how proofs go by induction: the tactic `"Induction"` builds an application of it.

## Basic Examples

The recursor of the natural numbers:

```wl
TypeOf[TypeTheoryTerm[InductiveRecursor[Naturals]]]
```

<!-- => ∀_m∶ℕ → Sort u m[0] → (∀_n∶ℕ m[n] → m[n + 1]) → ∀_t∶ℕ m[t] -->

---

Recursion: double a natural number, adding 2 for each successor:

```wl
double = TypeTheoryTerm[Function[{Typed[n, Naturals]}, InductiveRecursor[Naturals][
    Function[{Typed[t, Naturals]}, Naturals],
    0,
    Function[{Typed[k, Naturals], Typed[r, Naturals]}, r + 2],
    n
]]]
```

<!-- => (n ∶ ℕ) ↦ rec[(t ∶ ℕ) ↦ ℕ, 0, (k ∶ ℕ)(r ∶ ℕ) ↦ r + 2, n] -->

Applied to 5, it computes:

```wl
WeakHeadNormalForm[TypeTheoryTerm[double[5]]]
```

<!-- => 10 -->

---

Rose trees, each with a chain of rose trees as its children:

```wl
roses = TypeTheoryEnvironment[{
    TypeTheoryInductiveType[Chain, TypeSpecifier[{TypeUniverse[1]} -> TypeUniverse[1]], {
        ChainEmpty -> ForAll[{TypedImplicit[A, TypeUniverse[1]]}, Chain[A]],
        ChainLink -> ForAll[{TypedImplicit[A, TypeUniverse[1]], Typed[head, A], Typed[tail, Chain[A]]}, Chain[A]]
    }],
    TypeTheoryInductiveType[Rose, TypeUniverse[1], {RoseNode -> ForAll[{Typed[label, Naturals], Typed[children, Chain[Rose]]}, Rose]}]
}]
```

<!-- => TypeTheoryEnvironment summary box: 166 constants -->

A tree nested in a list of trees has a recursor on the list as well, with the same motives and minor premises:

```wl
TypeOf[TypeTheoryTerm[InductiveRecursor[Rose, 1], roses]]
```

<!-- => ∀_m1∶Rose → Sort u ∀_m2∶Chain[Rose] → Sort u (∀_label∶ℕ ∀_children∶Chain[Rose] m2[children] → m1[RoseNode[label, children]]) → m2[ChainEmpty] → (∀_head∶Rose ∀_tail∶Chain[Rose] m1[head] → m2[tail] → m2[ChainLink[head, tail]]) → ∀_t∶Chain[Rose] m2[t] -->
