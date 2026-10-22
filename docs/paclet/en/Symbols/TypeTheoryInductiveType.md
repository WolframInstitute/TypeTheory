---
Template: Symbol
Name: TypeTheoryInductiveType
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryInductiveType
Keywords: [inductive type, constructor, recursor, structure, parameters, indices, positivity, mutual, mutually inductive, nested, environment]
SeeAlso: [InductiveRecursor, TypeTheoryEnvironment, TypeTheoryDefinition, TypeTheoryNaturalNumbers]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[TypeTheoryInductiveType]()[*name*, *type*, {*constructor1* -> *type1*, ...}]</code> declares the inductive type *name* with the given constructors, and its recursor <code>[InductiveRecursor]()[*name*]</code>, when added to a [TypeTheoryEnvironment]().

<code>[TypeTheoryInductiveType]()[{*name1* -> *type1*, ...}, {*constructor1* -> *type1*, ...}]</code> declares mutually inductive types, each constructor ending in one of them, and a recursor for each.

## Details & Options

- The kernel checks that the type and every constructor's type are types, that each constructor takes the parameters first and ends in *name* applied to them, that *name* occurs only strictly positively, and that, unless *name* is a proposition, no field lives in a larger universe.
- The recursor takes the parameters, a motive, one minor premise per constructor with an induction hypothesis for each recursive field, the indices, and the term to eliminate. A proposition eliminates only into propositions, unless it has at most one constructor whose fields are proofs or indices.
- Mutually inductive types share their parameters and universe, and a constructor's fields may mention any of them. The recursor of each takes a motive for every type of the block and the minor premises of all their constructors; an induction hypothesis uses the motive of the type its field ends in.
- A type may occur nested in the parameters of an inductive type declared before it, as in a tree whose children are a list of trees. As Lean's kernel does, the kernel checks such a type as a mutual block with the container, for those parameters: the recursor takes a motive for each container too, and <code>[InductiveRecursor]()[*name*, *k*]</code> is the recursor on the *k*th container.
- An inductive type with one constructor, no indices and no recursive fields is a structure: `t[[i]]` is its field `i`.
- The option `"Parameters" -> n` makes the first `n` arguments parameters, which every constructor takes first and passes on unchanged; [Automatic]() takes as many as every constructor allows.
- The option `"UniverseParameters" -> {u, ...}` lists the universe parameters; [Automatic]() takes the symbols and strings in universe levels, in the order they appear.

## Basic Examples

Lists of natural numbers, and their length by recursion:

```wl
lists = TypeTheoryEnvironment[{
    TypeTheoryInductiveType[NaturalList, TypeUniverse[1], {
        EmptyNaturalList -> NaturalList,
        ConsList -> ForAll[{Typed[h, Naturals], Typed[t, NaturalList]}, NaturalList]
    }],
    TypeTheoryDefinition[ListLength, Typed[
        Function[{Typed[l, NaturalList]}, InductiveRecursor[NaturalList][
            Function[{Typed[x, NaturalList]}, Naturals],
            0,
            Function[{Typed[h, Naturals], Typed[t, NaturalList], Typed[r, Naturals]}, r + 1],
            l
        ]],
        TypeSpecifier[{NaturalList} -> Naturals]
    ]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 154 constants -->

The length of a list of three numbers:

```wl
WeakHeadNormalForm[TypeTheoryTerm[ListLength[ConsList[5, ConsList[6, ConsList[7, EmptyNaturalList]]]], lists]]
```

<!-- => 3 -->

## Scope

Vectors: an inductive family indexed by its length:

```wl
vectors = TypeTheoryEnvironment[TypeTheoryInductiveType[
    NaturalVector,
    ForAll[{Typed[n, Naturals]}, TypeUniverse[1]],
    {
        VectorEmpty -> NaturalVector[0],
        VectorCons -> ForAll[{TypedImplicit[n, Naturals], Typed[h, Naturals], Typed[t, NaturalVector[n]]}, NaturalVector[n + 1]]
    }
]]
```

<!-- => TypeTheoryEnvironment summary box: 153 constants -->

The length in a vector's type is checked by computation:

```wl
TypeTheoryCheck[TypeTheoryTerm[VectorCons[1, VectorCons[2, VectorEmpty]], vectors], TypeTheoryTerm[NaturalVector[2]]]
```

<!-- => Success["TypeChecked", ...] -->

---

A structure, a pair of natural numbers:

```wl
pairs = TypeTheoryEnvironment[TypeTheoryInductiveType[
    NaturalPair,
    TypeUniverse[1],
    {NaturalPairIntroduction -> ForAll[{Typed[a, Naturals], Typed[b, Naturals]}, NaturalPair]}
]]
```

<!-- => TypeTheoryEnvironment summary box: 152 constants -->

Its fields are projections:

```wl
WeakHeadNormalForm[TypeTheoryTerm[NaturalPairIntroduction[3, 4][[2]], pairs]]
```

<!-- => 4 -->

---

Even and odd numbers, declared together, each defined through the other:

```wl
parity = TypeTheoryEnvironment[TypeTheoryInductiveType[
    {Even -> TypeSpecifier[{Naturals} -> TypeUniverse[0]], Odd -> TypeSpecifier[{Naturals} -> TypeUniverse[0]]},
    {
        EvenZero -> Even[0],
        EvenSuccessor -> ForAll[{TypedImplicit[n, Naturals], Typed[h, Odd[n]]}, Even[n + 1]],
        OddSuccessor -> ForAll[{TypedImplicit[n, Naturals], Typed[h, Even[n]]}, Odd[n + 1]]
    }
]]
```

<!-- => TypeTheoryEnvironment summary box: 156 constants -->

Three is odd:

```wl
TypeTheoryCheck[TypeTheoryTerm[OddSuccessor[EvenSuccessor[OddSuccessor[EvenZero]]], parity], TypeTheoryTerm[Odd[3]]]
```

<!-- => Success["TypeChecked", ...] -->

The recursor of either takes a motive for both:

```wl
TypeOf[TypeTheoryTerm[InductiveRecursor[Even], parity]]
```

<!-- => ∀_m1∶∀_x∶ℕ Even[x] → Prop ∀_m2∶∀_x∶ℕ Odd[x] → Prop m1[0, EvenZero] ⇒ (∀_{n∶ℕ} ∀_h∶Odd[n] m2[n, h] ⇒ m1[n + 1, EvenSuccessor[h]]) ⇒ (∀_{n∶ℕ} ∀_h∶Even[n] m1[n, h] ⇒ m2[n + 1, OddSuccessor[h]]) ⇒ ∀_{x∶ℕ} ∀_t∶Even[x] m1[x, t] -->

---

Trees whose children form a list of trees: the list type is declared first, and the tree is nested in it:

```wl
roses = TypeTheoryEnvironment[{
    TypeTheoryInductiveType[Chain, TypeSpecifier[{TypeUniverse[1]} -> TypeUniverse[1]], {
        ChainEmpty -> ForAll[{TypedImplicit[A, TypeUniverse[1]]}, Chain[A]],
        ChainLink -> ForAll[{TypedImplicit[A, TypeUniverse[1]], Typed[head, A], Typed[tail, Chain[A]]}, Chain[A]]
    }],
    TypeTheoryInductiveType[Rose, TypeUniverse[1], {RoseNode -> ForAll[{Typed[label, Naturals], Typed[children, Chain[Rose]]}, Rose]}]
}]
```

<!-- => TypeTheoryEnvironment summary box: 157 constants -->

The recursor of the trees takes a motive for the list too:

```wl
TypeOf[TypeTheoryTerm[InductiveRecursor[Rose], roses]]
```

<!-- => ∀_m1∶Rose → Sort u ∀_m2∶Chain[Rose] → Sort u (∀_label∶ℕ ∀_children∶Chain[Rose] m2[children] → m1[RoseNode[label, children]]) → m2[ChainEmpty] → (∀_head∶Rose ∀_tail∶Chain[Rose] m1[head] → m2[tail] → m2[ChainLink[head, tail]]) → ∀_t∶Rose m1[t] -->

## Possible Issues

A type that occurs negatively in its own constructor would make the theory inconsistent, and is rejected:

```wl
TypeTheoryEnvironment[TypeTheoryInductiveType[Bad, TypeUniverse[1], {
    BadIntroduction -> ForAll[{Typed[f, TypeSpecifier[{Bad} -> False]]}, Bad]
}]]
```

<!-- => Failure["NonPositiveOccurrence", ...] -->

---

A type nested in a parameter that its container uses negatively is not strictly positive either:

```wl
TypeTheoryEnvironment[{
    TypeTheoryInductiveType[Arrowy, TypeSpecifier[{TypeUniverse[1]} -> TypeUniverse[1]], {
        ArrowyMake -> ForAll[{TypedImplicit[A, TypeUniverse[1]], Typed[f, TypeSpecifier[{A} -> Naturals]]}, Arrowy[A]]
    }],
    TypeTheoryInductiveType[Loopy, TypeUniverse[1], {LoopyMake -> ForAll[{Typed[a, Arrowy[Loopy]]}, Loopy]}]
}]
```

<!-- => Failure["NonPositiveOccurrence", ...] -->
