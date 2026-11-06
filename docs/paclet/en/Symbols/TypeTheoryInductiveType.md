---
Template: Symbol
Name: TypeTheoryInductiveType
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryInductiveType
Keywords: [inductive type, constructor, recursor, structure, enumeration, binary tree, parameters, indices, inductive family, inductive predicate, positivity, mutual, mutually inductive, nested, induction, environment]
SeeAlso: [InductiveRecursor, TypeTheoryEnvironment, TypeTheoryDefinition, TypeTheoryNaturalNumbers, TypeTheoryProof]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TypeTheoryIntroduction, ThePrelude]
---

## Usage

<code>[TypeTheoryInductiveType]()[*name*, *type*, {*constructor1* -> *type1*, ...}]</code> declares the inductive type *name* with the given constructors, and its recursor <code>[InductiveRecursor]()[*name*]</code>, when added to a [TypeTheoryEnvironment]().

<code>[TypeTheoryInductiveType]()[{*name1* -> *type1*, ...}, {*constructor1* -> *type1*, ...}]</code> declares mutually inductive types, each constructor ending in one of them, and a recursor for each.

## Details & Options

- *type* is the type of *name*: a universe, such as <code>[TypeUniverse]()[1]</code> for a type of data or <code>[TypeUniverse]()[0]</code> for a proposition, or a function type into one, whose arguments are the parameters and indices.
- The kernel checks that the type and every constructor's type are types, that each constructor takes the parameters first and ends in *name* applied to them, that *name* occurs only strictly positively, and that, unless *name* is a proposition, no field lives in a larger universe.
- The recursor takes the parameters, a motive, one minor premise per constructor with an induction hypothesis for each recursive field, the indices, and the term to eliminate. Applied to a constructor, it computes to that constructor's minor premise. The tactics `"Induction"` and `"Cases"` of [TypeTheoryProof]() use it.
- A proposition eliminates only into propositions, unless it has at most one constructor whose fields are proofs or indices.
- Mutually inductive types share their parameters and universe, and a constructor's fields may mention any of them. The recursor of each takes a motive for every type of the block and the minor premises of all their constructors; an induction hypothesis uses the motive of the type its field ends in.
- A type may occur nested in the parameters of an inductive type declared before it, as in a tree whose children are a list of trees. As Lean's kernel does, the kernel checks such a type as a mutual block with the container, for those parameters: the recursor takes a motive for each container too, and <code>[InductiveRecursor]()[*name*, *k*]</code> is the recursor on the *k*th container.
- An inductive type with one constructor, no indices and no recursive fields is a structure: `t[[i]]` is its field `i`.
- The option `"Parameters" -> n` makes the first `n` arguments parameters, which every constructor takes first and passes on unchanged; [Automatic]() takes as many as every constructor allows. The other arguments are indices, which a constructor may give any value.
- The option `"UniverseParameters" -> {u, ...}` lists the universe parameters; [Automatic]() takes the symbols and strings in universe levels, in the order they appear.

## Basic Examples

Binary trees, each a leaf or a node with two subtrees:

```wl
trees = TypeTheoryEnvironment[{TypeTheoryInductiveType[BinaryTree, TypeUniverse[1], {
    BinaryLeaf -> BinaryTree,
    BinaryNode -> ForAll[{Typed[left, BinaryTree], Typed[right, BinaryTree]}, BinaryTree]
}]}]
```

<!-- => TypeTheoryEnvironment summary box: 261 constants -->

The declaration adds the type, its constructors and its recursor:

```wl
Take[Keys[trees], -4]
```

<!-- => {BinaryTree, BinaryLeaf, BinaryNode, InductiveRecursor[BinaryTree]} -->

The recursor has a case for each constructor, with an induction hypothesis for each subtree:

```wl
TypeTheoryType[InductiveRecursor[BinaryTree], trees]
```

<!-- => ∀_m∶BinaryTree → Sort u m[BinaryLeaf] → (∀_left∶BinaryTree ∀_right∶BinaryTree m[left] → m[right] → m[BinaryNode[left, right]]) → ∀_t∶BinaryTree m[t] -->

Counting the nodes of a tree with it: a leaf has one, and a node one more than its two subtrees together:

```wl
counted = Append[trees, TypeTheoryDefinition[NodeCount, Typed[
    Function[{Typed[tree, BinaryTree]}, InductiveRecursor[BinaryTree][
        Function[{Typed[t, BinaryTree]}, Naturals],
        1,
        Function[{Typed[left, BinaryTree], Typed[right, BinaryTree], Typed[l, Naturals], Typed[r, Naturals]}, l + r + 1],
        tree
    ]],
    TypeSpecifier[{BinaryTree} -> Naturals]
]]]
```

<!-- => TypeTheoryEnvironment summary box: 262 constants -->

A node over a leaf and a node of two leaves has five nodes:

```wl
WeakHeadNormalForm[TypeTheoryTerm[NodeCount[BinaryNode[BinaryLeaf, BinaryNode[BinaryLeaf, BinaryLeaf]]], counted]]
```

<!-- => 5 -->

## Scope

An enumeration, the lights of a traffic light, and the light that follows each:

```wl
lights = TypeTheoryEnvironment[{
    TypeTheoryInductiveType[TrafficLight, TypeUniverse[1], {LightRed -> TrafficLight, LightAmber -> TrafficLight, LightGreen -> TrafficLight}],
    TypeTheoryDefinition[NextLight, Typed[
        Typed[l, TrafficLight] |-> InductiveRecursor[TrafficLight][Typed[t, TrafficLight] |-> TrafficLight, LightGreen, LightRed, LightAmber, l],
        TypeSpecifier[{TrafficLight} -> TrafficLight]
    ]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 263 constants -->

Two steps after red:

```wl
WeakHeadNormalForm[TypeTheoryTerm[NextLight[NextLight[LightRed]], lights]]
```

<!-- => LightAmber -->

Three steps come back to every light, by cases on the light:

```wl
TypeTheoryProof[ForAll[{Typed[l, TrafficLight]}, NextLight[NextLight[NextLight[l]]] == l], lights, {"Introduce"[l], "Cases"[l], "Reflexivity", "Reflexivity", "Reflexivity"}]
```

<!-- => Proof complete -->

---

A type with a parameter, binary trees with a label of any type at each leaf:

```wl
labelled = TypeTheoryEnvironment[{TypeTheoryInductiveType[LabelledTree, ForAll[{Typed[A, TypeUniverse[1]]}, TypeUniverse[1]], {
    LabelledLeaf -> ForAll[{TypedImplicit[A, TypeUniverse[1]], Typed[label, A]}, LabelledTree[A]],
    LabelledNode -> ForAll[{TypedImplicit[A, TypeUniverse[1]], Typed[left, LabelledTree[A]], Typed[right, LabelledTree[A]]}, LabelledTree[A]]
}]}]
```

<!-- => TypeTheoryEnvironment summary box: 261 constants -->

The parameter is found from the labels:

```wl
TypeTheoryType[LabelledNode[LabelledLeaf[1], LabelledLeaf[2]], labelled]
```

<!-- => LabelledTree[ℕ] -->

The recursor takes the parameter first, implicitly:

```wl
TypeTheoryType[InductiveRecursor[LabelledTree], labelled]
```

<!-- => ∀_{A∶Type} ∀_m∶LabelledTree[A] → Sort u (∀_label∶A m[LabelledLeaf[label]]) → (∀_left∶LabelledTree[A] ∀_right∶LabelledTree[A] m[left] → m[right] → m[LabelledNode[left, right]]) → ∀_t∶LabelledTree[A] m[t] -->

---

An inductive family, vectors indexed by their length:

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

<!-- => TypeTheoryEnvironment summary box: 261 constants -->

The length in a vector's type is checked by computation:

```wl
TypeTheoryCheck[TypeTheoryTerm[VectorCons[1, VectorCons[2, VectorEmpty]], vectors], TypeTheoryTerm[NaturalVector[2]]]
```

<!-- => Success["TypeChecked", ...] -->

A vector of two numbers is not of length 3:

```wl
TypeTheoryCheck[TypeTheoryTerm[VectorCons[1, VectorCons[2, VectorEmpty]], vectors], TypeTheoryTerm[NaturalVector[3]]]
```

<!-- => Failure["TypeMismatch", ...] -->

---

An inductive predicate, the even numbers, a proposition for each natural number:

```wl
evens = TypeTheoryEnvironment[TypeTheoryInductiveType[EvenNumber, TypeSpecifier[{Naturals} -> TypeUniverse[0]], {
    EvenZero -> EvenNumber[0],
    EvenStep -> ForAll[{TypedImplicit[n, Naturals], Typed[h, EvenNumber[n]]}, EvenNumber[n + 2]]
}]]
```

<!-- => TypeTheoryEnvironment summary box: 261 constants -->

6 is even, by the constructors applied in turn:

```wl
TypeTheoryProof[EvenNumber[6], evens, {"Constructor", "Constructor", "Constructor", "Constructor"}]
```

<!-- => Proof complete -->

---

A structure, a pair of natural numbers:

```wl
pairs = TypeTheoryEnvironment[TypeTheoryInductiveType[
    NaturalPair,
    TypeUniverse[1],
    {NaturalPairIntroduction -> ForAll[{Typed[a, Naturals], Typed[b, Naturals]}, NaturalPair]}
]]
```

<!-- => TypeTheoryEnvironment summary box: 260 constants -->

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

<!-- => TypeTheoryEnvironment summary box: 264 constants -->

Three is odd:

```wl
TypeTheoryCheck[TypeTheoryTerm[OddSuccessor[EvenSuccessor[OddSuccessor[EvenZero]]], parity], TypeTheoryTerm[Odd[3]]]
```

<!-- => Success["TypeChecked", ...] -->

The recursor of either takes a motive for both:

```wl
TypeTheoryType[InductiveRecursor[Even], parity]
```

<!-- => ∀_m1∶∀_x∶ℕ Even[x] → Prop ∀_m2∶∀_x∶ℕ Odd[x] → Prop m1[0, EvenZero] ⇒ (∀_{n∶ℕ} ∀_h∶Odd[n] m2[n, h] ⇒ m1[n + 1, EvenSuccessor[h]]) ⇒ (∀_{n∶ℕ} ∀_h∶Even[n] m1[n, h] ⇒ m2[n + 1, OddSuccessor[h]]) ⇒ ∀_{x∶ℕ} ∀_t∶Even[x] m1[x, t] -->

---

Trees whose children are a list of trees, nested in the prelude's [List]():

```wl
roses = TypeTheoryEnvironment[{TypeTheoryInductiveType[Rose, TypeUniverse[1], {
    RoseNode -> ForAll[{Typed[label, Naturals], Typed[children, {Rose}]}, Rose]
}]}]
```

<!-- => TypeTheoryEnvironment summary box: 261 constants -->

The declaration adds a recursor on the trees and one on their lists:

```wl
Take[Keys[roses], -4]
```

<!-- => {Rose, RoseNode, InductiveRecursor[Rose], InductiveRecursor[Rose, 1]} -->

The recursor of the trees takes a motive for the lists too:

```wl
TypeTheoryType[InductiveRecursor[Rose], roses]
```

<!-- => ∀_m1∶Rose → Sort u ∀_m2∶{Rose} → Sort u (∀_label∶ℕ ∀_children∶{Rose} m2[children] → m1[RoseNode[label, children]]) → m2[{}] → (∀_x∶Rose ∀_l∶{Rose} m1[x] → m2[l] → m2[Prepend[l, x]]) → ∀_t∶Rose m1[t] -->

The sum of the labels of a tree, by that recursor:

```wl
labelSums = Append[roses, TypeTheoryDefinition[LabelSum, Typed[
    Typed[r, Rose] |-> InductiveRecursor[Rose][
        Typed[t, Rose] |-> Naturals,
        Typed[l, {Rose}] |-> Naturals,
        {Typed[label, Naturals], Typed[children, {Rose}], Typed[s, Naturals]} |-> label + s,
        0,
        {Typed[x, Rose], Typed[l, {Rose}], Typed[a, Naturals], Typed[b, Naturals]} |-> a + b,
        r
    ],
    TypeSpecifier[{Rose} -> Naturals]
]]]
```

<!-- => TypeTheoryEnvironment summary box: 262 constants -->

The labels of a tree of four nodes add up to 10:

```wl
WeakHeadNormalForm[TypeTheoryTerm[LabelSum[RoseNode[1, {RoseNode[2, {}], RoseNode[3, {RoseNode[4, {}]}]}]], labelSums]]
```

<!-- => 10 -->

## Options

### Parameters

With [Automatic](), a type argument that every constructor passes on unchanged is a parameter. With `"Parameters" -> 0` it is an index, which a constructor takes as a field, so the type must live a universe up:

```wl
indexed = TypeTheoryEnvironment[{TypeTheoryInductiveType[Labelled, ForAll[{Typed[A, TypeUniverse[1]]}, TypeUniverse[2]], {
    LabelledIntroduction -> ForAll[{TypedImplicit[A, TypeUniverse[1]], Typed[label, A]}, Labelled[A]]
}, "Parameters" -> 0]}]
```

<!-- => TypeTheoryEnvironment summary box: 260 constants -->

Its declaration:

```wl
indexed[Labelled]
```

<!-- => inductive Labelled : Type → Type 1 | LabelledIntroduction : ∀_{A∶Type} A → Labelled[A] -->

The motive of its recursor takes the index:

```wl
TypeTheoryType[InductiveRecursor[Labelled], indexed]
```

<!-- => ∀_m∶∀_A∶Type Labelled[A] → Sort u (∀_{A∶Type} ∀_label∶A m[A, LabelledIntroduction[label]]) → ∀_{A∶Type} ∀_t∶Labelled[A] m[A, t] -->

---

A constructor must take the parameters first, so a family whose second argument varies has one parameter:

```wl
TypeTheoryEnvironment[{TypeTheoryInductiveType[Sized, ForAll[{Typed[A, TypeUniverse[1]], Typed[n, Naturals]}, TypeUniverse[1]], {
    SizedEmpty -> ForAll[{TypedImplicit[A, TypeUniverse[1]]}, Sized[A, 0]],
    SizedCons -> ForAll[{TypedImplicit[A, TypeUniverse[1]], TypedImplicit[n, Naturals], Typed[h, A], Typed[t, Sized[A, n]]}, Sized[A, n + 1]]
}, "Parameters" -> 2]}]
```

<!-- => Failure["ConstructorParameters", ...] -->

### UniverseParameters

The universe parameters named explicitly:

```wl
TypeTheoryEnvironment[{TypeTheoryInductiveType[Crate, ForAll[{Typed[A, TypeUniverse[v + 1]]}, TypeUniverse[v + 1]], {
    CrateIntroduction -> ForAll[{TypedImplicit[A, TypeUniverse[v + 1]], Typed[x, A]}, Crate[A]]
}, "UniverseParameters" -> {v}]}][Crate]
```

<!-- => inductive Crate : Type v → Type v | CrateIntroduction : ∀_{A∶Type v} A → Crate[A] -->

## Applications

A proof by induction on trees: mirroring a tree twice gives it back. Trees and their mirror image:

```wl
mirrored = TypeTheoryEnvironment[{
    TypeTheoryInductiveType[BinaryTree, TypeUniverse[1], {
        BinaryLeaf -> BinaryTree,
        BinaryNode -> ForAll[{Typed[left, BinaryTree], Typed[right, BinaryTree]}, BinaryTree]
    }],
    TypeTheoryDefinition[Mirror, Typed[
        Function[{Typed[tree, BinaryTree]}, InductiveRecursor[BinaryTree][
            Function[{Typed[t, BinaryTree]}, BinaryTree],
            BinaryLeaf,
            Function[{Typed[left, BinaryTree], Typed[right, BinaryTree], Typed[l, BinaryTree], Typed[r, BinaryTree]}, BinaryNode[r, l]],
            tree
        ]],
        TypeSpecifier[{BinaryTree} -> BinaryTree]
    ]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 262 constants -->

The mirror image of a tree:

```wl
NormalForm[TypeTheoryTerm[Mirror[BinaryNode[BinaryLeaf, BinaryNode[BinaryLeaf, BinaryLeaf]]], mirrored]]
```

<!-- => BinaryNode[BinaryNode[BinaryLeaf, BinaryLeaf], BinaryLeaf] -->

`"Induction"` gives a case for each constructor; in the case of a node, the goal computes to an equation of nodes, which the induction hypotheses rewrite:

```wl
TypeTheoryProof[ForAll[{Typed[t, BinaryTree]}, Mirror[Mirror[t]] == t], mirrored, {
    "Introduce"[t],
    "Induction"[t],
    "Reflexivity",
    "Introduce"[l, r, hl, hr],
    "Change"[BinaryNode[Mirror[Mirror[l]], Mirror[Mirror[r]]] == BinaryNode[l, r]],
    "Rewrite"[hl],
    "Rewrite"[hr]
}]
```

<!-- => Proof complete -->

## Properties and Relations

Binary trees:

```wl
trees = TypeTheoryEnvironment[{TypeTheoryInductiveType[BinaryTree, TypeUniverse[1], {
    BinaryLeaf -> BinaryTree,
    BinaryNode -> ForAll[{Typed[left, BinaryTree], Typed[right, BinaryTree]}, BinaryTree]
}]}]
```

<!-- => TypeTheoryEnvironment summary box: 261 constants -->

A constructor is a function into its type:

```wl
TypeTheoryType[BinaryNode, trees]
```

<!-- => BinaryTree → BinaryTree → BinaryTree -->

---

The prelude's lists are an inductive type with a parameter, as its declaration shows:

```wl
TypeTheoryEnvironment["Prelude"][List]
```

<!-- => inductive List : Type u → Type u | {} : ∀_{α∶Type u} {α} | Prepend : ∀_{α∶Type u} α → {α} → {α} -->

---

A structure, a pair of natural numbers:

```wl
pairs = TypeTheoryEnvironment[TypeTheoryInductiveType[NaturalPair, TypeUniverse[1], {
    NaturalPairIntroduction -> ForAll[{Typed[a, Naturals], Typed[b, Naturals]}, NaturalPair]
}]]
```

<!-- => TypeTheoryEnvironment summary box: 260 constants -->

A pair is equal by computation to the pair of its fields:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Typed[p, NaturalPair] |-> NaturalPairIntroduction[p[[1]], p[[2]]], pairs], TypeTheoryTerm[Typed[p, NaturalPair] |-> p, pairs]]
```

<!-- => True -->

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

---

A type of data may not hold a type of its own universe, which would make the theory inconsistent:

```wl
TypeTheoryEnvironment[TypeTheoryInductiveType[TypeHolder, TypeUniverse[1], {TypeHolderIntroduction -> ForAll[{Typed[A, TypeUniverse[1]]}, TypeHolder]}]]
```

<!-- => Failure["UniverseTooLarge", ...] -->

---

A constructor must end in the type it constructs:

```wl
TypeTheoryEnvironment[TypeTheoryInductiveType[Broken, TypeUniverse[1], {BrokenIntroduction -> Naturals}]]
```

<!-- => Failure["ConstructorResult", ...] -->

---

A proposition with two constructors eliminates only into propositions, so no function to the natural numbers can tell its proofs apart:

```wl
TypeTheoryEnvironment[{
    TypeTheoryInductiveType[Hidden, TypeUniverse[0], {HiddenA -> Hidden, HiddenB -> Hidden}],
    TypeTheoryDefinition[Reveal, Typed[Typed[h, Hidden] |-> InductiveRecursor[Hidden][Typed[t, Hidden] |-> Naturals, 0, 1, h], TypeSpecifier[{Hidden} -> Naturals]]]
}]
```

<!-- => Failure["TypeMismatch", ...] -->
