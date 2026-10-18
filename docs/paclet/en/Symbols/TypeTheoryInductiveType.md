---
Template: Symbol
Name: TypeTheoryInductiveType
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryInductiveType
Keywords: [inductive type, constructor, recursor, structure, parameters, indices, positivity, environment]
SeeAlso: [InductiveRecursor, TypeTheoryEnvironment, TypeTheoryDefinition, TypeTheoryNaturalNumbers]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[TypeTheoryInductiveType]()[*name*, *type*, {*constructor1* -> *type1*, ...}]</code> declares the inductive type *name* with the given constructors, and its recursor <code>[InductiveRecursor]()[*name*]</code>, when added to a [TypeTheoryEnvironment]().

## Details & Options

- The kernel checks that the type and every constructor's type are types, that each constructor takes the parameters first and ends in *name* applied to them, that *name* occurs only strictly positively, and that, unless *name* is a proposition, no field lives in a larger universe.
- The recursor takes the parameters, a motive, one minor premise per constructor with an induction hypothesis for each recursive field, the indices, and the term to eliminate. A proposition eliminates only into propositions, unless it has at most one constructor whose fields are proofs or indices.
- An inductive type with one constructor, no indices and no recursive fields is a structure: `t[[i]]` is its field `i`.
- The option `"Parameters" -> n` makes the first `n` arguments parameters, which every constructor takes first and passes on unchanged; [Automatic]() takes as many as every constructor allows.
- The option `"UniverseParameters" -> {u, ...}` lists the universe parameters; [Automatic]() takes the symbols and strings in universe levels, in the order they appear.

## Basic Examples

Lists of natural numbers, and their length by recursion:

```wl
lists = TypeTheoryEnvironment[TypeTheoryEnvironment["Prelude"], {
    TypeTheoryInductiveType[NaturalList, TypeUniverse[1], {
        EmptyList -> NaturalList,
        ConsList -> ForAll[{Typed[h, NonNegativeIntegers], Typed[t, NaturalList]}, NaturalList]
    }],
    TypeTheoryDefinition[ListLength, Typed[
        Function[{Typed[l, NaturalList]}, InductiveRecursor[NaturalList][
            Function[{Typed[x, NaturalList]}, NonNegativeIntegers],
            0,
            Function[{Typed[h, NonNegativeIntegers], Typed[t, NaturalList], Typed[r, NonNegativeIntegers]}, r + 1],
            l
        ]],
        TypeSpecifier[{NaturalList} -> NonNegativeIntegers]
    ]]
}];
WeakHeadNormalForm[TypeTheoryTerm[ListLength[ConsList[5, ConsList[6, ConsList[7, EmptyList]]]], lists]]
```

<!-- => 3 -->

## Scope

Vectors: an inductive family indexed by its length, which is checked by computation:

```wl
vectors = Append[TypeTheoryEnvironment["Prelude"], TypeTheoryInductiveType[
    NaturalVector,
    ForAll[{Typed[n, NonNegativeIntegers]}, TypeUniverse[1]],
    {
        VectorEmpty -> NaturalVector[0],
        VectorCons -> ForAll[{Annotation[Typed[n, NonNegativeIntegers], "Implicit"], Typed[h, NonNegativeIntegers], Typed[t, NaturalVector[n]]}, NaturalVector[n + 1]]
    }
]];
TypeTheoryCheck[TypeTheoryTerm[VectorCons[1, VectorCons[2, VectorEmpty]], vectors], TypeTheoryTerm[NaturalVector[2]]]
```

<!-- => True -->

---

A structure, whose fields are projections:

```wl
pairs = Append[TypeTheoryEnvironment["Prelude"], TypeTheoryInductiveType[
    NaturalPair,
    TypeUniverse[1],
    {NaturalPairIntroduction -> ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, NaturalPair]}
]];
WeakHeadNormalForm[TypeTheoryTerm[NaturalPairIntroduction[3, 4][[2]], pairs]]
```

<!-- => 4 -->

## Possible Issues

A type that occurs negatively in its own constructor would make the theory inconsistent, and is rejected:

```wl
Append[TypeTheoryEnvironment["Prelude"], TypeTheoryInductiveType[Bad, TypeUniverse[1], {
    BadIntroduction -> ForAll[{Typed[f, TypeSpecifier[{Bad} -> False]]}, Bad]
}]]
```

<!-- => Failure["NonPositiveOccurrence", ...] -->
