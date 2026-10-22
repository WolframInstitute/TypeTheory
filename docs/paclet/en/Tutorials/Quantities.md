---
Template: TechNote
Name: Quantities
Title: Erased and Affine Variables
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/tutorial/Quantities
Keywords: [quantities, affine, linear, erasure, erased arguments, quantitative type theory, BendTT, resources, rules]
RelatedGuides: [TypeTheory]
RelatedTutorials: [RulesAndComputation, ThePrelude]
---

Under rules with quantities, every binder says how many times the code that runs may use its variable: 0, never, so the variable is erased; 1, at most once, so it is affine; or Infinity, any number of times, the quantity of every binder written without one. This follows BendTT, an affine dependent type theory, and the quantitative type theory of McBride and Atkey. The kernel checks types as it always does, then counts how many times each variable is used outside the types, and rejects a function that uses its variable more than its quantity allows. The rules only ever reject more terms, so they are consistent whenever the calculus of inductive constructions is.

## Rules with Quantities

The rules of the prelude with the setting `"Quantities"`:

```wl
affineRules = TypeTheoryRules["CalculusOfInductiveConstructions", "Quantities" -> True]
```

<!-- => TypeTheoryRules summary box: CalculusOfInductiveConstructions -->

The prelude translated to them, with its axioms; every declaration checks again:

```wl
translated = TypeTheoryTranslate[TypeTheoryEnvironment["Prelude"], affineRules, "Axioms" -> True]
```

<!-- => Success["Translated", ...] -->

The translated prelude:

```wl
affinePrelude = translated["Environment"]
```

<!-- => TypeTheoryEnvironment summary box: 169 constants -->

## Binders with Quantities

A binder takes its quantity as the third argument of [Typed]() or [TypedImplicit](), and shows it before its variable, as Idris writes it. The identity, with its type argument erased and its argument affine:

```wl
identity = TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1], 0], Typed[x, A, 1]}, x], affinePrelude]
```

<!-- => {0 A ∶ Type} (1 x ∶ A) ↦ x -->

`A` appears only in the type of `x`, which is gone when the function runs, and `x` is used once. Its type:

```wl
TypeTheoryCheck[identity]
```

<!-- => ∀_{0 A ∶ Type} ∀_1 x∶A A -->

## The Live Check

The kernel counts the uses of each variable in the live parts of a term, the parts that run: everything but the types, and the arguments a function takes at quantity 0. A function that uses an affine variable twice does not check:

```wl
TypeTheoryEnvironment[affinePrelude, {TypeTheoryDefinition[DuplicatedPair, Function[{TypedImplicit[A, TypeUniverse[1], 0], Typed[x, A, 1]}, Pair[x, x]]]}]
```

<!-- => Failure["QuantityExceeded", ...] -->

Nor does one that uses an erased variable:

```wl
TypeTheoryEnvironment[affinePrelude, {TypeTheoryDefinition[ErasedUse, Function[{Typed[n, NonNegativeIntegers, 0]}, n]]}]
```

<!-- => Failure["QuantityExceeded", ...] -->

An argument counts as often as the binder that takes it says. An affine function may be applied once:

```wl
TypeTheoryEnvironment[affinePrelude, {TypeTheoryDefinition[ApplyOnce, Function[{TypedImplicit[A, TypeUniverse[1], 0], Typed[f, TypeSpecifier[{A} -> A], 1], Typed[x, A]}, f[x]]]}]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

But not twice:

```wl
TypeTheoryEnvironment[affinePrelude, {TypeTheoryDefinition[ApplyTwice, Function[{TypedImplicit[A, TypeUniverse[1], 0], Typed[f, TypeSpecifier[{A} -> A], 1], Typed[x, A]}, f[f[x]]]]}]
```

<!-- => Failure["QuantityExceeded", ...] -->

The functions of the prelude take their arguments at quantity Infinity, so an affine variable cannot be passed to one, which might copy it: `n + 1` uses an affine `n` more than once.

```wl
TypeTheoryEnvironment[affinePrelude, {TypeTheoryDefinition[AffineSuccessor, Function[{Typed[n, NonNegativeIntegers, 1]}, n + 1]]}]
```

<!-- => Failure["QuantityExceeded", ...] -->

An erased variable may appear where it is dead. The parameters of [EqualityReflexivity]() are erased, so the proof that an erased `n` equals itself checks:

```wl
TypeTheoryEnvironment[affinePrelude, {TypeTheoryTheorem[ErasedReflexivity, ForAll[{Typed[n, NonNegativeIntegers, 0]}, n == n], Function[{Typed[n, NonNegativeIntegers, 0]}, EqualityReflexivity[n]]]}]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

## Constructors and Recursors

The kernel gives the constructors and recursors of an inductive type their quantities. A constructor's parameters are erased, since the value it builds does not hold them:

```wl
TypeTheoryCheck[TypeTheoryTerm[Pair, affinePrelude]]
```

<!-- => ∀_{0 α ∶ Type u} ∀_{0 β ∶ Type v} α → β → CartesianProduct[α, β] -->

A recursor's parameters, motives and indices are erased too. The recursor of a type without a recursive field takes the value it matches, and its minor premises, once:

```wl
TypeTheoryCheck[TypeTheoryTerm[InductiveRecursor[CartesianProduct], affinePrelude]]
```

<!-- => ∀_{0 α ∶ Type u} ∀_{0 β ∶ Type v} ∀_0 m∶CartesianProduct[α, β] → Sort w ∀_1 Pair∶∀_x∶α ∀_y∶β m[Pair[x, y]] ∀_1 t∶CartesianProduct[α, β] m[t] -->

The recursor of a recursive type takes them any number of times, since a recursive call uses the parts of its argument again:

```wl
TypeTheoryCheck[TypeTheoryTerm[InductiveRecursor[NonNegativeIntegers], affinePrelude]]
```

<!-- => ∀_0 m∶ℕ → Sort u m[0] → (∀_n∶ℕ m[n] → m[n + 1]) → ∀_t∶ℕ m[t] -->

A match passes each field on at the quantity its constructor takes it. Pairs whose fields are affine, `A ⊗ B`, are an inductive type like any other, and a swap matches its pair once and uses each field once:

```wl
affine = TypeTheoryEnvironment[affinePrelude, {
    TypeTheoryInductiveType[CircleTimes, TypeSpecifier[{TypeUniverse[1], TypeUniverse[1]} -> TypeUniverse[1]], {
        Tensor -> ForAll[{TypedImplicit[A, TypeUniverse[1]], TypedImplicit[B, TypeUniverse[1]], Typed[a, A, 1], Typed[b, B, 1]}, CircleTimes[A, B]]
    }],
    TypeTheoryDefinition[Swap, Function[{TypedImplicit[A, TypeUniverse[1], 0], TypedImplicit[B, TypeUniverse[1], 0], Typed[p, CircleTimes[A, B], 1]},
        InductiveRecursor[CircleTimes][Function[{Typed[q, CircleTimes[A, B]]}, CircleTimes[B, A]], Function[{Typed[a, A], Typed[b, B]}, Tensor[b, a]], p]
    ]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 173 constants -->

The type of the swap:

```wl
TypeTheoryCheck[TypeTheoryTerm[Swap, affine]]
```

<!-- => ∀_{0 A ∶ Type} ∀_{0 B ∶ Type} ∀_1 p∶A ⊗ B B ⊗ A -->

It computes as any function does:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Swap[Tensor[1, 2]], affine]]
```

<!-- => Tensor[2, 1] -->

A field of an affine pair is affine in the match too, so the match may not copy it:

```wl
TypeTheoryEnvironment[affine, {TypeTheoryDefinition[CopyFirst, Function[{TypedImplicit[A, TypeUniverse[1], 0], TypedImplicit[B, TypeUniverse[1], 0], Typed[p, CircleTimes[A, B], 1]},
    InductiveRecursor[CircleTimes][Function[{Typed[q, CircleTimes[A, B]]}, CircleTimes[A, A]], Function[{Typed[a, A], Typed[b, B]}, Tensor[a, a]], p]
]]}]
```

<!-- => Failure["QuantityExceeded", ...] -->

The uses in the branches of a match add up, since each branch is part of the term until the match computes. An affine variable in both branches is used twice:

```wl
TypeTheoryEnvironment[affinePrelude, {TypeTheoryDefinition[Choose, Function[{TypedImplicit[A, TypeUniverse[1], 0], Typed[b, Booleans, 1], Typed[x, A, 1]},
    InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, A], x, x, b]
]]}]
```

<!-- => Failure["QuantityExceeded", ...] -->

Instead, each branch is a function that takes it, and the match is applied to it once, as BendTT's compiler binds a variable inside each branch:

```wl
TypeTheoryEnvironment[affinePrelude, {TypeTheoryDefinition[Choose, Function[{TypedImplicit[A, TypeUniverse[1], 0], Typed[b, Booleans, 1], Typed[x, A, 1]},
    InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, ForAll[{Typed[y, A, 1]}, A]], Function[{Typed[y, A]}, y], Function[{Typed[y, A]}, y], b][x]
]]}]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

## Function Types and Their Quantities

Two function types are the same only if their binders have the same quantity: a function that uses its argument once and one that may copy it have different types.

```wl
DefinitionallyEqualQ[TypeTheoryTerm[ForAll[{Typed[x, NonNegativeIntegers, 1]}, NonNegativeIntegers], affinePrelude], TypeTheoryTerm[TypeSpecifier[{NonNegativeIntegers} -> NonNegativeIntegers], affinePrelude]]
```

<!-- => False -->

A binder written without a quantity takes the one the expected type gives it:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{x}, x], affinePrelude], TypeTheoryTerm[ForAll[{Typed[x, NonNegativeIntegers, 1]}, NonNegativeIntegers], affinePrelude]]
```

<!-- => Success["TypeChecked", ...] -->

## Back to Rules Without Quantities

A translation to rules without quantities drops them, and every declaration checks again:

```wl
back = TypeTheoryTranslate[affine, TypeTheoryRules["CalculusOfInductiveConstructions"], "Axioms" -> True]
```

<!-- => Success["Translated", ...] -->

The swap there:

```wl
TypeTheoryCheck[TypeTheoryTerm[Swap, back["Environment"]]]
```

<!-- => ∀_{A ∶ Type} ∀_{B ∶ Type} A ⊗ B → B ⊗ A -->

Under rules without quantities, the prelude's among them, a binder may not have one:

```wl
TypeTheoryEnvironment[{TypeTheoryDefinition[AffineIdentity, Function[{Typed[n, NonNegativeIntegers, 1]}, n]]}]
```

<!-- => Failure["QuantitiesNotAllowed", ...] -->

## What Quantities Do Not Change

The rules with quantities are the calculus of inductive constructions with a check added, so everything that checks under them checks without them, and their consistency is that of the calculus. BendTT goes further: its consistency rests on affine code, so it drops universe levels for a single universe that contains itself, and the positivity of inductive types. Those are not rules TypeTheory has; nothing here depends on them. The quotient types keep the quantity Infinity on all their binders, so a lift takes its class any number of times.
