---
Template: TechNote
Name: InstancesAndCoercions
Title: Instances and Coercions
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/tutorial/InstancesAndCoercions
Keywords: [instance, type class, instance-implicit, coercion, Decidable, decide, elaboration, Lean]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TypeTheoryIntroduction, ThePrelude, RulesAndComputation]
---

Lean leaves out more than implicit arguments. An argument in square brackets, `[Decidable p]`, is found by type class resolution among the instances, and a term of the wrong type gets a coercion, `↑x`, in front of it. TypeTheory's elaborator does both. A definition declared with `"Instance" -> True` is an instance of the class its type ends in, and fills an argument of an instance-implicit binder; a definition declared with `"Coercion" -> True` is applied where a term's type is not the one its place expects. Neither is trusted: the kernel checks every term that elaboration builds with them.

## A Class and Its Instances

A class is a type like any other. `Inhabited[α]` holds one element of α, and `Default` takes that element from an instance-implicit argument, a binder written <code>[Annotation]()[[Typed]()[*h*, *class*], "InstanceImplicit"]</code>:

```wl
inhabited = TypeTheoryEnvironment[{
    TypeTheoryInductiveType[Inhabited, ForAll[{Typed[\[Alpha], TypeUniverse[u + 1]]}, TypeUniverse[u + 1]], {
        InhabitedIntroduction -> ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[x, \[Alpha]]}, Inhabited[\[Alpha]]]
    }],
    TypeTheoryDefinition[Default, Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Annotation[Typed[h, Inhabited[\[Alpha]]], "InstanceImplicit"]}, h[[1]]]],
    TypeTheoryDefinition[NaturalsInhabited, Typed[InhabitedIntroduction[0], Inhabited[Naturals]], "Instance" -> True],
    TypeTheoryDefinition[BooleansInhabited, Typed[InhabitedIntroduction["false"], Inhabited[Booleans]], "Instance" -> True]
}]
```

<!-- => TypeTheoryEnvironment summary box: 175 constants -->

`Default` where a natural number is expected finds the instance for the naturals, and computes to its element:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Typed[Default, Naturals], inhabited]]
```

<!-- => 0 -->

Where a Boolean is expected, it finds the other:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Typed[Default, Booleans], inhabited]]
```

<!-- => false -->

An instance shows as one, as Lean's `instance` declarations do:

```wl
inhabited[NaturalsInhabited]
```

<!-- => instance NaturalsInhabited : Inhabited[ℕ] := InhabitedIntroduction[0] -->

## Instances from Instances

An instance may take instance-implicit arguments of its own, found in turn: a pair is inhabited when both its components' types are, and a list always is:

```wl
pairs = TypeTheoryEnvironment[inhabited, {
    TypeTheoryDefinition[ListsInhabited, Typed[
        Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]]}, InhabitedIntroduction[EmptyList]],
        ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]]}, Inhabited[Lists[\[Alpha]]]]
    ], "Instance" -> True],
    TypeTheoryDefinition[PairInhabited, Typed[
        Function[
            {TypedImplicit[\[Alpha], TypeUniverse[u + 1]], TypedImplicit[\[Beta], TypeUniverse[v + 1]], Annotation[Typed[h, Inhabited[\[Alpha]]], "InstanceImplicit"], Annotation[Typed[k, Inhabited[\[Beta]]], "InstanceImplicit"]},
            InhabitedIntroduction[Pair[h[[1]], k[[1]]]]
        ],
        ForAll[
            {TypedImplicit[\[Alpha], TypeUniverse[u + 1]], TypedImplicit[\[Beta], TypeUniverse[v + 1]], Annotation[Typed[h, Inhabited[\[Alpha]]], "InstanceImplicit"], Annotation[Typed[k, Inhabited[\[Beta]]], "InstanceImplicit"]},
            Inhabited[CartesianProductType[\[Alpha], \[Beta]]]
        ]
    ], "Instance" -> True]
}]
```

<!-- => TypeTheoryEnvironment summary box: 177 constants -->

A default pair of a number and a list of Booleans comes from three instances:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Typed[Default, CartesianProductType[Naturals, Lists[Booleans]]], pairs]]
```

<!-- => (NaturalsInhabited〚1〛, ListsInhabited〚1〛) -->

The instances are tried the latest declared first, at most 32 deep. Where none applies, elaboration fails:

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed[Default, Option[Naturals]], pairs]]
```

<!-- => Failure["NoInstance", ...] -->

## Local Instances

Inside a function, a variable bound by an instance-implicit binder is an instance itself, found before any of the environment's, as Lean's local instances are. `DefaultPair` gets both its components from its argument `h`:

```wl
defaultPairs = TypeTheoryEnvironment[pairs, {
    TypeTheoryDefinition[DefaultPair, Function[
        {TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Annotation[Typed[h, Inhabited[\[Alpha]]], "InstanceImplicit"]},
        Pair[Typed[Default, \[Alpha]], Typed[Default, \[Alpha]]]
    ]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 178 constants -->

At the naturals it is a pair of zeros:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Typed[DefaultPair, CartesianProductType[Naturals, Naturals]], defaultPairs], TypeTheoryTerm[Pair[0, 0], defaultPairs]]
```

<!-- => True -->

## Decisions

The prelude's decisions are instances. [Decide]() takes a proposition and finds its decision, a term of <code>[Decidable]()[*p*]</code>, among them; [Less]() and [Unequal]() unfold to propositions that have one:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[2 < 3 && 4 != 5]]]
```

<!-- => true -->

The tactic `"Decide"` asks elaboration for the decision of its goal too, so an environment extends it with instances of its own. The prelude decides no [Nonempty]() type:

```wl
TypeTheoryProof[Nonempty[Naturals], {TypeTheoryTactic["Decide"]}]
```

<!-- => Failure["NotDecidable", ...] -->

An instance deciding that the naturals are nonempty is enough:

```wl
TypeTheoryProof[Nonempty[Naturals], TypeTheoryEnvironment[{
    TypeTheoryDefinition[NaturalsNonempty, Typed[DecidableTrue[NonemptyIntroduction[0]], Decidable[Nonempty[Naturals]]], "Instance" -> True]
}], {TypeTheoryTactic["Decide"]}]
```

<!-- => Proof complete -->

## Coercions

A coercion is a function of one explicit argument declared with `"Coercion" -> True`. Here the Booleans become natural numbers, true as 1, and any element becomes its option:

```wl
coercions = TypeTheoryEnvironment[{
    TypeTheoryDefinition[NaturalOfBoolean, Function[{Typed[b, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Naturals], 0, 1, b]], "Coercion" -> True],
    TypeTheoryDefinition[OptionOf, Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[x, \[Alpha]]}, OptionSome[x]], "Coercion" -> True]
}]
```

<!-- => TypeTheoryEnvironment summary box: 171 constants -->

`"true"` where a natural number is expected becomes `NaturalOfBoolean["true"]`, which computes to 1:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Typed["true", Naturals], coercions]]
```

<!-- => 1 -->

An argument is coerced the same way:

```wl
WeakHeadNormalForm[TypeTheoryTerm[NaturalNumberSuccessor["true"], coercions]]
```

<!-- => NaturalOfBoolean[true] + 1 -->

Coercions chain, at most three of them: a Boolean where an optional natural number is expected becomes a number, then its option:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Typed["true", Option[Naturals]], coercions]]
```

<!-- => OptionSome[NaturalOfBoolean[true]] -->

Both types must be known: a coercion is inserted only where no metavariable is left in either, as Lean waits for them. With no coercion that applies, the term's type is a mismatch:

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed[EmptyList, Naturals], coercions]]
```

<!-- => Failure["TypeMismatch", ...] -->

## The Kernel Checks Them

Instances and coercions are definitions. The kernel checks them as it checks any definition, and every term that elaboration builds with them, so a mistake in finding one can make elaboration fail, never let an ill-typed term through:

```wl
TypeTheoryCheck[coercions]
```

<!-- => Success["EnvironmentChecked", ...] -->

An instance whose value does not have its type is refused when it is declared:

```wl
TypeTheoryEnvironment[inhabited, {TypeTheoryDefinition[WrongInstance, Typed[InhabitedIntroduction["true"], Inhabited[Naturals]], "Instance" -> True]}]
```

<!-- => Failure["TypeMismatch", ...] -->
