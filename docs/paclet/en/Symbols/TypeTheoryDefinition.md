---
Template: Symbol
Name: TypeTheoryDefinition
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryDefinition
Keywords: [definition, declaration, function, unfolding, environment, universe polymorphism, instance, type class, coercion, opaque]
SeeAlso: [TypeTheoryEnvironment, TypeTheoryAxiom, TypeTheoryTheorem, WeakHeadNormalForm, Decidable]
RelatedGuides: [TypeTheory]
RelatedTutorials: [InstancesAndCoercions]
---

## Usage

<code>[TypeTheoryDefinition]()[*name*, *value*]</code> declares *name* as a definition with the given *value*, when added to a [TypeTheoryEnvironment]().

<code>[TypeTheoryDefinition]()[*name*, [Typed]()[*value*, *type*]]</code> gives the definition the given *type*.

## Details & Options

- A definition unfolds: computation replaces *name* by *value*. A definition may not mention itself; recursion goes through a recursor, [InductiveRecursor]().
- Without a type, the definition has the type of *value*.
- The option `"UniverseParameters" -> {u, ...}` lists the universe parameters; [Automatic]() takes the symbols and strings in universe levels, in the order they appear.
- The option `"Instance" -> True` makes the definition an instance of its class, the constant its type applies at the end, under its binders, as Lean's `instance`. Elaboration fills an argument of an instance-implicit binder, <code>[Annotation]()[[Typed]()[*x*, *class*], "InstanceImplicit"]</code>, with a variable bound by such a binder, or else with the first instance whose type unifies with the binder's, the latest declared first, finding the instance's own instance-implicit arguments in turn.
- The option `"Coercion" -> True` makes a function of one explicit argument, after its implicit ones, a coercion, as Lean's `@[coe]`: where a term's type does not unify with the one expected, elaboration applies the coercion from the one to the other, or a chain of at most three.
- An instance or a coercion is a definition as any other: the kernel checks it, and every term elaboration builds with it.
- The option `"Opaque" -> True` makes the definition opaque, as Lean's `opaque`: the kernel checks *value* against the type, but the definition never unfolds, so it equals only itself. Unlike an axiom of its type, it cannot make the theory inconsistent, since *value* is an element of the type.
- The option `"Overloads" -> *operation*`, for [Plus](), [Times](), [Subtract](), [Power](), [Minus](), [LessEqual](), [Less](), [GreaterEqual]() or [Greater](), makes the constant one more meaning of the operation, chosen by the types of its arguments and the type expected, as the integers' and rationals' operations are: an axiom `"polynomialAddition"` declared with `"Overloads" -> Plus` lets `p + q` add two polynomials, and shows as `p + q`.

## Basic Examples

Define doubling:

```wl
doubled = TypeTheoryEnvironment[TypeTheoryDefinition[Double, Function[{Typed[n, Naturals]}, n + n]]]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

Compute with it:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Double[21], doubled]]
```

<!-- => 42 -->

Its type:

```wl
TypeOf[TypeTheoryTerm[Double, doubled]]
```

<!-- => ℕ → ℕ -->

## Scope

The identity function on a type in any universe:

```wl
identity = TypeTheoryEnvironment[
    TypeTheoryDefinition[PolymorphicIdentity, Function[{TypedImplicit[A, TypeUniverse[u]], Typed[x, A]}, x]]
]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

A universe-polymorphic definition is used at each universe:

```wl
TypeOf[TypeTheoryTerm[PolymorphicIdentity[3], identity]]
```

<!-- => ℕ -->

Applied to a type, it is used one universe up:

```wl
TypeOf[TypeTheoryTerm[PolymorphicIdentity[Naturals], identity]]
```

<!-- => Type -->

---

The composition of two functions, applied to an argument:

```wl
composite = TypeTheoryEnvironment[TypeTheoryDefinition[Composite,
    Function[{TypedImplicit[A, TypeUniverse[u]], TypedImplicit[B, TypeUniverse[v]], TypedImplicit[C, TypeUniverse[w]], Typed[g, TypeSpecifier[{B} -> C]], Typed[f, TypeSpecifier[{A} -> B]], Typed[x, A]}, g[f[x]]]
]]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

[MakeBoxes]() definitions give a definition a notation. A term shows the arguments that are not implicit, so the rule matches those:

```wl
MakeBoxes[Composite[g_, f_, x_], form_] := MakeBoxes[SmallCircle[g, f][x], form];
TypeTheoryTerm[Function[{Typed[f, TypeSpecifier[{Naturals} -> Naturals]], Typed[n, Naturals]}, Composite[f, f, n]], composite]
```

<!-- => (f ∶ ℕ → ℕ) (n ∶ ℕ) ↦ (f∘f)[n] -->

---

An instance of a class: `Inhabited[α]` holds an element of α, and `Default` takes it from an instance-implicit argument:

```wl
inhabited = TypeTheoryEnvironment[{
    TypeTheoryInductiveType[Inhabited, ForAll[{Typed[A, TypeUniverse[u + 1]]}, TypeUniverse[u + 1]], {
        InhabitedIntroduction -> ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[x, A]}, Inhabited[A]]
    }],
    TypeTheoryDefinition[Default, Function[{TypedImplicit[A, TypeUniverse[u + 1]], Annotation[Typed[h, Inhabited[A]], "InstanceImplicit"]}, h[[1]]]],
    TypeTheoryDefinition[NaturalsInhabited, Typed[InhabitedIntroduction[7], Inhabited[Naturals]], "Instance" -> True]
}]
```

<!-- => TypeTheoryEnvironment summary box: 174 constants -->

`Default` where a natural number is expected finds the instance:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Typed[Default, Naturals], inhabited]]
```

<!-- => 7 -->

---

A coercion from the Booleans to the natural numbers, true as 1:

```wl
coerced = TypeTheoryEnvironment[
    TypeTheoryDefinition[NaturalOfBoolean, Function[{Typed[b, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Naturals], 0, 1, b]], "Coercion" -> True]
]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

A Boolean where a natural number is expected is coerced:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Typed["true", Naturals], coerced]]
```

<!-- => 1 -->

The declaration shows as a coercion:

```wl
coerced[NaturalOfBoolean]
```

<!-- => coercion NaturalOfBoolean : 𝔹 → ℕ := (b ∶ 𝔹) ↦ 𝔹_rec[(t ∶ 𝔹) ↦ ℕ, 0, 1, b] -->

---

An opaque definition, whose value the kernel checks:

```wl
secret = TypeTheoryEnvironment[TypeTheoryDefinition[Secret, Typed[42, Naturals], "Opaque" -> True]]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

It never unfolds, so it is not equal to its value:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Secret, secret], TypeTheoryTerm[42, secret]]
```

<!-- => False -->

The declaration shows as opaque:

```wl
secret[Secret]
```

<!-- => opaque Secret : ℕ := 42 -->

## Possible Issues

The type of an instance must end in a class, a constant applied to arguments, and a coercion must be a function:

```wl
TypeTheoryEnvironment[TypeTheoryDefinition[NotACoercion, Typed[0, Naturals], "Coercion" -> True]]
```

<!-- => Failure["CoercionTypeExpected", ...] -->

---

An opaque definition equals only itself, so a proof that needs its value does not check:

```wl
Append[
    TypeTheoryEnvironment[TypeTheoryDefinition[Secret, Typed[42, Naturals], "Opaque" -> True]],
    TypeTheoryTheorem[SecretValue, Secret == 42, EqualityReflexivity[42]]
]
```

<!-- => Failure["TypeMismatch", ...] -->

---

A definition cannot refer to itself:

```wl
TypeTheoryEnvironment[
    TypeTheoryDefinition[Loop, Typed[Function[{Typed[n, Naturals]}, Loop[n]], TypeSpecifier[{Naturals} -> Naturals]]]
]
```

<!-- => Failure["ElaborationFailed", ...] -->
