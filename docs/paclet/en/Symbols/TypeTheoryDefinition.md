---
Template: Symbol
Name: TypeTheoryDefinition
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryDefinition
Keywords: [definition, declaration, function, unfolding, recursion, recursor, environment, universe polymorphism, instance, type class, coercion, opaque, overloading, notation]
SeeAlso: [TypeTheoryEnvironment, TypeTheoryAxiom, TypeTheoryTheorem, InductiveRecursor, WeakHeadNormalForm, NormalForm, DefinitionallyEqualQ, Decidable]
RelatedGuides: [TypeTheory]
RelatedTutorials: [InstancesAndCoercions, TypeTheoryIntroduction]
---

## Usage

<code>[TypeTheoryDefinition]()[*name*, *value*]</code> declares *name* as a definition with the given *value*, when added to a [TypeTheoryEnvironment]().

<code>[TypeTheoryDefinition]()[*name*, [Typed]()[*value*, *type*]]</code> gives the definition the given *type*.

## Details & Options

- A definition unfolds: computation replaces *name* by *value*, so a term with *name* is equal by computation to the same term with *value*.
- A definition may not mention itself; recursion goes through a recursor, <code>[InductiveRecursor]()[*type*]</code>, which takes a case for each constructor of *type*.
- Without a type, the definition has the type of *value*. With one, *value* is checked against it.
- The option `"UniverseParameters" -> {u, ...}` lists the universe parameters; [Automatic]() takes the symbols and strings in universe levels, in the order they appear.
- The option `"Instance" -> True` makes the definition an instance of its class, the constant its type applies at the end, under its binders, as Lean's `instance`. Elaboration fills an argument of an instance-implicit binder, <code>[Annotation]()[[Typed]()[*x*, *class*], "InstanceImplicit"]</code>, with a variable bound by such a binder, or else with the first instance whose type unifies with the binder's, the latest declared first, finding the instance's own instance-implicit arguments in turn.
- The option `"Coercion" -> True` makes a function of one explicit argument, after its implicit ones, a coercion, as Lean's `@[coe]`: where a term's type does not unify with the one expected, elaboration applies the coercion from the one to the other, or a chain of at most three.
- An instance or a coercion is a definition as any other: the kernel checks it, and every term elaboration builds with it.
- The option `"Opaque" -> True` makes the definition opaque, as Lean's `opaque`: the kernel checks *value* against the type, but the definition never unfolds, so it equals only itself. Unlike an axiom of its type, it cannot make the theory inconsistent, since *value* is an element of the type.
- The option `"Overloads" -> *operation*`, for [Plus](), [Times](), [Subtract](), [Power](), [Minus](), [LessEqual](), [Less](), [GreaterEqual]() or [Greater](), makes the constant one more meaning of the operation, chosen by the types of its arguments and the type expected, as the integers' and rationals' operations are, and the constant shows as the operation.
- [MakeBoxes]() definitions give a definition a notation in terms, declarations and proofs, and [Format]() definitions give its symbol a display.

## Basic Examples

Define doubling:

```wl
doubled = TypeTheoryEnvironment[TypeTheoryDefinition[Double, Typed[n, Naturals] |-> n + n]]
```

<!-- => TypeTheoryEnvironment summary box: 231 constants -->

Compute with it:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Double[21], doubled]]
```

<!-- => 42 -->

Its type, which the kernel gave it from its value:

```wl
TypeTheoryType[Double, doubled]
```

<!-- => ℕ → ℕ -->

Its declaration:

```wl
doubled[Double]
```

<!-- => definition Double : ℕ → ℕ := (n ∶ ℕ) ↦ n + n -->

---

A definition by recursion, through the recursor of the natural numbers: the factorial is 1 at 0, and `(k + 1) r` at `k + 1` where `r` is its value at `k`:

```wl
factorial = TypeTheoryEnvironment[{TypeTheoryDefinition[NaturalFactorial, Typed[n, Naturals] |->
    InductiveRecursor[Naturals][Typed[k, Naturals] |-> Naturals, 1, {Typed[k, Naturals], Typed[r, Naturals]} |-> (k + 1) r, n]
]}]
```

<!-- => TypeTheoryEnvironment summary box: 231 constants -->

The factorial of 20:

```wl
WeakHeadNormalForm[TypeTheoryTerm[NaturalFactorial[20], factorial]]
```

<!-- => 2432902008176640000 -->

## Scope

A recursive definition and a theorem about it. The factorial:

```wl
factorial = TypeTheoryEnvironment[{TypeTheoryDefinition[NaturalFactorial, Typed[n, Naturals] |->
    InductiveRecursor[Naturals][Typed[k, Naturals] |-> Naturals, 1, {Typed[k, Naturals], Typed[r, Naturals]} |-> (k + 1) r, n]
]}]
```

<!-- => TypeTheoryEnvironment summary box: 231 constants -->

Its recursion equation holds by computation, so reflexivity proves it for every `n`, and the kernel checks the theorem:

```wl
recursion = TypeTheoryEnvironment[factorial, {TypeTheoryTheorem[FactorialSuccessor, TypeTheoryProof[
    ForAll[{Typed[n, Naturals]}, NaturalFactorial[n + 1] == (n + 1) NaturalFactorial[n]],
    factorial,
    {"Introduce"[n], "Reflexivity"}
]]}]
```

<!-- => TypeTheoryEnvironment summary box: 232 constants -->

The theorem:

```wl
recursion[FactorialSuccessor]
```

<!-- => theorem FactorialSuccessor : ∀_n∶ℕ NaturalFactorial[n + 1] == (n + 1) NaturalFactorial[n] -->

---

A predicate, the even numbers, defined by an existential statement:

```wl
even = TypeTheoryEnvironment[{TypeTheoryDefinition[EvenNumber, Typed[n, Naturals] |-> Exists[{Typed[k, Naturals]}, n == k + k]]}]
```

<!-- => TypeTheoryEnvironment summary box: 231 constants -->

Its type is that of a predicate on the natural numbers:

```wl
TypeTheoryType[EvenNumber, even]
```

<!-- => ℕ → Prop -->

10 is even, with the witness 5:

```wl
TypeTheoryProof[EvenNumber[10], even, {"Exact"["existsIntroduction"[5, "equalityReflexivity"[10]]]}]
```

<!-- => Proof complete -->

---

A definition may use those before it:

```wl
quadrupled = TypeTheoryEnvironment[{
    TypeTheoryDefinition[Double, Typed[n, Naturals] |-> n + n],
    TypeTheoryDefinition[Quadruple, Typed[n, Naturals] |-> Double[Double[n]]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 232 constants -->

Four times 5:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Quadruple[5], quadrupled]]
```

<!-- => 20 -->

---

A definition on the integers, extending them by their name:

```wl
distances = TypeTheoryEnvironment["Integers", {TypeTheoryDefinition[SquaredDistance, {Typed[x, Integers], Typed[y, Integers]} |-> (x - y)^2]}]
```

<!-- => TypeTheoryEnvironment summary box: 306 constants -->

Its type:

```wl
TypeTheoryType[SquaredDistance, distances]
```

<!-- => ℤ → ℤ → ℤ -->

---

The identity function on a type in any universe:

```wl
identity = TypeTheoryEnvironment[
    TypeTheoryDefinition[PolymorphicIdentity, {TypedImplicit[A, TypeUniverse[u]], Typed[x, A]} |-> x]
]
```

<!-- => TypeTheoryEnvironment summary box: 231 constants -->

Its universe parameter `u` and implicit argument `A` show in its declaration:

```wl
identity[PolymorphicIdentity]
```

<!-- => definition PolymorphicIdentity : ∀_{A∶Sort u} A → A := {A ∶ Sort u} (x ∶ A) ↦ x -->

Applied to a number, `A` is the natural numbers:

```wl
TypeTheoryType[PolymorphicIdentity[3], identity]
```

<!-- => ℕ -->

Applied to a type, it is used one universe up:

```wl
TypeTheoryType[PolymorphicIdentity[Naturals], identity]
```

<!-- => Type -->

---

The composition of two functions, applied to an argument:

```wl
composite = TypeTheoryEnvironment[TypeTheoryDefinition[Composite,
    Function[{TypedImplicit[A, TypeUniverse[u]], TypedImplicit[B, TypeUniverse[v]], TypedImplicit[C, TypeUniverse[w]], Typed[g, TypeSpecifier[{B} -> C]], Typed[f, TypeSpecifier[{A} -> B]], Typed[x, A]}, g[f[x]]]
]]
```

<!-- => TypeTheoryEnvironment summary box: 231 constants -->

Doubling after adding one, at 4:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Composite[Typed[n, Naturals] |-> n + n, Typed[n, Naturals] |-> n + 1, 4], composite]]
```

<!-- => 10 -->

[MakeBoxes]() definitions give a definition a notation. A term shows the arguments that are not implicit, so the rule matches those:

```wl
MakeBoxes[Composite[g_, f_, x_], form_] := MakeBoxes[SmallCircle[g, f][x], form];
TypeTheoryTerm[{Typed[f, TypeSpecifier[{Naturals} -> Naturals]], Typed[n, Naturals]} |-> Composite[f, f, n], composite]
```

<!-- => (f ∶ ℕ → ℕ) (n ∶ ℕ) ↦ (f∘f)[n] -->

## Options

### Instance

A class of monoids, a unit and an operation on a type, the operation of a monoid found from its instance, and the natural numbers under addition as an instance:

```wl
monoids = TypeTheoryEnvironment[{
    TypeTheoryInductiveType[Monoid, ForAll[{Typed[A, TypeUniverse[1]]}, TypeUniverse[1]], {
        MonoidIntroduction -> ForAll[{TypedImplicit[A, TypeUniverse[1]], Typed[unit, A], Typed[op, TypeSpecifier[{A, A} -> A]]}, Monoid[A]]
    }],
    TypeTheoryDefinition[MonoidOperation, {TypedImplicit[A, TypeUniverse[1]], Annotation[Typed[m, Monoid[A]], "InstanceImplicit"], Typed[x, A], Typed[y, A]} |-> m[[2]][x, y]],
    TypeTheoryDefinition[AdditiveNaturals, Typed[MonoidIntroduction[0, Plus], Monoid[Naturals]], "Instance" -> True]
}]
```

<!-- => TypeTheoryEnvironment summary box: 235 constants -->

The operation on two natural numbers finds the instance, and adds:

```wl
WeakHeadNormalForm[TypeTheoryTerm[MonoidOperation[3, 4], monoids]]
```

<!-- => 7 -->

The declaration shows as an instance:

```wl
monoids[AdditiveNaturals]
```

<!-- => instance AdditiveNaturals : Monoid[ℕ] := MonoidIntroduction[0, Plus] -->

### Coercion

A coercion from the Booleans to the natural numbers, true as 1:

```wl
coerced = TypeTheoryEnvironment[
    TypeTheoryDefinition[NaturalOfBoolean, Typed[b, Booleans] |-> InductiveRecursor[Booleans][Typed[t, Booleans] |-> Naturals, 0, 1, b], "Coercion" -> True]
]
```

<!-- => TypeTheoryEnvironment summary box: 231 constants -->

A Boolean added to a natural number is coerced:

```wl
TypeTheoryType[{Typed[b, Booleans], Typed[n, Naturals]} |-> n + b, coerced]
```

<!-- => 𝔹 → ℕ → ℕ -->

And computes as 1 or 0:

```wl
WeakHeadNormalForm[TypeTheoryTerm[3 + Typed["true", Booleans], coerced]]
```

<!-- => 4 -->

The declaration shows as a coercion:

```wl
coerced[NaturalOfBoolean]
```

<!-- => coercion NaturalOfBoolean : 𝔹 → ℕ := (b ∶ 𝔹) ↦ 𝔹_rec[(t ∶ 𝔹) ↦ ℕ, 0, 1, b] -->

### Opaque

An opaque definition, whose value the kernel checks:

```wl
secret = TypeTheoryEnvironment[TypeTheoryDefinition[Secret, Typed[42, Naturals], "Opaque" -> True]]
```

<!-- => TypeTheoryEnvironment summary box: 231 constants -->

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

### Overloads

Vectors of two natural numbers, whose addition `+` stands for:

```wl
vectors = TypeTheoryEnvironment[{
    TypeTheoryInductiveType[Vector2, TypeUniverse[1], {Vector2Introduction -> ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, Vector2]}],
    TypeTheoryDefinition[Vector2Addition, {Typed[v, Vector2], Typed[w, Vector2]} |-> Vector2Introduction[v[[1]] + w[[1]], v[[2]] + w[[2]]], "Overloads" -> Plus]
}]
```

<!-- => TypeTheoryEnvironment summary box: 234 constants -->

A sum of two vectors is their addition, which shows as `+`:

```wl
TypeTheoryTerm[{Typed[v, Vector2], Typed[w, Vector2]} |-> v + w, vectors]
```

<!-- => (v ∶ Vector2) (w ∶ Vector2) ↦ v + w -->

It computes:

```wl
NormalForm[TypeTheoryTerm[Vector2Introduction[1, 2] + Vector2Introduction[10, 20], vectors]]
```

<!-- => Vector2Introduction[11, 22] -->

### UniverseParameters

The universe parameters named explicitly:

```wl
TypeTheoryEnvironment[
    TypeTheoryDefinition[PolymorphicIdentity, {TypedImplicit[A, TypeUniverse[v]], Typed[x, A]} |-> x, "UniverseParameters" -> {v}]
][PolymorphicIdentity]
```

<!-- => definition PolymorphicIdentity : ∀_{A∶Sort v} A → A := {A ∶ Sort v} (x ∶ A) ↦ x -->

## Properties and Relations

Define doubling:

```wl
doubled = TypeTheoryEnvironment[TypeTheoryDefinition[Double, Typed[n, Naturals] |-> n + n]]
```

<!-- => TypeTheoryEnvironment summary box: 231 constants -->

A definition unfolds, so it is equal by computation to its value:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Typed[n, Naturals] |-> Double[n], doubled], TypeTheoryTerm[Typed[n, Naturals] |-> n + n, doubled]]
```

<!-- => True -->

---

A definition rests on no axiom:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[Answer, TypeTheoryEnvironment[TypeTheoryDefinition[Answer, Typed[42, Naturals]]]]]
```

<!-- => <||> -->

---

An axiom of the same type has no value, so it never computes:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Answer + 1, TypeTheoryEnvironment[TypeTheoryAxiom[Answer, Naturals]]]]
```

<!-- => ℕ_rec[(t ∶ ℕ) ↦ ℕ, Answer, (k ∶ ℕ) (r ∶ ℕ) ↦ r + 1, 0] + 1 -->

## Possible Issues

A definition cannot refer to itself; recursion goes through a recursor:

```wl
TypeTheoryEnvironment[
    TypeTheoryDefinition[Loop, Typed[Typed[n, Naturals] |-> Loop[n], TypeSpecifier[{Naturals} -> Naturals]]]
]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

The value must have the type given:

```wl
TypeTheoryEnvironment[TypeTheoryDefinition[Answer, Typed[42, Booleans]]]
```

<!-- => Failure["TypeMismatch", ...] -->

---

An opaque definition equals only itself, so a proof that needs its value does not check:

```wl
Append[
    TypeTheoryEnvironment[TypeTheoryDefinition[Secret, Typed[42, Naturals], "Opaque" -> True]],
    TypeTheoryTheorem[SecretValue, Secret == 42, "equalityReflexivity"[42]]
]
```

<!-- => Failure["TypeMismatch", ...] -->

---

A coercion must be a function:

```wl
TypeTheoryEnvironment[TypeTheoryDefinition[NotACoercion, Typed[0, Naturals], "Coercion" -> True]]
```

<!-- => Failure["CoercionTypeExpected", ...] -->

---

Elaboration finds an instance only of a type that has one. The monoids, with an instance for the natural numbers only:

```wl
monoids = TypeTheoryEnvironment[{
    TypeTheoryInductiveType[Monoid, ForAll[{Typed[A, TypeUniverse[1]]}, TypeUniverse[1]], {
        MonoidIntroduction -> ForAll[{TypedImplicit[A, TypeUniverse[1]], Typed[unit, A], Typed[op, TypeSpecifier[{A, A} -> A]]}, Monoid[A]]
    }],
    TypeTheoryDefinition[MonoidOperation, {TypedImplicit[A, TypeUniverse[1]], Annotation[Typed[m, Monoid[A]], "InstanceImplicit"], Typed[x, A], Typed[y, A]} |-> m[[2]][x, y]],
    TypeTheoryDefinition[AdditiveNaturals, Typed[MonoidIntroduction[0, Plus], Monoid[Naturals]], "Instance" -> True]
}]
```

<!-- => TypeTheoryEnvironment summary box: 235 constants -->

The operation on two Booleans finds none:

```wl
TypeTheoryType[MonoidOperation["true", "false"], monoids]
```

<!-- => Failure["NoInstance", ...] -->
