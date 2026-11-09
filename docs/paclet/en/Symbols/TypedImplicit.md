---
Template: Symbol
Name: TypedImplicit
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypedImplicit
Keywords: [implicit binder, implicit argument, binder, Typed, Annotation, elaboration, unification, strict implicit, instance implicit, quantity, Construct]
SeeAlso: [TypeTheoryTerm, TypeTheoryDefinition, TypeTheoryTheorem, TypeTheoryInductiveType, Construct, Annotation]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TypeTheoryIntroduction, Elaboration, Quantities]
---

## Usage

<code>[TypedImplicit]()[*x*, *A*]</code> is an implicit binder: a variable *x* of type *A* that is found from the other arguments rather than written, shown as `{x ∶ A}`.

## Details & Options

- [TypedImplicit]() is a binder of [ForAll](), [Function]() and [Exists](), wherever <code>[Typed]()[*x*, *A*]</code> is one: in terms, in statements and in the types of declarations.
- Where a constant with an implicit binder is applied, elaboration fills in the implicit argument by unification with the types of the explicit ones, or with the type the term is expected to have, as given by [Typed](). Where nothing determines it, elaboration gives a [Failure]() tagged `"UnsolvedImplicitArgument"`.
- The constructors and theorems of the prelude take their types, and the variables their hypotheses mention, as implicit arguments: `"some"[3]` is an option of natural numbers, and `"lessEqualAntisymmetry"[h1, h2]` finds its numbers from the proofs.
- <code>[Construct]()[*f*, *a*, ...]</code> gives every argument, implicit ones included.
- `"Introduce"` moves an implicit variable into the context of a proof as it moves an explicit one.
- <code>[TypedImplicit]()[*x*, *A*, *q*]</code> is an implicit binder of quantity *q*, 0 or 1, under rules with quantities, as <code>[Typed]()[*x*, *A*, *q*]</code> is an explicit one; see [TypeTheoryRules]().
- <code>[TypedImplicit]()[*x*, *A*]</code> is the same binder as <code>[Annotation]()[[Typed]()[*x*, *A*], "Implicit"]</code>, and terms and declarations read back with it. The strict implicit and instance implicit binders of Lean are written <code>[Annotation]()[[Typed]()[*x*, *A*], "StrictImplicit"]</code> and <code>[Annotation]()[[Typed]()[*x*, *A*], "InstanceImplicit"]</code>, and show as `⦃x ∶ A⦄` and `[x ∶ A]`.

## Basic Examples

A polymorphic identity whose type argument is implicit:

```wl
TypeTheoryType[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A]} |-> x]
```

<!-- => ∀_{A ∶ Type} A → A -->

---

The polymorphic identity, declared:

```wl
identity = TypeTheoryEnvironment[{TypeTheoryDefinition[PolymorphicIdentity, {TypedImplicit[A, TypeUniverse[u]], Typed[x, A]} |-> x]}]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

Declared, it is applied to its explicit argument alone:

```wl
WeakHeadNormalForm[TypeTheoryTerm[PolymorphicIdentity[5], identity]]
```

<!-- => 5 -->

---

The constructor `"some"` of [Option]() takes the type of its value implicitly:

```wl
TypeTheoryType["some"]
```

<!-- => ∀_{α ∶ Type u} α → Option[α] -->

## Scope

A theorem whose propositions are implicit:

```wl
swap = TypeTheoryEnvironment[{TypeTheoryTheorem[
    ConjunctionSwap,
    ForAll[{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]]}, Implies[a && b, b && a]],
    Function[{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]], h}, "andIntroduction"["andEliminationRight"[h], "andEliminationLeft"[h]]]
]}]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

Its declaration:

```wl
swap[ConjunctionSwap]
```

<!-- => theorem ConjunctionSwap : ∀_{a ∶ Prop} ∀_{b ∶ Prop} (a ∧ b) ⇒ (b ∧ a) -->

The propositions are found from the type of the proof it is applied to:

```wl
TypeTheoryType[ConjunctionSwap["andIntroduction"["trueIntroduction", "equalityReflexivity"[0]]], swap]
```

<!-- => 0 == 0 ∧ True -->

---

The implicit numbers of `"lessEqualAntisymmetry"` are found from the proofs of the two inequalities:

```wl
TypeTheoryType[{Typed[h1, 2 <= 3], Typed[h2, 3 <= 2]} |-> "lessEqualAntisymmetry"[h1, h2]]
```

<!-- => 2 <= 3 ⇒ 3 <= 2 ⇒ 2 == 3 -->

---

`"none"` has no argument to find its type from, so the type it is expected to have gives it:

```wl
TypeTheoryType[Typed["none", Option[Naturals]]]
```

<!-- => Option[ℕ] -->

---

[Construct]() gives the implicit argument explicitly:

```wl
TypeTheoryType[Construct["none", Naturals]]
```

<!-- => Option[ℕ] -->

---

The polymorphic identity, declared:

```wl
identity = TypeTheoryEnvironment[{TypeTheoryDefinition[PolymorphicIdentity, {TypedImplicit[A, TypeUniverse[u]], Typed[x, A]} |-> x]}]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

[Construct]() applies it to its type argument alone, which gives the identity of that type:

```wl
TypeTheoryType[Construct[PolymorphicIdentity, Naturals], identity]
```

<!-- => ℕ → ℕ -->

---

`"Introduce"` moves the implicit propositions into the context, with the hypothesis:

```wl
TypeTheoryProof[ForAll[{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]]}, Implies[a && b, b && a]], {"Introduce"[a, b, h]}]
```

<!-- => Proof, 1 goal: a ∶ Prop, b ∶ Prop, h ∶ a ∧ b ⊢ b ∧ a -->

---

Under rules with quantities, an implicit type argument of quantity 0 is erased when the function runs:

```wl
TypeTheoryType[{TypedImplicit[A, TypeUniverse[1], 0], Typed[x, A, 1]} |-> x, TypeTheoryEnvironment[TypeTheoryRules["CalculusOfInductiveConstructions", "Quantities" -> True]]]
```

<!-- => ∀_{0 A ∶ Type} ∀_1 x∶A A -->

## Properties and Relations

[TypedImplicit]() is the same binder as an implicit [Annotation]():

```wl
TypeTheoryType[{Annotation[Typed[A, TypeUniverse[1]], "Implicit"], Typed[x, A]} |-> x] === TypeTheoryType[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A]} |-> x]
```

<!-- => True -->

---

The polymorphic identity, declared:

```wl
identity = TypeTheoryEnvironment[{TypeTheoryDefinition[PolymorphicIdentity, {TypedImplicit[A, TypeUniverse[u]], Typed[x, A]} |-> x]}]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

Declarations read back with it:

```wl
InputForm[identity[PolymorphicIdentity]]
```

<!-- => TypeTheoryDefinition[PolymorphicIdentity, Typed[Function[{TypedImplicit[A, TypeUniverse[u]], Typed[x, A]}, x], ForAll[{TypedImplicit[A, TypeUniverse[u]]}, A -> A]]] -->

---

A strict implicit binder is an [Annotation]() of another kind:

```wl
TypeTheoryType[{Annotation[Typed[A, TypeUniverse[1]], "StrictImplicit"], Typed[x, A]} |-> x]
```

<!-- => ∀_⦃A ∶ Type⦄ A → A -->

---

An instance implicit binder is found among the instances of a class, here the decision of a proposition, which [Decide]() turns into a Boolean:

```wl
TypeTheoryType[{p, Annotation[Typed[d, Decidable[p]], "InstanceImplicit"]} |-> Decide[Not[p]]]
```

<!-- => ∀_p∶Prop ∀_[d∶Decidable[p]] 𝔹 -->

## Possible Issues

[TypedImplicit]() with a variable alone, `TypedImplicit[A]`, leaves its type to elaboration, as a bare binder does: here a type, since `x` has type `A`:

```wl
TypeTheoryType[{TypedImplicit[A], Typed[x, A]} |-> x]
```

<!-- => ∀_{A∶Type} A → A -->

---

Where nothing determines an implicit argument, elaboration fails: `"none" == "none"` could compare options of any type:

```wl
TypeTheoryType["none" == "none"]
```

<!-- => Failure["UnsolvedImplicitArgument", ...] -->

---

The polymorphic identity, declared:

```wl
identity = TypeTheoryEnvironment[{TypeTheoryDefinition[PolymorphicIdentity, {TypedImplicit[A, TypeUniverse[u]], Typed[x, A]} |-> x]}]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

An implicit argument is not written in an ordinary application, so here 5 is one argument too many; [Construct]() takes it:

```wl
TypeTheoryType[PolymorphicIdentity[Naturals, 5], identity]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

A quantity needs rules with quantities, which the prelude's are not:

```wl
TypeTheoryType[{TypedImplicit[A, TypeUniverse[1], 0], Typed[x, A]} |-> x]
```

<!-- => Failure["QuantitiesNotAllowed", ...] -->
