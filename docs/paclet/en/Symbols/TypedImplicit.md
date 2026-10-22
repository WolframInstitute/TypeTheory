---
Template: Symbol
Name: TypedImplicit
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypedImplicit
Keywords: [implicit binder, implicit argument, binder, Typed, Annotation, elaboration]
SeeAlso: [TypeTheoryTerm, TypeTheoryDefinition, TypeTheoryTheorem, TypeTheoryInductiveType]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TypeTheoryIntroduction]
---

## Usage

<code>[TypedImplicit]()[*x*, *A*]</code> is an implicit binder: a variable *x* of type *A* that is found from the other arguments rather than written, shown as `{x ∶ A}` as Lean writes it.

## Details & Options

- [TypedImplicit]() is a binder of [ForAll](), [Function]() and [Exists](), wherever <code>[Typed]()[*x*, *A*]</code> is one: in terms, in statements and in the types of declarations.
- Where a constant with an implicit binder is applied, elaboration fills in the implicit argument by unification with the types of the explicit ones, or with the type the term is expected to have. <code>[Construct]()[*f*, *a*, ...]</code> gives every argument, implicit ones included.
- <code>[TypedImplicit]()[*x*, *A*, *q*]</code> is an implicit binder of quantity *q*, 0 or 1, under rules with quantities, as <code>[Typed]()[*x*, *A*, *q*]</code> is an explicit one; see [TypeTheoryRules]().
- <code>[TypedImplicit]()[*x*, *A*]</code> is the same binder as <code>[Annotation]()[[Typed]()[*x*, *A*], "Implicit"]</code>, and terms and declarations read back with it. The strict implicit and instance implicit binders of Lean are written <code>[Annotation]()[[Typed]()[*x*, *A*], "StrictImplicit"]</code> and <code>[Annotation]()[[Typed]()[*x*, *A*], "InstanceImplicit"]</code>.

## Basic Examples

A polymorphic identity whose type argument is implicit:

```wl
TypeOf[TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A]}, x]]]
```

<!-- => ∀_{A ∶ Type} A → A -->

---

The polymorphic identity, declared:

```wl
identity = TypeTheoryEnvironment[{TypeTheoryDefinition[PolymorphicIdentity, Function[{TypedImplicit[A, TypeUniverse[u]], Typed[x, A]}, x]]}]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

Declared, it is applied to its explicit argument alone:

```wl
WeakHeadNormalForm[TypeTheoryTerm[PolymorphicIdentity[5], identity]]
```

<!-- => 5 -->

## Scope

A theorem whose propositions are implicit:

```wl
swap = TypeTheoryEnvironment[{TypeTheoryTheorem[
    ConjunctionSwap,
    ForAll[{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]]}, Implies[a && b, b && a]],
    Function[{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]], Typed[h, a && b]}, AndIntroduction[AndEliminationRight[h], AndEliminationLeft[h]]]
]}]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

Its declaration:

```wl
swap[ConjunctionSwap]
```

<!-- => theorem ConjunctionSwap : ∀_{a ∶ Prop} ∀_{b ∶ Prop} (a ∧ b) ⇒ (b ∧ a) -->

The propositions are found from the type of the proof it is applied to:

```wl
TypeOf[TypeTheoryTerm[ConjunctionSwap[AndIntroduction[TrueIntroduction, EqualityReflexivity[0]]], swap]]
```

<!-- => 0 == 0 ∧ True -->

---

The polymorphic identity, declared:

```wl
identity = TypeTheoryEnvironment[{TypeTheoryDefinition[PolymorphicIdentity, Function[{TypedImplicit[A, TypeUniverse[u]], Typed[x, A]}, x]]}]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

[Construct]() gives the implicit argument explicitly:

```wl
TypeOf[TypeTheoryTerm[Construct[PolymorphicIdentity, Naturals], identity]]
```

<!-- => ℕ → ℕ -->

## Properties and Relations

[TypedImplicit]() is the same binder as an implicit [Annotation]():

```wl
TypeOf[TypeTheoryTerm[Function[{Annotation[Typed[A, TypeUniverse[1]], "Implicit"], Typed[x, A]}, x]]] === TypeOf[TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A]}, x]]]
```

<!-- => True -->

---

The polymorphic identity, declared:

```wl
identity = TypeTheoryEnvironment[{TypeTheoryDefinition[PolymorphicIdentity, Function[{TypedImplicit[A, TypeUniverse[u]], Typed[x, A]}, x]]}]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

Declarations read back with it:

```wl
InputForm[identity[PolymorphicIdentity]]
```

<!-- => TypeTheoryDefinition[PolymorphicIdentity, Typed[Function[{TypedImplicit[A, TypeUniverse[u]], Typed[x, A]}, x], ForAll[{TypedImplicit[A, TypeUniverse[u]]}, TypeSpecifier[{A} -> A]]], "UniverseParameters" -> {u}] -->

---

A strict implicit binder is an [Annotation]() of another kind:

```wl
TypeOf[TypeTheoryTerm[Function[{Annotation[Typed[A, TypeUniverse[1]], "StrictImplicit"], Typed[x, A]}, x]]]
```

<!-- => ∀_⦃A ∶ Type⦄ A → A -->

## Possible Issues

[TypedImplicit]() takes a variable and its type:

```wl
TypeOf[TypeTheoryTerm[Function[{TypedImplicit[A], Typed[x, A]}, x]]]
```

<!-- => Failure["ElaborationFailed", ...] -->
