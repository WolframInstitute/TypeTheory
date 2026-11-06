---
Template: Symbol
Name: Decide
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Decide
Keywords: [decide, decision, Boolean, computation, instance, prelude, decidable proposition, decideSoundness, if then else]
SeeAlso: [Decidable, TypeTheoryTactic, Booleans, InductiveRecursor, WeakHeadNormalForm, NormalForm]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude, InstancesAndCoercions]
---

## Usage

<code>[Decide]()[*p*]</code> gives the Boolean of the decision of the proposition *p*: `"true"` if it decides *p* true, `"false"` if it decides *p* false.

<code>[Construct]()[[Decide](), *p*, *d*]</code> gives the Boolean of the decision *d* of *p*, given explicitly.

## Details & Options

- [Decide]() is a definition of the prelude, by recursion on the decision, as Lean's `decide`.
- The decision is an instance-implicit argument: elaboration finds it among the instances of <code>[Decidable]()[*p*]</code>.
- The prelude has instances deciding `==` and `<=` of natural numbers, `==` of Booleans, [True](), [False](), [Not](), [And]() and [Or](); a definition such as [Less]() or [Unequal](), or one of an environment's own, unfolds to a proposition that has one. A proposition with none, such as one with a quantifier, gives a [Failure]() tagged `"NoInstance"`.
- The decisions of `==` and `<=` compare literals in one step of the kernel, so large numbers decide at once.
- With variables, [Decide]() computes where the decision does not depend on them: `Decide[n + 1 == 0]` is `"false"` for every `n`, but `Decide[n <= n + 1]` does not compute until `n` is a number.
- `"decideSoundness"` turns a proof that <code>[Decide]()[*p*]</code> is `"true"` into a proof of *p*, and the tactic `"Decide"` of [TypeTheoryTactic]() proves a statement so.
- The Booleans are named by strings, `"true"` and `"false"`; <code>[InductiveRecursor]()[[Booleans]()]</code> takes a Boolean to one of two values, the value for `"false"` first.

## Basic Examples

The type of [Decide]():

```wl
TypeTheoryType[Decide]
```

<!-- => ∀_p∶Prop ∀_[d∶Decidable[p]] 𝔹 -->

---

2 == 2 is decided true:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[2 == 2]]]
```

<!-- => true -->

---

3 <= 2 is decided false:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[3 <= 2]]]
```

<!-- => false -->

## Scope

The connectives combine decisions, and [Less]() and [Unequal]() unfold to propositions with decisions:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[2 < 3 && 4 != 5]]]
```

<!-- => true -->

---

The sides compute before they are compared: 2^20 is 1048576, more than a million:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[2^20 <= 10^6]]]
```

<!-- => false -->

---

Literals are compared in one step, however large:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[123456789 <= 987654321]]]
```

<!-- => true -->

---

Equations of Booleans are decided too:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide["true" == "not"["false"]]]]
```

<!-- => true -->

---

A definition of an environment's own unfolds to a proposition with a decision:

```wl
zeros = TypeTheoryEnvironment[TypeTheoryDefinition[IsZero, Typed[n, Naturals] |-> n == 0]]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

`IsZero[0]` is decided true:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[IsZero[0]], zeros]]
```

<!-- => true -->

---

Under a binder, the decision computes where it does not depend on the variable; a successor is never 0:

```wl
NormalForm[TypeTheoryTerm[Typed[n, Naturals] |-> Decide[n + 1 == 0]]]
```

<!-- => (n ∶ ℕ) ↦ false -->

---

A decision given explicitly:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Construct[Decide, 3 <= 2, "lessEqualDecidable"[3, 2]]]]
```

<!-- => false -->

---

A function of a proposition that has a decision takes the decision as an instance-implicit argument:

```wl
TypeTheoryType[{Typed[p, TypeUniverse[0]], Annotation[Typed[d, Decidable[p]], "InstanceImplicit"]} |-> Decide[Not[p]]]
```

<!-- => ∀_p∶Prop ∀_[d∶Decidable[p]] 𝔹 -->

## Applications

The larger of two numbers, chosen by the decision of `m <= n`:

```wl
larger = TypeTheoryEnvironment[TypeTheoryDefinition[Larger,
    {Typed[m, Naturals], Typed[n, Naturals]} |-> InductiveRecursor[Booleans][Typed[b, Booleans] |-> Naturals, m, n, Decide[m <= n]]
]]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

The larger of 3 and 7:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Larger[3, 7], larger]]
```

<!-- => 7 -->

The larger of 9 and 4:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Larger[9, 4], larger]]
```

<!-- => 9 -->

`0 <= n` is decided true for every `n`, so the larger of 0 and `n` is `n` by computation:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, Larger[0, n] == n], larger, {"Introduce"[n], "Reflexivity"}]
```

<!-- => Proof complete -->

## Properties and Relations

`"decideSoundness"` turns a decision that computes to `"true"` into a proof:

```wl
TypeTheoryType["decideSoundness"]
```

<!-- => ∀_{p∶Prop} ∀_[d∶Decidable[p]] Decide[p] == true ⇒ p -->

---

`Decide[100 <= 1000]` computes to `"true"`, so `"equalityReflexivity"["true"]` proves that it is, and `"decideSoundness"` makes a proof of `100 <= 1000` of it:

```wl
TypeTheoryType[Typed["decideSoundness"["equalityReflexivity"["true"]], 100 <= 1000]]
```

<!-- => 100 <= 1000 -->

---

The tactic `"Decide"` builds that proof:

```wl
proof = TypeTheoryProof[And[1 <= 2, Not[2 == 3]], {"Decide"}]
```

<!-- => Proof complete -->

The proof term:

```wl
proof["Term"]
```

<!-- => decideSoundness[equalityReflexivity[true]] -->

---

[Decide]() is a definition by the recursor of [Decidable](), and rests on no axiom:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[Decide]]
```

<!-- => <||> -->

## Possible Issues

A proposition with no instance of [Decidable]() has no decision:

```wl
TypeTheoryType[Decide[Nonempty[Naturals]]]
```

<!-- => Failure["NoInstance", ...] -->

---

A statement about every natural number has no decision, since no computation checks them all:

```wl
TypeTheoryType[Decide[ForAll[{Typed[n, Naturals]}, n == n]]]
```

<!-- => Failure["NoInstance", ...] -->

---

A proposition variable has no decision unless an instance-implicit argument gives one:

```wl
TypeTheoryType[Typed[p, TypeUniverse[0]] |-> Decide[p]]
```

<!-- => Failure["UnsolvedImplicitArgument", ...] -->

---

The decision of `n <= n + 1` depends on `n`, so it does not compute:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, Decide[n <= n + 1] == "true"], {"Introduce"[n], "Reflexivity"}]
```

<!-- => Failure["NotReflexive", ...] -->

---

A definition by [Decide]() computes only where the decision does:

```wl
larger = TypeTheoryEnvironment[TypeTheoryDefinition[Larger,
    {Typed[m, Naturals], Typed[n, Naturals]} |-> InductiveRecursor[Booleans][Typed[b, Booleans] |-> Naturals, m, n, Decide[m <= n]]
]]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

The larger of `n` and `n + 1` is `n + 1`, but not by computation:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, Larger[n, n + 1] == n + 1], larger, {"Introduce"[n], "Reflexivity"}]
```

<!-- => Failure["NotReflexive", ...] -->

---

`"decideSoundness"` proves only what is decided true:

```wl
TypeTheoryType[Typed["decideSoundness"["equalityReflexivity"["true"]], 1000 <= 100]]
```

<!-- => Failure["TypeMismatch", ...] -->
