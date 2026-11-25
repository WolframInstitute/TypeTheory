---
Template: TechNote
Name: ZermeloFraenkelSetTheory
Title: Zermelo-Fraenkel Set Theory
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/tutorial/ZermeloFraenkelSetTheory
Keywords: [set theory, ZFC, Zermelo-Fraenkel, axiom of choice, Aczel, model, W-type, quotient, extensionality, regularity, replacement, classes, membership, Metamath, set.mm]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude, TheIntegers, Paradoxes]
---

Type theory and set theory are two foundations of mathematics, and each can model the other. <code>[TypeTheoryEnvironment]()["ZFC"]</code> builds the sets of Zermelo-Fraenkel set theory with choice inside the type theory, the way Peter Aczel did: a set is a well-founded tree whose branches are sets, and two trees are the same set when they have the same members. Every axiom of ZFC is then a theorem, proved from the three axioms of the prelude - propositional extensionality, the soundness of quotients and choice - and the environment declares no axiom of its own.

## The Environment

The prelude with the model:

```wl
zfc = TypeTheoryEnvironment["ZFC"]
```

<!-- => TypeTheoryEnvironment summary box: 340 constants -->

Its axioms are the prelude's:

```wl
Information[zfc, "Axioms"] === Information[TypeTheoryEnvironment["Prelude"], "Axioms"]
```

<!-- => True -->

## Pre-Sets

A pre-set is a small type of indices and a function from it to pre-sets: a tree, each of whose children is again a pre-set. It is an inductive type with one constructor, whose recursive field is a function:

```wl
zfc["PreSet"]
```

<!-- => inductive PreSet : Type 1 | preSet : ∀_{α∶Type} ∀_{elements∶α → PreSet} PreSet -->

Two pre-sets are equivalent when every element of each is equivalent to some element of the other, by recursion on the first and cases on the second:

```wl
zfc["preSetEquivalent"]
```

<!-- => definition preSetEquivalent : PreSet → PreSet → Prop := (x ∶ PreSet) ↦ PreSet_rec[...] -->

## Sets and Membership

A set is a class of equivalent pre-sets, a [QuotientType](). The indices of a pre-set range over the small types, so the sets live one universe above them:

```wl
zfc["Set"]
```

<!-- => definition Set : Type 1 := QuotientType[preSetEquivalent] -->

Membership, `x ∈ y`, is [Element](): x is equivalent to some element of y, lifted through both arguments with [QuotientLift]():

```wl
TypeTheoryType[TypeTheoryTerm[Element, "ZFC"]]
```

<!-- => Set → Set → Prop -->

Lifting computes, so membership of the classes of two pre-sets is membership of the pre-sets, with no proof:

```wl
DefinitionallyEqualQ[
	TypeTheoryTerm[{Typed[\[Alpha], TypeUniverse[1]], Typed[f, \[Alpha] -> "PreSet"], Typed[x, "PreSet"]} |-> Element["setOfPreSet"[x], "setOfPreSet"["preSet"[\[Alpha], f]]], "ZFC"],
	TypeTheoryTerm[{Typed[\[Alpha], TypeUniverse[1]], Typed[f, \[Alpha] -> "PreSet"], Typed[x, "PreSet"]} |-> Exists[{Typed[i, \[Alpha]]}, "preSetEquivalent"[x, f[i]]], "ZFC"]
]
```

<!-- => True -->

## Extensionality

Sets with the same members are equal. Equivalence of pre-sets is defined so that this holds, and the soundness of quotients turns equivalent pre-sets into equal sets:

```wl
TypeTheoryType[TypeTheoryTerm["extensionality", "ZFC"]]
```

<!-- => ∀_{a∶Set} ∀_{b∶Set} (∀_{z∶Set} z ∈ a ⇔ z ∈ b) ⇒ a == b -->

## Constructions

Every set this environment builds is a range: `"setRange"[α, F]` is the set of the values of a function F on a small type α, made by choosing a pre-set for each value. Its members are the values:

```wl
TypeTheoryType[TypeTheoryTerm["elementOfRange", "ZFC"]]
```

<!-- => ∀_{α∶Type} ∀_{F∶α → Set} ∀_{c∶Set} c ∈ setRange[α, F] ⇔ ∃_{j∶α} c == F[j] -->

Pairs are the range of a function on the Booleans, unions of one on pairs of indices, power sets of one on the predicates on the indices, separation of one on a subtype. Each comes with the theorem that says what its members are:

```wl
TypeTheoryType[TypeTheoryTerm["elementOfPair", "ZFC"]]
```

<!-- => ∀_{a∶Set} ∀_{b∶Set} ∀_{c∶Set} c ∈ pairSet[a, b] ⇔ c == a ∨ c == b -->

```wl
TypeTheoryType[TypeTheoryTerm["elementOfUnion", "ZFC"]]
```

<!-- => ∀_{a∶Set} ∀_{c∶Set} c ∈ unionSet[a] ⇔ ∃_{y∶Set} y ∈ a ∧ c ∈ y -->

```wl
TypeTheoryType[TypeTheoryTerm["elementOfPower", "ZFC"]]
```

<!-- => ∀_{a∶Set} ∀_{c∶Set} c ∈ powerSet[a] ⇔ ∀_{z∶Set} z ∈ c ⇒ z ∈ a -->

```wl
TypeTheoryType[TypeTheoryTerm["elementOfSeparation", "ZFC"]]
```

<!-- => ∀_{a∶Set} ∀_{P∶Set → Prop} ∀_{c∶Set} c ∈ separationSet[a, P] ⇔ c ∈ a ∧ P[c] -->

## A Theorem of One's Own

The theorems of the model are the tools for new ones. The pair of a with itself has a as its only member, from `"elementOfPair"` and `"orElimination"`, which takes either side of an [Or]() to the same conclusion:

```wl
singletons = TypeTheoryEnvironment["ZFC", {
	TypeTheoryTheorem[
		"pairSingleton",
		ForAll[{Typed[a, "Set"], Typed[c, "Set"]}, Implies[Element[c, "pairSet"[a, a]], c == a]],
		Function[{Typed[a, "Set"], Typed[c, "Set"], Typed[m, Element[c, "pairSet"[a, a]]]},
			"orElimination"["elementOfPair"[a, a, c][[1]][m], Function[{Typed[e, c == a]}, e], Function[{Typed[e, c == a]}, e]]
		]
	]
}]
```

<!-- => TypeTheoryEnvironment summary box: 341 constants -->

```wl
singletons["pairSingleton"]
```

<!-- => theorem pairSingleton : ∀_{a∶Set} ∀_{c∶Set} c ∈ pairSet[a, a] ⇒ c == a -->

## Regularity, Replacement, Infinity and Choice

Induction on membership comes from induction on pre-sets: a property that holds of a set whenever it holds of all its members holds of every set. Regularity follows, classically:

```wl
TypeTheoryType[TypeTheoryTerm["regularity", "ZFC"]]
```

<!-- => ∀_{x∶Set} (∃_{y∶Set} y ∈ x) ⇒ ∃_{y∶Set} y ∈ x ∧ ∀_{z∶Set} z ∈ y ⇒ ¬ z ∈ x -->

Replacement takes the chosen value of a functional relation at each member:

```wl
TypeTheoryType[TypeTheoryTerm["replacement", "ZFC"]]
```

<!-- => ∀_{ψ∶Set → Set → Prop} ∀_{x∶Set} (∀_{w∶Set} ∃_{y∶Set} ∀_{z∶Set} ψ[z, w] ⇒ z == y) ⇒ ∃_{y∶Set} ∀_{z∶Set} z ∈ y ⇔ ∃_{w∶Set} w ∈ x ∧ ψ[z, w] -->

Infinity gives every set x a set that contains it and in which every member is a member of another, the range of x, its singleton, the singleton of that and so on:

```wl
TypeTheoryType[TypeTheoryTerm["infinity", "ZFC"]]
```

<!-- => ∀_{x∶Set} ∃_{y∶Set} x ∈ y ∧ ∀_{z∶Set} z ∈ y ⇒ ∃_{w∶Set} z ∈ w ∧ w ∈ y -->

Choice picks a member of each nonempty member w of x: the set of the pairs of each such w with its chosen member shares exactly one member u of w with w. That the choice is unique rests on regularity: no set is a member of itself, and no two sets are members of each other.

```wl
TypeTheoryType[TypeTheoryTerm["choiceAxiom", "ZFC"]]
```

<!-- => ∀_{x∶Set} ∃_{y∶Set} ∀_{z∶Set} ∀_{w∶Set} z ∈ w ∧ w ∈ x ⇒ ∃_{v∶Set} ∀_{u∶Set} (∃_{t∶Set} (u ∈ w ∧ w ∈ t) ∧ u ∈ t ∧ t ∈ y) ⇔ u == v -->

## What the Axioms Rest On

[TypeTheoryAxiomClosure]() gives the axioms a theorem depends on. Extensionality needs the soundness of quotients and propositional extensionality; everything that chooses a representative, choice as well:

```wl
AssociationMap[
	Function[name, Sort[Keys[TypeTheoryAxiomClosure[TypeTheoryTerm[name, "ZFC"]]]]],
	{"extensionality", "elementOfPair", "elementOfUnion", "elementOfPower", "regularity", "replacement", "infinity", "choiceAxiom"}
]
```

<!-- => <|"extensionality" -> {"propositionalExtensionality", "quotientSoundness"}, "elementOfPair" -> {"choice", "propositionalExtensionality", "quotientSoundness"}, ...|>: every other one the three -->

## Classes

A class is a predicate on sets, `"Class"`. Every set is a class, `"setClass"[x]`, the class of its members; a class A is a member of a class B when it is a set and that set satisfies B, `"classElement"[A, B]`:

```wl
zfc["classElement"]
```

<!-- => definition classElement : Class → Class → Prop := (A ∶ Class) (B ∶ Class) ↦ ∃_{a∶Set} A == setClass[a] ∧ B[a] -->

Membership of the class of a set is not [Element]() itself, but it is equal to it, as functions. Rewriting a statement about classes of sets along this equality, and along its companion `"setClassEqualFunction"` for equality, turns it into one about [Element]() and [Equal]() of sets:

```wl
TypeTheoryType[TypeTheoryTerm["classElementFunction", "ZFC"]]
```

<!-- => ((B ∶ Class) (z ∶ Set) ↦ classElement[setClass[z], B]) == ((B ∶ Class) (z ∶ Set) ↦ B[z]) -->

Classes are the vocabulary of set.mm, the Metamath database of ZFC. [MetamathLink](https://www.wolframcloud.com/obj/wolframinstitute/MetamathLink) states set.mm's axioms over this environment and proves each from the theorems above, then translates set.mm's proofs into proof terms that TypeTheory's kernel checks: set.mm's 2 + 2 = 4, with all it needs down to its construction of the complex numbers, rests on the prelude's three axioms alone.
