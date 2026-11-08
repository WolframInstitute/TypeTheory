---
Template: Symbol
Name: QuotientLift
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/QuotientLift
Keywords: [quotient, lift, function on classes, well defined, respects the relation, Quot.lift, Lean, computation, prelude, integers, integer negation, integer addition]
SeeAlso: [QuotientType, QuotientIntroduction, QuotientInduction, TypeTheoryQuotients, WeakHeadNormalForm, DefinitionallyEqualQ]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude, RulesAndComputation, TheIntegers]
---

## Usage

<code>[QuotientLift]()[*f*, *h*, *q*]</code> applies the function *f* to the class *q*, given a proof *h* that <code>*f*[*a*] == *f*[*b*]</code> whenever <code>*r*[*a*, *b*]</code>.

## Details & Options

- [QuotientLift]() is a constant of the kernel, declared by [TypeTheoryQuotients]() in the prelude, as Lean's `Quot.lift`.
- The type α, the relation *r* and the codomain β of *f* are implicit arguments. β may be any type, data or a proposition.
- It computes on a class: <code>[QuotientLift]()[*f*, *h*, [QuotientIntroduction]()[*r*, *a*]]</code> is *f*[*a*]. This is one of the two computation rules of quotients, with that of [QuotientInduction]().
- *h* is what makes the lift well defined: two related elements, whose classes are equal by `"quotientSoundness"`, give the same value. When *f* gives classes, *h* is `"quotientSoundness"` applied to a proof that *f* takes related elements to related ones, as for the operations of the integers.
- A function of two classes lifts in one argument, then in the other; the proof for the first is by [QuotientInduction]() on the second class, as in `"integerAddition"`.
- A lift does not compute on a variable. [QuotientInduction](), or the tactic `"Induction"` on the variable, replaces it by the class of an element first.

## Basic Examples

The type of [QuotientLift]():

```wl
TypeTheoryType[QuotientLift]
```

<!-- => ∀_{α ∶ Sort u} ∀_{r ∶ α → α → Prop} ∀_{β ∶ Sort v} ∀_f∶α → β (∀_a∶α ∀_b∶α r[a, b] ⇒ f[a] == f[b]) → QuotientType[r] → β -->

---

The negation of the integers is lifted from swapping a pair, with the proof that swapping respects the relation:

```wl
TypeTheoryEnvironment["Integers"]["integerNegation"]
```

<!-- => definition integerNegation : ℤ → ℤ := (x ∶ ℤ) ↦ QuotientLift[(p ∶ ℕ × ℕ) ↦ integerOfPair[(p〚2〛, p〚1〛)], (p ∶ ℕ × ℕ) (q ∶ ℕ × ℕ) (e ∶ integerRelation[p, q]) ↦ quotientSoundness[integerNegationRespects[p, q, e]], x] -->

On a class it computes to the class of the swapped pair:

```wl
WeakHeadNormalForm[TypeTheoryTerm[-QuotientIntroduction["integerRelation", "pair"[2, 5]], "Integers"]]
```

<!-- => QuotientIntroduction[integerRelation, ((2, 5)〚2〛, (2, 5)〚1〛)] -->

---

The quotient of the natural numbers by equality:

```wl
equal = TypeTheoryTerm[Typed[{m, n} |-> m == n, Naturals -> Naturals -> TypeUniverse[0]]]
```

<!-- => m n ↦ m == n ∶ ℕ → ℕ → Prop -->

The successor respects equality, by congruence, so it lifts to the classes, and computes on one:

```wl
WeakHeadNormalForm[TypeTheoryTerm[QuotientLift[
    k |-> k + 1,
    {a, b, Typed[e, a == b]} |-> "equalityCongruence"[k |-> k + 1, e],
    QuotientIntroduction[equal, 5]
]]]
```

<!-- => 6 -->

## Scope

When the relation is the equation of the function's values, the proof of the relation is *h* itself. The total of a pair, on the classes of pairs with the same total:

```wl
WeakHeadNormalForm[TypeTheoryTerm[QuotientLift[
    Typed[p, CartesianProductType[Naturals, Naturals]] |-> p[[1]] + p[[2]],
    {p, q, e} |-> e,
    QuotientIntroduction[{Typed[p, CartesianProductType[Naturals, Naturals]], Typed[q, CartesianProductType[Naturals, Naturals]]} |-> p[[1]] + p[[2]] == q[[1]] + q[[2]], "pair"[2, 3]]
]]]
```

<!-- => 5 -->

---

The addition of the integers lifts twice, in the first argument and then in the second, and the proof for the first is by [QuotientInduction]() on the second:

```wl
TypeTheoryEnvironment["Integers"]["integerAddition"]
```

<!-- => definition integerAddition : ℤ → ℤ → ℤ := (x ∶ ℤ) (y ∶ ℤ) ↦ QuotientLift[(p ∶ ℕ × ℕ) ↦ integerAdditionOfPair[p, y], (p ∶ ℕ × ℕ) (q ∶ ℕ × ℕ) (e ∶ integerRelation[p, q]) ↦ QuotientInduction[(s ∶ ℕ × ℕ) ↦ quotientSoundness[integerAdditionRespectsLeft[p, q, s, e]], y], x] -->

The sum of -3, the class of (2, 5), and 3, the class of (4, 1), computes to the class of (6, 6):

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Typed[2 - 5, Integers] + Typed[4 - 1, Integers], "Integers"], TypeTheoryTerm[QuotientIntroduction["integerRelation", "pair"[6, 6]], "Integers"]]
```

<!-- => True -->

---

A lift into the Booleans: the equality test of the integers, which compares a + d with c + b for the pairs (a, b) and (c, d):

```wl
TypeTheoryEnvironment["Integers"]["integerEqual"]
```

<!-- => definition integerEqual : ℤ → ℤ → 𝔹 := (x ∶ ℤ) (y ∶ ℤ) ↦ QuotientLift[(p ∶ ℕ × ℕ) ↦ integerEqualOfPair[p, y], (p ∶ ℕ × ℕ) (q ∶ ℕ × ℕ) (e ∶ integerRelation[p, q]) ↦ QuotientInduction[(s ∶ ℕ × ℕ) ↦ equalOfEquivalent[p〚1〛 + s〚2〛, s〚1〛 + p〚2〛, q〚1〛 + s〚2〛, s〚1〛 + q〚2〛, integerEqualRespectsLeft[p, q, s, e]], y], x] -->

So deciding whether -3 + 3 is 0 computes through the lifts to a Boolean:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Decide[Typed[2 - 5, Integers] + Typed[4 - 1, Integers] == 0], "Integers"]]
```

<!-- => true -->

## Applications

Doubling an integer, defined on pairs. A theorem says that doubling both numbers of related pairs gives related pairs, and `"quotientSoundness"` turns it into the proof *h*:

```wl
doubling = TypeTheoryEnvironment["Integers", {
    TypeTheoryTheorem[DoublingRespects, TypeTheoryProof[
        ForAll[{Typed[p, CartesianProductType[Naturals, Naturals]], Typed[q, CartesianProductType[Naturals, Naturals]]},
            Implies["integerRelation"[p, q], "integerRelation"["pair"[2 p[[1]], 2 p[[2]]], "pair"[2 q[[1]], 2 q[[2]]]]]
        ],
        "Integers",
        {"Introduce"[p, q, h], "LinearArithmetic"}
    ]],
    TypeTheoryDefinition[IntegerDouble, Typed[x, Integers] |-> QuotientLift[
        Typed[p, CartesianProductType[Naturals, Naturals]] |-> "integerOfPair"["pair"[2 p[[1]], 2 p[[2]]]],
        {p, q, e} |-> "quotientSoundness"[DoublingRespects[p, q, e]],
        x
    ]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 356 constants -->

The double of -3, the class of (2, 5), computes to the class of (4, 10):

```wl
DefinitionallyEqualQ[TypeTheoryTerm[IntegerDouble[Typed[2 - 5, Integers]], doubling], TypeTheoryTerm[QuotientIntroduction["integerRelation", "pair"[4, 10]], doubling]]
```

<!-- => True -->

It is -6:

```wl
TypeTheoryProof[IntegerDouble[Typed[2 - 5, Integers]] == -6, doubling, {"Decide"}]
```

<!-- => Proof complete -->

## Properties and Relations

The prelude proves function extensionality with a lift: applying a function to a point respects being equal at every point, so it lifts to the classes of functions by that relation, and `"quotientSoundness"` makes two such functions one class:

```wl
TypeTheoryType["functionExtensionality"]
```

<!-- => ∀_{α ∶ Sort u} ∀_{β ∶ α → Sort v} ∀_{f ∶ ∀_x∶α β[x]} ∀_{g ∶ ∀_x∶α β[x]} (∀_x∶α f[x] == g[x]) ⇒ f == g -->

---

A lift computes on a class, but not on a variable: for an integer `x`, `-(-x)` is stuck at the lifts of negation, so it is not `x` by computation:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers]}, -(-x) == x], "Integers", {"Introduce"[x], "Reflexivity"}]
```

<!-- => Failure["NotReflexive", ...] -->

`"Induction"` on `x` makes it the class of a pair, on which the lifts compute:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers]}, -(-x) == x], "Integers", {"Introduce"[x], "Induction"[x], "Introduce"[p], "Reflexivity"}]
```

<!-- => Proof complete -->

## Possible Issues

A function lifts only with a proof that it respects the relation:

```wl
equal = TypeTheoryTerm[Typed[{m, n} |-> m == n, Naturals -> Naturals -> TypeUniverse[0]]]
```

<!-- => m n ↦ m == n ∶ ℕ → ℕ → Prop -->

A proof of something else is refused:

```wl
TypeTheoryType[QuotientLift[Typed[k, Naturals] |-> 7, {a, b, Typed[e, a == b]} |-> "equalityReflexivity"[a], QuotientIntroduction[equal, 5]]]
```

<!-- => Failure["TypeMismatch", ...] -->

---

A function that tells the elements of a class apart does not lift. The first number of a pair is not a function of the integer, since (2, 5) and (0, 3) are one integer, and the proof of the relation does not say that first numbers are equal:

```wl
TypeTheoryType[QuotientLift[
    Typed[p, CartesianProductType[Naturals, Naturals]] |-> p[[1]],
    {Typed[p, CartesianProductType[Naturals, Naturals]], Typed[q, CartesianProductType[Naturals, Naturals]], Typed[e, "integerRelation"[p, q]]} |-> e,
    Typed[2 - 5, Integers]
], "Integers"]
```

<!-- => Failure["TypeMismatch", ...] -->
