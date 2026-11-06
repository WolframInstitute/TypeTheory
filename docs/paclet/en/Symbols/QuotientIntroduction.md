---
Template: Symbol
Name: QuotientIntroduction
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/QuotientIntroduction
Keywords: [quotient, equivalence class, class of an element, representative, Quot.mk, Lean, prelude, integers, quotientSoundness]
SeeAlso: [QuotientType, QuotientLift, QuotientInduction, TypeTheoryQuotients, DefinitionallyEqualQ]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude, RulesAndComputation, TheIntegers]
---

## Usage

<code>[QuotientIntroduction]()[*r*, *a*]</code> is the class of *a* in <code>[QuotientType]()[*r*]</code>.

## Details & Options

- [QuotientIntroduction]() is a constant of the kernel, declared by [TypeTheoryQuotients]() in the prelude, as Lean's `Quot.mk`.
- The type α of *a* is an implicit argument; the relation *r* is explicit.
- The classes of two elements that *r* relates are equal by the axiom `"quotientSoundness"`, not by computation: <code>[QuotientIntroduction]()[*r*, *a*]</code> and <code>[QuotientIntroduction]()[*r*, *b*]</code> are equal by computation only when *a* and *b* are.
- [QuotientLift]() and [QuotientInduction]() compute on a class, to the function or the premise at its element.
- In <code>[TypeTheoryEnvironment]()["Integers"]</code>, `"integerOfPair"[p]` is <code>[QuotientIntroduction]()["integerRelation", *p*]</code>, and integers written with numbers are classes of pairs: `2 - 5` is the class of (2, 5), `-3` that of (0, 3), and a natural number *n* where an integer is expected that of (*n*, 0), by the coercion `"integerOfNatural"`.
- The type of a class shows as <code>[QuotientType]()[*r*]</code>, also where a definition names it, as [Integers]() names <code>[QuotientType]()["integerRelation"]</code>.

## Basic Examples

The type of [QuotientIntroduction]():

```wl
TypeTheoryType[QuotientIntroduction]
```

<!-- => ∀_{α ∶ Sort u} ∀_r∶α → α → Prop α → QuotientType[r] -->

---

The class of the pair (2, 5), the integer 2 - 5:

```wl
TypeTheoryType[QuotientIntroduction["integerRelation", "pair"[2, 5]], "Integers"]
```

<!-- => QuotientType[integerRelation] -->

---

The classes of (2, 5) and (3, 6) are equal by `"quotientSoundness"`, since 2 + 6 and 3 + 5 compute to 8:

```wl
TypeTheoryType[Typed["quotientSoundness"["equalityReflexivity"[8]], QuotientIntroduction["integerRelation", "pair"[2, 5]] == QuotientIntroduction["integerRelation", "pair"[3, 6]]], "Integers"]
```

<!-- => QuotientIntroduction[integerRelation, (2, 5)] == QuotientIntroduction[integerRelation, (3, 6)] -->

## Scope

An integer written as a difference of numbers is the class of the pair, by computation:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Typed[2 - 5, Integers], "Integers"], TypeTheoryTerm[QuotientIntroduction["integerRelation", "pair"[2, 5]], "Integers"]]
```

<!-- => True -->

---

The integers' function from pairs is the class:

```wl
TypeTheoryEnvironment["Integers"]["integerOfPair"]
```

<!-- => definition integerOfPair : ℕ × ℕ → ℤ := (p ∶ ℕ × ℕ) ↦ QuotientIntroduction[integerRelation, p] -->

---

A natural number *n* is the integer of the class of (*n*, 0), by a coercion inserted where an integer is expected:

```wl
TypeTheoryEnvironment["Integers"]["integerOfNatural"]
```

<!-- => coercion integerOfNatural : ℕ → ℤ := (n ∶ ℕ) ↦ integerOfPair[(n, 0)] -->

---

`"quotientSoundness"` as a tactic leaves the relation of the two elements to prove:

```wl
TypeTheoryProof[QuotientIntroduction["integerRelation", "pair"[2, 5]] == QuotientIntroduction["integerRelation", "pair"[0, 3]], "Integers", {"Apply"["quotientSoundness"]}]
```

<!-- => Proof, 1 goal: ⊢ integerRelation[(2, 5), (0, 3)] -->

---

The natural numbers up to parity, with the relation of having the same parity:

```wl
parity = TypeTheoryEnvironment[{
    TypeTheoryDefinition[Parity, Typed[
        Typed[n, Naturals] |-> InductiveRecursor[Naturals][Typed[k, Naturals] |-> Booleans, "false", {Typed[k, Naturals], Typed[r, Booleans]} |-> "not"[r], n],
        TypeSpecifier[{Naturals} -> Booleans]
    ]],
    TypeTheoryDefinition[SameParity, Typed[{Typed[m, Naturals], Typed[n, Naturals]} |-> Parity[m] == Parity[n], TypeSpecifier[{Naturals, Naturals} -> TypeUniverse[0]]]]
}]
```

<!-- => TypeTheoryEnvironment summary box: 259 constants -->

The classes of 1 and 7 are equal, since both numbers are odd by computation:

```wl
TypeTheoryProof[QuotientIntroduction[SameParity, 1] == QuotientIntroduction[SameParity, 7], parity, {"Apply"["quotientSoundness"], "Reflexivity"}]
```

<!-- => Proof complete -->

## Properties and Relations

The classes of (2, 5) and (3, 6) are equal, but not by computation:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[QuotientIntroduction["integerRelation", "pair"[2, 5]], "Integers"], TypeTheoryTerm[QuotientIntroduction["integerRelation", "pair"[3, 6]], "Integers"]]
```

<!-- => False -->

---

The axiom that makes the classes of related elements equal:

```wl
TypeTheoryType["quotientSoundness"]
```

<!-- => ∀_{α ∶ Sort u} ∀_{r ∶ α → α → Prop} ∀_{a ∶ α} ∀_{b ∶ α} r[a, b] ⇒ QuotientIntroduction[r, a] == QuotientIntroduction[r, b] -->

---

A lift computes on a class. Negation, lifted from swapping a pair, takes the class of (2, 5) to the class of the swapped pair:

```wl
WeakHeadNormalForm[TypeTheoryTerm[-QuotientIntroduction["integerRelation", "pair"[2, 5]], "Integers"]]
```

<!-- => QuotientIntroduction[integerRelation, ((2, 5)〚2〛, (2, 5)〚1〛)] -->

---

An equation of integer classes is decidable, so `"Decide"` proves it by computing a Boolean:

```wl
TypeTheoryProof[QuotientIntroduction["integerRelation", "pair"[2, 5]] == QuotientIntroduction["integerRelation", "pair"[0, 3]], "Integers", {"Decide"}]
```

<!-- => Proof complete -->

## Possible Issues

The element must be in the type the relation is on. A natural number is not a pair; `"integerOfNatural"` makes it an integer:

```wl
TypeTheoryType[QuotientIntroduction["integerRelation", 3], "Integers"]
```

<!-- => Failure["TypeMismatch", ...] -->

---

`"quotientSoundness"` needs a proof of the relation. (2, 5) and (0, 4) are not related, so 5 == 5 does not do:

```wl
TypeTheoryType[Typed["quotientSoundness"["equalityReflexivity"[5]], QuotientIntroduction["integerRelation", "pair"[2, 5]] == QuotientIntroduction["integerRelation", "pair"[0, 4]]], "Integers"]
```

<!-- => Failure["TypeMismatch", ...] -->

---

The constructive environment has the quotient types but not `"quotientSoundness"`, so there two classes are equal only by computation:

```wl
TypeTheoryType["quotientSoundness", "Constructive"]
```

<!-- => Failure["ElaborationFailed", ...] -->
