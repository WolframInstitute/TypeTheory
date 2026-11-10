---
Template: Symbol
Name: Naturals
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Naturals
Keywords: [natural numbers, NonNegativeIntegers, Nat, alias, literal, zero, successor, induction, arithmetic, prelude]
SeeAlso: [InductiveRecursor, TypeTheoryNaturalNumbers, NaturalNumberPredecessor, TypeTheoryTerm, NonNegativeIntegers]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TypeTheoryIntroduction, ThePrelude, TheIntegers]
---

## Usage

[Naturals]() is [NonNegativeIntegers](), the natural numbers of the prelude, by a shorter name.

## Details & Options

- [Naturals]() evaluates to [NonNegativeIntegers](). Held in a term, it stands for the same constant: a symbol whose value is a declared constant stands for that constant.
- The natural numbers are an inductive type of the prelude, with the constructors `"zero"` and `"successor"`. [TypeTheoryNaturalNumbers]() registers them as the natural numbers, so the literals `0`, `1`, `2`, ... are their elements, and the constructors show as `0` and `n + 1`.
- [Plus](), [Times](), [Power]() and [Subtract]() are defined by recursion, and the kernel computes them on literals with Wolfram integers. Subtraction stops at 0; the integers are in <code>[TypeTheoryEnvironment]()["Integers"]</code>.
- <code>[InductiveRecursor]()[[Naturals]()]</code> is the recursor of the natural numbers, which `"Induction"` builds. `"Decide"`, `"Ring"`, `"LinearArithmetic"` and `"NonlinearArithmetic"` prove statements about natural numbers; see [TypeTheoryTactic](). The proofs that `"LinearArithmetic"` and `"NonlinearArithmetic"` build compute with the literals of the statement, and with literals of a few hundred, or with products of a few dozen, the kernel can reject such a proof as a computation too deep to check, so their statements are best kept to small literals.
- [Naturals]() shows as ℕ, and terms and declarations read back with [NonNegativeIntegers](), the name of the constant. Outside a term, [Naturals]() is Wolfram's domain of the non-negative integers, as in [Element]() and [FindInstance]().
- A symbol of your own given a declared constant as its value stands for it the same way, unless a binder of the same name is in scope. [True]() and the other names overloaded by type are left to their own rules.

## Basic Examples

[Naturals]() is [NonNegativeIntegers]():

```wl
InputForm[Naturals]
```

<!-- => NonNegativeIntegers -->

---

The successor function on the natural numbers:

```wl
TypeTheoryType[Typed[n, Naturals] |-> n + 1]
```

<!-- => ℕ → ℕ -->

---

A literal is a natural number:

```wl
TypeTheoryType[42]
```

<!-- => ℕ -->

## Scope

Two successors of zero, written with the constructors:

```wl
TypeTheoryTerm["successor"["successor"["zero"]]]
```

<!-- => (0 + 1) + 1 -->

They are the literal 2:

```wl
DefinitionallyEqualQ[TypeTheoryTerm["successor"["successor"["zero"]]], TypeTheoryTerm[2]]
```

<!-- => True -->

---

The kernel computes with literals of any size:

```wl
WeakHeadNormalForm[TypeTheoryTerm[2^100]]
```

<!-- => 1267650600228229401496703205376 -->

---

The recursor of the natural numbers:

```wl
TypeTheoryType[InductiveRecursor[Naturals]]
```

<!-- => ∀_m∶ℕ → Sort u m[0] → (∀_n∶ℕ m[n] → m[n + 1]) → ∀_t∶ℕ m[t] -->

---

A proof by induction over the natural numbers:

```wl
TypeTheoryProof[ForAll[{n}, 0 + n == n], {
    "Introduce"[n],
    "Induction"[n],
    "Reflexivity",
    "Introduce"[k, ih],
    "Exact"["equalityCongruence"["successor", ih]]
}]
```

<!-- => Proof complete -->

---

A closed statement about natural numbers, by computing its decision:

```wl
TypeTheoryProof[And[3 * 4 == 12, 5 <= 7], {"Decide"}]
```

<!-- => Proof complete -->

---

The square of a sum, by `"Ring"`:

```wl
TypeTheoryProof[ForAll[{m, n}, (m + n)^2 == m^2 + 2 m n + n^2], {"Introduce"[m, n], "Ring"}]
```

<!-- => Proof complete -->

---

An inequality from a hypothesis, by `"LinearArithmetic"`:

```wl
TypeTheoryProof[ForAll[{m, n, Typed[h, m <= n]}, m < n + 1], {"Introduce"[m, n, h], "LinearArithmetic"}]
```

<!-- => Proof complete -->

## Properties and Relations

The declaration of the natural numbers:

```wl
TypeTheoryEnvironment["Prelude"][Naturals]
```

<!-- => inductive ℕ : Type | zero : ℕ | successor : ℕ → ℕ -->

---

[Naturals]() and [NonNegativeIntegers]() are the same constant:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Naturals], TypeTheoryTerm[NonNegativeIntegers]]
```

<!-- => True -->

---

A declaration written with [Naturals]() reads back with [NonNegativeIntegers]():

```wl
InputForm[TypeTheoryEnvironment[{TypeTheoryDefinition[Successor, Typed[n, Naturals] |-> n + 1]}][Successor]]
```

<!-- => TypeTheoryDefinition[Successor, Typed[Function[{Typed[n, NonNegativeIntegers]}, n + 1], NonNegativeIntegers -> NonNegativeIntegers]] -->

---

A symbol of your own whose value is a constant stands for it too:

```wl
Counting = NonNegativeIntegers;
TypeTheoryType[Typed[k, Counting] |-> k]
```

<!-- => ℕ → ℕ -->

---

The constructors and operations of the prelude's natural numbers, which the kernel computes on literals:

```wl
Information[TypeTheoryEnvironment["Prelude"], "NaturalNumbers"]
```

<!-- => <|"Type" -> ℤ_≥0, "Zero" -> "zero", "Successor" -> "successor", "Operations" -> <|"Addition" -> Plus, "Subtraction" -> Subtract, "Multiplication" -> Times, "Power" -> Power, "Equal" -> "equal", "LessEqual" -> "lessEqual"|>|> -->

---

Outside a term, [Naturals]() is Wolfram's domain, here for [FindInstance]():

```wl
FindInstance[n^2 == 49, n, Naturals]
```

<!-- => {{n -> 7}} -->

---

In the integers, `3 - 5` is `-2`:

```wl
TypeTheoryProof[Typed[3 - 5, Integers] == -2, "Integers", {"Decide"}]
```

<!-- => Proof complete -->

## Possible Issues

Subtraction of natural numbers stops at 0:

```wl
TypeTheoryProof[3 - 5 == 0, {"Reflexivity"}]
```

<!-- => Proof complete -->

---

A negative number is no natural number:

```wl
TypeTheoryType[-3]
```

<!-- => Failure["ElaborationFailed", ...] -->

---

A term holds the symbol it was written with, so terms written with [Naturals]() and [NonNegativeIntegers]() are not the same expression, though they are equal:

```wl
TypeTheoryTerm[Naturals] === TypeTheoryTerm[NonNegativeIntegers]
```

<!-- => False -->

---

A binder named [Naturals]() is a variable of its own:

```wl
TypeTheoryType[{Typed[Naturals, TypeUniverse[1]], Typed[x, Naturals]} |-> x]
```

<!-- => ∀_Naturals∶Type Naturals → Naturals -->
