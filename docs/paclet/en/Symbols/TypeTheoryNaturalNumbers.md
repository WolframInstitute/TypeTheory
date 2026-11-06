---
Template: Symbol
Name: TypeTheoryNaturalNumbers
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryNaturalNumbers
Keywords: [natural numbers, literals, addition, multiplication, arithmetic, integers, GMP, trusted, declaration, environment, unary numbers, GCD, decision]
SeeAlso: [TypeTheoryInductiveType, TypeTheoryEnvironment, Naturals, WeakHeadNormalForm, Decide]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude, RulesAndComputation]
---

## Usage

<code>[TypeTheoryNaturalNumbers]()[*type*, *zero*, *successor*]</code> registers the inductive type *type*, with the constructors *zero* and *successor*, as the natural numbers, so the literals `0`, `1`, `2`, ... are elements of *type*.

<code>[TypeTheoryNaturalNumbers]()[*type*, *zero*, *successor*, &lt;|*role* -> *operation*, ...|&gt;]</code> also registers operations that the kernel computes on literals with integers.

<code>[TypeTheoryNaturalNumbers]()[*type*, *zero*, *successor*, *addition*]</code> registers addition as the only operation.

## Details & Options

- The registration is checked strictly: *type* must be an inductive type in <code>[TypeUniverse]()[1]</code> with no parameters, indices or universe parameters, whose constructors are exactly *zero* and *successor*.
- A literal is its constructor form by computation: `2` is <code>*successor*[*successor*[*zero*]]</code>, in the prelude `"successor"["successor"["zero"]]`.
- An operation is registered for a role, which says what it computes on two literals *m* and *n*, or on one for `"Log2"`:

| role | computes |
| --- | --- |
| `"Addition"` | *m* + *n* |
| `"Subtraction"` | *m* - *n*, or 0 when *n* is larger |
| `"Multiplication"` | *m* *n* |
| `"Power"` | *m*^*n*, with 0^0 = 1 |
| `"Quotient"` | <code>[Quotient]()[*m*, *n*]</code>, or 0 when *n* is 0 |
| `"Remainder"` | <code>[Mod]()[*m*, *n*]</code>, or *m* when *n* is 0 |
| `"GCD"` | <code>[GCD]()[*m*, *n*]</code> |
| `"Log2"` | the largest *k* with 2^*k* ≤ *n*, or 0 when *n* is 0 |
| `"BitAnd"`, `"BitOr"`, `"BitXor"` | <code>[BitAnd]()[*m*, *n*]</code>, <code>[BitOr]()[*m*, *n*]</code>, <code>[BitXor]()[*m*, *n*]</code> |
| `"ShiftLeft"`, `"ShiftRight"` | *m* 2^*n*, and <code>[Quotient]()[*m*, 2^*n*]</code> |
| `"Equal"`, `"LessEqual"` | whether *m* = *n*, and whether *m* ≤ *n*, as a Boolean |

- These are the operations Lean's kernel computes on its literals with GMP, with the same values at 0. An operation of a role must be a definition or an axiom without universe parameters, of type <code>*type* → *type* → *type*</code>, <code>*type* → *type*</code> for `"Log2"`, and <code>*type* → *type* → *B*</code> for `"Equal"` and `"LessEqual"`, where *B* is an inductive type with two constructors without fields, false and then true, as [Booleans]() is.
- The kernel trusts that an operation computes what its role says, as Lean's kernel trusts GMP: an operation that computes something else makes the environment inconsistent. It checks the operation's type, not its definition. An axiom registered for a role computes on literals though it has no value.
- An operation computes on arguments that compute to literals, and unfolds otherwise. Powers and left shifts by 2^24 or more unfold, as in Lean.
- An environment registers its natural numbers once. A later registration of the same *type*, *zero* and *successor* adds operations. The prelude registers [NonNegativeIntegers]() with [Plus](), [Subtract](), [Times]() and [Power](), and with the Boolean comparisons `"equal"` and `"lessEqual"`, through which `"naturalNumberEqualityDecidable"` and `"lessEqualDecidable"` decide literals in one step; <code>[Information]()[*env*, "NaturalNumbers"]</code> lists the operations of an environment.
- Natural numbers of your own go in an environment built on the empty one, <code>[TypeTheoryEnvironment]()[]</code>.
- In a notebook, the zero of the registered natural numbers shows as `0`, and the successor of *n* as <code>*n* + 1</code>, as Lean shows them.

## Basic Examples

The prelude registers [NonNegativeIntegers]() as its natural numbers, so literals are natural numbers:

```wl
TypeTheoryType[3]
```

<!-- => ℕ -->

---

Its arithmetic computes on literals with integers, at once even for large numbers:

```wl
WeakHeadNormalForm[TypeTheoryTerm[2^64 - 1]]
```

<!-- => 18446744073709551615 -->

---

Natural numbers of your own:

```wl
unary = TypeTheoryEnvironment[TypeTheoryEnvironment[], {
    TypeTheoryInductiveType[Unary, TypeUniverse[1], {UnaryZero -> Unary, UnarySuccessor -> ForAll[{Typed[n, Unary]}, Unary]}],
    TypeTheoryNaturalNumbers[Unary, UnaryZero, UnarySuccessor]
}]
```

<!-- => TypeTheoryEnvironment summary box: 4 constants -->

Literals are of the new type:

```wl
TypeTheoryType[3, unary]
```

<!-- => Unary -->

A literal is its constructor form:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[2, unary], TypeTheoryTerm[UnarySuccessor[UnarySuccessor[UnaryZero]]]]
```

<!-- => True -->

The constructors show as numbers:

```wl
TypeTheoryTerm[UnarySuccessor[UnarySuccessor[UnaryZero]], unary]
```

<!-- => 0 + 1 + 1 -->

## Scope

Unary numbers with an addition by their recursor, not yet registered:

```wl
adding = TypeTheoryEnvironment[TypeTheoryEnvironment[], {
    TypeTheoryInductiveType[Unary, TypeUniverse[1], {UnaryZero -> Unary, UnarySuccessor -> ForAll[{Typed[n, Unary]}, Unary]}],
    TypeTheoryDefinition[UnaryAddition, {Typed[m, Unary], Typed[n, Unary]} |->
        InductiveRecursor[Unary][Typed[t, Unary] |-> Unary, m, {Typed[k, Unary], Typed[r, Unary]} |-> UnarySuccessor[r], n]
    ],
    TypeTheoryNaturalNumbers[Unary, UnaryZero, UnarySuccessor]
}]
```

<!-- => TypeTheoryEnvironment summary box: 5 constants -->

The addition computes by its recursor, one successor at a time:

```wl
NormalForm[TypeTheoryTerm[UnaryAddition[2, 3], adding]]
```

<!-- => 2 + 1 + 1 + 1 -->

A later registration adds the addition as an operation, given alone:

```wl
registered = Append[adding, TypeTheoryNaturalNumbers[Unary, UnaryZero, UnarySuccessor, UnaryAddition]]
```

<!-- => TypeTheoryEnvironment summary box: 5 constants -->

Now it computes on literals at once, with integers:

```wl
WeakHeadNormalForm[TypeTheoryTerm[UnaryAddition[1000000000000000000000000000000, 1000000000000000000000000000000], registered]]
```

<!-- => 2000000000000000000000000000000 -->

---

Several operations at once, by their roles, here addition and multiplication:

```wl
arithmetic = TypeTheoryEnvironment[TypeTheoryEnvironment[], {
    TypeTheoryInductiveType[Unary, TypeUniverse[1], {UnaryZero -> Unary, UnarySuccessor -> ForAll[{Typed[n, Unary]}, Unary]}],
    TypeTheoryDefinition[UnaryAddition, {Typed[m, Unary], Typed[n, Unary]} |->
        InductiveRecursor[Unary][Typed[t, Unary] |-> Unary, m, {Typed[k, Unary], Typed[r, Unary]} |-> UnarySuccessor[r], n]
    ],
    TypeTheoryDefinition[UnaryMultiplication, {Typed[m, Unary], Typed[n, Unary]} |->
        InductiveRecursor[Unary][Typed[t, Unary] |-> Unary, UnaryZero, {Typed[k, Unary], Typed[r, Unary]} |-> UnaryAddition[r, m], n]
    ],
    TypeTheoryNaturalNumbers[Unary, UnaryZero, UnarySuccessor, <|"Addition" -> UnaryAddition, "Multiplication" -> UnaryMultiplication|>]
}]
```

<!-- => TypeTheoryEnvironment summary box: 6 constants -->

A product of two nine-digit numbers:

```wl
WeakHeadNormalForm[TypeTheoryTerm[UnaryMultiplication[123456789, 987654321], arithmetic]]
```

<!-- => 121932631112635269 -->

---

An operation added to the prelude's: the left shift, *m* 2^*n*, registered by the alias [Naturals]():

```wl
shifted = TypeTheoryEnvironment[{
    TypeTheoryDefinition[NaturalNumberShiftLeft, {Typed[m, Naturals], Typed[n, Naturals]} |-> m * 2^n],
    TypeTheoryNaturalNumbers[Naturals, "zero", "successor", <|"ShiftLeft" -> NaturalNumberShiftLeft|>]
}]
```

<!-- => TypeTheoryEnvironment summary box: 251 constants -->

The shift computes on literals at once:

```wl
WeakHeadNormalForm[TypeTheoryTerm[NaturalNumberShiftLeft[3, 100], shifted]]
```

<!-- => 3802951800684688204490109616128 -->

---

An axiom registered for a role computes on literals, though it has no value. The greatest common divisor:

```wl
divisors = TypeTheoryEnvironment[{
    TypeTheoryAxiom[NaturalGCD, TypeSpecifier[{Naturals, Naturals} -> Naturals]],
    TypeTheoryNaturalNumbers[Naturals, "zero", "successor", <|"GCD" -> NaturalGCD|>]
}]
```

<!-- => TypeTheoryEnvironment summary box: 251 constants -->

The greatest common divisor of 1071 and 462:

```wl
WeakHeadNormalForm[TypeTheoryTerm[NaturalGCD[1071, 462], divisors]]
```

<!-- => 21 -->

Reflexivity proves an equation of its values:

```wl
TypeTheoryProof[NaturalGCD[12, 18] == 6, divisors, {"Reflexivity"}]
```

<!-- => Proof complete -->

---

The Boolean comparisons of the prelude compute on literals in one step:

```wl
WeakHeadNormalForm[TypeTheoryTerm["lessEqual"[10^20, 10^19]]]
```

<!-- => false -->

So `"Decide"` proves an inequation of large literals at once:

```wl
TypeTheoryProof[2^100 + 1 != 2^100, {"Decide"}]
```

<!-- => Proof complete -->

## Properties and Relations

The natural numbers of the prelude and their operations:

```wl
Information[TypeTheoryEnvironment["Prelude"], "NaturalNumbers"]
```

<!-- => <|"Type" -> ℤ_≥0, "Zero" -> "zero", "Successor" -> "successor", "Operations" -> <|"Addition" -> Plus, "Subtraction" -> Subtract, "Multiplication" -> Times, "Power" -> Power, "Equal" -> "equal", "LessEqual" -> "lessEqual"|>|> -->

---

The prelude registers them in three declarations, each adding operations:

```wl
Select[Normal[TypeTheoryEnvironment["Prelude"]], MatchQ[_TypeTheoryNaturalNumbers]]
```

<!-- => {TypeTheoryNaturalNumbers[ℤ_≥0, "zero", "successor", Association["Addition" -> Plus]], TypeTheoryNaturalNumbers[ℤ_≥0, "zero", "successor", Association["Subtraction" -> Subtract, "Multiplication" -> Times, "Power" -> Power]], TypeTheoryNaturalNumbers[ℤ_≥0, "zero", "successor", Association["Equal" -> "equal", "LessEqual" -> "lessEqual"]]} -->

---

Subtraction of natural numbers is 0 where the second is larger:

```wl
TypeTheoryProof[3 - 5 == 0, {"Reflexivity"}]
```

<!-- => Proof complete -->

---

And 0^0 is 1:

```wl
WeakHeadNormalForm[TypeTheoryTerm[0^0]]
```

<!-- => 1 -->

## Possible Issues

A type with two constructors that are not a zero and a successor cannot be registered:

```wl
TypeTheoryEnvironment[TypeTheoryEnvironment[], {
    TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}],
    TypeTheoryNaturalNumbers[Bit, BitZero, BitOne]
}]
```

<!-- => Failure["InvalidNaturalNumbers", ...] -->

---

The prelude has its natural numbers already, so another type cannot be registered there:

```wl
TypeTheoryEnvironment[{
    TypeTheoryInductiveType[Unary, TypeUniverse[1], {UnaryZero -> Unary, UnarySuccessor -> ForAll[{Typed[n, Unary]}, Unary]}],
    TypeTheoryNaturalNumbers[Unary, UnaryZero, UnarySuccessor]
}]
```

<!-- => Failure["NaturalNumbersRegistered", ...] -->

---

The kernel trusts a registered operation. Register a projection as addition:

```wl
trusted = TypeTheoryEnvironment[TypeTheoryEnvironment[], {
    TypeTheoryInductiveType[Unary, TypeUniverse[1], {UnaryZero -> Unary, UnarySuccessor -> ForAll[{Typed[n, Unary]}, Unary]}],
    TypeTheoryDefinition[FirstNumber, {Typed[m, Unary], Typed[n, Unary]} |-> m],
    TypeTheoryNaturalNumbers[Unary, UnaryZero, UnarySuccessor, <|"Addition" -> FirstNumber|>]
}]
```

<!-- => TypeTheoryEnvironment summary box: 5 constants -->

It computes as addition on literals, though its definition gives its first argument:

```wl
WeakHeadNormalForm[TypeTheoryTerm[FirstNumber[2, 3], trusted]]
```

<!-- => 5 -->

---

An operation must have the type of its role:

```wl
TypeTheoryEnvironment[{TypeTheoryNaturalNumbers[NonNegativeIntegers, "zero", "successor", <|"Quotient" -> NaturalNumberPredecessor|>]}]
```

<!-- => Failure["InvalidNaturalNumberOperation", ...] -->

---

A role must be one of those in the table:

```wl
TypeTheoryEnvironment[{
    TypeTheoryDefinition[Halve, Typed[n, Naturals] |-> n],
    TypeTheoryNaturalNumbers[Naturals, "zero", "successor", <|"Half" -> Halve|>]
}]
```

<!-- => Failure["InvalidNaturalNumberOperation", ...] -->
