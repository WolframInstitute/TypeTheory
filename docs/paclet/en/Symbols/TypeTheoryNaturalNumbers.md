---
Template: Symbol
Name: TypeTheoryNaturalNumbers
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryNaturalNumbers
Keywords: [natural numbers, literals, addition, multiplication, arithmetic, integers, GMP, trusted, declaration, environment]
SeeAlso: [TypeTheoryInductiveType, TypeTheoryEnvironment, NaturalNumberZero, NaturalNumberSuccessor]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[TypeTheoryNaturalNumbers]()[*type*, *zero*, *successor*]</code> registers the inductive type *type*, with the constructors *zero* and *successor*, as the natural numbers, so the literals `0`, `1`, `2`, ... are elements of *type*.

<code>[TypeTheoryNaturalNumbers]()[*type*, *zero*, *successor*, &lt;|*role* -> *operation*, ...|&gt;]</code> also registers operations that the kernel computes on literals with integers.

<code>[TypeTheoryNaturalNumbers]()[*type*, *zero*, *successor*, *addition*]</code> registers addition as the only operation.

## Details & Options

- The registration is checked strictly: *type* must be an inductive type in <code>[TypeUniverse]()[1]</code> with no parameters, indices or universe parameters, whose constructors are exactly *zero* and *successor*.
- A literal is its constructor form by computation: `2` is `successor[successor[zero]]`.
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

- These are the operations Lean's kernel computes on its literals with GMP, with the same values at 0. An operation of a role must be a definition or an axiom of type <code>*type* → *type* → *type*</code>, <code>*type* → *type*</code> for `"Log2"`, and <code>*type* → *type* → *B*</code> for `"Equal"` and `"LessEqual"`, where *B* is an inductive type with two constructors without fields, false and then true, as [Booleans]() is.
- The kernel trusts that an operation computes what its role says, as Lean's kernel trusts GMP: an operation that computes something else makes the environment inconsistent. It checks the operation's type, not its definition.
- An operation computes on arguments that compute to literals, and unfolds otherwise. Powers and left shifts by 2^24 or more unfold, as in Lean.
- An environment registers its natural numbers once. A later registration of the same *type*, *zero* and *successor* adds operations. The prelude registers [NonNegativeIntegers]() with [Plus](), [Subtract](), [Times]() and [Power](), and with the Boolean comparisons `"equal"` and `"lessEqual"`, through which [NaturalNumberEqualityDecidable]() and [LessEqualDecidable]() decide literals in one step; <code>[Information]()[*env*, "NaturalNumbers"]</code> lists the operations of an environment.
- Natural numbers of your own go in an environment built on the empty one, <code>[TypeTheoryEnvironment]()[]</code>.
- In a notebook, the zero of the registered natural numbers shows as `0`, and the successor of *n* as <code>*n* + 1</code>, as Lean shows them.

## Basic Examples

The prelude registers [NonNegativeIntegers]() as its natural numbers, so literals are natural numbers:

```wl
TypeOf[TypeTheoryTerm[3]]
```

<!-- => ℕ -->

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
TypeOf[TypeTheoryTerm[3, unary]]
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

A later registration adds an operation: here the left shift, *m* 2^*n*, registered by the alias [Naturals]():

```wl
shifted = TypeTheoryEnvironment[{
    TypeTheoryDefinition[NaturalNumberShiftLeft, Function[{Typed[m, Naturals], Typed[n, Naturals]}, m * 2^n]],
    TypeTheoryNaturalNumbers[Naturals, NaturalNumberZero, NaturalNumberSuccessor, <|"ShiftLeft" -> NaturalNumberShiftLeft|>]
}]
```

<!-- => TypeTheoryEnvironment summary box: 165 constants -->

The shift computes on literals at once:

```wl
WeakHeadNormalForm[TypeTheoryTerm[NaturalNumberShiftLeft[3, 100], shifted]]
```

<!-- => 3802951800684688204490109616128 -->

The operations of the environment's natural numbers:

```wl
Information[shifted, "NaturalNumbers"]
```

<!-- => <|"Type" -> NonNegativeIntegers, "Zero" -> NaturalNumberZero, "Successor" -> NaturalNumberSuccessor, "Operations" -> <|"Addition" -> Plus, "Subtraction" -> Subtract, "Multiplication" -> Times, "Power" -> Power, "Equal" -> "equal", "LessEqual" -> "lessEqual", "ShiftLeft" -> NaturalNumberShiftLeft|>|> -->

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

The kernel trusts a registered operation. Register a projection as addition:

```wl
trusted = TypeTheoryEnvironment[TypeTheoryEnvironment[], {
    TypeTheoryInductiveType[Unary, TypeUniverse[1], {UnaryZero -> Unary, UnarySuccessor -> ForAll[{Typed[n, Unary]}, Unary]}],
    TypeTheoryDefinition[FirstNumber, Function[{Typed[m, Unary], Typed[n, Unary]}, m]],
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
Append[TypeTheoryEnvironment["Prelude"], TypeTheoryNaturalNumbers[NonNegativeIntegers, NaturalNumberZero, NaturalNumberSuccessor, <|"Quotient" -> NaturalNumberPredecessor|>]]
```

<!-- => Failure["InvalidNaturalNumberOperation", ...] -->
