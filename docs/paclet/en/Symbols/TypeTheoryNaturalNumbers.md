---
Template: Symbol
Name: TypeTheoryNaturalNumbers
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryNaturalNumbers
Keywords: [natural numbers, literals, addition, integers, declaration, environment]
SeeAlso: [TypeTheoryInductiveType, TypeTheoryEnvironment, NaturalNumberZero, NaturalNumberSuccessor]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[TypeTheoryNaturalNumbers]()[*type*, *zero*, *successor*]</code> registers the inductive type *type*, with the constructors *zero* and *successor*, as the natural numbers, so the literals `0`, `1`, `2`, ... are elements of *type*.

<code>[TypeTheoryNaturalNumbers]()[*type*, *zero*, *successor*, *addition*]</code> also adds two literals by integer addition.

## Details & Options

- The kernel trusts what it computes on literals, so the registration is checked strictly: *type* must be an inductive type in <code>[TypeUniverse]()[1]</code> with no parameters, indices or universe parameters, whose constructors are exactly *zero* and *successor*.
- *addition* must be defined, up to the names of its variables, by recursion on its second argument, as the prelude's [Plus]() is. Then adding two literals as integers agrees with unfolding *addition*.
- A literal is its constructor form by computation: `2` is `successor[successor[zero]]`.
- An environment registers natural numbers once. The prelude registers [NonNegativeIntegers](), so natural numbers of your own go in an environment built on the empty one, <code>[TypeTheoryEnvironment]()[]</code>.
- In a notebook, the zero of the registered natural numbers shows as `0`, and the successor of *n* as <code>*n* + 1</code>, as Lean shows them.

## Basic Examples

The prelude registers [NonNegativeIntegers]() as its natural numbers, so literals are natural numbers:

```wl
TypeOf[TypeTheoryTerm[3]]
```

<!-- => ℕ -->

---

Natural numbers of your own:

```wl
unary = TypeTheoryEnvironment[TypeTheoryEnvironment[], {
    TypeTheoryInductiveType[Unary, TypeUniverse[1], {UnaryZero -> Unary, UnarySuccessor -> ForAll[{Typed[n, Unary]}, Unary]}],
    TypeTheoryNaturalNumbers[Unary, UnaryZero, UnarySuccessor]
}];
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

## Possible Issues

A type with two constructors that are not a zero and a successor cannot be registered:

```wl
TypeTheoryEnvironment[TypeTheoryEnvironment[], {
    TypeTheoryInductiveType[Bit, TypeUniverse[1], {BitZero -> Bit, BitOne -> Bit}],
    TypeTheoryNaturalNumbers[Bit, BitZero, BitOne]
}]
```

<!-- => Failure["InvalidNaturalNumbers", ...] -->
