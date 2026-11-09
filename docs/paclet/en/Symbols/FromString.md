---
Template: Symbol
Name: FromString
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/FromString
Keywords: [string literal, from string, IsString, fromString, OfNat, instance, class, default instance, strings, expressions, atoms, prelude]
SeeAlso: [Strings, Expressions, Atoms, Typed, TypeTheoryType]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, Elaboration, InstancesAndCoercions]
---

## Usage

<code>[FromString]()[*s*]</code> is the value of the type expected whose string is *s*: a string, an expression or an atom.

## Details & Options

- [FromString]() is a definition of the prelude, of the type `∀ {A} [IsString[A]] Strings → A`. Its instance argument, of the class `"IsString"`, is found by the type *A* expected: Haskell's class `IsString` with its `fromString`.
- The prelude has instances for [Strings](), the string itself, [Expressions](), the string as an expression, and [Atoms](), its atom `"stringAtom"[s]`. Another type gets its own by an instance of `"IsString"` declared with `"Instance" -> True`.
- Where nothing decides the type, <code>[FromString]()[*s*]</code> is the string *s*: the instance for [Strings]() is declared last, and the latest instance that fits is the one found. Inside a function, it is found before the function's variables go out of scope.
- A string literal applied to [FromString]() is the string, even where it names a constant: <code>[FromString]()["true"]</code> is the string `"true"`, though `"true"` alone is the Boolean.
- A string on its own, where no type is expected, is the name of a constant, as in <code>[TypeTheoryType]()["successor"]</code>; one that names none is refused, as a misspelled name would be. Write <code>[FromString]()[*s*]</code> or <code>[Typed]()[*s*, [Strings]()]</code> for the string.

## Basic Examples

The type of [FromString]():

```wl
TypeTheoryType[FromString]
```

<!-- => ∀_{A∶Type u} ∀_[c∶IsString[A]] Strings → A -->

---

Where nothing decides the type, it is a string:

```wl
TypeTheoryType[FromString["Hi"]]
```

<!-- => Strings -->

---

Where an expression is expected, it is the expression:

```wl
TypeTheoryType[Typed[FromString["Hi"], Expressions]]
```

<!-- => Expressions -->

## Scope

The class whose instances it finds:

```wl
TypeTheoryType["IsString"]
```

<!-- => Type u → Type u -->

---

Where an atom is expected, it is the atom of the string:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Typed[FromString["Hi"], Atoms]], TypeTheoryTerm["stringAtom"["Hi"]]]
```

<!-- => True -->

---

A function's result is a string where nothing else decides it:

```wl
TypeTheoryType[n |-> If[n == 0, FromString["none"], FromString["some"]]]
```

<!-- => ℕ → Strings -->

---

The type a function is given decides it:

```wl
TypeTheoryType[Typed[n |-> FromString["a"], NonNegativeIntegers -> Expressions]]
```

<!-- => ℕ → Expressions -->

---

It applies to a variable as well as a literal:

```wl
TypeTheoryType[s |-> Typed[FromString[s], Expressions]]
```

<!-- => Strings → Expressions -->

## Properties and Relations

A string that names a constant is the string as the argument of [FromString](), and the constant on its own:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[FromString["true"]], TypeTheoryTerm["string"[{116, 114, 117, 101}]]]
```

<!-- => True -->

---

At [Strings](), [FromString]() is the identity, which the kernel proves by computing:

```wl
TypeTheoryProof[ForAll[{s}, Typed[FromString[s], Strings] == s], {"Introduce"[s], "Reflexivity"}]
```

<!-- => Proof complete -->

---

At [Expressions](), it is the string written where an expression is expected:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Typed[FromString["Hi"], Expressions]], TypeTheoryTerm[Typed["Hi", Expressions]]]
```

<!-- => True -->

## Possible Issues

A type with no instance of `"IsString"` has no values written by strings:

```wl
TypeTheoryType[Typed[FromString["12"], NonNegativeIntegers]]
```

<!-- => Failure["NoInstance", ...] -->

---

A string on its own that names no constant is refused, as a misspelled name would be:

```wl
TypeTheoryType["Hi"]
```

<!-- => Failure["ElaborationFailed", ...] -->
