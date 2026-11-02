---
Template: Symbol
Name: TypeTheoryFormalize
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryFormalize
Keywords: [formalization, Wolfram Language definitions, DownValues, implementation, compiler, built-in signatures]
SeeAlso: [TypeTheoryDefinition, TypeTheoryAxiom, TypeTheoryEnvironment, TypeOf]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[TypeTheoryFormalize]()[*symbol*]</code> gives the declarations that make the Wolfram Language function *symbol* a constant of the default environment: a definition read off its definitions where they translate, typed by elaboration, and otherwise an axiom that *symbol* computes.

<code>[TypeTheoryFormalize]()[*symbol*, *environment*]</code> makes the declarations for *environment*.

## Details & Options

- The definitions are read by the compiler of the WolframKernel project, from the paclet Wolfram/KernelCompiler, which TypeTheory loads when it first formalizes a symbol. Where it is missing, [TypeTheoryFormalize]() gives a [Failure]() that names how to install it.
- A symbol is a [TypeTheoryDefinition]() where it has one definition, its arguments bound by plain patterns or by `_Integer` and `_Rational`, and its body arithmetic, list literals, calls of built-ins that have a signature, and calls of other symbols, formalized first and declared before it.
- Otherwise it is a [TypeTheoryAxiom]() with `"Implementation" -> symbol`: the Wolfram Language computes it, and the kernel never does.
- The option `"Type" -> type` gives the type the constant must have: a definition is checked against it, and an axiom takes it. Without it, an axiom's type is `"Expressions" -> ... -> "Expressions"`, one `"Expressions"` for each argument, `"Expressions"` being the type of any Wolfram Language expression.
- A built-in that a body calls is declared by its signature, where the environment does not declare it already: precise where the built-in allows, as [Simplify]() with the type ∀ A, A → A, and over `"Expressions"` otherwise, as [D](). The numbers of the environment go into `"Expressions"` by coercions. No equation about a built-in is assumed.
- The result is a list of declarations, to extend an environment with: <code>[TypeTheoryEnvironment]()[*environment*, [TypeTheoryFormalize]()[*symbol*, *environment*]]</code>.

## Basic Examples

A Wolfram Language function on integers:

```wl
square[x_Integer] := x^2 + 1
```

---

It translates, and elaboration types it:

```wl
TypeTheoryFormalize[square, TypeTheoryEnvironment["Integers"]]
```

<!-- => {TypeTheoryDefinition[square, Function[{Typed[x, Integers]}, x^2 + 1]]} -->

## Scope

A function that calls another is formalized after it:

```wl
square[x_Integer] := x^2 + 1;
next[x_Integer] := square[x] + 1;
integers = TypeTheoryEnvironment["Integers"];
formalized = TypeTheoryEnvironment[integers, TypeTheoryFormalize[next, integers]]
```

<!-- => TypeTheoryEnvironment summary box -->

```wl
TypeOf[TypeTheoryTerm[next, formalized]]
```

<!-- => ℤ → ℤ -->

---

A built-in with a signature is declared with it:

```wl
simplified[x_Integer] := Simplify[x + 1];
TypeTheoryFormalize[simplified, TypeTheoryEnvironment["Integers"]][[All, 1]]
```

<!-- => {Simplify, simplified} -->

## Options

### Type

A function that does not translate is an axiom of the type given, which it computes:

```wl
reversed[s_] := StringReverse[s];
TypeTheoryFormalize[reversed, "Type" -> Integers -> Integers]
```

<!-- => {TypeTheoryAxiom[reversed, Integers -> Integers, "Implementation" -> reversed]} -->

## Possible Issues

Without a type, a function that does not translate takes `"Expressions"` for each argument:

```wl
reversed[s_] := StringReverse[s];
Last[TypeTheoryFormalize[reversed, TypeTheoryEnvironment["Integers"]]]
```

<!-- => TypeTheoryAxiom[reversed, "Expressions" -> "Expressions", "Implementation" -> reversed] -->
