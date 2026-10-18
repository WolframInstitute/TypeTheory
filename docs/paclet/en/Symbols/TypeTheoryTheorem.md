---
Template: Symbol
Name: TypeTheoryTheorem
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryTheorem
Keywords: [theorem, proof, declaration, proposition, kernel, environment]
SeeAlso: [TypeTheoryProof, TypeTheoryEnvironment, TypeTheoryAxiom, TypeTheoryDefinition, TypeTheoryCheck]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[TypeTheoryTheorem]()[*name*, *statement*, *proof*]</code> declares *name* as a theorem: *proof* must prove *statement* when the declaration is added to a [TypeTheoryEnvironment]().

<code>[TypeTheoryTheorem]()[*name*, *proof*]</code> declares the statement of the finished [TypeTheoryProof]() *proof*.

## Details & Options

- *statement* must be a proposition, a type in <code>[TypeUniverse]()[0]</code>; under rules without Prop, as in the HoTT environment, it may be any type. *proof* is a term, a [TypeTheoryTerm](), or a finished [TypeTheoryProof]() written out or held in a symbol.
- The kernel checks *proof* against *statement* when the theorem is added; a proof that does not check gives a [Failure](). A theorem never unfolds.
- The option `"UniverseParameters" -> {u, ...}` lists the universe parameters; [Automatic]() takes the symbols and strings in universe levels, in the order they appear.

## Basic Examples

A theorem proved by computation:

```wl
arithmetic = TypeTheoryEnvironment[TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, EqualityReflexivity[4]]];
arithmetic[TwoPlusTwo]
```

<!-- => theorem TwoPlusTwo : 2 + 2 == 4 -->

## Scope

The statement of a finished proof:

```wl
proof = TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Reflexivity"]
}];
proved = TypeTheoryEnvironment[TypeTheoryTheorem[ZeroRightIdentity, proof]];
TypeOf[TypeTheoryTerm[ZeroRightIdentity, proved]]
```

<!-- => ∀_n∶ℕ n + 0 == n -->

A theorem applies like a function:

```wl
TypeOf[TypeTheoryTerm[ZeroRightIdentity[7], proved]]
```

<!-- => 7 + 0 == 7 -->

## Possible Issues

A proof of another statement is rejected:

```wl
TypeTheoryEnvironment[TypeTheoryTheorem[Wrong, 2 + 2 == 5, EqualityReflexivity[4]]]
```

<!-- => Failure["TypeMismatch", ...] -->

---

A theorem's statement must be a proposition:

```wl
TypeTheoryEnvironment[TypeTheoryTheorem[Three, NonNegativeIntegers, 3]]
```

<!-- => Failure["PropositionExpected", ...] -->
