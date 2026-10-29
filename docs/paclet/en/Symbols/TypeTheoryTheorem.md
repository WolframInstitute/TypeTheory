---
Template: Symbol
Name: TypeTheoryTheorem
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryTheorem
Keywords: [theorem, proof, declaration, proposition, kernel, environment]
SeeAlso: [TypeTheoryProof, TypeTheoryEnvironment, TypeTheoryAxiom, TypeTheoryDefinition, TypeTheoryCheck, TypeTheoryHole]
RelatedGuides: [TypeTheory]
---

## Usage

<code>[TypeTheoryTheorem]()[*name*, *statement*, *proof*]</code> declares *name* as a theorem: *proof* must prove *statement* when the declaration is added to a [TypeTheoryEnvironment]().

<code>[TypeTheoryTheorem]()[*name*, *proof*]</code> declares the statement of the finished [TypeTheoryProof]() *proof*.

## Details & Options

- *statement* must be a proposition, a type in <code>[TypeUniverse]()[0]</code>; under rules without Prop, as in the HoTT environment, it may be any type. *proof* is a term, a [TypeTheoryTerm](), or a finished [TypeTheoryProof]() written out or held in a symbol.
- The kernel checks *proof* against *statement* when the theorem is added; a proof that does not check gives a [Failure](). A theorem never unfolds.
- A proof may leave parts to give with [TypeTheoryHole](), or with the tactic `"Hole"`, as Lean's `sorry`: the environment then holds a constant <code>[TypeTheoryHole]()[*name*, *k*]</code> for each hole, before the theorem, and <code>[Information]()[[TypeTheoryTerm]()[*name*, *env*], "Holes"]</code> lists them. A proof with goals still open is no proof and gives a [Failure]().
- The option `"UniverseParameters" -> {u, ...}` lists the universe parameters; [Automatic]() takes the symbols and strings in universe levels, in the order they appear.

## Basic Examples

A theorem proved by computation:

```wl
arithmetic = TypeTheoryEnvironment[TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, EqualityReflexivity[4]]]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

Its declaration:

```wl
arithmetic[TwoPlusTwo]
```

<!-- => theorem TwoPlusTwo : 2 + 2 == 4 -->

## Scope

A finished proof:

```wl
proof = TypeTheoryProof[ForAll[{Typed[n, Naturals]}, n + 0 == n], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Proof complete -->

A theorem with it as its proof:

```wl
proved = TypeTheoryEnvironment[TypeTheoryTheorem[ZeroRightIdentity, proof]]
```

<!-- => TypeTheoryEnvironment summary box: 170 constants -->

The theorem states what the proof proved:

```wl
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
TypeTheoryEnvironment[TypeTheoryTheorem[Three, Naturals, 3]]
```

<!-- => Failure["PropositionExpected", ...] -->
