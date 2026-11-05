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
- The option `"UniverseParameters" -> {u, ...}` lists the universe parameters; [Automatic]() takes the symbols and strings in universe levels, in the order they appear, and makes each level that nothing in the declaration decides one more, `"u_1"`, `"u_2"`, …, as Lean does.
- The option `"Annotation" -> *data*` keeps *data*, a citation, the statement in words or anything else, in the theorem's record as it is given: <code>[Information]()[[TypeTheoryTerm]()[*name*, *env*], "Annotation"]</code> gives it back, and [Normal]() and a saved environment keep it.

## Basic Examples

A theorem proved by computation:

```wl
arithmetic = TypeTheoryEnvironment[TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, "equalityReflexivity"[4]]]
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
    "Introduce"[n],
    "Reflexivity"
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
TypeTheoryType[ZeroRightIdentity, proved]
```

<!-- => ∀_n∶ℕ n + 0 == n -->

A theorem applies like a function:

```wl
TypeTheoryType[ZeroRightIdentity[7], proved]
```

<!-- => 7 + 0 == 7 -->

---

A variable written without a type, whose sort nothing else decides, is a proposition in a statement that can be one:

```wl
TypeTheoryEnvironment[{TypeTheoryTheorem[SelfImplication, ForAll[{p}, Implies[p, p]], {p, h} |-> h]}][SelfImplication]
```

<!-- => theorem SelfImplication : ∀_p∶Prop p ⇒ p -->

---

A variable of any type gets its universe as a parameter of the theorem, `"u_1"`, which the statement names:

```wl
TypeTheoryEnvironment[{TypeTheoryTheorem[SelfEquality, ForAll[{A, Typed[x, A]}, x == x], {A, Typed[x, A]} |-> "equalityReflexivity"[x]]}][SelfEquality]
```

<!-- => theorem SelfEquality : ∀_A∶Sort u_1 ∀_x∶A x == x -->

## Possible Issues

A proof of another statement is rejected:

```wl
TypeTheoryEnvironment[TypeTheoryTheorem[Wrong, 2 + 2 == 5, "equalityReflexivity"[4]]]
```

<!-- => Failure["TypeMismatch", ...] -->

---

A theorem's statement must be a proposition:

```wl
TypeTheoryEnvironment[TypeTheoryTheorem[Three, Naturals, 3]]
```

<!-- => Failure["PropositionExpected", ...] -->
