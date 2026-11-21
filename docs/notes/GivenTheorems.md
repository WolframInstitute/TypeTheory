# Given theorems and their discharge

A design for checking a large cone in shards. A cone of millions of constants, imported from Lean, would take days to
check in one chain of batches. Theorem proofs can be checked apart from one another,
in parallel, if every theorem first enters a signature environment with its statement alone. This note is the
TypeTheory side; LeanLink's side (a cone walk that follows a theorem's type and not its proof, a given form, a
`"Check" -> "Proofs"` call, per-shard table files) is in its own plan.

## Why it is sound

TypeTheory never unfolds a theorem (Kernel.md). A theorem's proof changes no reduction and no definitional equality, so
an environment in which each theorem enters with its statement alone checks every other declaration exactly as the full
environment does. Definitions and inductive types still enter with their values, in dependency order, unsharded: the
kernel unfolds definitions and computes with recursors. Only theorem proofs, Lean's `_proof_N` lemmas among them, are
checked later.

What a proof may cite is the one condition the full order gave for free. Checked against the whole signature, a proof
of `T` could cite a theorem `U` declared after `T` whose proof cites `T`: both would be discharged, neither proved. So a
discharge asks that every constant a proof cites is declared before its theorem. Checking against the whole signature
with that condition is checking against the prefix before the theorem: constants declared later change no check of a
term that does not cite them.

## The declarations

- `TypeTheoryGiven[name, statement, "UniverseParameters" -> {...}]` declares a given: a record of kind `"Given"` with
  the statement as its type and no value. The statement is checked as a theorem's is: a proposition, or under rules
  without Prop any type. Reduction treats a given as it treats a theorem, never unfolding it, and the compiled kernel's
  input writes it as it writes an axiom, a constant without a value, so the compiled program is unchanged.
- `TypeTheoryAxiomClosure` lists the givens a term rests on apart from its axioms, under `"Given"`, so that a receipt
  can show every given matched by a discharge.
- A saved environment holds a given's record as any other; its kind is among those a saved file may hold.

## The discharge

`TypeTheoryDischarge[signature, <|name -> proof, ...|>]` gives `<|name -> verdict, ...|>` and does not extend the
signature. For each name:

1. `name` is a given of `signature`.
2. Every constant `proof` cites is declared before `name` in `signature`.
3. `proof` checks, and its type is the given's statement, with the same universe parameters.

A verdict is a `Success` that names the signature's content hash, the given, and the fingerprint of the proof's record
(the structural record hash of the kept-table design), or a `Failure` that says which condition failed. With
`Method -> "Compiled"` the proofs are checked as one batch by the compiled kernel, each as a theorem under a fresh name
with the given's statement; a failure is checked again by the other kernel and reported, and the rest of the batch goes
on.

## Shards and the receipt

A shard need not load the whole signature: for 5.6 M constants, about 220 M table rows at 13 µs a row, tens of GB in a
kernel. Its
signature is the cone of its batch of proofs, cut from the whole signature in the same order: the definitions and
inductive types the proofs reach, and the statements of the theorems they cite, as givens. The shard's signature agrees
with the whole one where its records' hashes, by name, are the whole one's: the structural record hashes make that a
comparison of fingerprints, whatever the tables' numbering.

The receipt for a statement `S` then holds:

- the whole signature checked in Lean's order, with its content hash;
- `S`'s axiom closure in it: Lean's three axioms and a set of givens;
- for every given in that set, a discharge verdict of success, from a shard whose signature's record hashes agree with
  the whole signature's on that shard's names.

The givens a discharge cites are themselves in the closure, so the set is closed under the proofs' citations, and the
order condition makes the citations well founded.

## Tests to write

- A given's statement that is not a proposition is refused; a given is never unfolded.
- A discharge of a correct proof succeeds; of a wrong proof, or one whose type is another statement, fails.
- A proof citing a theorem declared after its own fails the order condition, though it checks against the signature.
- The closure lists givens apart from axioms.
- A signature with givens saves and reads back, and a shard's cut signature agrees with the whole one by record hashes.
- Both kernels agree on every verdict.

## Files it touches

`Checking/Declarations.wl` (the declaration and the kind), `Checking/Queries.wl` (the closure and the discharge),
`Checking/SavedEnvironments.wl` (the kind in a saved file), `Checking/CompiledKernel.wl` (the input writing a given as
an axiom, no change to the program), and Kernel.md. Every one is in `$trustedSources`, so the change goes to Stephen
before it is made.
