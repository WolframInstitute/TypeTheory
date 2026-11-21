# Checking a development in shards

A development of millions of constants, imported from Lean, would take days to check in one chain of batches. Its
theorems' proofs can be checked apart from one another, in parallel, with nothing new in the kernel: the development is
checked once as its signature, and its proofs in shards cut from it in its order. This note is the TypeTheory side;
LeanLink's side (a cone walk, the cut of each shard, per-shard table files) is in its own plan.

## Why it is sound

TypeTheory never unfolds a theorem (Kernel.md). A theorem's proof changes no reduction and no definitional equality, so
the development's signature, the development with each theorem replaced by an axiom of its statement, checks every
other declaration exactly as the development does. Definitions and inductive types keep their values: the kernel
unfolds definitions and computes with recursors.

## The method

1. **The signature.** The development with its theorems as axioms of their statements, `TypeTheoryAxiom[name,
   statement]`, checked once, in order, as any environment is.
2. **The shards.** For a batch of theorems, the environment cut from the development in its order with the constants the
   batch needs: the batch's theorems with their proofs, `TypeTheoryTheorem[name, statement, proof]`, and every other
   constant as the signature has it. A shard is checked as any environment is, each declaration against those before
   it, so a proof cites only what comes before its theorem in the development: two theorems whose proofs cite each
   other cannot both check, a literal needs its natural numbers registered before it, and a rewrite rule declared later
   is not there yet.
3. **The comparison.** `Information[environment, "Signature"]` gives an environment's rules, its natural numbers and each
   record's structural hash by name, in order, a theorem's record read as that of an axiom of its statement. A shard is
   cut from the development where its signature agrees with the development's: the same rules, its natural numbers
   registered as there, and each of its constants with the hash it has there, in the order it has there.
4. **The assumptions.** A statement's closure in the signature stops at the axioms that are the development's theorems.
   Its assumptions are the axioms of that closure that are no theorem of the development, joined with the closures, in
   their shards, of the theorems it reaches, and of theirs. An axiom used only inside a proof shows only in the closure of
   that proof's theorem in its shard.

A receipt for a statement `S` then holds the signature checked, with its content hash; `S`'s closure in it; and for every
theorem the closures reach, a shard that checks, whose signature agrees with the development's, and the theorem's
closure in it.

## The threat model

The structural hashes are the fingerprints of saved environments: they show that a shard cut by this pipeline from one
export agrees with it, not that a shard from anywhere else does, since whoever makes a shard could make the hashes
along with it. `Information[environment, "StrongSignature"]` gives each record's SHA-256 over a table of its own terms
instead, for such a shard.

## What it does not need

An earlier design of this note had a declaration of its own for a theorem without its proof, and a function that
checked proofs against the whole signature, out of order. Checking out of order lost what checking in order gives for
free, and each part of that design put a piece of it back: a condition on the order of what a proof cites, the literals
and the rewrite rules after a theorem, names no proof may cite. A shard in the development's order needs none of them.

## Tests

In Tests/Checking/Queries.wlt: a shard with proofs agrees with its development's signature, structurally and by
SHA-256, and carries its proofs' closures; a proof citing what comes after it does not check, or its shard does not
agree; a shard with another statement or other rules does not agree; a signature survives a saved file.
