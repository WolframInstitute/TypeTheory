---
Template: TechNote
Name: RiemannHypothesis
Title: The Riemann Hypothesis in TypeTheory
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/tutorial/RiemannHypothesis
Keywords: [Riemann Hypothesis, Lean, Mathlib, lazy environment, TTE, tte, proof checking, overlay, large library]
RelatedGuides: [TypeTheory]
RelatedTutorials: [MathlibInTypeTheory, TypeTheoryIntroduction, ThePrelude]
---

[TypeTheory](https://www.wolframcloud.com/obj/wolframinstitute/TypeTheory) checks and queries large formal mathematical libraries. A single seekable `.tte` file holds the statement and definition environment of Levent Alpöge's Lean 4 claimed proof of the Riemann Hypothesis (1,484,705 declared constants, covering 1,246,092 theorem statements together with every definition, inductive type, constructor, recursor and quotient they depend on). Opening the file reads only its header, metadata, section directory, coarse two-level name index and per-block SHA-256 manifest, without decoding term graphs or materializing constant names. Every block read on demand is checked against the manifest before its terms are decoded.

This tutorial downloads the statement-only `.tte` archive once, opens it lazily with [Import]() using the `"TTE"` format, inspects `riemannHypothesis` and its Mathlib definition `RiemannHypothesis`, and proves a new theorem on top of the archive without copying or loading the rest of the library into memory.

## Downloading the Archive

The statement-only archive `rh-statements.tte` keeps every definition, inductive type, constructor, recursor, quotient and theorem statement in `riemannHypothesis`'s dependency cone, together with a compressed CSR dependency index, while omitting proof bodies so the file stays small enough for interactive use. Download it once into a local cache directory; a copy of another size, as a download cut short, is fetched again:

```wl
rhDirectory = FileNameJoin[{$UserBaseDirectory, "ApplicationData", "TypeTheory"}];
If[! DirectoryQ[rhDirectory], CreateDirectory[rhDirectory]];
rhFile = FileNameJoin[{rhDirectory, "rh-statements.tte"}];
rhURL = "https://www.wolframcloud.com/obj/wolframinstitute/TypeTheoryData/rh-statements.tte";
If[! FileExistsQ[rhFile] || FileByteCount[rhFile] =!= 773270624, URLDownload[rhURL, rhFile]];
FileByteCount[rhFile]
```

<!-- => 773270624 -->

## Opening the Environment Lazily

[Import]() with the `"TTE"` format opens a `.tte` archive lazily, verifying the header, metadata and SHA-256 manifest without decoding term blocks:

```wl
{openTime, rh} = AbsoluteTiming[Import[rhFile, "TTE"]];
rh
```

<!-- => TypeTheoryEnvironment summary box: 1484705 constants -->

Opening the entire 1.48-million-constant library takes a fraction of a second:

```wl
Quantity[Round[openTime, 0.001], "Seconds"]
```

<!-- => Quantity[0.127, "Seconds"] -->

## Metadata and Constant Lookup

[Length]() reads the constant count directly from the archive metadata:

```wl
Length[rh]
```

<!-- => 1484705 -->

[Information]() returns the precomputed counts by declaration kind without decoding term blocks:

```wl
Information[rh, "Kinds"]
```

<!-- => <|"InductiveType" -> 7970, "Constructor" -> 8342, "Recursor" -> 7972, "Quotient" -> 4, "Definition" -> 214231, "Axiom" -> 1246186|> -->

[KeyExistsQ]() checks membership through the two-level on-disk name index:

```wl
KeyExistsQ[rh, "riemannHypothesis"]
```

<!-- => True -->

Mathlib's own statement of the hypothesis is declared in the same archive:

```wl
KeyExistsQ[rh, "RiemannHypothesis"]
```

<!-- => True -->

The Riemann zeta function is declared alongside it:

```wl
KeyExistsQ[rh, "riemannZeta"]
```

<!-- => True -->

## Inspecting the Statement of the Riemann Hypothesis

[TypeTheoryType]() decodes only the block holding the requested constant's type, leaving the remaining constants on disk:

```wl
TypeTheoryType["riemannHypothesis", rh]
```

<!-- => TypeTheoryTerm["RiemannHypothesis", rh] -->

Mathlib's `RiemannHypothesis` itself is a proposition (`TypeUniverse[0]`):

```wl
TypeTheoryType["RiemannHypothesis", rh]
```

<!-- => TypeTheoryTerm[TypeUniverse[0], rh] -->

And `riemannZeta` has type `Complex -> Complex`:

```wl
TypeTheoryType["riemannZeta", rh]
```

<!-- => TypeTheoryTerm["Complex" -> "Complex", rh] -->

## Proving New Theorems on Top of the Archive

Extending a lazy [TypeTheoryEnvironment]() with a new declaration creates an overlay without copying or materializing the base archive. When the kernel checks the new theorem, it reads only the transitive statement cone of the constants the new proof mentions.

Declare and check a simple theorem directly on top of `RiemannHypothesis`:

```wl
extended = TypeTheoryEnvironment[
	rh,
	TypeTheoryTheorem[
		"riemannHypothesisSelfImplies",
		"RiemannHypothesis" -> "RiemannHypothesis",
		Function[{Typed[h, "RiemannHypothesis"]}, h]
	]
]
```

<!-- => TypeTheoryEnvironment summary box: 1484706 constants -->

The new theorem is checked by the kernel and can be queried alongside the base archive:

```wl
TypeTheoryType["riemannHypothesisSelfImplies", extended]
```

<!-- => TypeTheoryTerm[Implies["RiemannHypothesis", "RiemannHypothesis"], extended] -->

## Verification and Trust Boundary

Every one of the 1,246,092 theorems in the exported Lean 4 development of Levent Alpöge's claimed proof (`solution.ndjson.zst`, produced with `lean4export`) type-checked in TypeTheory's compiled Calculus of Inductive Constructions kernel across 649 cones (1,484,705 unique constants fingerprinted), with no Lean code in the checking path, zero holes, zero rewrite rules, zero fingerprint mismatches and zero order violations, resting only on Lean's three standard classical axioms:

- `Classical.choice`
- `Quot.sound`
- `propext`

Because a statement-only `.tte` omits proof bodies, it marks stripped theorems as axioms while preserving the exact structural [Information]() `"Signature"` of every constant, so each theorem's statement fingerprint matches the full proof-checked receipts bit-for-bit.
