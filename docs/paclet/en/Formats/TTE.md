---
Template: Format
Name: TTE
Extension: .tte
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/format/TTE
Description: TypeTheory environment files, one seekable file per environment, read lazily and checked block by block.
Keywords: [TTE, tte, Format 3, environment file, saved environment, lazy environment, Import, Export]
SeeAlso: [TypeTheoryEnvironment, Information, Import, Export]
RelatedGuides: [TypeTheory]
---

# TTE

TTE is the file format of TypeTheory's environments: one file holds an environment's constants, their types, values and proofs, and the indexes that let a query read only the part of the file it asks about. Loading the WolframInstitute/TypeTheory paclet registers the TTE import and export converters, which read a file as a <code>[TypeTheoryEnvironment]()</code> and write one.

## Background & Context

- Binary format, Format 3 of TypeTheory's saved environments. Format 2, a WXF file, holds an environment that is read whole.
- A file has a header, its metadata, an index of the names in two levels, and blocks of terms. Statements and values are in blocks of their own and proofs in blocks at the end, so a file of statements alone can be cut from one with proofs.
- Every block has a SHA-256 digest in a manifest that the header binds. A block is checked when it is first read, and a file whose header or blocks have changed is refused.
- Reading is lazy: opening a file reads its header and indexes, and a constant's terms are read when a query needs them.
- A file records the kernel of the TypeTheory that wrote it. A TypeTheory whose kernel differs reads it only with `"Check" -> True`, which checks every declaration again, so a saved environment is never taken on another kernel's word.
- An environment's content hash, <code>[Information]()[*env*, "Hash"]</code>, does not depend on the format that holds it.
- The converters are the code of <code>[TypeTheoryEnvironment]()[[File]()["file.tte"]]</code> and of <code>[Export]()["file.tte", *env*]</code>; the format is another door to it.

## Import & Export

- `Import["file.tte", "TTE"]` imports a TTE file, returning a <code>[TypeTheoryEnvironment]()</code> that reads the file lazily.
- `Import["file.tte", {"TTE", elem}]` imports the specified element.
- <code>[TypeTheoryEnvironment]()[[File]()["file.tte"]]</code> reads the same environment, and gives a <code>[Failure]()</code> that says why where `Import` gives `$Failed`.

---

- `Export["file.tte", env]` and `Export["file.tte", env, "TTE"]` write an environment as a TTE file.

## Import Elements

| "Environment" | the environment, read lazily (default) |
|---|---|
| "Constants" | the names of its constants |
| "Hash" | its content hash |

## Options

Import takes:

| "Check" | False | whether to check every declaration again, as a file that a TypeTheory with another kernel wrote needs |
|---|---|---|

Export takes:

| "IncludeProofs" | True | whether to write the proofs of theorems and opaque constants |
|---|---|---|
| "IncludeDependencies" | True | whether to write the index of the constants each constant uses |
| "Standalone" | False | whether to write the constants of the library environment an environment extends |
| "BlockSizes" | Automatic | the number of terms or records in a block of each kind |

- With `"IncludeProofs" -> False` a file holds statements alone: its theorems and opaque constants are read as axioms of their statements.
- An environment that extends a library environment, as one built on the prelude does, is written by default as the library's name and content hash and its own constants; reading it takes the library from the paclet and refuses it if its hash differs. `"Standalone" -> True` writes every constant.

## Examples

### Basic Examples

Write the integers' environment to a TTE file:

```wl
file = FileNameJoin[{$TemporaryDirectory, "integers.tte"}];
FileNameTake[Export[file, TypeTheoryEnvironment["Integers"]]]
```

<!-- => "integers.tte" -->

Import it back; the environment reads the file as queries need it:

```wl
integers = Import[file, "TTE"]
```

<!-- => TypeTheoryEnvironment summary box: the integers' constants -->

It is the environment that was written, with the same content hash:

```wl
Information[integers, "Hash"] === Information[TypeTheoryEnvironment["Integers"], "Hash"]
```

<!-- => True -->

### Import Elements

The elements of a TTE file:

```wl
Import[file, {"TTE", "Elements"}]
```

<!-- => {"Constants", "Environment", "Hash", "Summary"} -->

The names of its constants, read from its index:

```wl
Length[Import[file, {"TTE", "Constants"}]] === Length[Information[integers, "Constants"]]
```

<!-- => True -->

### Export Options

Without proofs, a file holds the statements alone:

```wl
statements = FileNameJoin[{$TemporaryDirectory, "integers-statements.tte"}];
FileNameTake[Export[statements, TypeTheoryEnvironment["Integers"], "IncludeProofs" -> False]]
```

<!-- => "integers-statements.tte" -->

It is smaller than the file with proofs:

```wl
FileByteCount[statements] < FileByteCount[file]
```

<!-- => True -->

and its theorems are read as axioms:

```wl
Length[Information[Import[statements, "TTE"], "Axioms"]] > Length[Information[integers, "Axioms"]]
```

<!-- => True -->

`"Standalone" -> True` writes the prelude's constants too, which the default file takes from the paclet:

```wl
standalone = FileNameJoin[{$TemporaryDirectory, "integers-standalone.tte"}];
Export[standalone, TypeTheoryEnvironment["Integers"], "Standalone" -> True];
FileByteCount[standalone] > FileByteCount[file]
```

<!-- => True -->

### Properties & Relations

<code>[TypeTheoryEnvironment]()[[File]()[...]]</code> reads a TTE file as `Import` does:

```wl
Information[TypeTheoryEnvironment[File[file]], "Hash"] === Information[integers, "Hash"]
```

<!-- => True -->

A WXF file of the same environment, Format 2, has the same content hash:

```wl
wxf = FileNameJoin[{$TemporaryDirectory, "integers.wxf"}];
Export[wxf, TypeTheoryEnvironment["Integers"]];
Information[TypeTheoryEnvironment[File[wxf]], "Hash"] === Information[integers, "Hash"]
```

<!-- => True -->

### Possible Issues

Wolfram 15 takes a registered format by its name and not by the extension of a file, so `Import` names it:

```wl
Import[file]
```

<!-- => $Failed, with Import::infer -->

A file changed after it was written is refused. `Import` gives `$Failed`, and <code>[TypeTheoryEnvironment]()[[File]()[...]]</code> the <code>[Failure]()</code> that says why:

```wl
forged = FileNameJoin[{$TemporaryDirectory, "forged.tte"}];
BinaryWrite[forged, Join[ByteArray[ConstantArray[0, 64]], Drop[ReadByteArray[file], 64]]];
Close[forged];
TypeTheoryEnvironment[File[forged]]
```

<!-- => Failure[...]: the header of the file is not a TTE header -->
