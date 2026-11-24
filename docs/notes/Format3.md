# Format 3 (`.tte`): Single-File Seekable Lazy Environment Format

Format 3 (`TTE3`) is a pure-Wolfram-Language, zero-dependency, single-file seekable binary container for
`TypeTheoryEnvironment`, extending the DAG row table of Format 2 (`Checking/SavedEnvironments.wl`) with
random-access block indexing, trailing proof storage, per-block SHA-256 verification, and a two-level
on-disk name index.

It is designed so that:

- Opening a 1.47M-constant / 1.065B-node environment takes milliseconds and tens of megabytes of RAM,
  without materializing constant names or decoding any term DAGs.
- Queries on types, kinds, signatures, and overlay declarations (`TypeTheoryType`, `KeyExistsQ`, `Length`,
  `Information[env, "Kinds" | "Signature"]`, and checking new declarations in an overlay) never touch
  theorem/opaque proof blocks.
- Every block read from disk is verified against a header-bound SHA-256 manifest and validated held
  before any expression evaluates.
- All file I/O uses only `OpenRead[path, BinaryFormat -> True]`, `SetStreamPosition`, and
  `ByteArray[BinaryReadList[stream, "Byte", n]]`, running identically on Wolfram 15 and WolframKernel v2.
- Both Wolfram Language (`Export["file.tte", env]` and the streaming batch writer) and external C/Python
  tools can produce valid `.tte` files whose `Meta["Hash"]` is byte-for-byte identical to Format 2's
  `environmentContentHash[env]`.

## File Layout

All multi-byte integers in the fixed header are little-endian unsigned 64-bit (`UnsignedInteger64`).
All variable-size payloads are standard Wolfram Exchange Format (WXF, `"8:"` or `"8:C"` zlib-compressed)
so packed integer arrays automatically choose minimal element widths (`int8`/`int16`/`int32`/`int64`) and
decode at native speed via `BinaryDeserialize[bytes, HoldComplete]`.

```text
+-------------------------------------------------------------------+ offset 0
| Leading Magic (8 bytes: "TTE3\0\0\0\3")                           |
+-------------------------------------------------------------------+ offset 8
| LeafBlocks[1 .. L]            (WXF lists of core leaves)          |
| LabelBlocks[1 .. K]           (WXF lists of names / binders)      |
| CubicalBlocks[1 .. Q]         (optional, WXF packed {M,2} ints)   |
| NodeBlocks[1 .. N]            (statement/def DAG, WXF {M,5} ints) |
| RecordMetaBlocks[1 .. R]      (declaration order metadata + names)|
| RecordDirBlocks[1 .. D]       (WXF packed {M,4} int64 table)      |
| NameIndexCoarse               (WXF packed {B} int64 max-hashes)   |
| NameIndexBuckets[1 .. B]      (sorted hash62 + recordId + names)  |
| RecordHashBlocks[1 .. H]      (optional, WXF packed {M,4} ints)   |
| DepBlocks[1 .. C]             (optional, CSR stmt/proof deps)     |
+-------------------------------------------------------------------+
| ProofNodeBlocks[1 .. P]       (TRAILING: theorem/opaque proofs)   |
+-------------------------------------------------------------------+
| Meta                          (WXF Association, small)            |
| SectionDirectory              (WXF Association of {off, len})     |
| Manifest                      (WXF Association of SHA-256 arrays) |
+-------------------------------------------------------------------+ EOF - 256
| Fixed Footer / Header (256 bytes, little-endian)                  |
+-------------------------------------------------------------------+ EOF
```

Placing the 8-byte magic at offset `0` and the 256-byte fixed header at `EOF - 256` lets writers emit the
entire file in a single forward pass with zero output seeking (matching Wolfram's forward-only
`OutputStream`). Placing `ProofNodeBlocks` last (immediately before `Meta`, `SectionDirectory`, and `Manifest`) guarantees
zero proof I/O during statement/type/definition queries and allows a statement-only `.tte` to be cut by
copying the prefix before `ProofNodeBlocks` and rewriting only `RecordDir`, `Meta`, `SectionDirectory`,
`Manifest`, and the 256-byte footer without decoding any terms.

## Fixed 256-Byte Footer / Header (at `EOF - 256`)

| Byte Range | Type | Field | Description |
|---|---|---|---|
| `0..7` | 8 bytes | `magic` | ASCII `"TTE3"` followed by bytes `0, 0, 0, 3` (`{84, 84, 69, 51, 0, 0, 0, 3}`). |
| `8..15` | `uint64` | `headerSize` | `256`. |
| `16..23` | `uint64` | `flags` | Bitmask: `1` = `HasProofNodeBlocks`, `2` = `HasDeps`, `4` = `HasRecordHashes`, `8` = `StatementOnly`, `16` = `HasCubicalBranches`. |
| `24..31` | `uint64` | `constantCount` | Number of constants in this file beyond `Base`. |
| `32..39` | `uint64` | `stmtNodeCount` | Number of rows in `NodeBlocks` (row IDs `1 .. stmtNodeCount`). |
| `40..47` | `uint64` | `proofNodeCount` | Number of rows in `ProofNodeBlocks` (row IDs `stmtNodeCount + 1 .. stmtNodeCount + proofNodeCount`). |
| `48..55` | `uint64` | `leafCount` | Number of leaves across `LeafBlocks` (leaf IDs `-1 .. -leafCount`). |
| `56..63` | `uint64` | `labelCount` | Number of labels across `LabelBlocks` (label IDs `1 .. labelCount`). |
| `64..71` | `uint64` | `stmtNodeBlockSize` | Rows per `NodeBlock` (default `65536`). |
| `72..79` | `uint64` | `proofNodeBlockSize` | Rows per `ProofNodeBlock` (default `65536`). |
| `80..87` | `uint64` | `leafBlockSize` | Leaves per `LeafBlock` (default `16384`). |
| `88..95` | `uint64` | `labelBlockSize` | Labels per `LabelBlock` (default `16384`). |
| `96..103` | `uint64` | `recordMetaBlockSize` | Records per `RecordMetaBlock` (default `4096`). |
| `104..111` | `uint64` | `sectionDirOffset` | 64-bit byte offset of `SectionDirectory`. |
| `112..119` | `uint64` | `sectionDirLength` | Byte length of `SectionDirectory`. |
| `120..127` | `uint64` | `metaOffset` | 64-bit byte offset of `Meta`. |
| `128..135` | `uint64` | `metaLength` | Byte length of `Meta`. |
| `136..143` | `uint64` | `manifestOffset` | 64-bit byte offset of `Manifest`. |
| `144..151` | `uint64` | `manifestLength` | Byte length of `Manifest`. |
| `152..183` | 32 bytes | `metaSha256` | Raw SHA-256 of the `Meta` bytes. |
| `184..215` | 32 bytes | `manifestSha256` | Raw SHA-256 of the `Manifest` bytes. |
| `216..247` | 32 bytes | `headerSha256` | Raw SHA-256 of header bytes `0..215`. |
| `248..255` | 8 bytes | `reserved` | All zero bytes. |

## Block Addressing & Encoding

### Node Rows (`NodeBlocks` and `ProofNodeBlocks`)

Each block is a WXF-serialized packed `{M, 5}` integer matrix (`1 <= M <= blockSize`).
Row ID `row` (`1 <= row <= stmtNodeCount + proofNodeCount`) lives in:

- `NodeBlocks[[Quotient[row - 1, stmtNodeBlockSize] + 1]]` at local index `Mod[row - 1, stmtNodeBlockSize] + 1`
  when `1 <= row <= stmtNodeCount`.
- `ProofNodeBlocks[[Quotient[row - stmtNodeCount - 1, proofNodeBlockSize] + 1]]` at local index
  `Mod[row - stmtNodeCount - 1, proofNodeBlockSize] + 1` when `row > stmtNodeCount`.

Row format `{code, c2, c3, c4, c5}` extends Format 2 with code `6` for `cubicalSystem`:

| Code | Core Term | Columns |
|---|---|---|
| `1` | `application[f, a]` | `{1, f, a, 0, 0}` |
| `2` | `lambdaAbstraction[name, dom, body, binder]` | `{2, label(name), dom, body, label(binder)}` |
| `3` | `dependentFunctionType[name, dom, cod, binder]` | `{3, label(name), dom, cod, label(binder)}` |
| `4` | `localDefinition[name, type, val, body]` | `{4, label(name), type, val, body}` |
| `5` | `projection[struct, index, term]` | `{5, label(struct), index, term, 0}` |
| `6` | `cubicalSystem[{{f1, t1}, ...}]` | `{6, cubicalStart, branchCount, 0, 0}` |

Part references (`f`, `a`, `dom`, `body`, `cod`, `type`, `val`, `term`, and entries of `CubicalBlocks`):

- Positive integer `p`: earlier row `1 <= p < row` (strict DAG acyclicity). Statement rows (`row <= stmtNodeCount`)
  can therefore never reference proof rows (`row > stmtNodeCount`).
- Negative integer `p`: leaf at index `-p` (`1 <= -p <= leafCount`).
- `0` is forbidden as a part reference.

`CubicalBlocks` (when `HasCubicalBranches` is set) chunks flat `{facePart, termPart}` pairs in blocks of
`cubicalBlockSize` (default `16384`), each stored as a WXF packed `{M, 2}` integer matrix.

### Leaves and Labels (`LeafBlocks`, `LabelBlocks`)

- Each `LeafBlock` is a WXF list of up to `leafBlockSize` core leaves (`boundVariable`, `universeSort`,
  `constantReference`, `naturalLiteral`, `intervalUniverse`). Every leaf is validated with `heldDataQ` and
  `leafTermQ` when the block is first loaded.
- Each `LabelBlock` is a WXF list of up to `labelBlockSize` labels (`nameQ` or `binderQ`), validated on
  first load.

### Fixed-Stride `RecordDirBlocks`

Each block covers up to `recordDirBlockSize` constants (default `16384`, stored in `Meta["BlockSizes"]`)
and is a WXF packed `{M, 4}` integer matrix with columns `{kindCode, typeRoot, valueRoot, recordFlags}`:

- `kindCode`: `1` = `Axiom`, `2` = `Definition`, `3` = `Opaque`, `4` = `Theorem`, `5` = `InductiveType`,
  `6` = `Constructor`, `7` = `Recursor`, `8` = `RewriteRule`, `9` = `Quotient`, `10` = `Cubical`, `11` = `Hole`.
- `typeRoot`: signed part ID (`> 0` statement row, `< 0` leaf, `0` when absent — e.g. `RewriteRule`).
- `valueRoot`: signed part ID (`> 0` statement row for `Definition`, `> stmtNodeCount` proof row for
  `Theorem`/`Opaque`, `< 0` leaf, `0` when absent).
- `recordFlags`: bit `1` = has `Annotation`, bit `2` = has `Overloads`, bit `4` = has `Implementation`.

### `RecordMetaBlocks`

Each block covers up to `recordMetaBlockSize` constants (default `4096`) in declaration order and is a WXF
Association:

```wl
<|
  "Names" -> {HoldComplete[name1], ...},
  "Meta" -> {<|...metadata without Type/Value...|>, ...}
|>
```

Non-`Type`/non-`Value` core terms (specifically `Recursor["Rules"][ctor]["RightHandSide"]` and
`RewriteRule["LeftHandSide" | "RightHandSide"]`) are stored as `termRef[row]` (pointing into `NodeBlocks`,
`1 <= row <= stmtNodeCount`) or direct core leaves, and decoded on demand via the same lazy DAG walker.

### Two-Level On-Disk `NameIndex`

Every constant name `HoldComplete[name]` has a deterministic 62-bit hash `nameHash62[name]`:

1. Serialize `name` to WXF bytes `b_1, ..., b_n` (`Normal[BinarySerialize[name]]`).
2. Compute the first two Horner prime residues from `SavedEnvironments.wl`:
   - `m1 = 2147483647`, `a1 = 1592653589`
   - `m2 = 2147483629`, `a2 = 1414213562`
   - `r_k = 0; for b in bytes: r_k = (r_k * a_k + b + 1) mod m_k; r_k = (r_k * a_k + n + 1) mod m_k`
3. `nameHash62 = r_1 * 2147483648 + r_2` (non-negative integer `< 2^62`).

All `constantCount` constants are sorted ascending by `(nameHash62, recordId)` and partitioned into buckets
of up to `nameBucketSize` entries (default `4096`):

- **`NameIndexCoarse`** (loaded once on open): WXF packed 1D integer array of length `B` holding the
  maximum `nameHash62` of each bucket.
- **`NameIndexBuckets[[b]]`** (loaded & cached on demand): WXF Association:
  ```wl
  <|
    "Hashes" -> packed1DInt64,
    "RecordIDs" -> packed1DInt64,
    "Names" -> {HoldComplete[...], ...}
  |>
  ```
Lookup performs binary search on `NameIndexCoarse`, loads candidate bucket(s) whose range contains
`nameHash62` (handling boundary ties across adjacent buckets), binary-searches `"Hashes"`, and verifies
exact equality `Names[[pos]] === name`.

### Optional `RecordHashBlocks` and CSR `DepBlocks`

- **`RecordHashBlocks`** (`flags` bit 2): chunked WXF packed `{M, 4}` integer matrices (up to
  `recordDirBlockSize` rows per block) storing each constant's 4-residue Format 2 structural fingerprint
  in declaration order.
- **`DepBlocks`** (`flags` bit 1): chunked WXF Associations (up to `recordMetaBlockSize` constants per
  block) storing CSR adjacency arrays for both statement dependencies and proof dependencies:
  ```wl
  <|
    "StmtOffsets" -> packed1DInt64,   (* length M + 1, 1-based *)
    "StmtTargets" -> packed1DInt64,   (* constant IDs 1..constantCount; 0 = base constant *)
    "ProofOffsets" -> packed1DInt64,  (* length M + 1, 1-based *)
    "ProofTargets" -> packed1DInt64
  |>
  ```
  `StmtTargets` lists constant IDs referenced by `Type`, `Definition["Value"]`, `InductiveType`/`Constructor`/
  `Recursor`/`Quotient`/`Cubical`/`RewriteRule` fields (plus `InductiveType`/`Constructors` links);
  `ProofTargets` lists additional constant IDs referenced by `Theorem["Value"]` and `Opaque["Value"]`.

### `Meta`, `SectionDirectory`, and `Manifest`

- **`Meta`** (WXF Association, SHA-256 verified against `header.metaSha256` on open):
  `"Format" -> "TypeTheoryEnvironment"`, `"FormatVersion" -> 3`, `"TypeTheoryVersion"`, `"KernelHash"`,
  `"Host"`, `"Rules"`, `"Base"`, `"NaturalNumbers"`, `"RewriteRuleIndex"`, `"OverloadIndex"`,
  `"KindCounts"`, `"BlockSizes"` (`<|"RecordDir" -> ..., "NameBucket" -> ..., "Cubical" -> ...|>`),
  `"Hash"` (identical to Format 2 `environmentContentHash[env]`).
- **`SectionDirectory`** (WXF Association, SHA-256 verified against `Manifest["SectionDirectory"]` on open):
  maps each section name to `{offset, length}` or a packed `{K, 2}` array of `{offset, length}` pairs.
- **`Manifest`** (WXF Association, SHA-256 verified against `header.manifestSha256` on open):
  maps `"SectionDirectory"` to its 32-byte `ByteArray` SHA-256 and each section name to a flat
  `32 * blockCount`-byte `ByteArray` of concatenated SHA-256 digests.

## Security & Trust-Boundary Invariants

1. **Header-bound Merkle manifest:** Opening checks `headerSha256`, `metaSha256`, `manifestSha256`, and
   `SectionDirectory`'s SHA-256 before trusting any offsets. Every lazily fetched block's raw bytes must
   match its 32-byte digest in `Manifest` before `BinaryDeserialize`.
2. **Held deserialization:** Every WXF payload is deserialized with `BinaryDeserialize[bytes, HoldComplete]`
   and checked with `heldDataQ` (with packed integer arrays blanked) before exiting `HoldComplete`.
3. **Strict DAG & depth validation:** Lazy node decoding enforces `1 <= child < row` (or valid leaf),
   valid label indices/types, unused zero columns, and a depth cap (`<= $kernelRecursionLimit`).
4. **Never blindly trust index metadata:** `Meta["RewriteRuleIndex"]` and `Meta["OverloadIndex"]` are
   validated with `inertQ` + `nameQ` on open, verified on every fetch (`record["Kind"] === "RewriteRule" &&
   record["Head"] === head`; `Lookup[record, "Overloads", None] === op`), and re-verified by
   `TypeTheoryCheck` across all `$derivedStoreKeys`.
5. **Bounded stream pool & on-disk mutation detection:** Streams are never stored on environment store
   symbols (which `withStoreCleanup` removes). A global bounded LRU stream pool (max 8 streams) manages
   file descriptors and verifies `{FileByteCount, FileDate}` against the snapshot recorded at open time.
6. **Statement-only cuts are honest:** A cut with `"IncludeProofs" -> False` converts stripped theorems
   to `"Axiom"` records (`ValueRoot = 0`) so `TypeTheoryCheck` and `TypeTheoryAxiomClosure` never claim
   an omitted proof is proved, while preserving `Information[env, "Signature"]`.
