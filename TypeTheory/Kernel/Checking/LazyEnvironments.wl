(* ::Package:: *)

(*
Format 3 (.tte): single-file seekable lazy environments.

A Format 3 file holds the DAG row table of Format 2 partitioned into fixed-size compressed WXF blocks,
with a 256-byte little-endian header, a two-level on-disk NameIndex, fixed-stride RecordDirBlocks,
declaration-order RecordMetaBlocks, trailing ProofNodeBlocks (for Theorem and Opaque proofs only),
optional RecordHashBlocks and CSR DepBlocks, a Meta chunk whose "Hash" is identical to Format 2's
environmentContentHash, a SectionDirectory, and a header-bound per-block SHA-256 Manifest.

Opening a Format 3 file verifies the header, Meta, Manifest, SectionDirectory, and coarse NameIndex
without materializing constant names or decoding any term DAGs. Every lazily read block is verified
against its 32-byte SHA-256 digest in Manifest and checked held (BinaryDeserialize[..., HoldComplete]
plus heldDataQ) before anything evaluates. File descriptors are managed by a global bounded LRU stream
pool keyed by canonical path, never stored on store symbols (which withStoreCleanup removes), and every
block read checks that the file on disk has not changed since open. All binary I/O uses OpenRead,
SetStreamPosition, and ByteArray[BinaryReadList[stream, "Byte", n]] for parity between Wolfram 15 and
WolframKernel v2.
*)


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[format3FileQ]
PackageScoped[loadFormat3Environment]
PackageScoped[saveFormat3Environment]
PackageScoped[cutFormat3StatementFile]
PackageScoped[openFormat3Writer]
PackageScoped[writeFormat3Batch]
PackageScoped[closeFormat3Writer]
PackageScoped[lazySourceQ]
PackageScoped[lazyConstantIndex]
PackageScoped[lazyConstantDeclaredQ]
PackageScoped[lazyConstantKind]
PackageScoped[lazyConstantRecord]
PackageScoped[lazyEnvironmentNames]
PackageScoped[lazyEnvironmentCount]
PackageScoped[lazyKindCounts]
PackageScoped[lazyNamesOfKind]
PackageScoped[lazyRecordHashes]
PackageScoped[lazyHasDepsQ]
PackageScoped[lazyConstantDeps]
PackageScoped[lazyConstantDepNames]
PackageScoped[lazyLocalName]
PackageScoped[recordDependencyNames]
PackageScoped[lazyDependencyCone]
PackageScoped[lazyMaterializeRecords]
PackageScoped[lazyVerifyDeps]
PackageScoped[closeLazyStreams]
PackageScoped[lazyStreamPoolCount]
PackageScoped[encodeFormat3Header]
PackageScoped[decodeFormat3Header]
PackageScoped[sha256Bytes]
PackageScoped[$lazyStreamPoolLimit]
PackageScoped[$lazyBlockReadCount]
PackageScoped[$lazyProofBlockReadCount]


(* ::Section:: *)
(*Usage Messages*)


format3FileQ::usage = "format3FileQ[file] gives True if file begins with the 8-byte Format 3 magic header."
loadFormat3Environment::usage = "loadFormat3Environment[file, check] opens a Format 3 (.tte) file lazily, checking its manifest and metadata, and replays every declaration if check is True."
saveFormat3Environment::usage = "saveFormat3Environment[file, environment, options] writes environment to file in Format 3 (.tte) and gives File[file]."
cutFormat3StatementFile::usage = "cutFormat3StatementFile[sourceFile, targetFile] writes a statement-only Format 3 (.tte) file from sourceFile without decoding term blocks, converting stripped theorems and opaque constants into axioms."
openFormat3Writer::usage = "openFormat3Writer[file, options] opens a streaming Format 3 (.tte) writer."
writeFormat3Batch::usage = "writeFormat3Batch[writer, records] appends an Association of <|HoldComplete[name] -> record, ...|> to a streaming Format 3 writer."
closeFormat3Writer::usage = "closeFormat3Writer[writer] finalizes a streaming Format 3 writer, writing trailing proof blocks, index, metadata, manifest, and header, and gives File[file]."
lazySourceQ::usage = "lazySourceQ[source] gives True if source is a valid Format 3 lazy environment handle."
lazyConstantIndex::usage = "lazyConstantIndex[source, HoldComplete[name]] gives the 1-based local constant index of name in source, or 0 if not present."
lazyConstantDeclaredQ::usage = "lazyConstantDeclaredQ[source, HoldComplete[name]] gives True if name is declared in source or its base."
lazyConstantKind::usage = "lazyConstantKind[source, HoldComplete[name]] gives the Kind string of name in source without decoding its terms."
lazyConstantRecord::usage = "lazyConstantRecord[source, HoldComplete[name], includeProof] reads the record of name from source, omitting ProofNodeBlocks decoding when includeProof is False for Theorem and Opaque constants."
lazyEnvironmentNames::usage = "lazyEnvironmentNames[source] gives all constant names of source (including its base) in declaration order."
lazyEnvironmentCount::usage = "lazyEnvironmentCount[source] gives the total number of constants in source (including its base) in O(1) time."
lazyKindCounts::usage = "lazyKindCounts[source] gives the Counts association of constant kinds in source (including its base) in O(1) time."
lazyNamesOfKind::usage = "lazyNamesOfKind[source, kind] gives the names of constants of the given Kind in source without decoding term blocks."
lazyRecordHashes::usage = "lazyRecordHashes[source] gives <|HoldComplete[name] -> fingerprint, ...|> for all constants in source (including its base)."
lazyHasDepsQ::usage = "lazyHasDepsQ[source] gives True if source includes a CSR DepBlocks section."
lazyConstantDeps::usage = "lazyConstantDeps[source, localId, includeProof] gives the constant IDs (positive = local, negative = base) that localId depends on from CSR DepBlocks."
lazyConstantDepNames::usage = "lazyConstantDepNames[source, localId, includeProof] gives the HoldComplete constant names that localId depends on from CSR DepBlocks."
lazyLocalName::usage = "lazyLocalName[source, localId] gives the HoldComplete name of local constant localId in source."
recordDependencyNames::usage = "recordDependencyNames[record] gives {statementDependencies, proofDependencies} of record as lists of HoldComplete names."
lazyDependencyCone::usage = "lazyDependencyCone[source, seedNames, includeProof] gives the sorted local constant IDs in the transitive dependency cone of seedNames."
lazyMaterializeRecords::usage = "lazyMaterializeRecords[store] materializes all records of a lazy environment store into an Association."
lazyVerifyDeps::usage = "lazyVerifyDeps[environment] verifies that CSR DepBlocks (if present) contain every constant dependency of every record in environment."
closeLazyStreams::usage = "closeLazyStreams[] closes all open file streams in the global lazy Format 3 stream pool."
lazyStreamPoolCount::usage = "lazyStreamPoolCount[] gives the number of currently open file streams in the global lazy Format 3 stream pool."
encodeFormat3Header::usage = "encodeFormat3Header[fields] encodes the 256-byte Format 3 little-endian footer/header."
decodeFormat3Header::usage = "decodeFormat3Header[bytes, file] decodes and SHA-256-verifies a 256-byte Format 3 footer/header."
sha256Bytes::usage = "sha256Bytes[byteArray] gives the 32-byte SHA-256 digest of byteArray."
$lazyStreamPoolLimit::usage = "$lazyStreamPoolLimit is the maximum number of open file streams kept in the global Format 3 LRU stream pool."
$lazyBlockReadCount::usage = "$lazyBlockReadCount counts disk block reads performed by Format 3 lazy environments."
$lazyProofBlockReadCount::usage = "$lazyProofBlockReadCount counts ProofNodeBlocks disk reads performed by Format 3 lazy environments."


(* ::Section:: *)
(*Function Definitions*)


$format3Magic = {84, 84, 69, 51, 0, 0, 0, 3}
$format3HeaderSize = 256

$format3FlagProofs = 1
$format3FlagDeps = 2
$format3FlagRecordHashes = 4
$format3FlagStatementOnly = 8
$format3FlagCubical = 16

$defaultBlockSizes = <|
	"StmtNode" -> 65536,
	"ProofNode" -> 65536,
	"Leaf" -> 16384,
	"Label" -> 16384,
	"RecordMeta" -> 4096,
	"RecordDir" -> 16384,
	"NameBucket" -> 4096,
	"Cubical" -> 16384
|>

$format3KindToCode = <|
	"Axiom" -> 1, "Definition" -> 2, "Opaque" -> 3, "Theorem" -> 4,
	"InductiveType" -> 5, "Constructor" -> 6, "Recursor" -> 7,
	"RewriteRule" -> 8, "Quotient" -> 9, "Cubical" -> 10, "Hole" -> 11
|>
$format3CodeToKind = AssociationMap[Reverse, $format3KindToCode]

$lazyStreamPoolLimit = 0
$lazyStreamPool = <||>
$lazyStreamTick = 0
$lazySourceCounter = 0
$lazyBlockReadCount = 0
$lazyProofBlockReadCount = 0
$lazyBlockCacheLimit = 64
$lazyRecordCacheLimit = 4096


(* ::Subsection:: *)
(*Low-level binary helpers (Wolfram 15 + WolframKernel v2 portable)*)


sha256Bytes[bytes_ByteArray] := With[{digest = Quiet[Hash[bytes, "SHA256", "ByteArray"]]},
	If[ ByteArrayQ[digest] && Length[digest] == 32,
		digest,
		ByteArray[Map[Function[hex, FromDigits[hex, 16]], StringPartition[Hash[bytes, "SHA256", "HexString"], 2]]]
	]
]

byteSlice[bytes_ByteArray, start_Integer, end_Integer] := With[{sliced = Quiet[Take[bytes, {start, end}]]},
	If[ ByteArrayQ[sliced],
		sliced,
		ByteArray[Take[Normal[bytes], {start, end}]]
	]
]

encodeUint64LE[n_Integer] := Reverse[IntegerDigits[n, 256, 8]]

decodeUint64LE[bytes_List] := FromDigits[Reverse[bytes], 256]

writeAllBytes[stream_, bytes_ByteArray] := BinaryWrite[stream, bytes]

(* Read exactly length bytes starting at offset from stream using BinaryReadList["Byte"] for W15/v2 parity *)
readExactBytes[stream_, offset_Integer, length_Integer] := Module[{raw},
	If[length == 0, Return[ByteArray[{}], Module]];
	If[offset < 0 || length < 0, kernelFailure["SavedEnvironmentInvalid", "Invalid block range in saved environment.", {}]];
	If[Quiet[SetStreamPosition[stream, offset]] === $Failed, kernelFailure["SavedEnvironmentUnreadable", "Failed to seek in saved environment.", {}]];
	raw = Quiet[BinaryReadList[stream, "Byte", length]];
	If[ ! ListQ[raw] || Length[raw] =!= length,
		kernelFailure["SavedEnvironmentInvalid", "Unexpected end of file while reading saved environment.", {}]
	];
	ByteArray[raw]
]

format3FileQ[file_String] := If[ ! FileExistsQ[file] || Quiet[FileByteCount[file]] < 8 + $format3HeaderSize,
	False,
	Module[{stream},
		WithCleanup[
			stream = Quiet[OpenRead[file, BinaryFormat -> True]],
			If[! MatchQ[stream, _InputStream], False, Quiet[BinaryReadList[stream, "Byte", 8]] === $format3Magic],
			If[MatchQ[stream, _InputStream], Quiet[Close[stream]]]
		]
	]
]

nameHash62[name_] := First[nameHashes62[{name}]]

nameHashes62[{}] := {}
nameHashes62[names_List] := With[{prints = bytesFingerprints[Map[BinarySerialize, names]]},
	Developer`ToPackedArray[prints[[1]] * 2147483648 + prints[[2]]]
]


(* ::Subsection:: *)
(*Global bounded LRU stream pool & on-disk mutation guard*)


closeLazyStreams[] := (
	Scan[Function[entry, Quiet[Close[entry["Stream"]]]], Values[$lazyStreamPool]];
	$lazyStreamPool = <||>;
	Null
)

lazyStreamPoolCount[] := Length[$lazyStreamPool]

fileSnapshot[path_String] := With[{size = Quiet[FileByteCount[path]], date = Quiet[FileDate[path]]},
	If[ ! IntegerQ[size] || ! MatchQ[date, _DateObject],
		kernelFailure["SavedEnvironmentUnreadable", "`1` cannot be read.", {path}],
		{size, date}
	]
]

poolStreamFor[source_Symbol] := Module[
	{path = source["Path"], expectedSize = source["ByteCount"], expectedDate = source["FileDate"], current, entry, stream, oldestKey},
	current = Quiet[{FileByteCount[path], FileDate[path]}];
	If[ current =!= {expectedSize, expectedDate},
		If[ KeyExistsQ[$lazyStreamPool, path],
			Quiet[Close[$lazyStreamPool[path]["Stream"]]];
			KeyDropFrom[$lazyStreamPool, path]
		];
		kernelFailure["SavedEnvironmentChangedOnDisk", "`1` was modified or removed on disk after it was opened.", {path}]
	];
	If[ KeyExistsQ[$lazyStreamPool, path],
		entry = $lazyStreamPool[path];
		If[ entry["ByteCount"] === expectedSize && entry["FileDate"] === expectedDate && MemberQ[Streams[], entry["Stream"]],
			$lazyStreamPool[path] = Append[entry, "LastUsed" -> ++$lazyStreamTick];
			Return[entry["Stream"], Module]
		];
		Quiet[Close[entry["Stream"]]];
		KeyDropFrom[$lazyStreamPool, path]
	];
	While[ Length[$lazyStreamPool] >= Max[1, $lazyStreamPoolLimit],
		oldestKey = First[MinimalBy[Keys[$lazyStreamPool], Function[k, $lazyStreamPool[k]["LastUsed"]]]];
		Quiet[Close[$lazyStreamPool[oldestKey]["Stream"]]];
		KeyDropFrom[$lazyStreamPool, oldestKey]
	];
	stream = Quiet[OpenRead[path, BinaryFormat -> True]];
	If[ ! MatchQ[stream, _InputStream],
		kernelFailure["SavedEnvironmentUnreadable", "`1` cannot be opened.", {path}]
	];
	$lazyStreamPool[path] = <|"Stream" -> stream, "ByteCount" -> expectedSize, "FileDate" -> expectedDate, "LastUsed" -> ++$lazyStreamTick|>;
	stream
]

readSourceRange[source_Symbol, offset_Integer, length_Integer] := Module[{path = source["Path"], expectedSize = source["ByteCount"], expectedDate = source["FileDate"], stream},
	If[ offset < 8 || length < 0 || offset + length > expectedSize - $format3HeaderSize,
		kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {path}]
	];
	If[ ! IntegerQ[$lazyStreamPoolLimit] || $lazyStreamPoolLimit <= 0,
		If[ Quiet[{FileByteCount[path], FileDate[path]}] =!= {expectedSize, expectedDate},
			kernelFailure["SavedEnvironmentChangedOnDisk", "`1` was modified or removed on disk after it was opened.", {path}]
		];
		WithCleanup[
			stream = Quiet[OpenRead[path, BinaryFormat -> True]],
			If[ ! MatchQ[stream, _InputStream],
				kernelFailure["SavedEnvironmentUnreadable", "`1` cannot be opened.", {path}]
			];
			readExactBytes[stream, offset, length],
			If[MatchQ[stream, _InputStream], Quiet[Close[stream]]]
		],
		readExactBytes[poolStreamFor[source], offset, length]
	]
]


(* ::Subsection:: *)
(*Header encoding / decoding & verified block reading*)


encodeFormat3Header[fields_Association] := Module[{prefix, digest},
	prefix = Join[
		$format3Magic,
		encodeUint64LE[$format3HeaderSize],
		encodeUint64LE[fields["Flags"]],
		encodeUint64LE[fields["ConstantCount"]],
		encodeUint64LE[fields["StmtNodeCount"]],
		encodeUint64LE[fields["ProofNodeCount"]],
		encodeUint64LE[fields["LeafCount"]],
		encodeUint64LE[fields["LabelCount"]],
		encodeUint64LE[fields["StmtNodeBlockSize"]],
		encodeUint64LE[fields["ProofNodeBlockSize"]],
		encodeUint64LE[fields["LeafBlockSize"]],
		encodeUint64LE[fields["LabelBlockSize"]],
		encodeUint64LE[fields["RecordMetaBlockSize"]],
		encodeUint64LE[fields["SectionDirOffset"]],
		encodeUint64LE[fields["SectionDirLength"]],
		encodeUint64LE[fields["MetaOffset"]],
		encodeUint64LE[fields["MetaLength"]],
		encodeUint64LE[fields["ManifestOffset"]],
		encodeUint64LE[fields["ManifestLength"]],
		Normal[fields["MetaSha256"]],
		Normal[fields["ManifestSha256"]]
	];
	digest = sha256Bytes[ByteArray[prefix]];
	ByteArray[Join[prefix, Normal[digest], ConstantArray[0, 8]]]
]

decodeFormat3Header[headerBytes_ByteArray, file_String] := Module[{raw = Normal[headerBytes], expectedDigest, actualDigest, fields},
	If[ Length[raw] =!= $format3HeaderSize || Take[raw, 8] =!= $format3Magic,
		kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {file}]
	];
	expectedDigest = ByteArray[Take[raw, {217, 248}]];
	actualDigest = sha256Bytes[ByteArray[Take[raw, 216]]];
	If[ actualDigest =!= expectedDigest,
		kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {file}]
	];
	fields = <|
		"HeaderSize" -> decodeUint64LE[Take[raw, {9, 16}]],
		"Flags" -> decodeUint64LE[Take[raw, {17, 24}]],
		"ConstantCount" -> decodeUint64LE[Take[raw, {25, 32}]],
		"StmtNodeCount" -> decodeUint64LE[Take[raw, {33, 40}]],
		"ProofNodeCount" -> decodeUint64LE[Take[raw, {41, 48}]],
		"LeafCount" -> decodeUint64LE[Take[raw, {49, 56}]],
		"LabelCount" -> decodeUint64LE[Take[raw, {57, 64}]],
		"StmtNodeBlockSize" -> decodeUint64LE[Take[raw, {65, 72}]],
		"ProofNodeBlockSize" -> decodeUint64LE[Take[raw, {73, 80}]],
		"LeafBlockSize" -> decodeUint64LE[Take[raw, {81, 88}]],
		"LabelBlockSize" -> decodeUint64LE[Take[raw, {89, 96}]],
		"RecordMetaBlockSize" -> decodeUint64LE[Take[raw, {97, 104}]],
		"SectionDirOffset" -> decodeUint64LE[Take[raw, {105, 112}]],
		"SectionDirLength" -> decodeUint64LE[Take[raw, {113, 120}]],
		"MetaOffset" -> decodeUint64LE[Take[raw, {121, 128}]],
		"MetaLength" -> decodeUint64LE[Take[raw, {129, 136}]],
		"ManifestOffset" -> decodeUint64LE[Take[raw, {137, 144}]],
		"ManifestLength" -> decodeUint64LE[Take[raw, {145, 152}]],
		"MetaSha256" -> ByteArray[Take[raw, {153, 184}]],
		"ManifestSha256" -> ByteArray[Take[raw, {185, 216}]]
	|>;
	If[ fields["HeaderSize"] =!= $format3HeaderSize ||
		Min[Lookup[fields, {"StmtNodeBlockSize", "ProofNodeBlockSize", "LeafBlockSize", "LabelBlockSize", "RecordMetaBlockSize"}]] < 1,
		kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {file}]
	];
	fields
]

(* Extract only verified String keys from a held atomic Association without evaluating any key or value *)
heldStringKeys[HoldComplete[association_Association]] /; AtomQ[Unevaluated[association]] :=
	Cases[Keys[association, HoldComplete], HoldComplete[s_String] :> s]
heldStringKeys[_] := {}

blankPackedKeys[held : HoldComplete[association_Association], keys_List] /; AtomQ[Unevaluated[association]] := Fold[
	Function[{data, key},
		If[ MatchQ[Quiet[Extract[data, {1, Key[key]}, HoldComplete]], HoldComplete[array_ /; Developer`PackedArrayQ[Unevaluated[array], Integer]]],
			ReplacePart[data, {1, Key[key]} -> 0],
			data
		]
	],
	held,
	keys
]
blankPackedKeys[held_, _] := held

blankByteArrayValues[held : HoldComplete[association_Association]] /; AtomQ[Unevaluated[association]] := Fold[
	Function[{data, key},
		If[ MatchQ[Quiet[Extract[data, {1, Key[key]}, HoldComplete]], HoldComplete[b_ByteArray /; AtomQ[Unevaluated[b]]]],
			ReplacePart[data, {1, Key[key]} -> 0],
			data
		]
	],
	held,
	heldStringKeys[held]
]
blankByteArrayValues[held_] := held

deserializeHeldChecked[bytes_ByteArray, expectedDigest_ByteArray, blankKeys_, file_String] := Module[{held},
	If[ sha256Bytes[bytes] =!= expectedDigest,
		kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {file}]
	];
	held = Quiet[BinaryDeserialize[bytes, HoldComplete]];
	If[ ! MatchQ[held, _HoldComplete],
		kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {file}]
	];
	With[{checked = Which[
			blankKeys === "ByteArrays", blankByteArrayValues[held],
			blankKeys === "PackedInteger", If[MatchQ[held, HoldComplete[a_ /; Developer`PackedArrayQ[Unevaluated[a], Integer]]], HoldComplete[0], held],
			blankKeys === "AllPackedValues", blankPackedKeys[held, heldStringKeys[held]],
			ListQ[blankKeys] && blankKeys =!= {}, blankPackedKeys[held, blankKeys],
			True, held
		]},
		If[ ! heldDataQ[checked],
			kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {file}]
		]
	];
	First[held]
]

manifestDigestOf[source_Symbol, section_String, blockIndex_Integer] := With[{entry = Lookup[source["Manifest"], section, None]},
	If[ ! ByteArrayQ[entry] || blockIndex < 1 || 32 * blockIndex > Length[entry],
		kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {source["Path"]}]
	];
	byteSlice[entry, 32 * (blockIndex - 1) + 1, 32 * blockIndex]
]

sectionRangeOf[source_Symbol, section_String, blockIndex_Integer] := With[{entries = Lookup[source["SectionDirectory"], section, None]},
	Which[
		blockIndex == 0 && ListQ[entries] && Length[entries] == 2 && AllTrue[entries, IntegerQ],
			entries,
		MatrixQ[entries, IntegerQ] && Last[Dimensions[entries]] == 2 && 1 <= blockIndex <= Length[entries],
			entries[[blockIndex]],
		True,
			kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {source["Path"]}]
	]
]

readVerifiedBlock[source_Symbol, section_String, blockIndex_Integer, blankKeys_] := Module[
	{cacheKey = {section, blockIndex}, cache = source["BlockCache"], range, digest, bytes, value},
	If[ KeyExistsQ[cache, cacheKey],
		Return[cache[cacheKey], Module]
	];
	range = sectionRangeOf[source, section, blockIndex];
	digest = manifestDigestOf[source, section, If[blockIndex == 0, 1, blockIndex]];
	$lazyBlockReadCount++;
	If[section === "ProofNodeBlocks", $lazyProofBlockReadCount++];
	bytes = readSourceRange[source, First[range], Last[range]];
	value = deserializeHeldChecked[bytes, digest, blankKeys, source["Path"]];
	If[ Length[cache] >= $lazyBlockCacheLimit,
		cache = Drop[cache, Quotient[$lazyBlockCacheLimit, 4]]
	];
	source["BlockCache"] = Append[cache, cacheKey -> value];
	value
]


(* ::Subsection:: *)
(*Validation of Format 3 metadata, blocks, and records*)


format3MetaQ[meta_Association, header_Association] := And[
	SubsetQ[Keys[meta], {"Format", "FormatVersion", "KernelHash", "Rules", "Base", "NaturalNumbers", "RewriteRuleIndex", "OverloadIndex", "KindCounts", "BlockSizes", "Hash"}],
	meta["Format"] === "TypeTheoryEnvironment",
	meta["FormatVersion"] === 3,
	StringQ[meta["KernelHash"]],
	rulesQ[meta["Rules"]],
	MatchQ[meta["Base"], None | KeyValuePattern[{"Name" -> _String, "Hash" -> _String}]],
	inertQ[meta["NaturalNumbers"], 1],
	indexAssociationQ[meta["RewriteRuleIndex"]],
	indexAssociationQ[meta["OverloadIndex"]],
	kindCountsQ[meta["KindCounts"], header["ConstantCount"]],
	AssociationQ[meta["BlockSizes"]] && AllTrue[Values[meta["BlockSizes"]], Function[n, IntegerQ[n] && n >= 1]],
	StringQ[meta["Hash"]]
]
format3MetaQ[_, _] := False

indexAssociationQ[index_Association] := And[
	AllTrue[Keys[index], nameQ],
	AllTrue[Values[index], Function[names, ListQ[names] && AllTrue[names, nameQ]]]
]
indexAssociationQ[_] := False

kindCountsQ[counts_Association, total_Integer] := And[
	SubsetQ[Keys[$format3KindToCode], Keys[counts]],
	AllTrue[Values[counts], Function[n, IntegerQ[n] && n >= 0]],
	Total[Values[counts]] == total
]
kindCountsQ[_, _] := False

(* Record metadata validation: allows termRef[0] for Type slot, termRef[-1] for Value slot, and 1..stmtNodeCount for Recursor/RewriteRule terms *)
format3RecordMetaQ[record_Association, stmtNodeCount_Integer] := And[
	KeyExistsQ[$format3KindToCode, record["Kind"]],
	format3InertQ[KeyDrop[record, "Annotation"], stmtNodeCount],
	annotationQ[Lookup[record, "Annotation", None]]
]
format3RecordMetaQ[_, _] := False

format3InertQ[_String | _Integer | True | False | None | Infinity, _] := True
format3InertQ[termRef[0 | -1], _] := True
format3InertQ[termRef[reference_Integer], stmtNodeCount_Integer] := 1 <= reference <= stmtNodeCount
format3InertQ[list_List, stmtNodeCount_Integer] := AllTrue[list, Function[element, format3InertQ[element, stmtNodeCount]]]
format3InertQ[association_Association, stmtNodeCount_Integer] := And[
	AllTrue[Keys[association], Function[key, format3InertQ[key, stmtNodeCount]]],
	AllTrue[Values[association], Function[value, format3InertQ[value, stmtNodeCount]]]
]
format3InertQ[value_, _] := nameQ[value] || levelQ[value] || leafTermQ[value]


(* ::Subsection:: *)
(*Opening a Format 3 file*)


lazySourceQ[source_Symbol] := IntegerQ[source["Identifier"]]
lazySourceQ[_] := False

loadFormat3Environment[file_String, check_] := Module[
	{
		snapshot = fileSnapshot[file], fileSize, fileDate, stream, headerBytes, header,
		metaBytes, meta, manifestBytes, manifest, sectionDirBytes, sectionDir,
		coarseBytes, coarseHashes, loadBase, source, loadedStore, loaded, rewrittenIndex, overloadedIndex
	},
	{fileSize, fileDate} = snapshot;
	If[ fileSize < 8 + $format3HeaderSize,
		kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {file}]
	];
	WithCleanup[
		stream = Quiet[OpenRead[file, BinaryFormat -> True]],
		If[ ! MatchQ[stream, _InputStream],
			kernelFailure["SavedEnvironmentUnreadable", "`1` cannot be opened.", {file}]
		];
		If[ Normal[readExactBytes[stream, 0, 8]] =!= $format3Magic,
			kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {file}]
		];
		headerBytes = readExactBytes[stream, fileSize - $format3HeaderSize, $format3HeaderSize];
		header = decodeFormat3Header[headerBytes, file];
		If[ header["MetaOffset"] < 8 || header["MetaOffset"] + header["MetaLength"] > fileSize - $format3HeaderSize ||
			header["ManifestOffset"] < 8 || header["ManifestOffset"] + header["ManifestLength"] > fileSize - $format3HeaderSize ||
			header["SectionDirOffset"] < 8 || header["SectionDirOffset"] + header["SectionDirLength"] > fileSize - $format3HeaderSize,
			kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {file}]
		];
		metaBytes = readExactBytes[stream, header["MetaOffset"], header["MetaLength"]];
		manifestBytes = readExactBytes[stream, header["ManifestOffset"], header["ManifestLength"]];
		sectionDirBytes = readExactBytes[stream, header["SectionDirOffset"], header["SectionDirLength"]],
		If[MatchQ[stream, _InputStream], Quiet[Close[stream]]]
	];
	meta = deserializeHeldChecked[metaBytes, header["MetaSha256"], {}, file];
	If[ ! AssociationQ[meta] || ! format3MetaQ[meta, header],
		kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {file}]
	];
	manifest = deserializeHeldChecked[manifestBytes, header["ManifestSha256"], "ByteArrays", file];
	If[ ! AssociationQ[manifest] || ! ByteArrayQ[Lookup[manifest, "SectionDirectory", None]],
		kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {file}]
	];
	sectionDir = deserializeHeldChecked[sectionDirBytes, manifest["SectionDirectory"], "AllPackedValues", file];
	If[ ! AssociationQ[sectionDir],
		kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {file}]
	];
	If[ meta["KernelHash"] =!= $kernelHash && ! TrueQ[check],
		kernelFailure[
			"SavedByAnotherKernel",
			"`1` was saved by TypeTheory `2`, whose kernel differs from this one; read it with \"Check\" -> True to check its `3` constants again.",
			{file, Lookup[meta, "TypeTheoryVersion", "unknown"], header["ConstantCount"]}
		]
	];
	loadBase = Replace[meta["Base"], {None :> emptyEnvironmentOf[meta["Rules"]], KeyValuePattern["Name" -> name_String] :> TypeTheoryEnvironment[name]}];
	If[ ! environmentQ[loadBase] || environmentRules[loadBase] =!= meta["Rules"],
		kernelFailure["SavedEnvironmentBase", "`1` extends the environment `2`, which this TypeTheory does not have.", {file, Lookup[Replace[meta["Base"], Except[_Association] -> <||>], "Name", None]}]
	];
	If[ AssociationQ[meta["Base"]] && meta["Base"]["Hash"] =!= environmentContentHash[loadBase] && ! TrueQ[check],
		kernelFailure[
			"SavedEnvironmentBaseChanged",
			"`1` was saved over the environment `2` as it was then, and its declarations have changed since; read it with \"Check\" -> True to check its `3` constants again.",
			{file, meta["Base"]["Name"], header["ConstantCount"]}
		]
	];
	Module[{lazyHandle},
		ClearAttributes[lazyHandle, Temporary];
		lazyHandle["Identifier"] = ++$lazySourceCounter;
		lazyHandle["Path"] = file;
		lazyHandle["ByteCount"] = fileSize;
		lazyHandle["FileDate"] = fileDate;
		lazyHandle["Header"] = header;
		lazyHandle["Meta"] = meta;
		lazyHandle["Manifest"] = manifest;
		lazyHandle["SectionDirectory"] = sectionDir;
		lazyHandle["Base"] = loadBase;
		lazyHandle["BaseCount"] = environmentCount[loadBase];
		lazyHandle["ConstantCount"] = header["ConstantCount"];
		lazyHandle["StmtNodeCount"] = header["StmtNodeCount"];
		lazyHandle["ProofNodeCount"] = header["ProofNodeCount"];
		lazyHandle["LeafCount"] = header["LeafCount"];
		lazyHandle["LabelCount"] = header["LabelCount"];
		lazyHandle["BlockCache"] = <||>;
		lazyHandle["StatementCache"] = <||>;
		lazyHandle["FullCache"] = <||>;
		lazyHandle["NameCoarse"] = If[ header["ConstantCount"] == 0,
			{},
			With[{coarse = readVerifiedBlock[lazyHandle, "NameIndexCoarse", 0, "PackedInteger"]},
				If[ ! Developer`PackedArrayQ[coarse, Integer, 1] && ! VectorQ[coarse, IntegerQ],
					kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {file}]
				];
				coarse
			]
		];
		source = lazyHandle
	];
	(* Build the lazy TypeTheoryEnvironment store *)
	With[{baseStore = First[loadBase]},
		rewrittenIndex = Merge[{Replace[baseStore["RewriteRuleIndex"], Except[_Association] -> <||>], meta["RewriteRuleIndex"]}, Apply[Join]];
		overloadedIndex = Merge[{Replace[baseStore["OverloadIndex"], Except[_Association] -> <||>], meta["OverloadIndex"]}, Apply[Join]];
		loaded = newLazyEnvironment[loadBase, source, meta["Rules"], rewrittenIndex, overloadedIndex, meta["NaturalNumbers"]]
	];
	loadedStore = First[loaded];
	loadedStore["ContentHash"] = meta["Hash"];
	loadedStore["Provenance"] = <|"Source" -> File[file], "Hash" -> meta["Hash"], "Checked" -> False, "FormatVersion" -> 3|>;
	If[ TrueQ[check],
		Replace[TypeTheoryCheck[loaded], failure_Failure :> throwFailure[failure]];
		loadedStore["Provenance"] = Append[loadedStore["Provenance"], "Checked" -> True]
	];
	loaded
]


(* ::Subsection:: *)
(*Lazy lookup & DAG-cone decoding*)


binarySearchFirstGE[array_, target_Integer] := Module[{lo = 1, hi = Length[array], mid, ans = Length[array] + 1},
	While[ lo <= hi,
		mid = Quotient[lo + hi, 2];
		If[ array[[mid]] >= target,
			ans = mid;
			hi = mid - 1,
			lo = mid + 1
		]
	];
	ans
]

readNameBucket[source_Symbol, bucketIndex_Integer] := With[{bucket = readVerifiedBlock[source, "NameIndexBuckets", bucketIndex, {"Hashes", "RecordIDs"}]},
	If[ ! AssociationQ[bucket] || ! SubsetQ[Keys[bucket], {"Hashes", "RecordIDs", "Names"}] ||
		! VectorQ[bucket["Hashes"], IntegerQ] || ! VectorQ[bucket["RecordIDs"], IntegerQ] ||
		! ListQ[bucket["Names"]] || Length[bucket["Hashes"]] =!= Length[bucket["RecordIDs"]] ||
		Length[bucket["Hashes"]] =!= Length[bucket["Names"]] ||
		! AllTrue[bucket["Names"], nameQ],
		kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {source["Path"]}]
	];
	bucket
]

lazyConstantIndex[source_Symbol, name_HoldComplete] := Module[
	{count = source["ConstantCount"], coarse = source["NameCoarse"], hash, startBucket, bucketIndex, bucket, hashes, pos, found = 0},
	If[count == 0, Return[0, Module]];
	hash = nameHash62[name];
	startBucket = binarySearchFirstGE[coarse, hash];
	If[startBucket > Length[coarse], Return[0, Module]];
	bucketIndex = startBucket;
	While[ bucketIndex <= Length[coarse] && found == 0,
		bucket = readNameBucket[source, bucketIndex];
		hashes = bucket["Hashes"];
		pos = binarySearchFirstGE[hashes, hash];
		While[ pos <= Length[hashes] && hashes[[pos]] == hash && found == 0,
			If[ bucket["Names"][[pos]] === name,
				found = bucket["RecordIDs"][[pos]];
				If[ ! IntegerQ[found] || found < 1 || found > count,
					kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {source["Path"]}]
				]
			];
			pos++
		];
		(* Only continue to next bucket if the last hash in this bucket equals target hash *)
		If[found == 0 && Length[hashes] > 0 && Last[hashes] == hash, bucketIndex++, Break[]]
	];
	found
]

lazyConstantDeclaredQ[source_Symbol, name_HoldComplete] :=
	lazyConstantIndex[source, name] > 0 || constantDeclaredQ[source["Base"], name]

readRecordDirBlock[source_Symbol, blockIndex_Integer] := With[{mat = readVerifiedBlock[source, "RecordDirBlocks", blockIndex, "PackedInteger"]},
	If[ ! MatrixQ[mat, IntegerQ] || Last[Dimensions[mat]] =!= 4,
		kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {source["Path"]}]
	];
	mat
]

recordDirEntry[source_Symbol, localId_Integer] := With[
	{blockSize = source["Meta"]["BlockSizes"]["RecordDir"]},
	With[{block = readRecordDirBlock[source, Quotient[localId - 1, blockSize] + 1], localPos = Mod[localId - 1, blockSize] + 1},
		If[ localPos > Length[block],
			kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {source["Path"]}]
		];
		block[[localPos]]
	]
]

readRecordMetaBlock[source_Symbol, blockIndex_Integer] := With[{block = readVerifiedBlock[source, "RecordMetaBlocks", blockIndex, {}]},
	If[ ! AssociationQ[block] || ! SubsetQ[Keys[block], {"Names", "Meta"}] ||
		! ListQ[block["Names"]] || ! ListQ[block["Meta"]] || Length[block["Names"]] =!= Length[block["Meta"]] ||
		! AllTrue[block["Names"], nameQ] ||
		! AllTrue[block["Meta"], Function[m, format3RecordMetaQ[m, source["StmtNodeCount"]]]],
		kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {source["Path"]}]
	];
	block
]

recordMetaEntry[source_Symbol, localId_Integer] := With[
	{blockSize = source["Header"]["RecordMetaBlockSize"]},
	With[{block = readRecordMetaBlock[source, Quotient[localId - 1, blockSize] + 1], localPos = Mod[localId - 1, blockSize] + 1},
		If[ localPos > Length[block["Meta"]],
			kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {source["Path"]}]
		];
		{block["Names"][[localPos]], block["Meta"][[localPos]]}
	]
]

readLeafBlock[source_Symbol, blockIndex_Integer] := With[{block = readVerifiedBlock[source, "LeafBlocks", blockIndex, {}]},
	If[ ! ListQ[block] || ! AllTrue[block, leafTermQ],
		kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {source["Path"]}]
	];
	block
]

readLabelBlock[source_Symbol, blockIndex_Integer] := With[{block = readVerifiedBlock[source, "LabelBlocks", blockIndex, {}]},
	If[ ! ListQ[block] || ! AllTrue[block, Function[label, nameQ[label] || binderQ[label]]],
		kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {source["Path"]}]
	];
	block
]

readNodeBlock[source_Symbol, section_String, blockIndex_Integer] := With[{mat = readVerifiedBlock[source, section, blockIndex, "PackedInteger"]},
	If[ ! MatrixQ[mat, IntegerQ] || Last[Dimensions[mat]] =!= 5,
		kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {source["Path"]}]
	];
	mat
]

readCubicalBlock[source_Symbol, blockIndex_Integer] := With[{mat = readVerifiedBlock[source, "CubicalBlocks", blockIndex, "PackedInteger"]},
	If[ ! MatrixQ[mat, IntegerQ] || Last[Dimensions[mat]] =!= 2,
		kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {source["Path"]}]
	];
	mat
]

fetchLeaf[source_Symbol, leafId_Integer] := Module[{blockSize = source["Header"]["LeafBlockSize"], block, pos},
	If[ leafId < 1 || leafId > source["LeafCount"],
		kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {source["Path"]}]
	];
	block = readLeafBlock[source, Quotient[leafId - 1, blockSize] + 1];
	pos = Mod[leafId - 1, blockSize] + 1;
	If[ pos > Length[block],
		kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {source["Path"]}]
	];
	block[[pos]]
]

fetchLabel[source_Symbol, labelId_Integer, test_] := Module[{blockSize = source["Header"]["LabelBlockSize"], block, pos, label},
	If[ labelId < 1 || labelId > source["LabelCount"],
		kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {source["Path"]}]
	];
	block = readLabelBlock[source, Quotient[labelId - 1, blockSize] + 1];
	pos = Mod[labelId - 1, blockSize] + 1;
	If[ pos > Length[block],
		kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {source["Path"]}]
	];
	label = block[[pos]];
	If[ ! test[label],
		kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {source["Path"]}]
	];
	label
]

fetchNodeRow[source_Symbol, rowId_Integer, allowProof_] := Module[
	{stmtCount = source["StmtNodeCount"], proofCount = source["ProofNodeCount"], blockSize, block, pos},
	Which[
		1 <= rowId <= stmtCount,
			blockSize = source["Header"]["StmtNodeBlockSize"];
			block = readNodeBlock[source, "NodeBlocks", Quotient[rowId - 1, blockSize] + 1];
			pos = Mod[rowId - 1, blockSize] + 1,
		TrueQ[allowProof] && stmtCount < rowId <= stmtCount + proofCount,
			blockSize = source["Header"]["ProofNodeBlockSize"];
			block = readNodeBlock[source, "ProofNodeBlocks", Quotient[rowId - stmtCount - 1, blockSize] + 1];
			pos = Mod[rowId - stmtCount - 1, blockSize] + 1,
		True,
			kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {source["Path"]}]
	];
	If[ pos > Length[block],
		kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {source["Path"]}]
	];
	block[[pos]]
]

fetchCubicalPairs[source_Symbol, start_Integer, count_Integer] := Module[
	{blockSize = Lookup[source["Meta"]["BlockSizes"], "Cubical", 16384], pairs = {}, index, block, pos},
	If[ BitAnd[source["Header"]["Flags"], $format3FlagCubical] == 0 || start < 1 || count < 0,
		kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {source["Path"]}]
	];
	Table[
		block = readCubicalBlock[source, Quotient[index - 1, blockSize] + 1];
		pos = Mod[index - 1, blockSize] + 1;
		If[pos > Length[block], kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {source["Path"]}]];
		block[[pos]],
		{index, start, start + count - 1}
	]
]

validatePartRef[part_Integer, parentRow_Integer, leafCount_Integer, path_String] := If[
	! ((1 <= part < parentRow) || (-leafCount <= part <= -1)),
	kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {path}]
]

(* Iterative lazy DAG-cone decoder: decodes only the sub-DAG reachable from rootPart, enforcing strict
   1 <= child < row acyclicity, leaf/label bounds, zero unused columns, and depth <= $kernelRecursionLimit *)
decodeLazyPart[source_Symbol, rootPart_Integer, allowProof_] := Block[
	{
		decPath = source["Path"], decLeafCount = source["LeafCount"],
		decBuilt = <||>, decStack, decEntry, decRowId, decReady, decDepth, decRow, decCode, decChildren, decPairs, decPartVal
	},
	Which[
		rootPart < 0,
			Return[fetchLeaf[source, -rootPart], Block],
		rootPart == 0,
			kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {decPath}]
	];
	decPartVal = Function[p, If[p < 0, fetchLeaf[source, -p], decBuilt[p]]];
	decStack = {{rootPart, False, 1}, None};
	While[ decStack =!= None,
		decEntry = First[decStack];
		decStack = Last[decStack];
		decRowId = decEntry[[1]];
		decReady = decEntry[[2]];
		decDepth = decEntry[[3]];
		If[ decDepth > $kernelRecursionLimit,
			kernelFailure["SavedEnvironmentInvalid", "`1` exceeds maximum term depth `2`.", {decPath, $kernelRecursionLimit}]
		];
		If[ ! KeyExistsQ[decBuilt, decRowId],
			decRow = fetchNodeRow[source, decRowId, allowProof];
			decCode = decRow[[1]];
			If[ decReady,
				decBuilt[decRowId] = Switch[decCode,
					1,
						Construct[application, decPartVal[decRow[[2]]], decPartVal[decRow[[3]]]],
					2,
						Construct[lambdaAbstraction, fetchLabel[source, decRow[[2]], nameQ], decPartVal[decRow[[3]]], decPartVal[decRow[[4]]], fetchLabel[source, decRow[[5]], binderQ]],
					3,
						Construct[dependentFunctionType, fetchLabel[source, decRow[[2]], nameQ], decPartVal[decRow[[3]]], decPartVal[decRow[[4]]], fetchLabel[source, decRow[[5]], binderQ]],
					4,
						Construct[localDefinition, fetchLabel[source, decRow[[2]], nameQ], decPartVal[decRow[[3]]], decPartVal[decRow[[4]]], decPartVal[decRow[[5]]]],
					5,
						Construct[projection, fetchLabel[source, decRow[[2]], nameQ], decRow[[3]], decPartVal[decRow[[4]]]],
					6,
						decPairs = fetchCubicalPairs[source, decRow[[2]], decRow[[3]]];
						Construct[cubicalSystem, Map[decPartVal, decPairs, {2}]],
					_,
						kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {decPath}]
				],
				(* Validate row structure and push unbuilt row children *)
				decChildren = Switch[decCode,
					1,
						If[decRow[[4]] =!= 0 || decRow[[5]] =!= 0, kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {decPath}]];
						{decRow[[2]], decRow[[3]]},
					2 | 3,
						{decRow[[3]], decRow[[4]]},
					4,
						{decRow[[3]], decRow[[4]], decRow[[5]]},
					5,
						If[decRow[[3]] < 0 || decRow[[5]] =!= 0, kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {decPath}]];
						{decRow[[4]]},
					6,
						If[decRow[[4]] =!= 0 || decRow[[5]] =!= 0, kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {decPath}]];
						Flatten[fetchCubicalPairs[source, decRow[[2]], decRow[[3]]], 1],
					_,
						kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {decPath}]
				];
				Scan[Function[c, validatePartRef[c, decRowId, decLeafCount, decPath]], decChildren];
				decStack = {{decRowId, True, decDepth}, decStack};
				Scan[
					Function[c, If[c > 0 && ! KeyExistsQ[decBuilt, c], decStack = {{c, False, decDepth + 1}, decStack}]],
					Reverse[decChildren]
				]
			]
		]
	];
	decBuilt[rootPart]
]

resolveLazyMetaTerms[source_Symbol, expr_, typeRoot_Integer, valueRoot_Integer, allowProof_] := Replace[expr, {
	termRef[0] :> decodeLazyPart[source, typeRoot, False],
	termRef[-1] :> decodeLazyPart[source, valueRoot, allowProof],
	termRef[row_Integer] :> decodeLazyPart[source, row, False],
	association_Association :> Map[Function[v, resolveLazyMetaTerms[source, v, typeRoot, valueRoot, allowProof]], association],
	list_List :> Map[Function[v, resolveLazyMetaTerms[source, v, typeRoot, valueRoot, allowProof]], list],
	other_ :> other
}]

lazyConstantKind[source_Symbol, name_HoldComplete] := With[{localId = lazyConstantIndex[source, name]},
	If[ localId == 0,
		constantStatementRecord[source["Base"], name]["Kind"],
		With[{kindCode = First[recordDirEntry[source, localId]]},
			Lookup[$format3CodeToKind, kindCode, kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {source["Path"]}]]
		]
	]
]

lazyConstantRecord[source_Symbol, name_HoldComplete, includeProof_] := Module[
	{localId, cacheKey, cache, dir, kindCode, kind, typeRoot, valueRoot, metaPair, metaName, meta, omitProof, record},
	localId = lazyConstantIndex[source, name];
	If[ localId == 0,
		Return[
			If[TrueQ[includeProof], constantRecord[source["Base"], name], constantStatementRecord[source["Base"], name]],
			Module
		]
	];
	cacheKey = If[TrueQ[includeProof], "FullCache", "StatementCache"];
	cache = source[cacheKey];
	If[ KeyExistsQ[cache, localId],
		Return[cache[localId], Module]
	];
	(* If FullCache already holds it, StatementCache can reuse it directly without disk I/O *)
	If[ ! TrueQ[includeProof] && KeyExistsQ[source["FullCache"], localId],
		Return[source["FullCache"][localId], Module]
	];
	dir = recordDirEntry[source, localId];
	{kindCode, typeRoot, valueRoot} = Take[dir, 3];
	kind = Lookup[$format3CodeToKind, kindCode, kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {source["Path"]}]];
	metaPair = recordMetaEntry[source, localId];
	{metaName, meta} = metaPair;
	If[ metaName =!= name,
		kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {source["Path"]}]
	];
	(* Statement-only cut converts stripped Theorem/Opaque records honestly to Axiom *)
	If[ BitAnd[source["Header"]["Flags"], $format3FlagStatementOnly] =!= 0 && kind === "Axiom" && MemberQ[{"Theorem", "Opaque"}, meta["Kind"]],
		meta = Join[<|"Kind" -> "Axiom"|>, KeyDrop[meta, {"Kind", "Value"}]]
	];
	If[ meta["Kind"] =!= kind,
		kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {source["Path"]}]
	];
	omitProof = ! TrueQ[includeProof] && MemberQ[{"Theorem", "Opaque"}, kind];
	record = If[ omitProof,
		resolveLazyMetaTerms[source, KeyDrop[meta, "Value"], typeRoot, 0, False],
		resolveLazyMetaTerms[source, meta, typeRoot, valueRoot, MemberQ[{"Theorem", "Opaque"}, kind]]
	];
	If[ Length[cache] >= $lazyRecordCacheLimit,
		cache = Drop[cache, Quotient[$lazyRecordCacheLimit, 4]]
	];
	source[cacheKey] = Append[cache, localId -> record];
	If[ ! omitProof && cacheKey === "StatementCache",
		source["FullCache"] = Append[If[Length[source["FullCache"]] >= $lazyRecordCacheLimit, Drop[source["FullCache"], Quotient[$lazyRecordCacheLimit, 4]], source["FullCache"]], localId -> record]
	];
	record
]


(* ::Subsection:: *)
(*Bulk / summary queries on a lazy source*)


lazyEnvironmentCount[source_Symbol] := source["BaseCount"] + source["ConstantCount"]

lazyKindCounts[source_Symbol] := Merge[{environmentKindCounts[source["Base"]], source["Meta"]["KindCounts"]}, Total]

lazyLocalNames[source_Symbol] := Module[
	{count = source["ConstantCount"], blockSize = source["Header"]["RecordMetaBlockSize"], blockCount},
	If[count == 0, Return[{}, Module]];
	blockCount = Ceiling[count / blockSize];
	Catenate[Table[readRecordMetaBlock[source, b]["Names"], {b, blockCount}]]
]

lazyEnvironmentNames[source_Symbol] := Join[environmentNames[source["Base"]], lazyLocalNames[source]]

lazyNamesOfKind[source_Symbol, kind_String] := Module[
	{
		baseNames = Select[environmentNames[source["Base"]], Function[n, constantStatementRecord[source["Base"], n]["Kind"] === kind]],
		count = source["ConstantCount"], targetCode = Lookup[$format3KindToCode, kind, 0],
		dirBlockSize, dirBlocks, matchingIds = {}, b, mat, localHits, offset = 0
	},
	If[count == 0 || targetCode == 0, Return[baseNames, Module]];
	dirBlockSize = source["Meta"]["BlockSizes"]["RecordDir"];
	dirBlocks = Ceiling[count / dirBlockSize];
	Do[
		mat = readRecordDirBlock[source, b];
		localHits = Flatten[Position[mat[[All, 1]], targetCode, {1}, Heads -> False]];
		If[localHits =!= {}, AppendTo[matchingIds, offset + localHits]];
		offset += Length[mat],
		{b, dirBlocks}
	];
	matchingIds = Catenate[matchingIds];
	Join[baseNames, Map[Function[id, First[recordMetaEntry[source, id]]], matchingIds]]
]

lazyRecordHashes[source_Symbol] := Module[
	{baseHashes = environmentRecordHashes[source["Base"]], count = source["ConstantCount"], names, blockCount, rows},
	If[count == 0, Return[baseHashes, Module]];
	names = lazyLocalNames[source];
	If[ BitAnd[source["Header"]["Flags"], $format3FlagRecordHashes] =!= 0,
		blockCount = Length[Lookup[source["SectionDirectory"], "RecordHashBlocks", {}]];
		rows = Join @@ Table[
			With[{mat = readVerifiedBlock[source, "RecordHashBlocks", b, "PackedInteger"]},
				If[ ! MatrixQ[mat, IntegerQ] || Last[Dimensions[mat]] =!= 4,
					kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {source["Path"]}]
				];
				mat
			],
			{b, blockCount}
		];
		If[ Length[rows] =!= count,
			kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {source["Path"]}]
		];
		Join[baseHashes, AssociationThread[names, Normal[rows]]],
		(* Fallback: compute record fingerprints if optional RecordHashBlocks absent *)
		Join[baseHashes, recordFingerprints[AssociationMap[Function[n, lazyConstantRecord[source, n, True]], names]]]
	]
]

lazyMaterializeRecords[store_Symbol] := Module[{source = store["LazySource"], names, baseRecords, localRecords},
	If[! lazySourceQ[source], kernelFailure["SavedEnvironmentInvalid", "The lazy environment handle is no longer valid.", {}]];
	names = lazyLocalNames[source];
	baseRecords = AssociationMap[Function[n, constantRecord[source["Base"], n]], environmentNames[source["Base"]]];
	localRecords = AssociationMap[Function[n, lazyConstantRecord[source, n, True]], names];
	Join[baseRecords, localRecords, store["Overlay"]]
]


(* ::Subsection:: *)
(*Optional CSR DepBlocks queries & verification*)


lazyHasDepsQ[source_Symbol] := BitAnd[source["Header"]["Flags"], $format3FlagDeps] =!= 0

readDepBlock[source_Symbol, blockIndex_Integer] := With[{block = readVerifiedBlock[source, "DepBlocks", blockIndex, {"StmtOffsets", "StmtTargets", "ProofOffsets", "ProofTargets"}]},
	If[ ! AssociationQ[block] || ! SubsetQ[Keys[block], {"StmtOffsets", "StmtTargets", "ProofOffsets", "ProofTargets"}] ||
		! VectorQ[block["StmtOffsets"], IntegerQ] || ! VectorQ[block["StmtTargets"], IntegerQ] ||
		! VectorQ[block["ProofOffsets"], IntegerQ] || ! VectorQ[block["ProofTargets"], IntegerQ],
		kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {source["Path"]}]
	];
	block
]

lazyConstantDeps[source_Symbol, localId_Integer, includeProof_] := Module[
	{blockSize = source["Header"]["RecordMetaBlockSize"], block, pos, sStart, sEnd, pStart, pEnd, stmtIds, proofIds},
	block = readDepBlock[source, Quotient[localId - 1, blockSize] + 1];
	pos = Mod[localId - 1, blockSize] + 1;
	If[ pos >= Length[block["StmtOffsets"]] || pos >= Length[block["ProofOffsets"]],
		kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {source["Path"]}]
	];
	sStart = block["StmtOffsets"][[pos]];
	sEnd = block["StmtOffsets"][[pos + 1]] - 1;
	stmtIds = If[sEnd >= sStart, block["StmtTargets"][[sStart ;; sEnd]], {}];
	If[ ! TrueQ[includeProof],
		stmtIds,
		pStart = block["ProofOffsets"][[pos]];
		pEnd = block["ProofOffsets"][[pos + 1]] - 1;
		proofIds = If[pEnd >= pStart, block["ProofTargets"][[pStart ;; pEnd]], {}];
		Join[stmtIds, proofIds]
	]
]

lazyDependencyCone[source_Symbol, seedNames_List, includeProof_] := Module[
	{visited = <||>, stack = None, id, deps, d},
	Scan[
		Function[name, With[{idx = lazyConstantIndex[source, name]},
			If[idx > 0 && ! KeyExistsQ[visited, idx], visited[idx] = True; stack = {idx, stack}]
		]],
		seedNames
	];
	While[ stack =!= None,
		id = First[stack];
		stack = Last[stack];
		deps = lazyConstantDeps[source, id, includeProof];
		Scan[
			Function[depId,
				If[ depId > 0 && depId <= source["ConstantCount"] && ! KeyExistsQ[visited, depId],
					visited[depId] = True;
					stack = {depId, stack}
				]
			],
			deps
		]
	];
	Sort[Keys[visited]]
]

(* Extract all constant names directly referenced by a record's statement fields vs proof value *)
recordTermConstants[term_] := Block[{rtcSeen = <||>, rtcFound = <||>, rtcStack = {term, None}, rtcCur},
	While[ rtcStack =!= None,
		rtcCur = First[rtcStack];
		rtcStack = Last[rtcStack];
		If[ ! KeyExistsQ[rtcSeen, rtcCur],
			rtcSeen[rtcCur] = True;
			rtcStack = Replace[rtcCur, {
				constantReference[name_, _] :> (rtcFound[name] = True; rtcStack),
				application[f_, a_] :> {f, {a, rtcStack}},
				(lambdaAbstraction | dependentFunctionType)[_, dom_, body_, _] :> {dom, {body, rtcStack}},
				localDefinition[_, type_, val_, body_] :> {type, {val, {body, rtcStack}}},
				projection[struct_, _, t_] :> (rtcFound[struct] = True; {t, rtcStack}),
				cubicalSystem[branches_List] :> Fold[Function[{r, b}, {b, r}], rtcStack, Reverse[Flatten[branches, 1]]],
				_ -> rtcStack
			}]
		]
	];
	Keys[rtcFound]
]

recordDependencyNames[record_Association] := Module[{stmtDeps, proofDeps = {}},
	stmtDeps = Switch[record["Kind"],
		"Axiom" | "Hole",
			recordTermConstants[record["Type"]],
		"Definition",
			Join[recordTermConstants[record["Type"]], recordTermConstants[record["Value"]]],
		"Theorem" | "Opaque",
			proofDeps = recordTermConstants[record["Value"]];
			recordTermConstants[record["Type"]],
		"InductiveType",
			Join[recordTermConstants[record["Type"]], Lookup[record, "Constructors", {}], Lookup[record, "Block", {}]],
		"Constructor",
			Join[recordTermConstants[record["Type"]], {record["InductiveType"]}],
		"Recursor",
			Join[
				recordTermConstants[record["Type"]],
				{record["InductiveType"]},
				Keys[Lookup[record, "Rules", <||>]],
				Catenate[Map[Function[r, recordTermConstants[r["RightHandSide"]]], Values[Lookup[record, "Rules", <||>]]]]
			],
		"RewriteRule",
			Join[{record["Head"]}, recordTermConstants[record["LeftHandSide"]], recordTermConstants[record["RightHandSide"]]],
		"Quotient",
			Join[
				recordTermConstants[record["Type"]],
				DeleteCases[Join[Lookup[record, {"QuotientType", "Introduction", "Equality"}, None], Lookup[record, "QuotientNames", {}]], None]
			],
		"Cubical",
			Join[recordTermConstants[record["Type"]], DeleteCases[{Lookup[record, "Sum", None]}, None]],
		_,
			{}
	];
	{DeleteDuplicates[stmtDeps], Complement[DeleteDuplicates[proofDeps], stmtDeps]}
]

lazyLocalName[source_Symbol, localId_Integer] := First[recordMetaEntry[source, localId]]

lazyConstantDepNames[source_Symbol, localId_Integer, includeProof_] := Module[
	{ids = lazyConstantDeps[source, localId, includeProof], baseNames = environmentNames[source["Base"]]},
	Map[
		Function[depId,
			Which[
				depId > 0 && depId <= source["ConstantCount"],
					First[recordMetaEntry[source, depId]],
				depId < 0 && -depId <= Length[baseNames],
					baseNames[[-depId]],
				True,
					kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {source["Path"]}]
			]
		],
		ids
	]
]

(* Trust-boundary check called by TypeTheoryCheck: ensures CSR DepBlocks cannot omit any dependency *)
lazyVerifyDeps[TypeTheoryEnvironment[store_Symbol]] := Module[
	{source = store["LazySource"], baseNames, names, nameToId, id, rec, expectedStmt, expectedProof, actualStmt, actualAll, reqStmt, reqProof},
	If[! lazySourceQ[source] || ! lazyHasDepsQ[source], Return[True, Module]];
	baseNames = environmentNames[source["Base"]];
	names = lazyLocalNames[source];
	nameToId = Join[AssociationThread[baseNames, -Range[Length[baseNames]]], AssociationThread[names, Range[Length[names]]]];
	Do[
		rec = lazyConstantRecord[source, names[[id]], True];
		{expectedStmt, expectedProof} = recordDependencyNames[rec];
		reqStmt = DeleteCases[Lookup[nameToId, expectedStmt, 0], 0];
		reqProof = DeleteCases[Lookup[nameToId, expectedProof, 0], 0];
		actualStmt = lazyConstantDeps[source, id, False];
		actualAll = lazyConstantDeps[source, id, True];
		If[ ! SubsetQ[actualStmt, reqStmt] || ! SubsetQ[actualAll, Join[reqStmt, reqProof]],
			kernelFailure["DeclarationMismatch", "The dependency table of `1` does not match its record.", {HoldForm @@ names[[id]]}]
		],
		{id, Length[names]}
	];
	True
]


(* ::Subsection:: *)
(*Writing Format 3 (.tte) files*)


Options[saveFormat3Environment] = {
	"IncludeProofs" -> True,
	"IncludeDependencies" -> True,
	"Standalone" -> False,
	"BlockSizes" -> Automatic
}

resolveBlockSizes[Automatic] := $defaultBlockSizes
resolveBlockSizes[custom_Association] := Join[$defaultBlockSizes, KeyTake[custom, Keys[$defaultBlockSizes]]]
resolveBlockSizes[_] := $defaultBlockSizes

$f3SharedStmtIndex = <||>
$f3LocalNodeRow = None
$f3LeafCount = 0
$f3LabelCount = 0
$f3StreamingProofQ = False

(* Two-level DAG deduplication for Format 3: $f3LocalNodeRow caches expression pointers within one record,
   while $f3NodeIndex / $f3SharedStmtIndex deduplicate globally across records by flat 5-integer row tuples
   (or {"c", pairs} for cubicalSystem), keeping zero composite WL terms in global index keys. *)
f3LookupTuple[key_] := Lookup[$f3NodeIndex, Key[key], Lookup[$f3SharedStmtIndex, Key[key], 0]]

f3InternLeaf[leaf_] := Lookup[$f3LeafIndex, Key[leaf], ($f3LeafCount++; Sow[leaf, $f3LeafSowTag]; $f3LeafIndex[leaf] = $f3LeafCount)]

f3InternLabel[label_] := Lookup[$f3LabelIndex, Key[label], ($f3LabelCount++; Sow[label, $f3LabelSowTag]; $f3LabelIndex[label] = $f3LabelCount)]

(* Node emission helper supporting both Format 2 codes 1..5 and code 6 for cubicalSystem *)
format3EmitTerm[root_] := If[ ! compositeTermQ[root],
	-f3InternLeaf[root],
	If[ AssociationQ[$f3LocalNodeRow],
		format3EmitTermLocal[root],
		Block[{$f3LocalNodeRow = <||>}, format3EmitTermLocal[root]]
	]
]

format3EmitTermLocal[root_] := If[ KeyExistsQ[$f3LocalNodeRow, root],
	Lookup[$f3LocalNodeRow, Key[root]],
	Block[{emitStack = {{root, False}, None}, emitEntry, emitCur, emitReady, emitRow, emitPairs, emitKey, emitExisting, emitStart},
		While[ emitStack =!= None,
			emitEntry = First[emitStack];
			emitStack = Last[emitStack];
			emitCur = First[emitEntry];
			emitReady = Last[emitEntry];
			If[ ! KeyExistsQ[$f3LocalNodeRow, emitCur],
				If[ emitReady,
					If[ Head[emitCur] === cubicalSystem,
						emitPairs = Map[format3Part, First[emitCur], {2}];
						emitKey = {"c", emitPairs};
						emitExisting = f3LookupTuple[emitKey];
						If[ emitExisting > 0,
							$f3LocalNodeRow[emitCur] = emitExisting,
							If[ TrueQ[$f3StreamingProofQ],
								kernelFailure["UnsupportedStreamingCubicalProof", "Cubical system terms inside theorem proofs are not supported by the streaming Format 3 writer; use Export directly.", {}]
							];
							emitStart = $f3CubicalCount + 1;
							Scan[Function[pair, Sow[pair, $f3CubicalTag]], emitPairs];
							$f3CubicalCount += Length[emitPairs];
							Sow[{6, emitStart, Length[emitPairs], 0, 0}, $f3NodeSowTag];
							$f3NodeIndex[emitKey] = ++$f3NodeCount;
							$f3LocalNodeRow[emitCur] = $f3NodeCount
						],
						emitRow = format3PackRow[emitCur];
						emitExisting = f3LookupTuple[emitRow];
						If[ emitExisting > 0,
							$f3LocalNodeRow[emitCur] = emitExisting,
							Sow[emitRow, $f3NodeSowTag];
							$f3NodeIndex[emitRow] = ++$f3NodeCount;
							$f3LocalNodeRow[emitCur] = $f3NodeCount
						]
					],
					emitStack = format3PushChildren[emitCur, {{emitCur, True}, emitStack}]
				]
			]
		];
		Lookup[$f3LocalNodeRow, Key[root]]
	]
]

format3PushChild[child_, stack_] := If[compositeTermQ[child] && ! KeyExistsQ[$f3LocalNodeRow, child], {{child, False}, stack}, stack]

format3PushChildren[application[f_, a_], stack_] := format3PushChild[f, format3PushChild[a, stack]]
format3PushChildren[(lambdaAbstraction | dependentFunctionType)[_, dom_, body_, _], stack_] := format3PushChild[dom, format3PushChild[body, stack]]
format3PushChildren[localDefinition[_, type_, val_, body_], stack_] := format3PushChild[type, format3PushChild[val, format3PushChild[body, stack]]]
format3PushChildren[projection[_, _, t_], stack_] := format3PushChild[t, stack]
format3PushChildren[cubicalSystem[branches_List], stack_] := Fold[Function[{rest, b}, format3PushChild[b, rest]], stack, Reverse[Flatten[branches, 1]]]
format3PushChildren[_, stack_] := stack

format3Part[term_] := If[compositeTermQ[term],
	Lookup[$f3LocalNodeRow, Key[term]],
	-f3InternLeaf[term]
]

format3Label[label_] := f3InternLabel[label]

format3PackRow[application[f_, a_]] := {1, format3Part[f], format3Part[a], 0, 0}
format3PackRow[lambdaAbstraction[name_, dom_, body_, binder_]] := {2, format3Label[name], format3Part[dom], format3Part[body], format3Label[binder]}
format3PackRow[dependentFunctionType[name_, dom_, cod_, binder_]] := {3, format3Label[name], format3Part[dom], format3Part[cod], format3Label[binder]}
format3PackRow[localDefinition[name_, type_, val_, body_]] := {4, format3Label[name], format3Part[type], format3Part[val], format3Part[body]}
format3PackRow[projection[struct_, index_, term_]] := {5, format3Label[struct], index, format3Part[term], 0}

(* Encode non-Type/non-Value composite terms (Recursor rules, RewriteRule LHS/RHS) into termRef[row] *)
format3EncodeMetaValue[value_] := Which[
	compositeTermQ[value], termRef[format3EmitTerm[value]],
	AssociationQ[value], Map[format3EncodeMetaValue, value],
	ListQ[value], Map[format3EncodeMetaValue, value],
	True, value
]

format3EncodeRecordStmt[record_Association, includeProofs_] := If[ record["Kind"] === "Recursor",
	Block[{$f3LocalNodeRow = <||>}, format3EncodeRecordStmtBody[record, includeProofs]],
	format3EncodeRecordStmtBody[record, includeProofs]
]

format3EncodeRecordStmtBody[record_Association, includeProofs_] := Module[
	{effective = record, kind, typeRoot = 0, meta, flags = 0},
	If[ ! TrueQ[includeProofs] && MemberQ[{"Theorem", "Opaque"}, effective["Kind"]],
		effective = Join[<|"Kind" -> "Axiom"|>, KeyDrop[effective, {"Kind", "Value"}]]
	];
	kind = effective["Kind"];
	If[ KeyExistsQ[effective, "Type"] && effective["Type"] =!= None,
		typeRoot = format3EmitTerm[effective["Type"]]
	];
	If[Lookup[effective, "Annotation", None] =!= None, flags = BitOr[flags, 1]];
	If[KeyExistsQ[effective, "Overloads"], flags = BitOr[flags, 2]];
	If[KeyExistsQ[effective, "Implementation"], flags = BitOr[flags, 4]];
	meta = Association[KeyValueMap[
		Function[{k, v},
			k -> Which[
				k === "Type" && v =!= None, termRef[0],
				k === "Value" && v =!= None, termRef[-1],
				k === "Annotation", v,
				True, format3EncodeMetaValue[v]
			]
		],
		effective
	]];
	<|
		"Kind" -> kind,
		"KindCode" -> $format3KindToCode[kind],
		"TypeRoot" -> typeRoot,
		"ValueRoot" -> If[kind === "Definition" && KeyExistsQ[effective, "Value"], format3EmitTerm[effective["Value"]], 0],
		"Flags" -> flags,
		"Meta" -> meta,
		"DeferredProof" -> If[TrueQ[includeProofs] && MemberQ[{"Theorem", "Opaque"}, kind] && KeyExistsQ[effective, "Value"], effective["Value"], None],
		"Effective" -> effective
	|>
]

writeBlockToStream[stream_, expr_] := Module[{offset = StreamPosition[stream], bytes = BinarySerialize[expr, PerformanceGoal -> "Size"], digest},
	digest = sha256Bytes[bytes];
	writeAllBytes[stream, bytes];
	{{offset, Length[bytes]}, digest}
]

writePartitionedBlocks[stream_, items_List, blockSize_Integer, wrap_] := Module[{chunks, ranges = {}, digests = {}, res},
	If[items === {}, Return[{{}, ByteArray[{}]}, Module]];
	chunks = Partition[items, UpTo[blockSize]];
	Do[
		res = writeBlockToStream[stream, wrap[chunk]];
		AppendTo[ranges, First[res]];
		AppendTo[digests, Last[res]],
		{chunk, chunks}
	];
	{Developer`ToPackedArray[ranges], ByteArray[Catenate[Normal /@ digests]]}
]

buildDepBlock[localIds_List, effectiveRecords_List, nameToId_Association] := Module[
	{stmtOffsets = {1}, stmtTargets = {}, proofOffsets = {1}, proofTargets = {}, sNames, pNames, sIds, pIds},
	Do[
		{sNames, pNames} = recordDependencyNames[rec];
		sIds = Sort[DeleteDuplicates[DeleteCases[Lookup[nameToId, sNames, 0], 0]]];
		pIds = Sort[DeleteDuplicates[DeleteCases[Lookup[nameToId, pNames, 0], 0]]];
		AppendTo[stmtTargets, sIds];
		AppendTo[stmtOffsets, Last[stmtOffsets] + Length[sIds]];
		AppendTo[proofTargets, pIds];
		AppendTo[proofOffsets, Last[proofOffsets] + Length[pIds]],
		{rec, effectiveRecords}
	];
	<|
		"StmtOffsets" -> Developer`ToPackedArray[stmtOffsets],
		"StmtTargets" -> Developer`ToPackedArray[Catenate[stmtTargets]],
		"ProofOffsets" -> Developer`ToPackedArray[proofOffsets],
		"ProofTargets" -> Developer`ToPackedArray[Catenate[proofTargets]]
	|>
]

(* Compute exact Format-2-identical record hashes (or Format 1 hashes when cubicalSystem is present) *)
computeFormat3RecordHashes[names_List, encoded_List, stmtRows_List, proofRows_List, leaves_List, labels_List, hasCubical_] := Module[
	{allRows, depths, rowPrints, refRecords},
	If[names === {}, Return[<||>, Module]];
	If[ TrueQ[hasCubical],
		AssociationThread[names, Transpose[bytesFingerprints[Map[Function[e, BinarySerialize[e["Effective"]]], encoded]]]],
		allRows = Join[stmtRows, proofRows];
		If[ allRows === {},
			AssociationThread[names, Transpose[bytesFingerprints[Map[Function[e, BinarySerialize[e["Effective"]]], encoded]]]],
			allRows = Developer`ToPackedArray[allRows];
			depths = Developer`ToPackedArray[rowDepths[allRows]];
			rowPrints = rowFingerprints[allRows, depths, valueFingerprints[leaves], valueFingerprints[labels]];
			refRecords = AssociationThread[names, Map[format3FingerprintRecord[#, leaves] &, encoded]];
			recordHashesOf[refRecords, rowPrints]
		]
	]
]

format3FingerprintRecord[entry_Association, leaves_List] := Module[
	{typePart = entry["TypeRoot"], valPart = entry["ValueRoot"], meta = entry["Meta"]},
	Map[
		Function[v, Replace[v, {
			termRef[0] :> If[typePart > 0, termRef[typePart], leaves[[-typePart]]],
			termRef[-1] :> If[valPart > 0, termRef[valPart], leaves[[-valPart]]]
		}]],
		meta
	]
]

saveFormat3Environment[file_String, environment : TypeTheoryEnvironment[store_Symbol], options : OptionsPattern[saveFormat3Environment]] := catchKernelFailure @ Block[
	{
		$f3NodeIndex = <||>, $f3SharedStmtIndex = <||>, $f3LocalNodeRow = <||>, $f3NodeCount = 0, $f3LeafIndex = <||>, $f3LabelIndex = <||>, $f3LeafCount = 0, $f3LabelCount = 0, $f3CubicalCount = 0,
		$f3NodeSowTag, $f3LeafSowTag, $f3LabelSowTag, $f3CubicalTag, $f3StreamingProofQ = False
	},
	Module[
	{
		includeProofs = TrueQ[OptionValue[saveFormat3Environment, {options}, "IncludeProofs"]],
		includeDeps = TrueQ[OptionValue[saveFormat3Environment, {options}, "IncludeDependencies"]],
		standalone = TrueQ[OptionValue[saveFormat3Environment, {options}, "Standalone"]],
		blockSizes = resolveBlockSizes[OptionValue[saveFormat3Environment, {options}, "BlockSizes"]],
		saveBase, baseCount, allNames, localNames, localRecords,
		stmtPhase, encoded, stmtRows, cubicalPairs, proofPhase, proofRows,
		leaves, labels, hasCubical, dirRows, recordHashes, allRecordHashes, contentHash,
		localRewriteIndex, localOverloadIndex, kindCounts,
		stream, sectionDir = <||>, manifest = <||>,
		hashes62, sortOrder, sortedHashes, sortedIds, sortedNames, bucketChunks, coarseMax, bucketRanges, bucketDigests,
		nameToId, depBlocks, depRanges, depDigests, flags = 0,
		meta, metaBytes, metaOffset, metaDigest,
		sectionDirBytes, sectionDirOffset, sectionDirDigest,
		manifestBytes, manifestOffset, manifestDigest, headerBytes
	},
	saveBase = If[standalone, None, environmentBase[environment]];
	baseCount = Replace[saveBase, {None -> 0, {_, baseEnv_} :> environmentCount[baseEnv]}];
	allNames = environmentNames[environment];
	localNames = Drop[allNames, baseCount];
	localRecords = Map[
		Function[n, If[includeProofs, constantRecord[environment, n], constantStatementRecord[environment, n]]],
		localNames
	];
	(* Phase 1: Statement/Definition/Recursor/RewriteRule nodes (1 .. stmtNodeCount) *)
	$f3NodeSowTag = "StmtNodes";
	{encoded, {stmtRows, cubicalPairs}} = Reap[
		Map[Function[rec, format3EncodeRecordStmt[rec, includeProofs]], localRecords],
		{"StmtNodes", $f3CubicalTag}
	];
	stmtRows = Replace[stmtRows, {{r_List} :> r, {} -> {}}];
	cubicalPairs = Replace[cubicalPairs, {{p_List} :> p, {} -> {}}];
	(* Phase 2: Trailing Theorem/Opaque Proof nodes (stmtNodeCount + 1 .. total) *)
	$f3NodeSowTag = "ProofNodes";
	{encoded, proofRows} = Reap[
		Map[
			Function[entry,
				If[ entry["DeferredProof"] =!= None,
					Append[entry, "ValueRoot" -> format3EmitTerm[entry["DeferredProof"]]],
					entry
				]
			],
			encoded
		],
		"ProofNodes"
	];
	proofRows = Replace[proofRows, {{r_List} :> r, {} -> {}}];
	leaves = Keys[$f3LeafIndex];
	labels = Keys[$f3LabelIndex];
	hasCubical = cubicalPairs =!= {};
	dirRows = Map[Function[e, {e["KindCode"], e["TypeRoot"], e["ValueRoot"], e["Flags"]}], encoded];
	recordHashes = computeFormat3RecordHashes[localNames, encoded, stmtRows, proofRows, leaves, labels, hasCubical];
	allRecordHashes = Replace[saveBase, {
		None :> recordHashes,
		{_, baseEnv_} :> Join[environmentRecordHashes[baseEnv], recordHashes]
	}];
	contentHash = If[ includeProofs,
		contentHashFromRecords[environment, allRecordHashes],
		Hash[
			BinarySerialize[<|
				"Rules" -> environmentRules[environment],
				"NaturalNumbers" -> store["NaturalNumbers"],
				"RewriteRuleIndex" -> store["RewriteRuleIndex"],
				"Records" -> allRecordHashes
			|>],
			"SHA256",
			"HexString"
		]
	];
	If[saveBase === None && includeProofs, rememberContentHash[environment, allRecordHashes]];
	localRewriteIndex = Merge[
		MapThread[Function[{n, e}, If[e["Kind"] === "RewriteRule", <|e["Effective"]["Head"] -> {n}|>, Nothing]], {localNames, encoded}],
		Apply[Join]
	];
	localOverloadIndex = Merge[
		MapThread[Function[{n, e}, If[KeyExistsQ[e["Effective"], "Overloads"], <|e["Effective"]["Overloads"] -> {n}|>, Nothing]], {localNames, encoded}],
		Apply[Join]
	];
	kindCounts = Counts[Lookup[encoded, "Kind"]];
	If[proofRows =!= {}, flags = BitOr[flags, $format3FlagProofs]];
	If[includeDeps && localNames =!= {}, flags = BitOr[flags, $format3FlagDeps]];
	If[localNames =!= {}, flags = BitOr[flags, $format3FlagRecordHashes]];
	If[! includeProofs, flags = BitOr[flags, $format3FlagStatementOnly]];
	If[hasCubical, flags = BitOr[flags, $format3FlagCubical]];
	WithCleanup[
		stream = OpenWrite[file, BinaryFormat -> True],
		(* Leading 8-byte magic header *)
		writeAllBytes[stream, ByteArray[$format3Magic]];
		(* 1. LeafBlocks *)
		{sectionDir["LeafBlocks"], manifest["LeafBlocks"]} = writePartitionedBlocks[stream, leaves, blockSizes["Leaf"], Identity];
		(* 2. LabelBlocks *)
		{sectionDir["LabelBlocks"], manifest["LabelBlocks"]} = writePartitionedBlocks[stream, labels, blockSizes["Label"], Identity];
		(* 3. Optional CubicalBlocks *)
		If[ hasCubical,
			{sectionDir["CubicalBlocks"], manifest["CubicalBlocks"]} = writePartitionedBlocks[stream, cubicalPairs, blockSizes["Cubical"], Developer`ToPackedArray]
		];
		(* 4. Statement NodeBlocks *)
		{sectionDir["NodeBlocks"], manifest["NodeBlocks"]} = writePartitionedBlocks[stream, stmtRows, blockSizes["StmtNode"], Developer`ToPackedArray];
		(* 5. RecordMetaBlocks *)
		{sectionDir["RecordMetaBlocks"], manifest["RecordMetaBlocks"]} = writePartitionedBlocks[
			stream,
			Transpose[{localNames, Lookup[encoded, "Meta"]}],
			blockSizes["RecordMeta"],
			Function[chunk, <|"Names" -> chunk[[All, 1]], "Meta" -> chunk[[All, 2]]|>]
		];
		(* 6. RecordDirBlocks *)
		{sectionDir["RecordDirBlocks"], manifest["RecordDirBlocks"]} = writePartitionedBlocks[stream, dirRows, blockSizes["RecordDir"], Developer`ToPackedArray];
		(* 7. Two-level NameIndex *)
		If[ localNames =!= {},
			hashes62 = nameHashes62[localNames];
			sortOrder = Ordering[Transpose[{hashes62, Range[Length[localNames]]}]];
			sortedHashes = hashes62[[sortOrder]];
			sortedIds = sortOrder;
			sortedNames = localNames[[sortOrder]];
			bucketChunks = Partition[Range[Length[localNames]], UpTo[blockSizes["NameBucket"]]];
			coarseMax = Developer`ToPackedArray[Map[Function[idxs, sortedHashes[[Last[idxs]]]], bucketChunks]];
			{sectionDir["NameIndexCoarse"], manifest["NameIndexCoarse"]} = writeBlockToStream[stream, coarseMax];
			bucketRanges = {};
			bucketDigests = {};
			Do[
				With[{res = writeBlockToStream[stream, <|
						"Hashes" -> Developer`ToPackedArray[sortedHashes[[idxs]]],
						"RecordIDs" -> Developer`ToPackedArray[sortedIds[[idxs]]],
						"Names" -> sortedNames[[idxs]]
					|>]},
					AppendTo[bucketRanges, First[res]];
					AppendTo[bucketDigests, Last[res]]
				],
				{idxs, bucketChunks}
			];
			sectionDir["NameIndexBuckets"] = Developer`ToPackedArray[bucketRanges];
			manifest["NameIndexBuckets"] = ByteArray[Catenate[Normal /@ bucketDigests]]
		];
		(* 8. RecordHashBlocks *)
		{sectionDir["RecordHashBlocks"], manifest["RecordHashBlocks"]} = writePartitionedBlocks[
			stream,
			Values[recordHashes],
			blockSizes["RecordDir"],
			Developer`ToPackedArray
		];
		(* 9. Optional CSR DepBlocks *)
		If[ includeDeps && localNames =!= {},
			With[{baseNames = Take[allNames, baseCount]},
				nameToId = Join[AssociationThread[baseNames, -Range[Length[baseNames]]], AssociationThread[localNames, Range[Length[localNames]]]]
			];
			depRanges = {};
			depDigests = {};
			Do[
				With[{res = writeBlockToStream[stream, buildDepBlock[idxs, Lookup[encoded[[idxs]], "Effective"], nameToId]]},
					AppendTo[depRanges, First[res]];
					AppendTo[depDigests, Last[res]]
				],
				{idxs, Partition[Range[Length[localNames]], UpTo[blockSizes["RecordMeta"]]]}
			];
			sectionDir["DepBlocks"] = Developer`ToPackedArray[depRanges];
			manifest["DepBlocks"] = ByteArray[Catenate[Normal /@ depDigests]]
		];
		(* 10. TRAILING ProofNodeBlocks *)
		If[ proofRows =!= {},
			{sectionDir["ProofNodeBlocks"], manifest["ProofNodeBlocks"]} = writePartitionedBlocks[stream, proofRows, blockSizes["ProofNode"], Developer`ToPackedArray]
		];
		(* 11. Meta *)
		meta = <|
			"Format" -> "TypeTheoryEnvironment",
			"FormatVersion" -> 3,
			"TypeTheoryVersion" -> PacletObject[File[$pacletDirectory]]["Version"],
			"KernelHash" -> $kernelHash,
			"Host" -> <|"VersionNumber" -> $VersionNumber, "ReleaseNumber" -> $ReleaseNumber, "Version" -> $Version|>,
			"Rules" -> environmentRules[environment],
			"Base" -> Replace[saveBase, {None -> None, {name_, baseEnv_} :> <|"Name" -> name, "Hash" -> environmentContentHash[baseEnv]|>}],
			"NaturalNumbers" -> store["NaturalNumbers"],
			"RewriteRuleIndex" -> localRewriteIndex,
			"OverloadIndex" -> localOverloadIndex,
			"KindCounts" -> kindCounts,
			"BlockSizes" -> KeyTake[blockSizes, {"RecordDir", "NameBucket", "Cubical"}],
			"Hash" -> contentHash
		|>;
		metaOffset = StreamPosition[stream];
		metaBytes = BinarySerialize[meta, PerformanceGoal -> "Size"];
		metaDigest = sha256Bytes[metaBytes];
		writeAllBytes[stream, metaBytes];
		(* 12. SectionDirectory *)
		sectionDirOffset = StreamPosition[stream];
		sectionDirBytes = BinarySerialize[sectionDir, PerformanceGoal -> "Size"];
		sectionDirDigest = sha256Bytes[sectionDirBytes];
		manifest["SectionDirectory"] = sectionDirDigest;
		writeAllBytes[stream, sectionDirBytes];
		(* 13. Manifest *)
		manifestOffset = StreamPosition[stream];
		manifestBytes = BinarySerialize[manifest, PerformanceGoal -> "Size"];
		manifestDigest = sha256Bytes[manifestBytes];
		writeAllBytes[stream, manifestBytes];
		(* 14. Finalize 256-byte Footer/Header at EOF *)
		headerBytes = encodeFormat3Header[<|
			"Flags" -> flags,
			"ConstantCount" -> Length[localNames],
			"StmtNodeCount" -> Length[stmtRows],
			"ProofNodeCount" -> Length[proofRows],
			"LeafCount" -> Length[leaves],
			"LabelCount" -> Length[labels],
			"StmtNodeBlockSize" -> blockSizes["StmtNode"],
			"ProofNodeBlockSize" -> blockSizes["ProofNode"],
			"LeafBlockSize" -> blockSizes["Leaf"],
			"LabelBlockSize" -> blockSizes["Label"],
			"RecordMetaBlockSize" -> blockSizes["RecordMeta"],
			"SectionDirOffset" -> sectionDirOffset,
			"SectionDirLength" -> Length[sectionDirBytes],
			"MetaOffset" -> metaOffset,
			"MetaLength" -> Length[metaBytes],
			"ManifestOffset" -> manifestOffset,
			"ManifestLength" -> Length[manifestBytes],
			"MetaSha256" -> metaDigest,
			"ManifestSha256" -> manifestDigest
		|>];
		writeAllBytes[stream, headerBytes],
		If[MatchQ[stream, _OutputStream], Quiet[Close[stream]]]
	];
	File[file]
	]
]


(* ::Subsection:: *)
(*Zero-decode statement-only cut from an existing Format 3 file*)


cutFormat3StatementFile[sourceFile_String, targetFile_String] := catchKernelFailure @ Module[
	{
		loaded = loadFormat3Environment[ExpandFileName[sourceFile], False],
		source, header, meta, sectionDir, manifest,
		outStream, newSectionDir = <||>, newManifest = <||>,
		copySection, dirBlockCount, newDirRanges = {}, newDirDigests = {}, b, mat, updated,
		newKindCounts, cutHashes, allCutHashes, newHash, newFlags, newMeta,
		metaOffset, metaBytes, metaDigest, dirOffset, dirBytes, manOffset, manBytes, manDigest, headerBytes
	},
	source = First[loaded]["LazySource"];
	header = source["Header"];
	meta = source["Meta"];
	sectionDir = source["SectionDirectory"];
	manifest = source["Manifest"];
	WithCleanup[
		outStream = OpenWrite[targetFile, BinaryFormat -> True],
		writeAllBytes[outStream, ByteArray[$format3Magic]];
		(* Copy verbatim all non-proof, non-RecordDir sections without decoding any term DAGs *)
		copySection = Function[secName,
			If[ KeyExistsQ[sectionDir, secName],
				With[{entries = sectionDir[secName]},
					If[ ListQ[entries] && Length[entries] == 2 && AllTrue[entries, IntegerQ],
						With[{bytes = readSourceRange[source, First[entries], Last[entries]], digest = manifestDigestOf[source, secName, 1], off = StreamPosition[outStream]},
							If[sha256Bytes[bytes] =!= digest, kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {sourceFile}]];
							writeAllBytes[outStream, bytes];
							newSectionDir[secName] = {off, Length[bytes]};
							newManifest[secName] = digest
						],
						Module[{ranges = {}, digests = {}},
							Do[
								With[{bytes = readSourceRange[source, entries[[i, 1]], entries[[i, 2]]], digest = manifestDigestOf[source, secName, i], off = StreamPosition[outStream]},
									If[sha256Bytes[bytes] =!= digest, kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {sourceFile}]];
									writeAllBytes[outStream, bytes];
									AppendTo[ranges, {off, Length[bytes]}];
									AppendTo[digests, digest]
								],
								{i, Length[entries]}
							];
							newSectionDir[secName] = Developer`ToPackedArray[ranges];
							newManifest[secName] = ByteArray[Catenate[Normal /@ digests]]
						]
					]
				]
			]
		];
		Scan[copySection, {"LeafBlocks", "LabelBlocks", "CubicalBlocks", "NodeBlocks", "RecordMetaBlocks", "NameIndexCoarse", "NameIndexBuckets"}];
		(* Rewrite RecordDirBlocks: convert Theorem (4) and Opaque (3) to Axiom (1) with ValueRoot = 0 *)
		dirBlockCount = Length[Lookup[sectionDir, "RecordDirBlocks", {}]];
		Do[
			mat = Normal[readRecordDirBlock[source, b]];
			updated = Map[
				Function[row, If[row[[1]] == 3 || row[[1]] == 4, {1, row[[2]], 0, row[[4]]}, row]],
				mat
			];
			With[{res = writeBlockToStream[outStream, Developer`ToPackedArray[updated]]},
				AppendTo[newDirRanges, First[res]];
				AppendTo[newDirDigests, Last[res]]
			],
			{b, dirBlockCount}
		];
		If[ newDirRanges =!= {},
			newSectionDir["RecordDirBlocks"] = Developer`ToPackedArray[newDirRanges];
			newManifest["RecordDirBlocks"] = ByteArray[Catenate[Normal /@ newDirDigests]]
		];
		(* Preserve statement-only CSR DepBlocks (empty ProofTargets) so CompiledKernel cone extraction stays O(cone) *)
		If[ BitAnd[header["Flags"], $format3FlagDeps] =!= 0 && KeyExistsQ[sectionDir, "DepBlocks"],
			Module[{depBlockCount = Length[sectionDir["DepBlocks"]], depRanges = {}, depDigests = {}, db, res},
				Do[
					db = readDepBlock[source, b];
					res = writeBlockToStream[outStream, <|
						"StmtOffsets" -> db["StmtOffsets"],
						"StmtTargets" -> db["StmtTargets"],
						"ProofOffsets" -> Developer`ToPackedArray[ConstantArray[1, Length[db["StmtOffsets"]]]],
						"ProofTargets" -> Developer`ToPackedArray[{}]
					|>];
					AppendTo[depRanges, First[res]];
					AppendTo[depDigests, Last[res]],
					{b, depBlockCount}
				];
				If[ depRanges =!= {},
					newSectionDir["DepBlocks"] = Developer`ToPackedArray[depRanges];
					newManifest["DepBlocks"] = ByteArray[Catenate[Normal /@ depDigests]]
				]
			]
		];
		(* Update KindCounts: fold Theorem + Opaque counts into Axiom *)
		newKindCounts = meta["KindCounts"];
		With[{stripped = Lookup[newKindCounts, "Theorem", 0] + Lookup[newKindCounts, "Opaque", 0]},
			newKindCounts = KeyDrop[newKindCounts, {"Theorem", "Opaque"}];
			If[stripped > 0, newKindCounts["Axiom"] = Lookup[newKindCounts, "Axiom", 0] + stripped]
		];
		(* Recompute record hashes for stripped theorem/opaque statements only (zero proof decoding!) *)
		cutHashes = Module[{localNames = lazyLocalNames[source], baseHashes = environmentRecordHashes[source["Base"]], existing, strippedNames},
			existing = If[ BitAnd[header["Flags"], $format3FlagRecordHashes] =!= 0,
				KeyDrop[lazyRecordHashes[source], Keys[baseHashes]],
				recordFingerprints[AssociationMap[Function[n, lazyConstantRecord[source, n, False]], localNames]]
			];
			strippedNames = Join[lazyNamesOfKind[source, "Theorem"], lazyNamesOfKind[source, "Opaque"]];
			strippedNames = Intersection[strippedNames, localNames];
			If[ strippedNames =!= {},
				existing = Join[
					existing,
					recordFingerprints[AssociationMap[
						Function[n, Join[<|"Kind" -> "Axiom"|>, KeyDrop[lazyConstantRecord[source, n, False], {"Kind", "Value"}]]],
						strippedNames
					]]
				]
			];
			existing
		];
		If[ Length[cutHashes] > 0,
			{newSectionDir["RecordHashBlocks"], newManifest["RecordHashBlocks"]} = writePartitionedBlocks[
				outStream,
				Values[cutHashes],
				meta["BlockSizes"]["RecordDir"],
				Developer`ToPackedArray
			]
		];
		allCutHashes = Join[environmentRecordHashes[source["Base"]], cutHashes];
		newHash = Hash[
			BinarySerialize[<|
				"Rules" -> meta["Rules"],
				"NaturalNumbers" -> meta["NaturalNumbers"],
				"RewriteRuleIndex" -> First[loaded]["RewriteRuleIndex"],
				"Records" -> allCutHashes
			|>],
			"SHA256",
			"HexString"
		];
		newFlags = BitOr[
			BitAnd[header["Flags"], BitNot[$format3FlagProofs]],
			BitOr[$format3FlagStatementOnly, If[Length[cutHashes] > 0, $format3FlagRecordHashes, 0]]
		];
		newMeta = Join[meta, <|"KindCounts" -> newKindCounts, "Hash" -> newHash|>];
		metaOffset = StreamPosition[outStream];
		metaBytes = BinarySerialize[newMeta, PerformanceGoal -> "Size"];
		metaDigest = sha256Bytes[metaBytes];
		writeAllBytes[outStream, metaBytes];
		dirOffset = StreamPosition[outStream];
		dirBytes = BinarySerialize[newSectionDir, PerformanceGoal -> "Size"];
		newManifest["SectionDirectory"] = sha256Bytes[dirBytes];
		writeAllBytes[outStream, dirBytes];
		manOffset = StreamPosition[outStream];
		manBytes = BinarySerialize[newManifest, PerformanceGoal -> "Size"];
		manDigest = sha256Bytes[manBytes];
		writeAllBytes[outStream, manBytes];
		headerBytes = encodeFormat3Header[<|
			"Flags" -> newFlags,
			"ConstantCount" -> header["ConstantCount"],
			"StmtNodeCount" -> header["StmtNodeCount"],
			"ProofNodeCount" -> 0,
			"LeafCount" -> header["LeafCount"],
			"LabelCount" -> header["LabelCount"],
			"StmtNodeBlockSize" -> header["StmtNodeBlockSize"],
			"ProofNodeBlockSize" -> header["ProofNodeBlockSize"],
			"LeafBlockSize" -> header["LeafBlockSize"],
			"LabelBlockSize" -> header["LabelBlockSize"],
			"RecordMetaBlockSize" -> header["RecordMetaBlockSize"],
			"SectionDirOffset" -> dirOffset,
			"SectionDirLength" -> Length[dirBytes],
			"MetaOffset" -> metaOffset,
			"MetaLength" -> Length[metaBytes],
			"ManifestOffset" -> manOffset,
			"ManifestLength" -> Length[manBytes],
			"MetaSha256" -> metaDigest,
			"ManifestSha256" -> manDigest
		|>];
		writeAllBytes[outStream, headerBytes],
		If[MatchQ[outStream, _OutputStream], Quiet[Close[outStream]]]
	];
	File[targetFile]
]


(* ::Subsection:: *)
(*Streaming / incremental Format 3 writer (O(batch) peak RAM)*)


Options[openFormat3Writer] = {
	"Rules" -> Automatic,
	"Base" -> None,
	"NaturalNumbers" -> None,
	"IncludeProofs" -> True,
	"IncludeDependencies" -> True,
	"BlockSizes" -> Automatic,
	"MaxDedupeNodes" -> 500000
}

openFormat3Writer[file_String, options : OptionsPattern[openFormat3Writer]] := catchKernelFailure @ Module[{writer},
	Module[{
			rules = Replace[OptionValue[openFormat3Writer, {options}, "Rules"], Automatic :> $defaultRules],
			base = OptionValue[openFormat3Writer, {options}, "Base"],
			natural = OptionValue[openFormat3Writer, {options}, "NaturalNumbers"],
			includeProofs = TrueQ[OptionValue[openFormat3Writer, {options}, "IncludeProofs"]],
			includeDeps = TrueQ[OptionValue[openFormat3Writer, {options}, "IncludeDependencies"]],
			blockSizes = resolveBlockSizes[OptionValue[openFormat3Writer, {options}, "BlockSizes"]],
			maxDedupe = Replace[OptionValue[openFormat3Writer, {options}, "MaxDedupeNodes"], Except[_Integer?Positive] -> 500000],
			mainStream = OpenWrite[file, BinaryFormat -> True],
			proofTmp = file <> ".proofs.tmp",
			proofStream
		},
		proofStream = If[includeProofs, OpenWrite[proofTmp, BinaryFormat -> True], None];
		writeAllBytes[mainStream, ByteArray[$format3Magic]];
		writer["File"] = file;
		writer["ProofTmp"] = proofTmp;
		writer["MainStream"] = mainStream;
		writer["ProofStream"] = proofStream;
		writer["Rules"] = rules;
		writer["Base"] = base;
		writer["NaturalNumbers"] = natural;
		writer["IncludeProofs"] = includeProofs;
		writer["IncludeDependencies"] = includeDeps;
		writer["BlockSizes"] = blockSizes;
		writer["MaxDedupeNodes"] = maxDedupe;
		writer["Closed"] = False;
		writer["Names"] = {};
		writer["NameToId"] = Replace[base, {
			None -> <||>,
			name_String :> With[{bNames = environmentNames[TypeTheoryEnvironment[name]]}, AssociationThread[bNames, -Range[Length[bNames]]]],
			env_?environmentQ :> With[{bNames = environmentNames[env]}, AssociationThread[bNames, -Range[Length[bNames]]]]
		}];
		writer["KindCounts"] = <||>;
		writer["RewriteRuleIndex"] = <||>;
		writer["OverloadIndex"] = <||>;
		writer["StmtNodeIndex"] = <||>;
		writer["StmtNodeCount"] = 0;
		writer["ProofNodeCount"] = 0;
		writer["LeafIndex"] = <||>;
		writer["LabelIndex"] = <||>;
		writer["LeafCount"] = 0;
		writer["LabelCount"] = 0;
		writer["CubicalCount"] = 0;
		writer["LeafBuffer"] = {};
		writer["LabelBuffer"] = {};
		writer["StmtNodeBuffer"] = {};
		writer["ProofNodeBuffer"] = {};
		writer["CubicalBuffer"] = {};
		writer["MetaNameBuffer"] = {};
		writer["MetaRecBuffer"] = {};
		writer["DirBuffer"] = {};
		writer["RecordHashList"] = {};
		writer["DepStmtBuf"] = {};
		writer["DepProofBuf"] = {};
		writer["SectionDir"] = <|
			"LeafBlocks" -> {}, "LabelBlocks" -> {}, "CubicalBlocks" -> {},
			"NodeBlocks" -> {}, "RecordMetaBlocks" -> {}, "RecordDirBlocks" -> {},
			"RecordHashBlocks" -> {}, "DepBlocks" -> {}, "ProofNodeBlocks" -> {}
		|>;
		writer["Manifest"] = <|
			"LeafBlocks" -> {}, "LabelBlocks" -> {}, "CubicalBlocks" -> {},
			"NodeBlocks" -> {}, "RecordMetaBlocks" -> {}, "RecordDirBlocks" -> {},
			"RecordHashBlocks" -> {}, "DepBlocks" -> {}, "ProofNodeBlocks" -> {}
		|>;
		writer["ProofBlockInfo"] = {};
		writer
	]
]

flushWriterBuffer[writer_Symbol, stream_, secName_String, bufKey_String, blockSize_Integer, wrap_, force_] := Module[{buf = writer[bufKey], chunk, res},
	While[ Length[buf] >= blockSize || (TrueQ[force] && Length[buf] > 0),
		chunk = Take[buf, UpTo[blockSize]];
		buf = Drop[buf, Length[chunk]];
		res = writeBlockToStream[stream, wrap[chunk]];
		writer["SectionDir"] = Append[writer["SectionDir"], secName -> Append[writer["SectionDir"][secName], First[res]]];
		writer["Manifest"] = Append[writer["Manifest"], secName -> Append[writer["Manifest"][secName], Last[res]]]
	];
	writer[bufKey] = buf;
]

flushWriterMetaAndDeps[writer_Symbol, force_] := Module[
	{bs = writer["BlockSizes"]["RecordMeta"], names = writer["MetaNameBuffer"], recs = writer["MetaRecBuffer"], k, res},
	While[ Length[names] >= bs || (TrueQ[force] && Length[names] > 0),
		k = Min[bs, Length[names]];
		res = writeBlockToStream[writer["MainStream"], <|"Names" -> Take[names, k], "Meta" -> Take[recs, k]|>];
		writer["SectionDir"] = Append[writer["SectionDir"], "RecordMetaBlocks" -> Append[writer["SectionDir"]["RecordMetaBlocks"], First[res]]];
		writer["Manifest"] = Append[writer["Manifest"], "RecordMetaBlocks" -> Append[writer["Manifest"]["RecordMetaBlocks"], Last[res]]];
		names = Drop[names, k];
		recs = Drop[recs, k]
	];
	writer["MetaNameBuffer"] = names;
	writer["MetaRecBuffer"] = recs;
	flushWriterDeps[writer, force]
]

resolvePendingDep[entry_List, nameToId_Association] := If[ Last[entry] === {},
	entry,
	With[{resolved = DeleteCases[Lookup[nameToId, Last[entry], 0], 0], still = Select[Last[entry], Function[n, ! KeyExistsQ[nameToId, n]]]},
		{Sort[DeleteDuplicates[Join[First[entry], resolved]]], still}
	]
]

flushWriterDeps[writer_Symbol, force_] := Module[
	{bs = writer["BlockSizes"]["RecordMeta"], sDeps = writer["DepStmtBuf"], pDeps = writer["DepProofBuf"], nameToId = writer["NameToId"], k, sc, pc, sOff, pOff, res},
	If[! TrueQ[writer["IncludeDependencies"]], Return[Null, Module]];
	While[ Length[sDeps] >= bs || (TrueQ[force] && Length[sDeps] > 0),
		k = Min[bs, Length[sDeps]];
		sc = Map[Function[e, resolvePendingDep[e, nameToId]], Take[sDeps, k]];
		pc = Map[Function[e, resolvePendingDep[e, nameToId]], Take[pDeps, k]];
		(* Hold block back if an InductiveType was split across a batch boundary until its constructors arrive *)
		If[ ! TrueQ[force] && (AnyTrue[sc, Last[#] =!= {} &] || AnyTrue[pc, Last[#] =!= {} &]),
			sDeps = Join[sc, Drop[sDeps, k]];
			pDeps = Join[pc, Drop[pDeps, k]];
			Break[]
		];
		sc = Map[First, sc];
		pc = Map[First, pc];
		sOff = Prepend[Accumulate[Length /@ sc] + 1, 1];
		pOff = Prepend[Accumulate[Length /@ pc] + 1, 1];
		res = writeBlockToStream[writer["MainStream"], <|
			"StmtOffsets" -> Developer`ToPackedArray[sOff],
			"StmtTargets" -> Developer`ToPackedArray[Catenate[sc]],
			"ProofOffsets" -> Developer`ToPackedArray[pOff],
			"ProofTargets" -> Developer`ToPackedArray[Catenate[pc]]
		|>];
		writer["SectionDir"] = Append[writer["SectionDir"], "DepBlocks" -> Append[writer["SectionDir"]["DepBlocks"], First[res]]];
		writer["Manifest"] = Append[writer["Manifest"], "DepBlocks" -> Append[writer["Manifest"]["DepBlocks"], Last[res]]];
		sDeps = Drop[sDeps, k];
		pDeps = Drop[pDeps, k]
	];
	writer["DepStmtBuf"] = sDeps;
	writer["DepProofBuf"] = pDeps;
]

flushWriterProofNodes[writer_Symbol, force_] := Module[{bs = writer["BlockSizes"]["ProofNode"], buf = writer["ProofNodeBuffer"], chunk, bytes, digest, off},
	If[writer["ProofStream"] === None, Return[Null, Module]];
	While[ Length[buf] >= bs || (TrueQ[force] && Length[buf] > 0),
		chunk = Take[buf, UpTo[bs]];
		buf = Drop[buf, Length[chunk]];
		off = StreamPosition[writer["ProofStream"]];
		bytes = BinarySerialize[Developer`ToPackedArray[chunk], PerformanceGoal -> "Size"];
		digest = sha256Bytes[bytes];
		writeAllBytes[writer["ProofStream"], bytes];
		writer["ProofBlockInfo"] = Append[writer["ProofBlockInfo"], {off, Length[bytes], digest}]
	];
	writer["ProofNodeBuffer"] = buf;
]

(* In streaming mode, proof rows use negative-offset temporary numbering internally? No: proof rows cannot
   reference later statement rows! To guarantee 1 <= stmtRow <= stmtNodeCount < proofRow in streaming mode,
   proof rows in each batch are stored in ProofStream with local proof IDs (1..proofNodeCount), and when
   referenced from RecordDir we tag proof valueRoots with offset -2^60? Even simpler: store proof nodes
   with 1-based local proof IDs and offset them by +stmtNodeCount only at close when rewriting RecordDir?
   Wait: proof rows can reference BOTH stmt rows (1..stmtNodeCount) AND earlier proof rows! To avoid any
   renumbering of proof rows at close, encode proof-to-proof refs during streaming? Even simpler:
   each batch can record {stmtRows, proofRows} cleanly if ProofNodeBlocks uses a separate sentinel or
   if ProofNodeBlocks in streaming mode shifts ONLY proof-self references at close!
   Let's keep streaming 100% exact and simple: use offset 2^40 + proofId for proof rows during streaming,
   and rewrite those > 2^40 entries in ProofStream blocks + DirBuffer to stmtNodeCount + (id - 2^40) on close! *)
$streamProofTag = 2^40

writeFormat3Batch[writer_Symbol, records_Association] := catchKernelFailure @ Block[
	{
		$f3NodeIndex = writer["StmtNodeIndex"], $f3SharedStmtIndex = <||>, $f3LocalNodeRow = <||>, $f3NodeCount = writer["StmtNodeCount"],
		$f3LeafIndex = writer["LeafIndex"], $f3LabelIndex = writer["LabelIndex"],
		$f3LeafCount = writer["LeafCount"], $f3LabelCount = writer["LabelCount"], $f3CubicalCount = writer["CubicalCount"],
		$f3NodeSowTag = "StmtNodes", $f3LeafSowTag = "NewLeaves", $f3LabelSowTag = "NewLabels", $f3CubicalTag = "NewCubical",
		$f3StreamingProofQ = False
	},
	Module[
	{
		includeProofs = writer["IncludeProofs"], bs = writer["BlockSizes"], maxDedupe = writer["MaxDedupeNodes"],
		names = Keys[records], recs = Values[records], encoded, stmtRows, cubicalPairs, proofRows,
		sLeaves1, sLabels1, sLeaves2, sLabels2, newLeaves, newLabels,
		proofCount = writer["ProofNodeCount"], sNames, pNames, sIds, pIds,
		nameToId = writer["NameToId"], startId = Length[writer["Names"]], batchHashes
	},
	If[TrueQ[writer["Closed"]], kernelFailure["WriterClosed", "The Format 3 writer is already closed.", {}]];
	If[Length[records] == 0, Return[writer, Module]];
	Do[nameToId[names[[i]]] = startId + i, {i, Length[names]}];
	writer["NameToId"] = nameToId;
	writer["Names"] = Join[writer["Names"], names];
	(* Phase 1: Statement nodes (uses ONLY StmtNodeIndex so statement rows never point to proof rows) *)
	{encoded, {stmtRows, cubicalPairs, sLeaves1, sLabels1}} = Reap[
		Map[Function[rec, format3EncodeRecordStmt[rec, includeProofs]], recs],
		{"StmtNodes", "NewCubical", "NewLeaves", "NewLabels"}
	];
	stmtRows = Replace[stmtRows, {{r_List} :> r, {} -> {}}];
	cubicalPairs = Replace[cubicalPairs, {{p_List} :> p, {} -> {}}];
	sLeaves1 = Replace[sLeaves1, {{l_List} :> l, {} -> {}}];
	sLabels1 = Replace[sLabels1, {{l_List} :> l, {} -> {}}];
	writer["StmtNodeCount"] = $f3NodeCount;
	(* Phase 2: Proof nodes share StmtNodeIndex read-only ($f3SharedStmtIndex) + batch-local proof dedup ($f3NodeIndex = <||>) *)
	$f3SharedStmtIndex = $f3NodeIndex;
	$f3NodeIndex = <||>;
	$f3NodeSowTag = "ProofNodes";
	$f3StreamingProofQ = True;
	$f3NodeCount = $streamProofTag + proofCount;
	{encoded, {proofRows, sLeaves2, sLabels2}} = Reap[
		Map[
			Function[entry,
				If[ entry["DeferredProof"] =!= None,
					Append[entry, "ValueRoot" -> format3EmitTerm[entry["DeferredProof"]]],
					entry
				]
			],
			encoded
		],
		{"ProofNodes", "NewLeaves", "NewLabels"}
	];
	proofRows = Replace[proofRows, {{r_List} :> r, {} -> {}}];
	sLeaves2 = Replace[sLeaves2, {{l_List} :> l, {} -> {}}];
	sLabels2 = Replace[sLabels2, {{l_List} :> l, {} -> {}}];
	writer["ProofNodeCount"] = $f3NodeCount - $streamProofTag;
	(* Bound dedup caches to MaxDedupeNodes so streaming stays O(batch) RAM & linear time *)
	writer["StmtNodeIndex"] = If[Length[$f3SharedStmtIndex] > maxDedupe, <||>, $f3SharedStmtIndex];
	writer["LeafIndex"] = If[Length[$f3LeafIndex] > maxDedupe, <||>, $f3LeafIndex];
	writer["LabelIndex"] = If[Length[$f3LabelIndex] > maxDedupe, <||>, $f3LabelIndex];
	writer["LeafCount"] = $f3LeafCount;
	writer["LabelCount"] = $f3LabelCount;
	writer["CubicalCount"] = $f3CubicalCount;
	(* Compute batch record hashes independently from Effective records (format-2 structural fingerprints!) *)
	batchHashes = recordFingerprints[AssociationThread[names, Lookup[encoded, "Effective"]]];
	writer["RecordHashList"] = Join[writer["RecordHashList"], Values[batchHashes]];
	(* Update KindCounts, RewriteRuleIndex, OverloadIndex *)
	writer["KindCounts"] = Merge[{writer["KindCounts"], Counts[Lookup[encoded, "Kind"]]}, Total];
	Do[
		With[{n = names[[i]], e = encoded[[i]]},
			If[e["Kind"] === "RewriteRule", writer["RewriteRuleIndex"] = Merge[{writer["RewriteRuleIndex"], <|e["Effective"]["Head"] -> {n}|>}, Apply[Join]]];
			If[KeyExistsQ[e["Effective"], "Overloads"], writer["OverloadIndex"] = Merge[{writer["OverloadIndex"], <|e["Effective"]["Overloads"] -> {n}|>}, Apply[Join]]];
			If[ TrueQ[writer["IncludeDependencies"]],
				{sNames, pNames} = recordDependencyNames[e["Effective"]];
				sIds = Sort[DeleteDuplicates[DeleteCases[Lookup[nameToId, sNames, 0], 0]]];
				pIds = Sort[DeleteDuplicates[DeleteCases[Lookup[nameToId, pNames, 0], 0]]];
				writer["DepStmtBuf"] = Append[writer["DepStmtBuf"], {sIds, Select[sNames, Function[depN, ! KeyExistsQ[nameToId, depN]]]}];
				writer["DepProofBuf"] = Append[writer["DepProofBuf"], {pIds, Select[pNames, Function[depN, ! KeyExistsQ[nameToId, depN]]]}]
			]
		],
		{i, Length[names]}
	];
	(* Incrementally flush newly interned leaves, labels, cubical pairs, nodes, metadata, and deps *)
	newLeaves = Join[sLeaves1, sLeaves2];
	If[newLeaves =!= {}, writer["LeafBuffer"] = Join[writer["LeafBuffer"], newLeaves]; flushWriterBuffer[writer, writer["MainStream"], "LeafBlocks", "LeafBuffer", bs["Leaf"], Identity, False]];
	newLabels = Join[sLabels1, sLabels2];
	If[newLabels =!= {}, writer["LabelBuffer"] = Join[writer["LabelBuffer"], newLabels]; flushWriterBuffer[writer, writer["MainStream"], "LabelBlocks", "LabelBuffer", bs["Label"], Identity, False]];
	If[cubicalPairs =!= {}, writer["CubicalBuffer"] = Join[writer["CubicalBuffer"], cubicalPairs]; flushWriterBuffer[writer, writer["MainStream"], "CubicalBlocks", "CubicalBuffer", bs["Cubical"], Developer`ToPackedArray, False]];
	If[stmtRows =!= {}, writer["StmtNodeBuffer"] = Join[writer["StmtNodeBuffer"], stmtRows]; flushWriterBuffer[writer, writer["MainStream"], "NodeBlocks", "StmtNodeBuffer", bs["StmtNode"], Developer`ToPackedArray, False]];
	If[proofRows =!= {}, writer["ProofNodeBuffer"] = Join[writer["ProofNodeBuffer"], proofRows]; flushWriterProofNodes[writer, False]];
	writer["MetaNameBuffer"] = Join[writer["MetaNameBuffer"], names];
	writer["MetaRecBuffer"] = Join[writer["MetaRecBuffer"], Lookup[encoded, "Meta"]];
	flushWriterMetaAndDeps[writer, False];
	writer["DirBuffer"] = Join[writer["DirBuffer"], Map[Function[e, {e["KindCode"], e["TypeRoot"], e["ValueRoot"], e["Flags"]}], encoded]];
	writer
	]
]

remapStreamProofRef[val_Integer, stmtCount_Integer] := If[val > $streamProofTag, stmtCount + (val - $streamProofTag), val]

remapStreamProofMatrix[mat_, stmtCount_Integer] := Module[{arr = Normal[mat], row, code},
	Developer`ToPackedArray[Table[
		row = arr[[i]];
		code = row[[1]];
		Switch[code,
			1, {1, remapStreamProofRef[row[[2]], stmtCount], remapStreamProofRef[row[[3]], stmtCount], 0, 0},
			2 | 3, {code, row[[2]], remapStreamProofRef[row[[3]], stmtCount], remapStreamProofRef[row[[4]], stmtCount], row[[5]]},
			4, {4, row[[2]], remapStreamProofRef[row[[3]], stmtCount], remapStreamProofRef[row[[4]], stmtCount], remapStreamProofRef[row[[5]], stmtCount]},
			5, {5, row[[2]], row[[3]], remapStreamProofRef[row[[4]], stmtCount], 0},
			_, row
		],
		{i, Length[arr]}
	]]
]

closeFormat3Writer[writer_Symbol] := catchKernelFailure @ Module[
	{
		file = writer["File"], stream = writer["MainStream"], bs = writer["BlockSizes"],
		stmtCount = writer["StmtNodeCount"], proofCount = writer["ProofNodeCount"],
		remLeaves, remLabels, dirRows, localNames = writer["Names"],
		hashes62, sortOrder, sortedHashes, sortedIds, sortedNames, bucketChunks, coarseMax,
		bucketRanges = {}, bucketDigests = {}, proofIn, info, rawBytes, mat, remapped, res,
		sectionDir = <||>, manifest = <||>, flags = 0,
		base = writer["Base"], baseEnv, baseHashes, allHashes, rewriteIndex, contentHash,
		meta, metaOffset, metaBytes, metaDigest, dirOffset, dirBytes, manOffset, manBytes, manDigest, headerBytes
	},
	If[TrueQ[writer["Closed"]], Return[File[file], Module]];
	writer["Closed"] = True;
	WithCleanup[
		Null,
		(* Flush remaining leaves, labels, cubical, stmt nodes, meta, deps, proof nodes *)
		flushWriterBuffer[writer, stream, "LeafBlocks", "LeafBuffer", bs["Leaf"], Identity, True];
		flushWriterBuffer[writer, stream, "LabelBlocks", "LabelBuffer", bs["Label"], Identity, True];
		flushWriterBuffer[writer, stream, "CubicalBlocks", "CubicalBuffer", bs["Cubical"], Developer`ToPackedArray, True];
		flushWriterBuffer[writer, stream, "NodeBlocks", "StmtNodeBuffer", bs["StmtNode"], Developer`ToPackedArray, True];
		flushWriterMetaAndDeps[writer, True];
		flushWriterProofNodes[writer, True];
		If[MatchQ[writer["ProofStream"], _OutputStream], Quiet[Close[writer["ProofStream"]]]];
		(* Write RecordDirBlocks with remapped proof ValueRoots *)
		dirRows = Map[Function[row, {row[[1]], row[[2]], remapStreamProofRef[row[[3]], stmtCount], row[[4]]}], writer["DirBuffer"]];
		{sectionDir["RecordDirBlocks"], manifest["RecordDirBlocks"]} = writePartitionedBlocks[stream, dirRows, bs["RecordDir"], Developer`ToPackedArray];
		(* Copy accumulated section ranges & manifests *)
		Scan[
			Function[sec,
				If[ writer["SectionDir"][sec] =!= {},
					sectionDir[sec] = Developer`ToPackedArray[writer["SectionDir"][sec]];
					manifest[sec] = ByteArray[Catenate[Normal /@ writer["Manifest"][sec]]]
				]
			],
			{"LeafBlocks", "LabelBlocks", "CubicalBlocks", "NodeBlocks", "RecordMetaBlocks", "DepBlocks"}
		];
		(* Write NameIndex *)
		If[ localNames =!= {},
			hashes62 = nameHashes62[localNames];
			sortOrder = Ordering[Transpose[{hashes62, Range[Length[localNames]]}]];
			sortedHashes = hashes62[[sortOrder]];
			sortedIds = sortOrder;
			sortedNames = localNames[[sortOrder]];
			bucketChunks = Partition[Range[Length[localNames]], UpTo[bs["NameBucket"]]];
			coarseMax = Developer`ToPackedArray[Map[Function[idxs, sortedHashes[[Last[idxs]]]], bucketChunks]];
			{sectionDir["NameIndexCoarse"], manifest["NameIndexCoarse"]} = writeBlockToStream[stream, coarseMax];
			Do[
				res = writeBlockToStream[stream, <|
					"Hashes" -> Developer`ToPackedArray[sortedHashes[[idxs]]],
					"RecordIDs" -> Developer`ToPackedArray[sortedIds[[idxs]]],
					"Names" -> sortedNames[[idxs]]
				|>];
				AppendTo[bucketRanges, First[res]];
				AppendTo[bucketDigests, Last[res]],
				{idxs, bucketChunks}
			];
			sectionDir["NameIndexBuckets"] = Developer`ToPackedArray[bucketRanges];
			manifest["NameIndexBuckets"] = ByteArray[Catenate[Normal /@ bucketDigests]]
		];
		(* Write RecordHashBlocks *)
		If[ writer["RecordHashList"] =!= {},
			{sectionDir["RecordHashBlocks"], manifest["RecordHashBlocks"]} = writePartitionedBlocks[stream, writer["RecordHashList"], bs["RecordDir"], Developer`ToPackedArray]
		];
		(* Stream trailing ProofNodeBlocks from temp file, remapping proof-to-proof references to stmtCount + localProofId *)
		If[ proofCount > 0 && writer["ProofBlockInfo"] =!= {},
			WithCleanup[
				proofIn = OpenRead[writer["ProofTmp"], BinaryFormat -> True],
				Module[{pRanges = {}, pDigests = {}},
					Do[
						rawBytes = readExactBytes[proofIn, info[[1]], info[[2]]];
						mat = BinaryDeserialize[rawBytes];
						remapped = remapStreamProofMatrix[mat, stmtCount];
						res = writeBlockToStream[stream, remapped];
						AppendTo[pRanges, First[res]];
						AppendTo[pDigests, Last[res]],
						{info, writer["ProofBlockInfo"]}
					];
					sectionDir["ProofNodeBlocks"] = Developer`ToPackedArray[pRanges];
					manifest["ProofNodeBlocks"] = ByteArray[Catenate[Normal /@ pDigests]]
				],
				If[MatchQ[proofIn, _InputStream], Quiet[Close[proofIn]]]
			]
		];
		(* Compute Meta["Hash"] matching Format 2 *)
		baseEnv = Replace[base, {None -> None, name_String :> TypeTheoryEnvironment[name], env_?environmentQ :> env}];
		baseHashes = If[baseEnv === None, <||>, environmentRecordHashes[baseEnv]];
		allHashes = Join[baseHashes, AssociationThread[localNames, writer["RecordHashList"]]];
		rewriteIndex = If[baseEnv === None, writer["RewriteRuleIndex"], Merge[{First[baseEnv]["RewriteRuleIndex"], writer["RewriteRuleIndex"]}, Apply[Join]]];
		contentHash = Hash[
			BinarySerialize[<|
				"Rules" -> writer["Rules"],
				"NaturalNumbers" -> writer["NaturalNumbers"],
				"RewriteRuleIndex" -> rewriteIndex,
				"Records" -> allHashes
			|>],
			"SHA256",
			"HexString"
		];
		If[proofCount > 0, flags = BitOr[flags, $format3FlagProofs]];
		If[TrueQ[writer["IncludeDependencies"]] && localNames =!= {}, flags = BitOr[flags, $format3FlagDeps]];
		If[writer["RecordHashList"] =!= {}, flags = BitOr[flags, $format3FlagRecordHashes]];
		If[! TrueQ[writer["IncludeProofs"]], flags = BitOr[flags, $format3FlagStatementOnly]];
		If[writer["CubicalCount"] > 0, flags = BitOr[flags, $format3FlagCubical]];
		meta = <|
			"Format" -> "TypeTheoryEnvironment",
			"FormatVersion" -> 3,
			"TypeTheoryVersion" -> PacletObject[File[$pacletDirectory]]["Version"],
			"KernelHash" -> $kernelHash,
			"Host" -> <|"VersionNumber" -> $VersionNumber, "ReleaseNumber" -> $ReleaseNumber, "Version" -> $Version|>,
			"Rules" -> writer["Rules"],
			"Base" -> Replace[baseEnv, {None -> None, env_ :> <|"Name" -> First[env]["LibraryName"], "Hash" -> environmentContentHash[env]|>}],
			"NaturalNumbers" -> writer["NaturalNumbers"],
			"RewriteRuleIndex" -> writer["RewriteRuleIndex"],
			"OverloadIndex" -> writer["OverloadIndex"],
			"KindCounts" -> writer["KindCounts"],
			"BlockSizes" -> KeyTake[bs, {"RecordDir", "NameBucket", "Cubical"}],
			"Hash" -> contentHash
		|>;
		metaOffset = StreamPosition[stream];
		metaBytes = BinarySerialize[meta, PerformanceGoal -> "Size"];
		metaDigest = sha256Bytes[metaBytes];
		writeAllBytes[stream, metaBytes];
		dirOffset = StreamPosition[stream];
		dirBytes = BinarySerialize[sectionDir, PerformanceGoal -> "Size"];
		manifest["SectionDirectory"] = sha256Bytes[dirBytes];
		writeAllBytes[stream, dirBytes];
		manOffset = StreamPosition[stream];
		manBytes = BinarySerialize[manifest, PerformanceGoal -> "Size"];
		manDigest = sha256Bytes[manBytes];
		writeAllBytes[stream, manBytes];
		headerBytes = encodeFormat3Header[<|
			"Flags" -> flags,
			"ConstantCount" -> Length[localNames],
			"StmtNodeCount" -> stmtCount,
			"ProofNodeCount" -> proofCount,
			"LeafCount" -> writer["LeafCount"],
			"LabelCount" -> writer["LabelCount"],
			"StmtNodeBlockSize" -> bs["StmtNode"],
			"ProofNodeBlockSize" -> bs["ProofNode"],
			"LeafBlockSize" -> bs["Leaf"],
			"LabelBlockSize" -> bs["Label"],
			"RecordMetaBlockSize" -> bs["RecordMeta"],
			"SectionDirOffset" -> dirOffset,
			"SectionDirLength" -> Length[dirBytes],
			"MetaOffset" -> metaOffset,
			"MetaLength" -> Length[metaBytes],
			"ManifestOffset" -> manOffset,
			"ManifestLength" -> Length[manBytes],
			"MetaSha256" -> metaDigest,
			"ManifestSha256" -> manDigest
		|>];
		writeAllBytes[stream, headerBytes],
		If[MatchQ[writer["ProofStream"], _OutputStream], Quiet[Close[writer["ProofStream"]]]];
		If[MatchQ[stream, _OutputStream], Quiet[Close[stream]]];
		If[FileExistsQ[writer["ProofTmp"]], Quiet[DeleteFile[writer["ProofTmp"]]]]
	];
	File[file]
]
