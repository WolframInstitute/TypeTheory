(* ::Package:: *)

(* Tests for Format 3 (.tte) single-file seekable lazy environments: round-trip parity with Format 2,
   zero proof I/O on statement/type/signature/overlay queries, all 11 constant kinds + cubical systems,
   statement-only cuts, streaming batch writer with multi-block chunking, FD pool & on-disk change guards,
   and trust-boundary forgery/tampering rejections.
   Run with: wolframscript -f scripts/run_tests.wls TypeTheory/Tests/Checking/LazyEnvironments.wlt *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

directory = CreateDirectory[]
tteFile[name_String] := FileNameJoin[{directory, name <> ".tte"}]
wxfFile[name_String] := FileNameJoin[{directory, name <> ".wxf"}]

pkg = "WolframInstitute`TypeTheory`PackageScope`";
sym[name_String] := Symbol[pkg <> name]

prelude = TypeTheoryEnvironment["Prelude"]
arithmetic = Append[prelude, TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, "equalityReflexivity"[4]]]

(* Helper to rewrite a Format 3 file's section/meta/manifest with valid SHA-256s for forgery tests *)
rewriteFormat3File[srcFile_String, dstFile_String, transform_] := Module[
	{
		raw = Normal[ReadByteArray[srcFile]], fileSize, headerBytes, header,
		metaBytes, meta, manBytes, manifest, dirBytes, sectionDir,
		readRaw, newState, outStream, newMeta, newSecDir, newManifest, newFlags,
		newStmtCount, newProofCount, newLeafCount, newLabelCount,
		secBytes, off, dig, newMetaBytes, newMetaOff, newMetaDig,
		newDirBytes, newDirOff, newManBytes, newManOff, newManDig, newHeader
	},
	fileSize = Length[raw];
	headerBytes = ByteArray[Take[raw, {fileSize - 255, fileSize}]];
	header = sym["decodeFormat3Header"][headerBytes, srcFile];
	readRaw = Function[{o, l}, ByteArray[Take[raw, {o + 1, o + l}]]];
	meta = BinaryDeserialize[readRaw[header["MetaOffset"], header["MetaLength"]]];
	manifest = BinaryDeserialize[readRaw[header["ManifestOffset"], header["ManifestLength"]]];
	sectionDir = BinaryDeserialize[readRaw[header["SectionDirOffset"], header["SectionDirLength"]]];
	newState = transform[<|"Raw" -> raw, "Header" -> header, "Meta" -> meta, "SectionDirectory" -> sectionDir, "Manifest" -> manifest, "ReadRaw" -> readRaw|>];
	outStream = OpenWrite[dstFile, BinaryFormat -> True];
	BinaryWrite[outStream, ByteArray[{84, 84, 69, 51, 0, 0, 0, 3}]];
	newSecDir = <||>;
	newManifest = <||>;
	KeyValueMap[
		Function[{secName, entries},
			If[ ListQ[entries] && Length[entries] == 2 && AllTrue[entries, IntegerQ],
				secBytes = Lookup[newState, Key[{"Override", secName}], readRaw[First[entries], Last[entries]]];
				off = StreamPosition[outStream];
				BinaryWrite[outStream, secBytes];
				newSecDir[secName] = {off, Length[secBytes]};
				newManifest[secName] = sym["sha256Bytes"][secBytes],
				Block[{ranges = {}, digests = {}},
					Do[
						secBytes = Lookup[newState, Key[{"Override", secName, i}], readRaw[entries[[i, 1]], entries[[i, 2]]]];
						off = StreamPosition[outStream];
						BinaryWrite[outStream, secBytes];
						AppendTo[ranges, {off, Length[secBytes]}];
						AppendTo[digests, sym["sha256Bytes"][secBytes]],
						{i, Length[entries]}
					];
					newSecDir[secName] = Developer`ToPackedArray[ranges];
					newManifest[secName] = ByteArray[Catenate[Normal /@ digests]]
				]
			]
		],
		newState["SectionDirectory"]
	];
	newMetaBytes = Lookup[newState, "RawMetaBytes", BinarySerialize[newState["Meta"], PerformanceGoal -> "Size"]];
	newMetaOff = StreamPosition[outStream];
	newMetaDig = sym["sha256Bytes"][newMetaBytes];
	BinaryWrite[outStream, newMetaBytes];
	newDirBytes = Lookup[newState, "RawSectionDirBytes", BinarySerialize[newSecDir, PerformanceGoal -> "Size"]];
	newDirOff = StreamPosition[outStream];
	newManifest["SectionDirectory"] = sym["sha256Bytes"][newDirBytes];
	BinaryWrite[outStream, newDirBytes];
	newManBytes = BinarySerialize[newManifest, PerformanceGoal -> "Size"];
	newManOff = StreamPosition[outStream];
	newManDig = sym["sha256Bytes"][newManBytes];
	BinaryWrite[outStream, newManBytes];
	newHeader = sym["encodeFormat3Header"][Join[newState["Header"], <|
		"SectionDirOffset" -> newDirOff,
		"SectionDirLength" -> Length[newDirBytes],
		"MetaOffset" -> newMetaOff,
		"MetaLength" -> Length[newMetaBytes],
		"ManifestOffset" -> newManOff,
		"ManifestLength" -> Length[newManBytes],
		"MetaSha256" -> newMetaDig,
		"ManifestSha256" -> newManDig
	|>]];
	BinaryWrite[outStream, newHeader];
	Close[outStream];
	dstFile
]


(* ::Section:: *)
(*Round-Trip, Format 2 Hash Parity, and Auto-Detection*)


VerificationTest[
	{
		Export[tteFile["arith"], arithmetic],
		Export[tteFile["arith_standalone"], arithmetic, "Standalone" -> True],
		Export[wxfFile["arith_f3"], arithmetic, "FormatVersion" -> 3]
	},
	{File[tteFile["arith"]], File[tteFile["arith_standalone"]], File[wxfFile["arith_f3"]]},
	TestID -> "Export-writes-Format-3-by-extension-and-FormatVersion-option"
]

VerificationTest[
	Module[{l1, l2, l3, hOrig = sym["environmentContentHash"][arithmetic]},
		l1 = TypeTheoryEnvironment[File[tteFile["arith"]]];
		l2 = TypeTheoryEnvironment[File[tteFile["arith_standalone"]]];
		l3 = TypeTheoryEnvironment[File[wxfFile["arith_f3"]]];
		{
			sym["environmentContentHash"][l1] === hOrig,
			sym["environmentContentHash"][l2] === hOrig,
			sym["environmentContentHash"][l3] === hOrig,
			Information[l1, "Provenance"]["FormatVersion"],
			Information[l3, "Provenance"]["FormatVersion"],
			Information[l1, "Provenance"]["Checked"],
			Keys[l1] === Keys[arithmetic],
			Keys[l2] === Keys[arithmetic],
			Length[l2] === Length[arithmetic],
			Normal[l2] === Normal[arithmetic],
			Information[l2, "Kinds"] === Information[arithmetic, "Kinds"],
			Information[l2, "Axioms"] === Information[arithmetic, "Axioms"],
			Information[l2, "NaturalNumbers"] === Information[arithmetic, "NaturalNumbers"]
		}
	],
	{True, True, True, 3, 3, False, True, True, True, True, True, True, True},
	TestID -> "Format-3-matches-Format-2-content-hash-and-all-queries-with-magic-auto-detect"
]

VerificationTest[
	Module[{l1, l2, lChecked},
		l1 = TypeTheoryEnvironment[File[tteFile["arith"]]];
		l2 = TypeTheoryEnvironment[File[tteFile["arith_standalone"]]];
		lChecked = TypeTheoryEnvironment[File[tteFile["arith_standalone"]], "Check" -> True];
		{
			MatchQ[TypeTheoryCheck[l1], _Success],
			MatchQ[TypeTheoryCheck[l2], _Success],
			MatchQ[TypeTheoryCheck[l1, Method -> "Symbolic"], _Success],
			Information[lChecked, "Provenance"]["Checked"]
		}
	],
	{True, True, True, True},
	TestID -> "TypeTheoryCheck-verifies-Format-3-environments-compiled-and-symbolic"
]


(* ::Section:: *)
(*Zero Proof I/O and Overlay Extension*)


VerificationTest[
	Module[{loaded, ext, box, r1, r2, r3, r4, r5, declMatch},
		loaded = TypeTheoryEnvironment[File[tteFile["arith_standalone"]]];
		WolframInstitute`TypeTheory`PackageScope`$lazyProofBlockReadCount = 0;
		(* All of these must touch zero ProofNodeBlocks *)
		{Length[loaded], KeyExistsQ[loaded, TwoPlusTwo], KeyExistsQ[loaded, MissingConstantXYZ]};
		Information[loaded, "Kinds"];
		Information[loaded, "Axioms"];
		Information[loaded, "Theorems"];
		TypeTheoryType[TwoPlusTwo, loaded];
		box = MakeBoxes[loaded, StandardForm];
		r1 = WolframInstitute`TypeTheory`PackageScope`$lazyProofBlockReadCount;
		Information[loaded, "Signature"];
		r2 = WolframInstitute`TypeTheory`PackageScope`$lazyProofBlockReadCount;
		(* Overlay extension + compiled kernel cone check must touch zero ProofNodeBlocks *)
		ext = Append[loaded, TypeTheoryTheorem[ThreePlusThree, 3 + 3 == 6, "equalityReflexivity"[6]]];
		r3 = WolframInstitute`TypeTheory`PackageScope`$lazyProofBlockReadCount;
		(* AxiomClosure uses CSR DepBlocks and touches zero ProofNodeBlocks *)
		TypeTheoryAxiomClosure[TypeTheoryTerm[TwoPlusTwo, loaded]];
		r4 = WolframInstitute`TypeTheory`PackageScope`$lazyProofBlockReadCount;
		(* Explicitly requesting the theorem declaration decodes its proof on demand *)
		declMatch = (loaded[TwoPlusTwo] === arithmetic[TwoPlusTwo]);
		r5 = WolframInstitute`TypeTheory`PackageScope`$lazyProofBlockReadCount;
		{
			r1, r2, r3, r4, r5 > 0, declMatch,
			Length[ext] === Length[loaded] + 1,
			KeyExistsQ[ext, ThreePlusThree],
			Information[ext, "Kinds"]["Theorem"] === Information[loaded, "Kinds"]["Theorem"] + 1,
			MatchQ[TypeTheoryCheck[TypeTheoryTerm[ThreePlusThree, ext], TypeTheoryTerm[3 + 3 == 6, ext]], _Success],
			MatchQ[box, _String | _InterpretationBox | _TemplateBox]
		}
	],
	{0, 0, 0, 0, True, True, True, True, True, True, True},
	TestID -> "Normal-queries-signature-axiom-closure-and-overlay-extension-read-zero-proof-blocks"
]


(* ::Section:: *)
(*All Kinds: Cubical, RewriteRules, Overloads, Holes, Annotations*)


VerificationTest[
	Module[{cub = TypeTheoryEnvironment["Cubical"], file = tteFile["cubical"], loaded},
		Export[file, cub, "Standalone" -> True];
		loaded = TypeTheoryEnvironment[File[file]];
		{
			sym["environmentContentHash"][loaded] === sym["environmentContentHash"][cub],
			Normal[loaded] === Normal[cub],
			MatchQ[TypeTheoryCheck[loaded], _Success]
		}
	],
	{True, True, True},
	TestID -> "Format-3-round-trips-cubical-systems-with-matching-hash-and-check"
]

VerificationTest[
	Module[{rwRules, file = tteFile["allkinds"], loaded, rwEnv},
		rwRules = TypeTheoryRules["CalculusOfInductiveConstructions", "RewriteRules" -> True];
		rwEnv = TypeTheoryEnvironment[rwRules, {
			TypeTheoryAxiom[MyType, TypeUniverse[1]],
			TypeTheoryAxiom[MyProp, TypeUniverse[0]],
			TypeTheoryAxiom[myZero, MyType],
			TypeTheoryAxiom[myOp, MyType -> MyType],
			TypeTheoryRewriteRule[myRule, ForAll[{Typed[x, MyType]}, myOp[myOp[x]] -> x]],
			TypeTheoryDefinition[myId, Function[Typed[x, MyType], x], "Annotation" -> <|"Note" -> "test", "Expr" -> HoldForm[1 + 1]|>],
			TypeTheoryTheorem[myThm, MyProp -> MyProp, Function[Typed[x, MyProp], x]]
		}];
		Export[file, rwEnv, "Standalone" -> True];
		loaded = TypeTheoryEnvironment[File[file]];
		{
			sym["environmentContentHash"][loaded] === sym["environmentContentHash"][rwEnv],
			Normal[loaded] === Normal[rwEnv],
			Information[loaded, "RewriteRules"] === Information[rwEnv, "RewriteRules"],
			Information[loaded, "Annotations"] === Information[rwEnv, "Annotations"],
			DefinitionallyEqualQ[TypeTheoryTerm[myOp[myOp[myZero]], loaded], TypeTheoryTerm[myZero, loaded]],
			MatchQ[TypeTheoryCheck[loaded], _Success]
		}
	],
	{True, True, True, True, True, True},
	TestID -> "Format-3-round-trips-rewrite-rules-and-annotations-cleanly"
]


(* ::Section:: *)
(*Statement-Only Cut (IncludeProofs -> False and Zero-Decode Cut)*)


VerificationTest[
	Module[{fFull = tteFile["arith_standalone"], fOptCut = tteFile["opt_cut"], fZeroCut = tteFile["zero_cut"], loadedOpt, loadedZero},
		Export[fOptCut, arithmetic, "Standalone" -> True, "IncludeProofs" -> False];
		sym["cutFormat3StatementFile"][fFull, fZeroCut];
		loadedOpt = TypeTheoryEnvironment[File[fOptCut]];
		loadedZero = TypeTheoryEnvironment[File[fZeroCut]];
		{
			Information[loadedOpt, "Signature"] === Information[arithmetic, "Signature"],
			Information[loadedZero, "Signature"] === Information[arithmetic, "Signature"],
			Lookup[Information[loadedOpt, "Kinds"], "Theorem", 0],
			Lookup[Information[loadedZero, "Kinds"], "Theorem", 0],
			TypeTheoryAxiomClosure[TypeTheoryTerm[TwoPlusTwo, loadedOpt]],
			TypeTheoryAxiomClosure[TypeTheoryTerm[TwoPlusTwo, loadedZero]],
			MatchQ[TypeTheoryCheck[loadedOpt], _Success],
			MatchQ[TypeTheoryCheck[loadedZero], _Success],
			FileByteCount[fZeroCut] < FileByteCount[fFull]
		}
	],
	{True, True, 0, 0, <|TwoPlusTwo -> "Proposition"|>, <|TwoPlusTwo -> "Proposition"|>, True, True, True},
	TestID -> "Statement-only-cuts-preserve-signature-convert-theorems-to-axioms-and-check"
]


(* ::Section:: *)
(*Streaming Batch Writer with Multi-Block Chunking*)


VerificationTest[
	Module[
		{
			file = tteFile["streamed"], smallBlocks, writer, allNames, batchChunks, loaded, proofReads
		},
		smallBlocks = <|
			"StmtNode" -> 16, "ProofNode" -> 16, "Leaf" -> 8, "Label" -> 8,
			"RecordMeta" -> 7, "RecordDir" -> 11, "NameBucket" -> 9, "Cubical" -> 8
		|>;
		writer = sym["openFormat3Writer"][file,
			"Rules" -> Information[arithmetic, "Rules"],
			"Base" -> None,
			"NaturalNumbers" -> First[arithmetic]["NaturalNumbers"],
			"BlockSizes" -> smallBlocks
		];
		allNames = sym["environmentNames"][arithmetic];
		batchChunks = Partition[allNames, UpTo[23]];
		Do[
			sym["writeFormat3Batch"][writer, AssociationMap[Function[n, sym["constantRecord"][arithmetic, n]], chunk]],
			{chunk, batchChunks}
		];
		sym["closeFormat3Writer"][writer];
		loaded = TypeTheoryEnvironment[File[file]];
		WolframInstitute`TypeTheory`PackageScope`$lazyProofBlockReadCount = 0;
		TypeTheoryType[TwoPlusTwo, loaded];
		proofReads = WolframInstitute`TypeTheory`PackageScope`$lazyProofBlockReadCount;
		{
			sym["environmentContentHash"][loaded] === sym["environmentContentHash"][arithmetic],
			Keys[loaded] === Keys[arithmetic],
			Normal[loaded] === Normal[arithmetic],
			Information[loaded, "Signature"] === Information[arithmetic, "Signature"],
			proofReads,
			MatchQ[TypeTheoryCheck[loaded], _Success]
		}
	],
	{True, True, True, True, 0, True},
	TestID -> "Streaming-batch-writer-with-small-blocks-round-trips-and-matches-Format-2-hash"
]


(* ::Section:: *)
(*Deep DAG & Shared Subterms*)


VerificationTest[
	Module[
		{
			base, oneRecord, app = sym["application"], cref = sym["constantReference"], addRecs = sym["addConstantRecords"],
			fRef, aRef, gRef, deepTerm, dagTerm, deepEnv, file = tteFile["deep_dag"], loaded
		},
		base = TypeTheoryEnvironment[TypeTheoryEnvironment[], {
			TypeTheoryAxiom["T", TypeUniverse[1]],
			TypeTheoryAxiom["a", "T"],
			TypeTheoryAxiom["f", "T" -> "T"],
			TypeTheoryAxiom["g", "T" -> "T" -> "T"],
			TypeTheoryDefinition["one", "f"["a"]]
		}];
		oneRecord = First[base]["Records"][HoldComplete["one"]];
		fRef = cref[HoldComplete["f"], {}];
		aRef = cref[HoldComplete["a"], {}];
		gRef = cref[HoldComplete["g"], {}];
		deepTerm = Nest[Function[t, Construct[app, fRef, t]], aRef, 1600];
		dagTerm = Nest[Function[t, Construct[app, Construct[app, gRef, t], t]], aRef, 12];
		deepEnv = addRecs[base, <|
			HoldComplete["deep"] -> Association[oneRecord, "Value" -> deepTerm],
			HoldComplete["dag"] -> Association[oneRecord, "Value" -> dagTerm]
		|>];
		Export[file, deepEnv, "Standalone" -> True];
		loaded = TypeTheoryEnvironment[File[file]];
		{
			sym["constantRecord"][loaded, HoldComplete["deep"]]["Value"] === deepTerm,
			sym["constantRecord"][loaded, HoldComplete["dag"]]["Value"] === dagTerm,
			Information[loaded, "Signature"] === Information[deepEnv, "Signature"]
		}
	],
	{True, True, True},
	TestID -> "Format-3-decodes-deep-terms-and-shared-DAGs-without-hitting-RecursionLimit"
]


(* ::Section:: *)
(*Trust Boundary: Tampering, Code Execution, DAG Forgery, Index Forgery, FD Pool*)


(* 1. Flip a byte inside the trailing footer -> rejected on open *)
VerificationTest[
	Module[{bytes = Normal[ReadByteArray[tteFile["arith"]]], bad = tteFile["bad_header"]},
		bytes[[-20]] = BitXor[bytes[[-20]], 255];
		BinaryWrite[bad, ByteArray[bytes]];
		Close[bad];
		TypeTheoryEnvironment[File[bad]]["Tag"]
	],
	"SavedEnvironmentInvalid",
	TestID -> "Tampered-Format-3-header-is-refused-on-open"
]

(* 2. Flip a byte inside a lazily loaded ProofNodeBlock -> opens fine, fails on first proof touch *)
VerificationTest[
	Module[{src = tteFile["arith_standalone"], bad = tteFile["bad_proof_block"], raw, fileSize, header, sectionDir, pOff, pLen, loaded, typeOK, err},
		raw = Normal[ReadByteArray[src]];
		fileSize = Length[raw];
		header = sym["decodeFormat3Header"][ByteArray[Take[raw, {fileSize - 255, fileSize}]], src];
		sectionDir = BinaryDeserialize[ByteArray[Take[raw, {header["SectionDirOffset"] + 1, header["SectionDirOffset"] + header["SectionDirLength"]}]]];
		{pOff, pLen} = First[sectionDir["ProofNodeBlocks"]];
		raw[[pOff + Quotient[pLen, 2]]] = BitXor[raw[[pOff + Quotient[pLen, 2]]], 1];
		BinaryWrite[bad, ByteArray[raw]];
		Close[bad];
		loaded = TypeTheoryEnvironment[File[bad]];
		typeOK = MatchQ[TypeTheoryType[TwoPlusTwo, loaded], _TypeTheoryTerm];
		err = sym["catchKernelFailure"][sym["constantRecord"][loaded, HoldComplete[TwoPlusTwo]]];
		{typeOK, FailureQ[err], err["Tag"]}
	],
	{True, True, "SavedEnvironmentInvalid"},
	TestID -> "Tampered-ProofNodeBlock-fails-SHA-256-verification-on-first-touch"
]

(* 3. Crafted Meta with unevaluated call (even with valid SHA-256!) -> refused without running code *)
VerificationTest[
	Module[{bad = tteFile["bad_code_meta"], calls = {}, res},
		Block[{evilCall},
			SetAttributes[evilCall, HoldAll];
			evilCall[x_] := AppendTo[calls, x];
			rewriteFormat3File[tteFile["arith"], bad, Function[st,
				Append[st, "RawMetaBytes" -> BinarySerialize[Unevaluated[Association[
					"Format" -> "TypeTheoryEnvironment", "FormatVersion" -> 3, "KernelHash" -> "",
					"Rules" -> evilCall[1], "Base" -> None, "NaturalNumbers" -> None,
					"RewriteRuleIndex" -> Association[evilCall[2] -> {}], "OverloadIndex" -> Association[],
					"KindCounts" -> Association[], "BlockSizes" -> Association[], "Hash" -> ""
				]]]]
			]];
			res = TypeTheoryEnvironment[File[bad]];
			{FailureQ[res], res["Tag"], calls}
		]
	],
	{True, "SavedEnvironmentInvalid", {}},
	TestID -> "Crafted-Format-3-Meta-carrying-code-is-refused-without-evaluating-it"
]

(* 4. Crafted SectionDirectory carrying code in key (even with valid SHA-256!) -> refused without running code *)
VerificationTest[
	Module[{bad = tteFile["bad_code_secdir"], calls = {}, res},
		Block[{evilDirCall},
			SetAttributes[evilDirCall, HoldAll];
			evilDirCall[x_] := AppendTo[calls, x];
			rewriteFormat3File[tteFile["arith"], bad, Function[st,
				Append[st, "RawSectionDirBytes" -> BinarySerialize[Unevaluated[Association[evilDirCall[99] -> {8, 8}]]]]
			]];
			res = TypeTheoryEnvironment[File[bad]];
			{FailureQ[res], res["Tag"], calls}
		]
	],
	{True, "SavedEnvironmentInvalid", {}},
	TestID -> "Crafted-Format-3-SectionDirectory-carrying-code-is-refused-without-evaluating-it"
]

(* 5. Forged DAG cycle / self-reference in NodeBlock (with valid SHA-256!) -> rejected by lazy DAG decoder *)
VerificationTest[
	Module[{bad = tteFile["bad_dag_cycle"], loaded, err},
		rewriteFormat3File[tteFile["arith"], bad, Function[st,
			Module[{entries = st["SectionDirectory"]["NodeBlocks"], mat},
				mat = Normal[BinaryDeserialize[st["ReadRaw"][entries[[1, 1]], entries[[1, 2]]]]];
				(* Make row 1 reference itself (row 1 -> row 1 cycle!) *)
				mat[[1]] = {1, 1, 1, 0, 0};
				Append[st, {"Override", "NodeBlocks", 1} -> BinarySerialize[Developer`ToPackedArray[mat], PerformanceGoal -> "Size"]]
			]
		]];
		loaded = TypeTheoryEnvironment[File[bad]];
		err = sym["catchKernelFailure"][sym["constantRecord"][loaded, HoldComplete[TwoPlusTwo]]];
		{FailureQ[err], err["Tag"]}
	],
	{True, "SavedEnvironmentInvalid"},
	TestID -> "Forged-DAG-cycle-in-NodeBlock-is-rejected-by-lazy-decoder"
]

(* 6. Forged RewriteRuleIndex pointing to non-RewriteRule constant (valid SHA-256!) -> rejected on fetch and check *)
VerificationTest[
	Module[{bad = tteFile["bad_rw_index"], loaded, fetchErr, checkErr},
		rewriteFormat3File[tteFile["arith"], bad, Function[st,
			Append[st, "Meta" -> Append[st["Meta"], "RewriteRuleIndex" -> <|HoldComplete[TwoPlusTwo] -> {HoldComplete[TwoPlusTwo]}|>]]
		]];
		loaded = TypeTheoryEnvironment[File[bad]];
		fetchErr = sym["catchKernelFailure"][sym["rewriteRuleRecords"][loaded, HoldComplete[TwoPlusTwo]]];
		checkErr = TypeTheoryCheck[loaded];
		{FailureQ[fetchErr], fetchErr["Tag"], FailureQ[checkErr], checkErr["Tag"]}
	],
	{True, "SavedEnvironmentInvalid", True, "DeclarationMismatch"},
	TestID -> "Forged-RewriteRuleIndex-is-rejected-on-fetch-and-by-TypeTheoryCheck"
]

(* 7. Forged OverloadIndex pointing to constant without Overloads (valid SHA-256!) -> rejected on fetch and check *)
VerificationTest[
	Module[{bad = tteFile["bad_overload_index"], loaded, fetchErr, checkErr},
		rewriteFormat3File[tteFile["arith"], bad, Function[st,
			Append[st, "Meta" -> Append[st["Meta"], "OverloadIndex" -> <|HoldComplete[Plus] -> {HoldComplete[TwoPlusTwo]}|>]]
		]];
		loaded = TypeTheoryEnvironment[File[bad]];
		fetchErr = sym["catchKernelFailure"][sym["overloadingConstants"][loaded, HoldComplete[Plus]]];
		checkErr = TypeTheoryCheck[loaded];
		{FailureQ[fetchErr], fetchErr["Tag"], FailureQ[checkErr], checkErr["Tag"]}
	],
	{True, "SavedEnvironmentInvalid", True, "DeclarationMismatch"},
	TestID -> "Forged-OverloadIndex-is-rejected-on-fetch-and-by-TypeTheoryCheck"
]

(* 8. Forged CSR DepBlocks omitting a dependency (valid SHA-256!) -> rejected by TypeTheoryCheck *)
VerificationTest[
	Module[{bad = tteFile["bad_deps"], loaded, checkErr},
		rewriteFormat3File[tteFile["arith"], bad, Function[st,
			Module[{entries = st["SectionDirectory"]["DepBlocks"], dep},
				dep = BinaryDeserialize[st["ReadRaw"][entries[[1, 1]], entries[[1, 2]]]];
				dep["StmtOffsets"] = Developer`ToPackedArray[ConstantArray[1, Length[dep["StmtOffsets"]]]];
				dep["StmtTargets"] = Developer`ToPackedArray[{}];
				dep["ProofOffsets"] = Developer`ToPackedArray[ConstantArray[1, Length[dep["ProofOffsets"]]]];
				dep["ProofTargets"] = Developer`ToPackedArray[{}];
				Append[st, {"Override", "DepBlocks", 1} -> BinarySerialize[dep, PerformanceGoal -> "Size"]]
			]
		]];
		loaded = TypeTheoryEnvironment[File[bad]];
		checkErr = TypeTheoryCheck[loaded];
		{FailureQ[checkErr], checkErr["Tag"]}
	],
	{True, "DeclarationMismatch"},
	TestID -> "Forged-DepBlocks-omitting-dependencies-is-rejected-by-TypeTheoryCheck"
]

(* 9. Different KernelHash refused on Check -> False, accepted on Check -> True *)
VerificationTest[
	Module[{bad = tteFile["other_kernel"], errUnchecked, okChecked},
		rewriteFormat3File[tteFile["arith"], bad, Function[st,
			Append[st, "Meta" -> Append[st["Meta"], "KernelHash" -> "0000000000000000000000000000000000000000000000000000000000000000"]]
		]];
		errUnchecked = TypeTheoryEnvironment[File[bad]];
		okChecked = TypeTheoryEnvironment[File[bad], "Check" -> True];
		{FailureQ[errUnchecked], errUnchecked["Tag"], Head[okChecked], Information[okChecked, "Provenance"]["Checked"]}
	],
	{True, "SavedByAnotherKernel", TypeTheoryEnvironment, True},
	TestID -> "Different-KernelHash-is-refused-unless-Check-is-True"
]

(* 10. File modified on disk after open -> detected on next lazy block read *)
VerificationTest[
	Module[{mutFile = tteFile["mutated"], loaded, err},
		CopyFile[tteFile["arith_standalone"], mutFile, OverwriteTarget -> True];
		loaded = TypeTheoryEnvironment[File[mutFile]];
		(* Append 1 extra byte to modify FileByteCount on disk *)
		With[{s = OpenAppend[mutFile, BinaryFormat -> True]}, BinaryWrite[s, ByteArray[{0}]]; Close[s]];
		err = sym["catchKernelFailure"][sym["constantRecord"][loaded, HoldComplete[TwoPlusTwo]]];
		{FailureQ[err], err["Tag"]}
	],
	{True, "SavedEnvironmentChangedOnDisk"},
	TestID -> "File-modified-on-disk-after-open-is-detected-on-lazy-read"
]

(* 11. Global bounded LRU stream pool never leaks FDs past $lazyStreamPoolLimit, and default mode keeps 0 open FDs *)
VerificationTest[
	Block[{WolframInstitute`TypeTheory`PackageScope`$lazyStreamPoolLimit = 4, files, envs, maxPool = 0, afterClose, defaultPool},
		sym["closeLazyStreams"][];
		files = Table[CopyFile[tteFile["arith"], tteFile["pool_" <> ToString[i]], OverwriteTarget -> True], {i, 12}];
		envs = Map[Function[f, TypeTheoryEnvironment[File[f]]], files];
		Do[
			TypeTheoryType[TwoPlusTwo, env];
			maxPool = Max[maxPool, sym["lazyStreamPoolCount"][]],
			{env, envs}
		];
		sym["closeLazyStreams"][];
		afterClose = sym["lazyStreamPoolCount"][];
		Block[{WolframInstitute`TypeTheory`PackageScope`$lazyStreamPoolLimit = 0},
			TypeTheoryType[TwoPlusTwo, TypeTheoryEnvironment[File[First[files]]]];
			defaultPool = sym["lazyStreamPoolCount"][]
		];
		{maxPool <= 4, maxPool >= 1, afterClose, defaultPool}
	],
	{True, True, 0, 0},
	TestID -> "Global-LRU-stream-pool-bounds-open-file-descriptors-and-closes-cleanly"
]

sym["closeLazyStreams"][]
DeleteDirectory[directory, DeleteContents -> True]
