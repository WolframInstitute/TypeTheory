(* ::Package:: *)

(* Tests for saved environments: Export["file.wxf", environment] writes an environment, and
   TypeTheoryEnvironment[File["file.wxf"]] reads it back without checking its declarations again.
   Run with: TestReport["TypeTheory/Tests/Checking/SavedEnvironments.wlt"] from the repository root. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

directory = CreateDirectory[]

savedFile[name_String] := FileNameJoin[{directory, name <> ".wxf"}]

prelude = TypeTheoryEnvironment["Prelude"]

arithmetic = Append[prelude, TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, "equalityReflexivity"[4]]]

savedData[name_String] := First[BinaryDeserialize[ReadByteArray[savedFile[name]], HoldComplete]]


VerificationTest[
	Export[savedFile["arithmetic"], arithmetic],
	File[savedFile["arithmetic"]],
	TestID -> "Export-writes-an-environment-to-a-WXF-file"
]

VerificationTest[
	With[{loaded = TypeTheoryEnvironment[File[savedFile["arithmetic"]]]},
		{Keys[loaded] === Keys[arithmetic], Normal[loaded] === Normal[arithmetic], Information[loaded, "NaturalNumbers"] === Information[arithmetic, "NaturalNumbers"]}
	],
	{True, True, True},
	TestID -> "A-saved-environment-reads-back-with-the-same-declarations"
]

VerificationTest[
	With[{loaded = TypeTheoryEnvironment[File[savedFile["arithmetic"]]]},
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[TwoPlusTwo, loaded], TypeTheoryTerm[2 + 2 == 4, loaded]], _Success]
	],
	True,
	TestID -> "A-theorem-of-a-saved-environment-can-be-used"
]

VerificationTest[
	With[{data = savedData["arithmetic"]},
		{data["Base"]["Name"], data["Names"], data["KernelHash"] === WolframInstitute`TypeTheory`PackageScope`$kernelHash}
	],
	{"Prelude", {HoldComplete[TwoPlusTwo]}, True},
	TestID -> "A-file-holds-only-the-constants-beyond-the-library-environment-it-extends"
]

(* a row's parts, by its code: {1, f, a, 0, 0}, {2 | 3, name, domain, body, binder}, {4, name, type, value, body} and
   {5, structure, index, term, 0}, each part an earlier row, or a leaf negated *)
rowParts[row_List] := row[[Replace[First[row], {1 -> {2, 3}, 2 | 3 -> {3, 4}, 4 -> {3, 4, 5}, 5 -> {4}}]]]

VerificationTest[
	With[{data = savedData["arithmetic"]},
		{
			data["FormatVersion"],
			Developer`PackedArrayQ[data["Table"], Integer, 2],
			AllTrue[Range[Length[data["Table"]]], Function[row, AllTrue[rowParts[data["Table"][[row]]], Function[part, part < row && part != 0 && part >= -Length[data["Leaves"]]]]]]
		}
	],
	{2, True, True},
	TestID -> "Each-row-of-a-file-names-only-rows-before-it"
]

VerificationTest[
	{
		Information[TypeTheoryEnvironment[File[savedFile["arithmetic"]]], "Provenance"]["Checked"],
		Information[TypeTheoryEnvironment[File[savedFile["arithmetic"]], "Check" -> True], "Provenance"]["Checked"],
		Information[arithmetic, "Provenance"]["Checked"]
	},
	{False, True, True},
	TestID -> "Reading-a-file-is-not-checking-it-unless-asked"
]

VerificationTest[
	Export[savedFile["integers"], TypeTheoryEnvironment["Integers"]];
	With[{loaded = TypeTheoryEnvironment[File[savedFile["integers"]]], integers = TypeTheoryEnvironment["Integers"]},
		{Keys[loaded] === Keys[integers], AllTrue[Keys[integers], Function[name, loaded[name] === integers[name]]]}
	],
	{True, True},
	TestID -> "A-library-environment-saves-over-the-one-it-extends"
]

changedFile[data_Association] := With[{changed = savedFile["changed"]},
	BinaryWrite[changed, BinarySerialize[data]];
	Close[changed];
	{FailureQ[TypeTheoryEnvironment[File[changed]]], TypeTheoryEnvironment[File[changed]]["Tag"]}
]

VerificationTest[
	Module[{data = savedData["arithmetic"]},
		data["Table"] = Developer`ToPackedArray[Append[data["Table"], {1, Length[data["Table"]] + 5, 1, 0, 0}]];
		data["Depths"] = Developer`ToPackedArray[Append[data["Depths"], Max[data["Depths"]] + 1]];
		changedFile[data]
	],
	{True, "SavedEnvironmentInvalid"},
	TestID -> "A-file-whose-rows-were-changed-is-refused"
]

(* the rows are built a depth at a time, so a row must be deeper than each row it names *)
VerificationTest[
	Module[{data = savedData["arithmetic"]},
		data["Depths"] = Developer`ToPackedArray[ConstantArray[1, Length[data["Depths"]]]];
		changedFile[data]
	],
	{True, "SavedEnvironmentInvalid"},
	TestID -> "A-file-whose-depths-were-changed-is-refused"
]

VerificationTest[
	Module[{data = savedData["integers"]},
		data["Labels"] = ReplacePart[data["Labels"], First[FirstPosition[data["Labels"], HoldComplete[_], None, {1}]] -> 1];
		changedFile[data]
	],
	{True, "SavedEnvironmentInvalid"},
	TestID -> "A-file-whose-names-were-changed-is-refused"
]

(* a cubical system's row has a form of its own, which only the format of rows holds *)
VerificationTest[
	Export[savedFile["cubical"], TypeTheoryEnvironment["Cubical"]];
	With[{data = savedData["cubical"], loaded = TypeTheoryEnvironment[File[savedFile["cubical"]]]},
		{data["FormatVersion"], Count[data["Nodes"], {"c", _}] > 0, Normal[loaded] === Normal[TypeTheoryEnvironment["Cubical"]]}
	],
	{1, True, True},
	TestID -> "An-environment-with-cubical-systems-is-written-in-rows"
]

VerificationTest[
	Module[{data = savedData["cubical"]},
		data["Nodes"] = Append[data["Nodes"], {"a", WolframInstitute`TypeTheory`PackageScope`termRef[Length[data["Nodes"]] + 5], WolframInstitute`TypeTheory`PackageScope`termRef[1]}];
		changedFile[data]
	],
	{True, "SavedEnvironmentInvalid"},
	TestID -> "A-file-of-rows-whose-rows-were-changed-is-refused"
]

(* a file written from an unevaluated expression, with calls in a value and in a key: taking the data out of
   HoldComplete would make the calls, so reading the file must refuse it before *)
VerificationTest[
	Module[{carrying = savedFile["carrying"], calls = {}},
		Block[{carriedCall},
			SetAttributes[carriedCall, HoldAll];
			carriedCall[argument_] := AppendTo[calls, argument];
			BinaryWrite[carrying, BinarySerialize[Unevaluated[Association[
				"Format" -> "TypeTheoryEnvironment", "FormatVersion" -> 1, "KernelHash" -> "", "Rules" -> carriedCall[1], "Base" -> None,
				"Nodes" -> {}, "Names" -> {}, "Records" -> Association[carriedCall[2] -> 1], "NaturalNumbers" -> None, "RewriteRuleIndex" -> Association[], "Hash" -> ""
			]]]];
			Close[carrying];
			{TypeTheoryEnvironment[File[carrying]]["Tag"], calls}
		]
	],
	{"SavedEnvironmentInvalid", {}},
	TestID -> "A-file-that-carries-code-is-refused-without-running-it"
]

(* an annotation may hold a computation, as the evidence of a check, and reading it back runs nothing: not even an
   association it holds that is not made yet *)
VerificationTest[
	Module[{annotated = savedFile["annotated"], printed = {}, loaded},
		Export[annotated, Append[prelude, TypeTheoryTheorem[Annotated, 1 == 1, "equalityReflexivity"[1], "Annotation" -> <|"Check" -> HoldForm[Association[Print["evaluated while reading"]]]|>]]];
		Block[{Print = Function[Null, AppendTo[printed, {##}], HoldAll]},
			loaded = TypeTheoryEnvironment[File[annotated]]
		];
		{printed, Head[loaded], Information[TypeTheoryTerm[Annotated, loaded], "Annotation"]}
	],
	{{}, TypeTheoryEnvironment, <|"Check" -> HoldForm[Association[Print["evaluated while reading"]]]|>},
	TestID -> "A-computation-an-annotation-holds-does-not-run-when-the-file-is-read"
]

VerificationTest[
	Module[{again = Append[prelude, TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, "equalityReflexivity"[4]]]},
		Export[savedFile["again"], again];
		savedData["again"]["Hash"] === savedData["arithmetic"]["Hash"]
	],
	True,
	TestID -> "The-content-hash-is-the-same-for-the-same-declarations"
]

VerificationTest[
	Module[{data = savedData["arithmetic"], other = savedFile["other"]},
		data["KernelHash"] = "another kernel";
		BinaryWrite[other, BinarySerialize[data]];
		Close[other];
		{TypeTheoryEnvironment[File[other]]["Tag"], Keys[TypeTheoryEnvironment[File[other], "Check" -> True]] === Keys[arithmetic]}
	],
	{"SavedByAnotherKernel", True},
	TestID -> "A-file-of-another-kernel-reads-only-with-a-check"
]

(* whether a quotient is trusted is decided where the axiom closure asks, by its equations in the environment, so the
   closure is the same for an environment built, saved and read back, and read back with its declarations checked
   again: a projection registered as the quotient fails its equations and is named *)
VerificationTest[
	With[
		{
			lied = TypeTheoryEnvironment[prelude, {
				TypeTheoryDefinition[
					FirstNumber,
					Typed[Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, m], TypeSpecifier[{NonNegativeIntegers, NonNegativeIntegers} -> NonNegativeIntegers]]
				],
				TypeTheoryNaturalNumbers[NonNegativeIntegers, "zero", "successor", <|"Quotient" -> FirstNumber|>]
			}]
		},
		Export[savedFile["lied"], lied];
		Map[
			Function[environment, TypeTheoryAxiomClosure[TypeTheoryTerm[Typed["equalityReflexivity"[FirstNumber[2, 3]], FirstNumber[2, 3] == 0], environment]]],
			{lied, TypeTheoryEnvironment[File[savedFile["lied"]]], TypeTheoryEnvironment[File[savedFile["lied"]], "Check" -> True]}
		]
	],
	ConstantArray[<|FirstNumber -> "Registration"|>, 3],
	TestID -> "A-trusted-quotient-is-named-alike-before-and-after-saving"
]

DeleteDirectory[directory, DeleteContents -> True]

(* The hash that names the kernel which saved a file is of bytes, the version and a line for each source file, so every
   engine gives the same string for the same sources, where the hash of an expression is each engine's own: the value
   for a fixed input is pinned, whatever order the files are given in, and it is the SHA-256 of the text written out. *)
VerificationTest[
	{
		WolframInstitute`TypeTheory`PackageScope`kernelSourcesHash["1.2.3", {{"C.wl", "aa11"}, {"A/b.wl", "00ff"}}],
		WolframInstitute`TypeTheory`PackageScope`kernelSourcesHash["1.2.3", {{"A/b.wl", "00ff"}, {"C.wl", "aa11"}}],
		Hash[ByteArray[ToCharacterCode["1.2.3\n00ff A/b.wl\naa11 C.wl", "UTF-8"]], "SHA256", "HexString"],
		StringMatchQ[WolframInstitute`TypeTheory`PackageScope`$kernelHash, Repeated[HexadecimalCharacter, {64}]]
	},
	{
		"bba502f332594f612197512b36f7413d8db656c2c2704ee6b8a0869ab447ec4c",
		"bba502f332594f612197512b36f7413d8db656c2c2704ee6b8a0869ab447ec4c",
		"bba502f332594f612197512b36f7413d8db656c2c2704ee6b8a0869ab447ec4c",
		True
	},
	TestID -> "The-hash-of-the-kernels-sources-is-of-bytes-the-same-on-every-engine"
]
