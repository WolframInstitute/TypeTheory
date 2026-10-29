(* ::Package:: *)

(* Tests for saved environments: Export["file.wxf", environment] writes an environment, and
   TypeTheoryEnvironment[File["file.wxf"]] reads it back without checking its declarations again.
   Run with: TestReport["TypeTheory/Tests/Checking/SavedEnvironments.wlt"] from the repository root. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

directory = CreateDirectory[]

savedFile[name_String] := FileNameJoin[{directory, name <> ".wxf"}]

prelude = TypeTheoryEnvironment["Prelude"]

arithmetic = Append[prelude, TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, EqualityReflexivity[4]]]

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

VerificationTest[
	With[{data = savedData["arithmetic"]},
		AllTrue[
			Range[Length[data["Nodes"]]],
			Function[row, AllTrue[Cases[data["Nodes"][[row]], WolframInstitute`TypeTheory`PackageScope`termRef[reference_] :> reference, Infinity], Function[reference, reference < row]]]
		]
	],
	True,
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

VerificationTest[
	Module[{data = savedData["arithmetic"], changed},
		data["Nodes"] = Append[data["Nodes"], {"a", WolframInstitute`TypeTheory`PackageScope`termRef[Length[data["Nodes"]] + 5], WolframInstitute`TypeTheory`PackageScope`termRef[1]}];
		changed = savedFile["changed"];
		BinaryWrite[changed, BinarySerialize[data]];
		Close[changed];
		{FailureQ[TypeTheoryEnvironment[File[changed]]], TypeTheoryEnvironment[File[changed]]["Tag"]}
	],
	{True, "SavedEnvironmentInvalid"},
	TestID -> "A-file-whose-rows-were-changed-is-refused"
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

VerificationTest[
	Module[{again = Append[prelude, TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, EqualityReflexivity[4]]]},
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

DeleteDirectory[directory, DeleteContents -> True]
