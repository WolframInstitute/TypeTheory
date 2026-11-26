(* ::Package:: *)

(* Tests for Formats/EnvironmentFiles.wl: Format 3 environment files as the TTE format of Import and Export, registered
   with ImportExport`RegisterImport and ImportExport`RegisterExport when the paclet loads.
   Run with: wolframscript -f scripts/run_tests.wls TypeTheory/Tests/Formats/EnvironmentFiles.wlt *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

directory = CreateDirectory[]
formatFile[name_String] := FileNameJoin[{directory, name}]

prelude = TypeTheoryEnvironment["Prelude"]
preludeHash = Information[prelude, "Hash"]


VerificationTest[
	{MemberQ[$ImportFormats, "TTE"], MemberQ[$ExportFormats, "TTE"]},
	{True, True},
	TestID -> "TTE-is-a-format-of-Import-and-Export"
]

VerificationTest[
	With[{file = formatFile["prelude.tte"]},
		{
			Export[file, prelude, "TTE"] === file,
			Head[Import[file, "TTE"]],
			Information[Import[file, "TTE"], "Hash"] === preludeHash
		}
	],
	{True, TypeTheoryEnvironment, True},
	TestID -> "Export-and-Import-of-TTE-keep-the-environment"
]

VerificationTest[
	With[{file = formatFile["elements.tte"]},
		Export[file, prelude, "TTE"];
		{
			Import[file, {"TTE", "Hash"}] === preludeHash,
			Length[Import[file, {"TTE", "Constants"}]] === Length[Information[prelude, "Constants"]],
			SubsetQ[Import[file, {"TTE", "Elements"}], {"Constants", "Environment", "Hash"}]
		}
	],
	{True, True, True},
	TestID -> "The-elements-of-TTE"
]

(* Wolfram 15 takes a registered format by its name only: a .tte file and "FormatVersion" -> 3 name it *)
VerificationTest[
	{
		Export[formatFile["byextension.tte"], prelude] === formatFile["byextension.tte"],
		Information[Import[formatFile["byextension.tte"], "TTE"], "Hash"] === preludeHash,
		Export[formatFile["version3.wxf"], prelude, "FormatVersion" -> 3] === formatFile["version3.wxf"],
		Information[Import[formatFile["version3.wxf"], "TTE"], "Hash"] === preludeHash
	},
	{True, True, True, True},
	TestID -> "A-tte-file-and-FormatVersion-3-name-the-TTE-format"
]

VerificationTest[
	{
		WolframInstitute`TypeTheory`PackageScope`$environmentFileExportOptions === Keys[Options[WolframInstitute`TypeTheory`PackageScope`saveFormat3Environment]],
		Export[formatFile["statements.tte"], prelude, "TTE", "IncludeProofs" -> False] === formatFile["statements.tte"],
		Export[formatFile["full.tte"], prelude, "TTE"];
		FileByteCount[formatFile["statements.tte"]] < FileByteCount[formatFile["full.tte"]],
		Head[Import[formatFile["statements.tte"], "TTE"]]
	},
	{True, True, True, TypeTheoryEnvironment},
	TestID -> "The-export-options-of-TTE-are-those-of-the-writer"
]

(* a file whose header is forged is refused: Import gives $Failed, as for any failing converter, and the reader gives
   the Failure that says why *)
VerificationTest[
	With[{file = formatFile["forged.tte"]},
		Export[formatFile["source.tte"], prelude, "TTE"];
		With[{bytes = ReadByteArray[formatFile["source.tte"]], stream = OpenWrite[file, BinaryFormat -> True]},
			BinaryWrite[stream, Join[ByteArray[ConstantArray[0, 64]], Drop[bytes, 64]]];
			Close[stream]
		];
		{Quiet[Import[file, "TTE"]], FailureQ[TypeTheoryEnvironment[File[file]]]}
	],
	{$Failed, True},
	TestID -> "A-forged-tte-file-is-refused-through-Import"
]

VerificationTest[
	Quiet[Export[formatFile["notanenvironment.tte"], 1 + 1, "TTE"]],
	$Failed,
	TestID -> "Only-an-environment-exports-as-TTE"
]

DeleteDirectory[directory, DeleteContents -> True]
