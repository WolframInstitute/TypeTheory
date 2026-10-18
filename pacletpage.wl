(* ::Package:: *)

(* pacletpage.wl - what build_docs.wls and release.wls share: loading PacletPage
   (WolframInstitute/PacletPage) and the options TypeTheory is built and published with, kept
   in one place so the two scripts cannot drift apart. *)

$repoDirectory = DirectoryName[$InputFileName]

$pacletDirectory = FileNameJoin[{$repoDirectory, "TypeTheory"}]

$docsDirectory = FileNameJoin[{$repoDirectory, "docs", "paclet", "en"}]

(* The documentation site, and the paclet resource it is built around, belong to this account.
   PacletPage refuses to publish from a kernel connected as any other, and never connects by itself. *)

$siteAccount = "wolframinstitute@wolframinstitute.org"

$minimumPacletPage = "0.3.11"

$pacletPageResource = "https://www.wolframcloud.com/obj/wolframinstitute/DeployedResources/Paclet/WolframInstitute/PacletPage"

versionKey[version_String] := PadRight[FromDigits /@ StringCases[version, DigitCharacter ..], 3]

newEnoughQ[paclet_PacletObject] := Order[versionKey[paclet["Version"]], versionKey[$minimumPacletPage]] <= 0
newEnoughQ[_] := False

(* The newest PacletPage this machine has, with a checkout named by PACLETPAGE_DIR added to the
   candidates. Nothing is installed: a missing or older PacletPage stops the script with the line that
   installs the current release. *)

loadPacletPage[] := Module[{directory = Environment["PACLETPAGE_DIR"], paclet},
	If[ StringQ[directory],
		If[! DirectoryQ[directory], Print["FATAL: PACLETPAGE_DIR is not a directory: ", directory]; Exit[1]];
		PacletDirectoryLoad[directory]
	];
	paclet = First[PacletFind["WolframInstitute/PacletPage"], None];
	If[ ! newEnoughQ[paclet],
		Print["FATAL: PacletPage ", $minimumPacletPage, " or later is needed; this machine has ", If[paclet === None, "none", paclet["Version"]], ". Install it with"];
		Print["    PacletInstall[ResourceObject[\"", $pacletPageResource, "\"]]"];
		Print["or set PACLETPAGE_DIR to a PacletPage checkout."];
		Exit[1]
	];
	Needs["WolframInstitute`PacletPage`"];
	paclet["Version"]
]

$buildOptions = {"Source" -> $docsDirectory}

(* A build is good when every page converted and no section reads a name that only an earlier section
   gave a value. PacletPage keeps such a page out of its cache, so every build reports it until it is fixed. *)

checkBuild[result_] := Module[{unevaluated},
	If[! AssociationQ[result], Print["FATAL: BuildPacletDocumentation gave ", Short[result, 2]]; Exit[1]];
	Print["pages: ", Length[result["Notebooks"]], " (", Length[result["Evaluated"]], " evaluated, ", Length[result["Cached"]], " cached)   definition: ", result["Definition"]];
	If[ result["Failed"] =!= {},
		Print["FAILED: ", result["Failed"]];
		Exit[1]
	];
	unevaluated = Lookup[result, "Unevaluated", <||>];
	If[ Length[unevaluated] > 0,
		KeyValueMap[
			Function[{file, reports}, Print["UNEVALUATED ", FileNameTake[file], ": ", StringRiffle[Function[report, report["Heading"] <> " reads " <> StringRiffle[ToString /@ report["Symbols"], ", "]] /@ reports, "; "]]],
			unevaluated
		];
		Exit[1]
	]
]

(* The function is named in full: this file is read before PacletPage is loaded. *)

buildDocumentation[] := checkBuild[WolframInstitute`PacletPage`BuildPacletDocumentation[
	$pacletDirectory,
	Sequence @@ $buildOptions,
	Sequence @@ If[MemberQ[$ScriptCommandLine, "--no-cache"], {"UseCache" -> False}, {}]
]]

$resourceOptions = {}

(* Feedback sent through the site's form is readable by the site's owner, by signed-in
   wolframinstitute.org accounts, and by the readers listed. *)

$siteOptions = {
	"FeedbackOptions" -> {"Domains" -> {"wolframinstitute.org"}, "Readers" -> {"nikm@wolfram.com"}}
}
