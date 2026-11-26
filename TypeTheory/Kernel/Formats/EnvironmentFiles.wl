(* ::Package:: *)

(*
EnvironmentFiles: the TTE format of Import and Export, outside Checking/, whose files are all trusted sources.

A Format 3 environment file (.tte, read and written in LazyEnvironments.wl) is a format of Import and Export: loading
the paclet registers its converters with the framework's own functions, ImportExport`RegisterImport and
ImportExport`RegisterExport, as Wolfram's formats are registered:

	Import[file, "TTE"]                   the environment the file holds, read lazily
	Import[file, {"TTE", element}]        the element "Environment", "Constants" or "Hash"
	Export[file, environment, "TTE"]      the environment written, with the options of saveFormat3Environment

This file decides nothing: Import reads with TypeTheoryEnvironment[File[file]], which checks the file's header and
the hash of every block it reads, and refuses a forged file, so it stays outside $trustedSources. Wolfram 15 takes a
registered format by its name, not by the extension of a file (it keeps the extensions it is given and reads none), so
Export["x.tte", environment] reaches the converter through the rule of SavedEnvironments.wl that names the format.
*)


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[importEnvironmentFile]
PackageScoped[exportEnvironmentFile]
PackageScoped[environmentElement]
PackageScoped[$environmentFileExportOptions]


(* ::Section:: *)
(*Usage Messages*)


importEnvironmentFile::usage = "importEnvironmentFile[file, options] is the import converter of the TTE format: the rules of the environment file holds, or $Failed."
exportEnvironmentFile::usage = "exportEnvironmentFile[file, environment, options] is the export converter of the TTE format: it writes environment to file in \
Format 3 and gives file, or $Failed."
environmentElement::usage = "environmentElement[property][rules, options] is the element property of the TTE format: Information of the environment in \
the rules an import gave."
$environmentFileExportOptions::usage = "$environmentFileExportOptions are the options Export takes for the TTE format, those of saveFormat3Environment."


(* ::Section:: *)
(*Definitions*)


(* the names of the options of saveFormat3Environment, written out since this file may load before LazyEnvironments.wl *)
$environmentFileExportOptions = {"IncludeProofs", "IncludeDependencies", "Standalone", "BlockSizes"}

(* Import and Export read a converter's failure only as $Failed, so a converter fails as Wolfram's own do, with the
   framework's message and $Failed; TypeTheoryEnvironment[File[file]] gives the Failure that says why *)
importEnvironmentFile[file_String, ___] := Replace[TypeTheoryEnvironment[File[file]], {
	environment_?environmentQ :> {"Environment" -> environment},
	_ :> (Message[Import::fmterr, "TTE"]; $Failed)
}]

environmentElement[property_String][rules_List, ___] := Replace[
	Lookup[rules, "Environment", $Failed],
	environment_?environmentQ :> Information[environment, property]
]

exportEnvironmentFile[file_String, environment_?environmentQ, options___] := Replace[
	saveFormat3Environment[file, environment, FilterRules[{options}, $environmentFileExportOptions]],
	{File[_] :> file, _ :> $Failed}
]
(* Export hands the converter its expression as the default element, "Environment" :> environment *)
exportEnvironmentFile[file_String, (Rule | RuleDelayed)["Environment", environment_], options___] := exportEnvironmentFile[file, environment, options]
exportEnvironmentFile[_, value_, ___] := (Message[Export::type, Head[value], "TTE"]; $Failed)

ImportExport`RegisterImport["TTE", importEnvironmentFile,
	{"Constants" -> environmentElement["Constants"], "Hash" -> environmentElement["Hash"]},
	"AvailableElements" -> {"Environment", "Constants", "Hash"},
	"DefaultElement" -> "Environment",
	"BinaryFormat" -> True,
	"Extensions" -> {"*.tte"}
]

ImportExport`RegisterExport["TTE", exportEnvironmentFile,
	"DefaultElement" -> "Environment",
	"BinaryFormat" -> True,
	"Options" -> $environmentFileExportOptions,
	"Extensions" -> {"*.tte"}
]
