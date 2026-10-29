(* ::Package:: *)

(*
Saved environments: an environment written to a file, and read back without checking its declarations again.

Export["file.wxf", environment] writes the environment, and TypeTheoryEnvironment[File["file.wxf"]] reads it back. A
file holds each term once, as Lean's .olean files do: the distinct composite subterms of the records, each in a row
of a table after the rows of its parts, a part being termRef[row], and the records with termRef[row] for each term.
The library environments share their records with the environments built on them, so a file stores only the
records beyond the largest library environment it extends, its base, which it names:

	"Format"              "TypeTheoryEnvironment"
	"FormatVersion"       1
	"TypeTheoryVersion"   the version of the paclet that wrote the file
	"KernelHash"          SHA-256 of the paclet's version and kernel sources: a file reads fast only into the kernel that wrote it
	"Host"                <|"VersionNumber", "ReleaseNumber", "Version"|> of the session that wrote it, for the record
	"Rules"               the TypeTheoryRules
	"Base"                None, or <|"Name" -> name, "Hash" -> content hash|> of the library environment it extends
	"Nodes"               {node, ...}: {"a", f, a}, {"l", name, domain, body, binder}, {"p", name, domain, codomain, binder},
	                      {"d", name, type, value, body}, {"j", structure, index, term}, {"c", {{face, term}, ...}}
	"Names", "Records"    the constants beyond the base, in the order they were declared
	"NaturalNumbers", "RewriteRuleIndex"
	"Hash"                the content hash: SHA-256 of all the environment's contents, base included, as the file would hold
	                      them with no base. An environment built the same way has the same hash in every session; terms
	                      keep the names of their binders for display, so the same declarations written differently, as
	                      Normal writes a function type without its binder's name, can give an equal environment whose
	                      hash differs

Reading a file is a convenience, not a check: its records are taken as the file has them, as Lean takes an .olean.
TypeTheoryEnvironment[File[...], "Check" -> True] reads the file and then replays every declaration with
TypeTheoryCheck, as lean4checker replays an environment, and it is how to read a file another kernel wrote. The
file is read held, with BinaryDeserialize[bytes, HoldComplete], and nothing in it evaluates: before any term is
built, every row must name earlier rows only, and the records, names and settings may hold only core terms and
inert data, so that no code a file carries can run.

The paclet's own library environments are saved in its Environments directory when it is released, and read
from there when they are first asked for if the kernel that wrote them is the one loading them; otherwise they
are built and checked as before. The environment variable TYPETHEORY_SAVED_ENVIRONMENTS=0 makes a session build
them always, as scripts/environment_hashes.wls does to compare the files with what building gives.
*)


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[libraryEnvironment]
PackageScoped[saveEnvironment]
PackageScoped[environmentProvenance]
PackageScoped[environmentContentHash]
PackageScoped[$kernelHash]
PackageScoped[termRef]


(* ::Section:: *)
(*Usage Messages*)


libraryEnvironment::usage = "libraryEnvironment[name, base, build] gives the library environment name, read from the paclet's Environments \
directory over the environment base if this kernel wrote the file there, and otherwise the value of build, marked as the library name."
environmentProvenance::usage = "environmentProvenance[environment] gives where environment came from: its declarations, checked, or a file."
saveEnvironment::usage = "saveEnvironment[file, environment] writes environment to file and gives File[file]."
environmentContentHash::usage = "environmentContentHash[environment] gives the content hash of environment, the same in every session."
$kernelHash::usage = "$kernelHash is the SHA-256 of the paclet's version and kernel sources, which a saved environment records."
termRef::usage = "termRef[row] stands in a saved environment for the term of a row of its table."


(* ::Section:: *)
(*Function Definitions*)


$formatVersion = 1

$pacletDirectory = ParentDirectory[DirectoryName[$InputFileName], 2]

(* FileHash reads each file itself: ReadByteArray would read FinalEvaluations.wl, which is being loaded when the prelude
   is read, from where the loader's open stream has got to *)
$kernelHash := $kernelHash = Hash[
	{
		PacletObject[File[$pacletDirectory]]["Version"],
		Map[{FileNameDrop[#, FileNameDepth[$pacletDirectory]], FileHash[#, "SHA256", All, "HexString"]}&, Sort[FileNames["*.wl", FileNameJoin[{$pacletDirectory, "Kernel"}], Infinity]]]
	},
	"SHA256",
	"HexString"
]


(* ::Subsection:: *)
(*Writing*)


TypeTheoryEnvironment /: Export[file : (_String | File[_String]), environment : TypeTheoryEnvironment[_Symbol]?environmentQ] /; ToLowerCase[FileExtension[file]] === "wxf" :=
	saveEnvironment[Replace[file, File[path_] :> path], environment]
TypeTheoryEnvironment /: Export[file : (_String | File[_String]), environment : TypeTheoryEnvironment[_Symbol]?environmentQ, "WXF"] :=
	saveEnvironment[Replace[file, File[path_] :> path], environment]

saveEnvironment[file_String, environment_] := catchKernelFailure @ Block[{saveBase = environmentBase[environment], saveContents, saveStream},
	saveContents = environmentContents[environment, saveBase];
	saveStream = OpenWrite[file, BinaryFormat -> True];
	BinaryWrite[saveStream, BinarySerialize[
		Join[
			<|
				"Format" -> "TypeTheoryEnvironment",
				"FormatVersion" -> $formatVersion,
				"TypeTheoryVersion" -> PacletObject[File[$pacletDirectory]]["Version"],
				"KernelHash" -> $kernelHash,
				"Host" -> <|"VersionNumber" -> $VersionNumber, "ReleaseNumber" -> $ReleaseNumber, "Version" -> $Version|>,
				"Base" -> Replace[saveBase, {None -> None, {name_, base_} :> <|"Name" -> name, "Hash" -> environmentContentHash[base]|>}]
			|>,
			saveContents,
			<|"Hash" -> environmentContentHash[environment]|>
		],
		PerformanceGoal -> "Size"
	]];
	Close[saveStream];
	File[file]
]

(* the nearest library environment whose records environment's begin with, as {name, environment}, or None *)
environmentBase[TypeTheoryEnvironment[store_Symbol]] := Replace[store["Library"], {
	library_Symbol /; StringQ[library["LibraryName"]] :> {library["LibraryName"], TypeTheoryEnvironment[library]},
	_ -> None
}]

(* the contents of environment beyond base, its terms in a table of rows, sown as they are made *)
environmentContents[environment : TypeTheoryEnvironment[store_Symbol], base_] := Block[
	{$nodeIndex = <||>, $nodeCount = 0, contentNames, contentRecords, contentNodes},
	contentNames = Drop[environmentNames[environment], Replace[base, {None -> 0, {_, baseEnvironment_} :> Length[environmentNames[baseEnvironment]]}]];
	{contentRecords, contentNodes} = Reap[AssociationMap[Function[name, recordRefs[constantRecord[environment, name]]], contentNames], $nodeTag];
	<|
		"Rules" -> environmentRules[environment],
		"Nodes" -> Replace[contentNodes, {{nodes_List} :> nodes, {} -> {}}],
		"Names" -> contentNames,
		"Records" -> contentRecords,
		"NaturalNumbers" -> store["NaturalNumbers"],
		"RewriteRuleIndex" -> store["RewriteRuleIndex"]
	|>
]

(* the hash of all of an environment's contents, the same in every session for an environment built the same way *)
environmentContentHash[environment : TypeTheoryEnvironment[store_Symbol]] := Replace[
	store["ContentHash"],
	_store :> (store["ContentHash"] = Hash[BinarySerialize[environmentContents[environment, None]], "SHA256", "HexString"])
]

compositeTermQ[_application | _lambdaAbstraction | _dependentFunctionType | _localDefinition | _projection | _cubicalSystem] := True
compositeTermQ[_] := False

recordRefs[record_Association] := Map[valueRefs, record]
valueRefs[value_] := Which[
	compositeTermQ[value], termRef[nodeRow[value]],
	AssociationQ[value], Map[valueRefs, value],
	ListQ[value], Map[valueRefs, value],
	True, value
]

(* the row of a composite term, its own added after the rows of its parts *)
nodeRow[term_] := Lookup[$nodeIndex, Key[term], addNode[term]]
addNode[term_] := Block[{node = termNode[term]}, Sow[node, $nodeTag]; $nodeIndex[term] = ++$nodeCount]

part[term_] := If[compositeTermQ[term], termRef[nodeRow[term]], term]

termNode[application[function_, argument_]] := {"a", part[function], part[argument]}
termNode[lambdaAbstraction[name_, domain_, body_, binder_]] := {"l", name, part[domain], part[body], binder}
termNode[dependentFunctionType[name_, domain_, codomain_, binder_]] := {"p", name, part[domain], part[codomain], binder}
termNode[localDefinition[name_, type_, value_, body_]] := {"d", name, part[type], part[value], part[body]}
termNode[projection[structure_, index_, term_]] := {"j", structure, index, part[term]}
termNode[cubicalSystem[branches_List]] := {"c", Map[part, branches, {2}]}


(* ::Subsection:: *)
(*Reading*)


Options[loadEnvironment] = {"Check" -> False}

TypeTheoryEnvironment[File[file_String], options : OptionsPattern[loadEnvironment]] := withStoreCleanup @ catchKernelFailure @ loadEnvironment[
	ExpandFileName[file],
	OptionValue[loadEnvironment, {options}, "Check"]
]

loadEnvironment[file_String, check_] := Block[{loadData = readEnvironmentFile[file], loadBase, loaded},
	If[ loadData["KernelHash"] =!= $kernelHash && ! TrueQ[check],
		kernelFailure[
			"SavedByAnotherKernel",
			"`1` was saved by TypeTheory `2`, whose kernel differs from this one; read it with \"Check\" -> True to check its `3` constants again.",
			{file, loadData["TypeTheoryVersion"], Length[loadData["Names"]]}
		]
	];
	loadBase = Replace[loadData["Base"], {None :> emptyEnvironmentOf[loadData["Rules"]], KeyValuePattern["Name" -> name_String] :> TypeTheoryEnvironment[name]}];
	If[ ! environmentQ[loadBase] || environmentRules[loadBase] =!= loadData["Rules"],
		kernelFailure["SavedEnvironmentBase", "`1` extends the environment `2`, which this TypeTheory does not have.", {file, loadData["Base"]["Name"]}]
	];
	loaded = environmentFromContents[loadBase, loadData, File[file]];
	If[ TrueQ[check],
		Replace[TypeTheoryCheck[loaded], failure_Failure :> throwFailure[failure]];
		With[{loadedStore = First[loaded]}, loadedStore["Provenance"] = Append[loadedStore["Provenance"], "Checked" -> True]]
	];
	loaded
]

(* A library environment of the paclet: read over base from the file the release saved, if this kernel wrote it and
   it extends base, and otherwise built; either way marked with its name, which the environments built on it record. *)
SetAttributes[libraryEnvironment, HoldRest]
libraryEnvironment[name_String, base_, build_] := Block[{libraryResult = Replace[savedLibraryEnvironment[name, base], None :> build]},
	With[{libraryStore = First[libraryResult]}, libraryStore["LibraryName"] = name];
	libraryResult
]

environmentProvenance[TypeTheoryEnvironment[store_Symbol]] := Replace[store["Provenance"], _store :> <|"Source" -> "Declarations", "Checked" -> True|>]

savedLibraryEnvironment[name_String, base_] := Quiet @ Block[{libraryFile = FileNameJoin[{$pacletDirectory, "Environments", name <> ".wxf"}], libraryData},
	If[ ! FileExistsQ[libraryFile] || Environment["TYPETHEORY_SAVED_ENVIRONMENTS"] === "0", Return[None, Block]];
	libraryData = catchKernelFailure[readEnvironmentFile[libraryFile]];
	If[ ! AssociationQ[libraryData] || libraryData["KernelHash"] =!= $kernelHash || libraryData["Rules"] =!= environmentRules[base], Return[None, Block]];
	If[ Lookup[Replace[libraryData["Base"], None -> <||>], "Name", None] =!= Replace[First[base]["LibraryName"], Except[_String] -> None], Return[None, Block]];
	Replace[catchKernelFailure[environmentFromContents[base, libraryData, File[libraryFile]]], _Failure -> None]
]

(* the file's data, read held and checked to be inert before anything in it is used *)
readEnvironmentFile[file_String] := Block[{fileBytes = Quiet[ReadByteArray[file]], fileData},
	If[ ! ByteArrayQ[fileBytes], kernelFailure["SavedEnvironmentUnreadable", "`1` cannot be read.", {file}]];
	fileData = Quiet[BinaryDeserialize[fileBytes, HoldComplete]];
	If[ ! MatchQ[fileData, HoldComplete[_Association]] || ! savedDataQ[First[fileData]],
		kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {file}]
	];
	First[fileData]
]

savedDataQ[data_Association] := And[
	SubsetQ[Keys[data], {"Format", "FormatVersion", "KernelHash", "Rules", "Base", "Nodes", "Names", "Records", "NaturalNumbers", "RewriteRuleIndex", "Hash"}],
	data["Format"] === "TypeTheoryEnvironment",
	data["FormatVersion"] === $formatVersion,
	rulesQ[data["Rules"]],
	MatchQ[data["Base"], None | KeyValuePattern[{"Name" -> _String, "Hash" -> _String}]],
	ListQ[data["Nodes"]] && AllTrue[Range[Length[data["Nodes"]]], Function[row, nodeQ[data["Nodes"][[row]], row]]],
	ListQ[data["Names"]] && AllTrue[data["Names"], nameQ],
	AssociationQ[data["Records"]] && Keys[data["Records"]] === data["Names"],
	AllTrue[Values[data["Records"]], Function[record, recordQ[record, Length[data["Nodes"]] + 1]]],
	inertQ[data["NaturalNumbers"], 1] && inertQ[data["RewriteRuleIndex"], 1]
]
savedDataQ[_] := False

nodeQ[{"a", function_, argument_}, row_] := partQ[function, row] && partQ[argument, row]
nodeQ[{"l" | "p", name_, domain_, body_, binder_}, row_] := nameQ[name] && partQ[domain, row] && partQ[body, row] && binderQ[binder]
nodeQ[{"d", name_, type_, value_, body_}, row_] := nameQ[name] && partQ[type, row] && partQ[value, row] && partQ[body, row]
nodeQ[{"j", structure_, index_Integer?NonNegative, term_}, row_] := nameQ[structure] && partQ[term, row]
nodeQ[{"c", branches : {{_, _} ...}}, row_] := AllTrue[Flatten[branches, 1], Function[branch, partQ[branch, row]]]
nodeQ[_, _] := False

partQ[termRef[reference_Integer], row_] := 1 <= reference < row
partQ[leaf_, _] := leafTermQ[leaf]

leafTermQ[boundVariable[_Integer?NonNegative] | naturalLiteral[_Integer?NonNegative] | intervalUniverse[]] := True
leafTermQ[universeSort[level_]] := levelQ[level]
leafTermQ[constantReference[name_, levels_List]] := nameQ[name] && AllTrue[levels, levelQ]
leafTermQ[_] := False

levelQ[_Integer?NonNegative] := True
levelQ[levelParameter[name_]] := nameQ[name]
levelQ[levelSuccessor[level_, _Integer?Positive]] := levelQ[level]
levelQ[levelMaximum[levels___]] := AllTrue[{levels}, levelQ]
levelQ[levelImpredicativeMaximum[first_, second_]] := levelQ[first] && levelQ[second]
levelQ[_] := False

nameQ[HoldComplete[_Symbol | _String]] := True
nameQ[HoldComplete[InductiveRecursor[_Symbol | _String, ___Integer]]] := True
nameQ[_] := False

binderQ["Explicit" | "Implicit" | "StrictImplicit" | "InstanceImplicit"] := True
binderQ[{"Explicit" | "Implicit" | "StrictImplicit" | "InstanceImplicit", 0 | 1}] := True
binderQ[_] := False

recordQ[record_Association, rows_] := And[
	MemberQ[{"Axiom", "Definition", "Opaque", "Theorem", "InductiveType", "Constructor", "Recursor", "RewriteRule", "Quotient", "Cubical"}, record["Kind"]],
	inertQ[record, rows]
]
recordQ[_, _] := False

(* data that holds nothing that could evaluate: strings, numbers, names, levels, core leaves and terms by row *)
inertQ[_String | _Integer | True | False | None | Infinity, _] := True
inertQ[termRef[reference_Integer], rows_] := 1 <= reference < rows
inertQ[list_List, rows_] := AllTrue[list, Function[element, inertQ[element, rows]]]
inertQ[association_Association, rows_] := AllTrue[Keys[association], Function[key, inertQ[key, rows]]] && AllTrue[Values[association], Function[value, inertQ[value, rows]]]
inertQ[value_, _] := nameQ[value] || levelQ[value] || leafTermQ[value]

(* the environment of base extended with the file's constants, its terms built once from their rows *)
environmentFromContents[base : TypeTheoryEnvironment[baseStore_Symbol], data_Association, source_] := Block[
	{$rowTerms = rowTerms[data["Nodes"]], loadedRecords, loadedEnvironment},
	loadedRecords = Map[termsFromRefs, data["Records"]];
	loadedEnvironment = addConstantRecords[base, loadedRecords];
	With[{loadedStore = First[loadedEnvironment]},
		loadedStore["NaturalNumbers"] = data["NaturalNumbers"];
		loadedStore["RewriteRuleIndex"] = data["RewriteRuleIndex"];
		loadedStore["Provenance"] = <|"Source" -> source, "Hash" -> data["Hash"], "Checked" -> False|>
	];
	loadedEnvironment
]

(* Each row's term, built from the terms of the rows before it, kept in an Association by row: on W15, a list filled
   in place costs its length at each row whose term holds earlier rows of the same list, whatever filled it first,
   which made the rows cost the square of their number. *)
rowTerms[nodes_List] := Block[{$rows = <||>},
	Do[$rows[row] = rowNodeTerm[nodes[[row]]], {row, Length[nodes]}];
	Values[$rows]
]

(* the terms for the rows a value names, mapped so that each comes out evaluated, inside the Block of $rowTerms *)
termsFromRefs[termRef[reference_Integer]] := $rowTerms[[reference]]
termsFromRefs[association_Association] := Map[termsFromRefs, association]
termsFromRefs[list_List] := Map[termsFromRefs, list]
termsFromRefs[other_] := other

rowPart[termRef[reference_Integer]] := $rows[reference]
rowPart[leaf_] := leaf

rowNodeTerm[{"a", function_, argument_}] := Construct[application, rowPart[function], rowPart[argument]]
rowNodeTerm[{"l", name_, domain_, body_, binder_}] := Construct[lambdaAbstraction, name, rowPart[domain], rowPart[body], binder]
rowNodeTerm[{"p", name_, domain_, codomain_, binder_}] := Construct[dependentFunctionType, name, rowPart[domain], rowPart[codomain], binder]
rowNodeTerm[{"d", name_, type_, value_, body_}] := Construct[localDefinition, name, rowPart[type], rowPart[value], rowPart[body]]
rowNodeTerm[{"j", structure_, index_, term_}] := Construct[projection, structure, index, rowPart[term]]
rowNodeTerm[{"c", branches_}] := Construct[cubicalSystem, Map[rowPart, branches, {2}]]
