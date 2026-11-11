(* ::Package:: *)

(*
Saved environments: an environment written to a file, and read back without checking its declarations again.

Export["file.wxf", environment] writes the environment, and TypeTheoryEnvironment[File["file.wxf"]] reads it back. A
file holds each term once: the distinct composite subterms of the records, each in a row
of a table after the rows of its parts, a part being termRef[row], and the records with termRef[row] for each term.
The library environments share their records with the environments built on them, so a file stores only the
records beyond the largest library environment it extends, its base, which it names:

	"Format"              "TypeTheoryEnvironment"
	"FormatVersion"       2, or 1 for an environment with a cubical system, whose table is "Nodes"
	"TypeTheoryVersion"   the version of the paclet that wrote the file
	"KernelHash"          SHA-256 of the paclet's version and kernel sources: a file reads fast only into the kernel that wrote it
	"Host"                <|"VersionNumber", "ReleaseNumber", "Version"|> of the session that wrote it, for the record
	"Rules"               the TypeTheoryRules
	"Base"                None, or <|"Name" -> name, "Hash" -> content hash|> of the library environment it extends
	"Table"               format 2: a packed array of the rows, five integers each, {code, x, y, z, w}: {1, f, a, 0, 0},
	                      {2, name, domain, body, binder} for a function, {3, name, domain, codomain, binder} for a function
	                      type, {4, name, type, value, body}, {5, structure, index, term, 0}; a part is the position of an
	                      earlier row, or a leaf's position in "Leaves", negated, and a name, structure or binder its
	                      position in "Labels"
	"Depths"              format 2: a packed array of each row's depth, one more than its deepest row part's
	"Leaves", "Labels"    format 2: the distinct leaf terms, and the names and binders, the rows name
	"Nodes"               format 1: {node, ...}: {"a", f, a}, {"l", name, domain, body, binder}, {"p", name, domain,
	                      codomain, binder}, {"d", name, type, value, body}, {"j", structure, index, term}, {"c", {{face,
	                      term}, ...}}, a part being termRef[row] or a leaf
	"Names", "Records"    the constants beyond the base, in the order they were declared
	"NaturalNumbers", "RewriteRuleIndex"
	"Hash"                the content hash: SHA-256 of all the environment's contents, base included, as the file would hold
	                      them with no base. An environment built the same way has the same hash in every session; terms
	                      keep the names of their binders for display, so the same declarations written differently, as
	                      Normal writes a function type without its binder's name, can give an equal environment whose
	                      hash differs

Reading a file is a convenience, not a check: its records are taken as the file has them.
TypeTheoryEnvironment[File[...], "Check" -> True] reads the file and then replays every declaration with
TypeTheoryCheck, as lean4checker replays an environment, and it is how to read a file another kernel wrote. The
file is read held, with BinaryDeserialize[bytes, HoldComplete], and nothing in it evaluates before it is checked:
every symbol it holds outside HoldComplete and HoldForm, keys included, must be one of those a saved environment is
written with, its packed integer arrays aside, and then every row must name earlier rows only, every name must be a
name, and the records and settings may hold only core terms and inert data, and annotations only data, so that no
code a file carries can run. Format 2 is that of tables: the rows are checked at once, as integers, and their terms
built a depth at a time, where a file of format 1, still read, has each row checked and built on its own.

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
PackageScoped[kernelSourcesHash]
PackageScoped[termRef]


(* ::Section:: *)
(*Usage Messages*)


libraryEnvironment::usage = "libraryEnvironment[name, base, build] gives the library environment name, read from the paclet's Environments \
directory over the environment base if this kernel wrote the file there, and otherwise the value of build, marked as the library name."
environmentProvenance::usage = "environmentProvenance[environment] gives where environment came from: its declarations, checked, or a file."
saveEnvironment::usage = "saveEnvironment[file, environment] writes environment to file and gives File[file]."
environmentContentHash::usage = "environmentContentHash[environment] gives the content hash of environment, the same in every session."
$kernelHash::usage = "$kernelHash is the SHA-256 of the paclet's version and kernel sources, which a saved environment records."
kernelSourcesHash::usage = "kernelSourcesHash[version, {{path, hash}, ...}] gives the SHA-256, in hexadecimal digits, of the bytes of the version and a line for each source file, its hash and its path: the same string on every engine."
termRef::usage = "termRef[row] stands in a saved environment for the term of a row of its table."


(* ::Section:: *)
(*Function Definitions*)


$formatVersion = 2

$pacletDirectory = ParentDirectory[DirectoryName[$InputFileName], 2]

(* FileHash reads each file itself: ReadByteArray would read FinalEvaluations.wl, which is being loaded when the prelude
   is read, from where the loader's open stream has got to. A path is written with /, whatever the system's separator. *)
$kernelHash := $kernelHash = kernelSourcesHash[
	PacletObject[File[$pacletDirectory]]["Version"],
	Map[
		Function[file, {StringRiffle[FileNameSplit[FileNameDrop[file, FileNameDepth[$pacletDirectory]]], "/"], FileHash[file, "SHA256", All, "HexString"]}],
		FileNames["*.wl", FileNameJoin[{$pacletDirectory, "Kernel"}], Infinity]
	]
]

(* The hash is of bytes. The hash of an expression is each engine's own, and with it a file saved on one engine read on
   another as saved by another kernel, to be checked again. The bytes are the version and a line for each file, its hash
   and then its path, the lines in order: they begin with hexadecimal digits, as many in each, and on those every
   ordering of strings agrees. *)
kernelSourcesHash[version_String, files_List] := Hash[
	ByteArray[ToCharacterCode[StringRiffle[Prepend[Sort[Map[Function[file, Last[file] <> " " <> First[file]], files]], version], "\n"], "UTF-8"]],
	"SHA256",
	"HexString"
]


(* ::Subsection:: *)
(*Writing*)


TypeTheoryEnvironment /: Export[file : (_String | File[_String]), environment : TypeTheoryEnvironment[_Symbol]?environmentQ] /; ToLowerCase[FileExtension[file]] === "wxf" :=
	saveEnvironment[Replace[file, File[path_] :> path], environment]
TypeTheoryEnvironment /: Export[file : (_String | File[_String]), environment : TypeTheoryEnvironment[_Symbol]?environmentQ, "WXF"] :=
	saveEnvironment[Replace[file, File[path_] :> path], environment]

saveEnvironment[file_String, environment_] := catchKernelFailure @ Block[{saveBase = environmentBase[environment], saveContents, fileContents, saveStream},
	saveContents = environmentContents[environment, saveBase];
	(* with no base, the contents are those the content hash is taken of *)
	If[saveBase === None, rememberContentHash[environment, saveContents]];
	fileContents = packedContents[saveContents];
	saveStream = OpenWrite[file, BinaryFormat -> True];
	BinaryWrite[saveStream, BinarySerialize[
		Join[
			<|
				"Format" -> "TypeTheoryEnvironment",
				"FormatVersion" -> fileContents["FormatVersion"],
				"TypeTheoryVersion" -> PacletObject[File[$pacletDirectory]]["Version"],
				"KernelHash" -> $kernelHash,
				"Host" -> <|"VersionNumber" -> $VersionNumber, "ReleaseNumber" -> $ReleaseNumber, "Version" -> $Version|>,
				"Base" -> Replace[saveBase, {None -> None, {name_, base_} :> <|"Name" -> name, "Hash" -> environmentContentHash[base]|>}]
			|>,
			KeyDrop[fileContents, "FormatVersion"],
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

rememberContentHash[TypeTheoryEnvironment[store_Symbol], contents_Association] :=
	If[! StringQ[store["ContentHash"]], store["ContentHash"] = Hash[BinarySerialize[contents], "SHA256", "HexString"]]

(* The contents in the table form of format 2, the rows as integers with the leaves and labels they name, each row's depth
   worked out; the content hash is still taken of the nodes. A cubical system's row has a form of its own, which only
   format 1 holds. *)
packedContents[contents_Association] := Block[{packedLabels = <||>, packedLeaves = <||>, packedRows},
	If[ MemberQ[contents["Nodes"], {"c", _}],
		Append[contents, "FormatVersion" -> 1],
		packedRows = packedRow /@ contents["Nodes"];
		Join[
			KeyDrop[contents, "Nodes"],
			<|
				"FormatVersion" -> $formatVersion,
				"Leaves" -> Keys[packedLeaves],
				"Labels" -> Keys[packedLabels],
				"Table" -> Developer`ToPackedArray[packedRows],
				"Depths" -> Developer`ToPackedArray[rowDepths[packedRows]]
			|>
		]
	]
]

packedRow[{"a", function_, argument_}] := {1, packedPart[function], packedPart[argument], 0, 0}
packedRow[{"l", name_, domain_, body_, binder_}] := {2, packedLabel[name], packedPart[domain], packedPart[body], packedLabel[binder]}
packedRow[{"p", name_, domain_, codomain_, binder_}] := {3, packedLabel[name], packedPart[domain], packedPart[codomain], packedLabel[binder]}
packedRow[{"d", name_, type_, value_, body_}] := {4, packedLabel[name], packedPart[type], packedPart[value], packedPart[body]}
packedRow[{"j", structure_, index_, term_}] := {5, packedLabel[structure], index, packedPart[term], 0}

packedPart[termRef[row_Integer]] := row
packedPart[leaf_] := -Lookup[packedLeaves, Key[leaf], packedLeaves[leaf] = Length[packedLeaves] + 1]

packedLabel[label_] := Lookup[packedLabels, Key[label], packedLabels[label] = Length[packedLabels] + 1]

rowDepths[rows_List] := Block[{computedDepths = ConstantArray[0, Length[rows]]},
	Do[computedDepths[[row]] = 1 + Max[0, computedDepths[[Select[rowParts[rows[[row]]], Positive]]]], {row, Length[rows]}];
	computedDepths
]

(* the parts of a row of the table, positions of rows or negated positions of leaves *)
rowParts[{1, function_, argument_, _, _}] := {function, argument}
rowParts[{2 | 3, _, domain_, body_, _}] := {domain, body}
rowParts[{4, _, type_, value_, body_}] := {type, value, body}
rowParts[{5, _, _, term_, _}] := {term}

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

(* The file's data, read held and checked before anything in it evaluates: taking an association out of HoldComplete
   evaluates its values, and reading its keys or values evaluates them, so first every symbol the data holds, apart
   from what HoldComplete or HoldForm holds in it, a name or an annotation's expression, must be one of the symbols
   a saved environment is written with, its keys read held with Keys[association, HoldComplete], as Cases does not
   look at keys. Then the data is taken out and checked in full. *)
readEnvironmentFile[file_String] := Block[{fileBytes = Quiet[ReadByteArray[file]], fileData},
	If[ ! ByteArrayQ[fileBytes], kernelFailure["SavedEnvironmentUnreadable", "`1` cannot be read.", {file}]];
	fileData = Quiet[BinaryDeserialize[fileBytes, HoldComplete]];
	If[ ! MatchQ[fileData, HoldComplete[_Association]] || ! heldDataQ[packedArraysBlanked[fileData]] || ! savedDataQ[First[fileData]],
		kernelFailure["SavedEnvironmentInvalid", "`1` is not a saved environment, or it was changed.", {file}]
	];
	First[fileData]
]

(* A table and its depths, packed arrays of integers, hold no symbol, and the symbols are looked for in the rest: an
   association atom's value is taken held, and replaced held *)
packedArraysBlanked[held : HoldComplete[association_Association]] /; AtomQ[Unevaluated[association]] := Fold[
	Function[{data, key},
		If[ MatchQ[Quiet[Extract[data, {1, Key[key]}, HoldComplete]], HoldComplete[array_ /; Developer`PackedArrayQ[Unevaluated[array], Integer]]],
			ReplacePart[data, {1, Key[key]} -> 0],
			data
		]
	],
	held,
	{"Table", "Depths"}
]
packedArraysBlanked[held_] := held

(* An association atom's keys are no parts that Cases sees, so they are checked apart. The test holds what it is given:
   a PatternTest would evaluate an Association[...] not yet made, as one held in an annotation's HoldForm is. *)
heldDataQ[held_HoldComplete] := And[
	writtenSymbolsQ[Replace[held, (HoldComplete | HoldForm)[_] -> 0, {2, Infinity}]],
	AllTrue[
		Cases[held, association_Association /; AtomQ[Unevaluated[association]] :> Keys[association, HoldComplete], {0, Infinity}],
		Function[keys, writtenSymbolsQ[Replace[keys, (HoldComplete | HoldForm)[_] -> 0, {2, Infinity}]]]
	]
]

writtenSymbolsQ[expression_] := SubsetQ[$writtenSymbols, DeleteDuplicates[Cases[expression, symbol_Symbol :> HoldComplete[symbol], {0, Infinity}, Heads -> True]]]

$writtenSymbols = HoldComplete /@ Unevaluated[{
	HoldComplete, Association, Rule, RuleDelayed, List, True, False, None, Null, Infinity, DirectedInfinity, DateObject, Missing, TypeTheoryRules,
	termRef, boundVariable, freeVariable, universeSort, constantReference, naturalLiteral, intervalUniverse,
	application, lambdaAbstraction, dependentFunctionType, localDefinition, projection, cubicalSystem,
	levelParameter, levelSuccessor, levelMaximum, levelImpredicativeMaximum
}]

savedDataQ[data_Association] := And[
	MemberQ[{1, $formatVersion}, data["FormatVersion"]],
	SubsetQ[
		Keys[data],
		Join[
			{"Format", "FormatVersion", "KernelHash", "Rules", "Base", "Names", "Records", "NaturalNumbers", "RewriteRuleIndex", "Hash"},
			If[data["FormatVersion"] === 2, {"Leaves", "Labels", "Table", "Depths"}, {"Nodes"}]
		]
	],
	data["Format"] === "TypeTheoryEnvironment",
	rulesQ[data["Rules"]],
	MatchQ[data["Base"], None | KeyValuePattern[{"Name" -> _String, "Hash" -> _String}]],
	If[ data["FormatVersion"] === 2,
		tableQ[data["Leaves"], data["Labels"], data["Table"], data["Depths"]],
		ListQ[data["Nodes"]] && AllTrue[Range[Length[data["Nodes"]]], Function[row, nodeQ[data["Nodes"][[row]], row]]]
	],
	ListQ[data["Names"]] && AllTrue[data["Names"], nameQ],
	AssociationQ[data["Records"]] && Keys[data["Records"]] === data["Names"],
	AllTrue[Values[data["Records"]], Function[record, recordQ[record, rowCount[data] + 1]]],
	inertQ[data["NaturalNumbers"], 1] && inertQ[data["RewriteRuleIndex"], 1]
]
savedDataQ[_] := False

rowCount[data_Association] := If[data["FormatVersion"] === 2, Length[data["Table"]], Length[data["Nodes"]]]

(* The table of format 2, checked at once, as integers: every code one of the five, every part an earlier row or a leaf,
   every depth one more than a row part's at least, every name or structure label a name and every binder label a
   binder, and the fields a code leaves unused 0; the leaves are checked one by one. *)
tableQ[leaves_List, labels_List, {}, {}] := AllTrue[leaves, leafTermQ]
tableQ[leaves_List, labels_List, table_, depths_] := And[
	Developer`PackedArrayQ[table, Integer, 2] && Last[Dimensions[table]] == 5,
	Developer`PackedArrayQ[depths, Integer, 1] && Length[depths] == Length[table] && Min[depths] >= 1 && Max[depths] <= Length[table],
	SubsetQ[{1, 2, 3, 4, 5}, Union[table[[All, 1]]]],
	tableRowsQ[leaves, labels, table, depths, PositionIndex[table[[All, 1]]]]
]
tableQ[_, _, _, _] := False

tableRowsQ[leaves_List, labels_List, table_, depths_, byCode_Association] := With[{at = Function[codes, Join @@ Lookup[byCode, codes, {}]]},
	And[
		AllTrue[
			{{at[{1}], 2}, {at[{1}], 3}, {at[{2, 3}], 3}, {at[{2, 3}], 4}, {at[{4}], 3}, {at[{4}], 4}, {at[{4}], 5}, {at[{5}], 4}},
			Function[pair, tablePartsQ[table, depths, Length[leaves], First[pair], Last[pair]]]
		],
		labelIdsQ[labels, table[[at[{2, 3, 4, 5}], 2]], nameQ],
		labelIdsQ[labels, table[[at[{2, 3}], 5]], binderQ],
		Max[0, Abs[table[[at[{1}], {4, 5}]]]] == 0 && Max[0, Abs[table[[at[{5}], 5]]]] == 0 && Min[0, table[[at[{5}], 3]]] == 0,
		AllTrue[leaves, leafTermQ]
	]
]

(* the parts in a column of the rows: an earlier row, of a smaller depth, or a leaf *)
tablePartsQ[table_, depths_, leafCount_Integer, rows_List, column_Integer] := With[{parts = table[[rows, column]]},
	With[{rowParts = UnitStep[parts - 1], leafParts = UnitStep[-parts - 1]},
		And[
			Total[rowParts + leafParts] == Length[parts],
			Max[-1, Pick[parts - rows, rowParts, 1]] < 0,
			Min[0, Pick[parts, leafParts, 1]] >= -leafCount,
			Min[1, Pick[depths[[rows]], rowParts, 1] - depths[[Pick[parts, rowParts, 1]]]] >= 1
		]
	]
]

labelIdsQ[labels_List, ids_, test_] := With[{distinct = Union[ids]},
	distinct === {} || Min[distinct] >= 1 && Max[distinct] <= Length[labels] && AllTrue[labels[[distinct]], test]
]

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
nameQ[HoldComplete[TypeTheoryHole[_Symbol | _String, _Integer?Positive]]] := True
nameQ[_] := False

binderQ["Explicit" | "Implicit" | "StrictImplicit" | "InstanceImplicit"] := True
binderQ[{"Explicit" | "Implicit" | "StrictImplicit" | "InstanceImplicit", 0 | 1}] := True
binderQ[_] := False

recordQ[record_Association, rows_] := And[
	MemberQ[{"Axiom", "Definition", "Opaque", "Theorem", "InductiveType", "Constructor", "Recursor", "RewriteRule", "Quotient", "Cubical", "Hole"}, record["Kind"]],
	inertQ[KeyDrop[record, "Annotation"], rows],
	annotationQ[Lookup[record, "Annotation", None]]
]
recordQ[_, _] := False

(* An annotation is data as the user gave it, a citation or the evidence of a computation, and what evaluates when it
   is read must be data too: strings, numbers, lists, associations and rules of such, dates, and anything held in
   HoldForm or HoldComplete, where nothing evaluates. *)
annotationQ[_String | _Integer | _Real | _Rational | True | False | None | Null] := True
annotationQ[list_List] := AllTrue[list, annotationQ]
annotationQ[association_Association] := AllTrue[Keys[association], annotationQ] && AllTrue[Values[association], annotationQ]
annotationQ[(Rule | RuleDelayed)[key_, value_]] := annotationQ[key] && annotationQ[value]
annotationQ[HoldForm[_] | HoldComplete[_]] := True
annotationQ[(DateObject | Missing)[arguments___]] := AllTrue[{arguments}, annotationQ]
annotationQ[_] := False

(* data that holds nothing that could evaluate: strings, numbers, names, levels, core leaves and terms by row *)
inertQ[_String | _Integer | True | False | None | Infinity, _] := True
inertQ[termRef[reference_Integer], rows_] := 1 <= reference < rows
inertQ[list_List, rows_] := AllTrue[list, Function[element, inertQ[element, rows]]]
inertQ[association_Association, rows_] := AllTrue[Keys[association], Function[key, inertQ[key, rows]]] && AllTrue[Values[association], Function[value, inertQ[value, rows]]]
inertQ[value_, _] := nameQ[value] || levelQ[value] || leafTermQ[value]

(* the environment of base extended with the file's constants, its terms built once from their rows *)
environmentFromContents[base : TypeTheoryEnvironment[baseStore_Symbol], data_Association, source_] := Block[
	{$rowTerms = If[data["FormatVersion"] === 2, tableTerms[data], rowTerms[data["Nodes"]]], loadedRecords, loadedEnvironment},
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

(* The terms of the table's rows, in order, built a depth at a time: the rows of a depth together, each code's with
   MapThread, from the terms of their parts, rows of the depths before and leaves, each depth's a list of its own, which
   nothing changes after. *)
tableTerms[data_Association] := Block[
	{savedLeaves = data["Leaves"], savedLabels = data["Labels"], savedTable = data["Table"], savedDepths = data["Depths"], savedOrder, savedStarts, savedIndexOf, savedLevelTerms = {}},
	If[savedTable === {}, Return[{}, Block]];
	savedOrder = Ordering[savedDepths];
	savedStarts = Prepend[Accumulate[BinCounts[savedDepths, {1, Max[savedDepths] + 1, 1}]], 0];
	savedIndexOf = ConstantArray[0, Length[savedTable]];
	savedIndexOf[[savedOrder]] = Range[Length[savedTable]] - savedStarts[[savedDepths[[savedOrder]]]];
	Do[AppendTo[savedLevelTerms, depthTerms[savedOrder[[savedStarts[[depth]] + 1 ;; savedStarts[[depth + 1]]]]]], {depth, Length[savedStarts] - 1}];
	Extract[savedLevelTerms, Transpose[{savedDepths, savedIndexOf}]]
]

depthTerms[positions_List] := Block[{depthRows = savedTable[[positions]], depthValues = ConstantArray[Null, Length[positions]]},
	KeyValueMap[Function[{code, at}, depthValues[[at]] = codeTerms[code, depthRows[[at]]]], PositionIndex[depthRows[[All, 1]]]];
	depthValues
]

codeTerms[1, rows_] := MapThread[application, {partTerms[rows[[All, 2]]], partTerms[rows[[All, 3]]]}]
codeTerms[2, rows_] := MapThread[lambdaAbstraction, {savedLabels[[rows[[All, 2]]]], partTerms[rows[[All, 3]]], partTerms[rows[[All, 4]]], savedLabels[[rows[[All, 5]]]]}]
codeTerms[3, rows_] := MapThread[dependentFunctionType, {savedLabels[[rows[[All, 2]]]], partTerms[rows[[All, 3]]], partTerms[rows[[All, 4]]], savedLabels[[rows[[All, 5]]]]}]
codeTerms[4, rows_] := MapThread[localDefinition, {savedLabels[[rows[[All, 2]]]], partTerms[rows[[All, 3]]], partTerms[rows[[All, 4]]], partTerms[rows[[All, 5]]]}]
codeTerms[5, rows_] := MapThread[projection, {savedLabels[[rows[[All, 2]]]], rows[[All, 3]], partTerms[rows[[All, 4]]]}]

partTerms[parts_] := Block[{partValues = ConstantArray[Null, Length[parts]], rowPositions = Flatten[Position[UnitStep[parts - 1], 1]], leafPositions = Flatten[Position[UnitStep[-parts - 1], 1]]},
	If[rowPositions =!= {}, partValues[[rowPositions]] = Extract[savedLevelTerms, Transpose[{savedDepths[[parts[[rowPositions]]]], savedIndexOf[[parts[[rowPositions]]]]}]]];
	If[leafPositions =!= {}, partValues[[leafPositions]] = savedLeaves[[-parts[[leafPositions]]]]];
	partValues
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
