(* ::Package:: *)

(* Tests for the kernel's local variables. A step of the kernel keeps its values in a Block or passes them in calls,
   not in a With, a Module, a :> rule or a named Function: on W15 those substitute by walking their bodies, a term
   put there included, as the tree the term writes out to. A Block variable is a global symbol while its Block runs,
   so each one without a $ is localized by one function only, and names no definition anywhere: Blocking a function's
   name would take the function away from everything the Block calls.
   Run with: TestReport["TypeTheory/Tests/Terms/Scoping.wlt"] from the repository root. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

Needs["CodeParser`"]

kernelFiles = FileNames["*.wl", FileNameJoin[{Directory[], "TypeTheory", "Kernel"}], Infinity]

localName[CodeParser`LeafNode[Symbol, name_String, _]] := name
localName[CodeParser`CallNode[CodeParser`LeafNode[Symbol, "Set" | "SetDelayed", _], {CodeParser`LeafNode[Symbol, name_String, _], _}, _]] := name
localName[_] := Nothing

definedName[CodeParser`CallNode[CodeParser`LeafNode[Symbol, "SetDelayed" | "Set", _], {left_, _}, _]] := Replace[left, {
	CodeParser`CallNode[CodeParser`LeafNode[Symbol, "Condition", _], {inner_, _}, _] :> Replace[inner, {CodeParser`CallNode[CodeParser`LeafNode[Symbol, name_String, _], _, _] :> name, _ :> None}],
	CodeParser`CallNode[CodeParser`LeafNode[Symbol, name_String, _], _, _] :> name,
	CodeParser`LeafNode[Symbol, name_String, _] :> name,
	_ :> None
}]
definedName[_] := None

(* {function, variable} for each variable without $ that a Block in the function's definitions localizes *)
blockLocals = DeleteDuplicates @ Catenate @ Map[
	Function[top, Catenate @ Cases[
		top,
		CodeParser`CallNode[CodeParser`LeafNode[Symbol, "Block", _], {CodeParser`CallNode[CodeParser`LeafNode[Symbol, "List", _], variables_List, _], ___}, _] :>
			Map[{definedName[top], #}&, Select[localName /@ variables, ! StringStartsQ[#, "$"]&]],
		{0, Infinity}
	]],
	Catenate[CodeParser`CodeParse[File[#]][[2]]& /@ kernelFiles]
]

(* the rules of every symbol of that name in TypeTheory's contexts *)
definitionsOf[name_String] := Catenate @ Map[
	Function[full, Replace[ToExpression[full, InputForm, HoldComplete], HoldComplete[symbol_] :> Join[OwnValues[symbol], DownValues[symbol], UpValues[symbol], SubValues[symbol]]]],
	Names["WolframInstitute`TypeTheory`*`" <> name]
]


VerificationTest[
	Length[blockLocals] > 0 && AllTrue[blockLocals[[All, 1]], StringQ],
	True,
	TestID -> "The-scan-finds-the-Block-locals-and-their-functions"
]

VerificationTest[
	Select[GatherBy[blockLocals, Last], Length[DeleteDuplicates[#[[All, 1]]]] > 1&],
	{},
	TestID -> "Each-Block-local-is-localized-by-one-function"
]

VerificationTest[
	Select[DeleteDuplicates[blockLocals[[All, 2]]], definitionsOf[#] =!= {}&],
	{},
	TestID -> "No-Block-local-names-a-definition"
]
