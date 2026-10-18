(* ::Package:: *)

(*
The environment: declared constants with their records, and the registered natural numbers.

	TypeTheoryEnvironment[<|
		"Constants" -> <|HoldComplete[name] -> record, ...|>,
		"NaturalNumbers" -> None | <|"Type" -> HoldComplete[type], "Zero" -> HoldComplete[zero],
			"Successor" -> HoldComplete[successor], "Addition" -> None | HoldComplete[addition]|>
	|>]

A record is an Association with "Kind" (one of "Axiom", "Definition", "Theorem", "InductiveType",
"Constructor", "Recursor"), "Type" (a core term), "UniverseParameters" ({HoldComplete[u], ...}) and the
fields of its kind:
	Definition, Theorem    "Value"
	InductiveType          "NumberOfParameters", "NumberOfIndices", "Constructors", "LargeElimination"
	Constructor            "InductiveType", "ConstructorIndex", "NumberOfParameters", "NumberOfFields"
	Recursor               "InductiveType", "NumberOfParameters", "NumberOfIndices", "NumberOfMinors",
	                       "Rules" (<|HoldComplete[constructor] -> <|"NumberOfFields", "RightHandSide"|>|>), "KLike"

An environment is a value: declaring a constant gives a new environment and leaves the old one as it
was, so a proof can branch or be undone without bookkeeping.

The kernel reports a failure by throwing a Failure with the tag $kernelFailureTag; every exported
function catches it with catchKernelFailure and returns it.
*)


(* ::Section:: *)
(*PackageExported*)


PackageExported[TypeTheoryEnvironment]
PackageExported[$TypeTheoryEnvironment]


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[emptyEnvironment]
PackageScoped[constantRecord]
PackageScoped[constantDeclaredQ]
PackageScoped[addConstantRecords]
PackageScoped[naturalNumberSettings]
PackageScoped[setNaturalNumberSettings]
PackageScoped[checkUniverseParameters]
PackageScoped[kernelFailure]
PackageScoped[throwFailure]
PackageScoped[catchKernelFailure]
PackageScoped[$kernelFailureTag]


(* ::Section:: *)
(*Usage Messages*)


TypeTheoryEnvironment::usage = "TypeTheoryEnvironment[data] is an environment of declared constants: axioms, definitions, theorems, and inductive types with their constructors and recursors.\n\
env[\"Constants\"] gives the names of the declared constants."
$TypeTheoryEnvironment::usage = "$TypeTheoryEnvironment is the environment used when none is given: the prelude, which declares True, False, Not, \
And, Or, Equal, Exists, NonNegativeIntegers, Plus and EqualityCongruence."

emptyEnvironment::usage = "emptyEnvironment[] gives an environment with no constants."
constantRecord::usage = "constantRecord[environment, HoldComplete[name]] gives the record of the constant name, or throws a kernel failure if it is not declared."
constantDeclaredQ::usage = "constantDeclaredQ[environment, HoldComplete[name]] gives True if name is declared in environment."
addConstantRecords::usage = "addConstantRecords[environment, <|HoldComplete[name] -> record, ...|>] gives environment with the records added; it throws a kernel failure if a name is already declared."
naturalNumberSettings::usage = "naturalNumberSettings[environment] gives the registered natural numbers of environment, or None."
setNaturalNumberSettings::usage = "setNaturalNumberSettings[environment, settings] gives environment with settings as its natural numbers."
checkUniverseParameters::usage = "checkUniverseParameters[HoldComplete[name], {HoldComplete[u], ...}, {term, ...}] throws a kernel failure unless the \
universe parameters are distinct and include every universe parameter the core terms mention."
kernelFailure::usage = "kernelFailure[tag, template, {parameter, ...}] throws a Failure with the given tag and message, to be caught by catchKernelFailure."
throwFailure::usage = "throwFailure[failure] throws failure, to be caught by catchKernelFailure."
catchKernelFailure::usage = "catchKernelFailure[expr] evaluates expr and gives its value, or the Failure a kernel function threw."
$kernelFailureTag::usage = "$kernelFailureTag is the tag kernel failures are thrown with."


(* ::Section:: *)
(*Function Definitions*)


emptyEnvironment[] := TypeTheoryEnvironment[<|"Constants" -> <||>, "NaturalNumbers" -> None|>]


constantRecord[TypeTheoryEnvironment[data_Association], name_HoldComplete] := Lookup[
	data["Constants"],
	Key[name],
	kernelFailure["UnknownConstant", "`1` is not declared.", {HoldForm @@ name}]
]

constantDeclaredQ[TypeTheoryEnvironment[data_Association], name_HoldComplete] := KeyExistsQ[data["Constants"], name]


addConstantRecords[environment : TypeTheoryEnvironment[data_Association], records_Association] := With[
	{clash = Select[Keys[records], Function[name, constantDeclaredQ[environment, name]]]},
	If[ clash =!= {},
		kernelFailure["AlreadyDeclared", "`1` is already declared.", {HoldForm @@ First[clash]}],
		TypeTheoryEnvironment[Append[data, "Constants" -> Join[data["Constants"], records]]]
	]
]


naturalNumberSettings[TypeTheoryEnvironment[data_Association]] := Lookup[data, "NaturalNumbers", None]

setNaturalNumberSettings[TypeTheoryEnvironment[data_Association], settings_] := TypeTheoryEnvironment[Append[data, "NaturalNumbers" -> settings]]


TypeTheoryEnvironment[data_Association]["Constants"] := Cases[Keys[data["Constants"]], HoldComplete[name_] :> HoldForm[name]]


checkUniverseParameters[name_HoldComplete, universeParameters_List, terms_List] := Which[
	! DuplicateFreeQ[universeParameters],
		kernelFailure["DuplicateUniverseParameter", "The universe parameters of `1` must be distinct.", {HoldForm @@ name}],
	! SubsetQ[universeParameters, Cases[terms, levelParameter[parameter_] :> parameter, Infinity]],
		kernelFailure["UndeclaredUniverseParameter", "`1` mentions a universe parameter that it does not declare.", {HoldForm @@ name}],
	True,
		Null
]


kernelFailure[tag_String, template_String, parameters_List] := throwFailure[
	Failure[tag, <|"MessageTemplate" -> template, "MessageParameters" -> parameters|>]
]

throwFailure[failure_Failure] := Throw[failure, $kernelFailureTag]

SetAttributes[catchKernelFailure, HoldFirst]
catchKernelFailure[expr_] := Catch[expr, $kernelFailureTag]


TypeTheoryEnvironment /: MakeBoxes[environment : TypeTheoryEnvironment[data_Association], format : StandardForm] := With[
	{records = Values[data["Constants"]]},
	BoxForm`ArrangeSummaryBox[
		TypeTheoryEnvironment,
		environment,
		None,
		{
			BoxForm`SummaryItem[{"Constants: ", Length[records]}],
			BoxForm`SummaryItem[{"Inductive types: ", Count[records, KeyValuePattern["Kind" -> "InductiveType"]]}]
		},
		{
			BoxForm`SummaryItem[{"Theorems: ", Count[records, KeyValuePattern["Kind" -> "Theorem"]]}],
			BoxForm`SummaryItem[{"Natural numbers: ", If[data["NaturalNumbers"] === None, "none", HoldForm @@ data["NaturalNumbers", "Type"]]}]
		},
		format,
		(* an environment can be large, and a notebook should not store a copy of it in every output *)
		"Interpretable" -> False
	]
]
