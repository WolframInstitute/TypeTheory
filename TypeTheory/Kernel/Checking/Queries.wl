(* ::Package:: *)

(*
Questions about terms and environments.

TypeTheoryTerm[term, environment] carries the environment its constants come from; TypeTheoryTerm[term]
without one is read in the prelude, or, beside a term that has one, in that term's. A term's universe parameters are the symbols and strings
in its universe levels. Answers are TypeTheoryTerm expressions in the same environment, read back from
core terms.

An environment behaves like an Association of its constants: environment[name] gives the declaration
that introduced name, Keys gives the names in the order they were declared, and Length, KeyExistsQ and
Normal work as for an Association, Normal giving the declarations themselves, in order. Information
gives "Constants", "Kinds", "Axioms", "RewriteRules", "NaturalNumbers" and "Rules".

An environment's store can be changed by hand. TypeTheoryCheck[environment] is how to trust it anyway:
it replays every declaration in order on the empty environment of the same rules with the core
declaration functions, and compares each record with the one the replay produces. Axioms and rewrite
rules are taken on trust, as their name says.
*)


(* ::Section:: *)
(*PackageExported*)


PackageExported[TypeTheoryCheck]
PackageExported[DefinitionallyEqualQ]
PackageExported[WeakHeadNormalForm]


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[termEnvironment]
PackageScoped[heldTerm]
PackageScoped[termSyntax]
PackageScoped[declarationOf]


(* ::Section:: *)
(*Usage Messages*)


TypeTheoryCheck::usage = "TypeTheoryCheck[term] gives the type of the TypeTheoryTerm term in its environment, or a Failure if it does not type-check.\n\
TypeTheoryCheck[term, type] gives a Success if term has the given type, and a Failure otherwise.\n\
TypeTheoryCheck[environment] checks every declaration of the TypeTheoryEnvironment environment again from scratch and gives a Success, \
or a Failure for the first declaration that does not check."
DefinitionallyEqualQ::usage = "DefinitionallyEqualQ[term1, term2] gives True if the TypeTheoryTerm expressions term1 and term2 are equal by computation \
in their environment, and False otherwise."
WeakHeadNormalForm::usage = "WeakHeadNormalForm[term] reduces the TypeTheoryTerm term until its head can no longer reduce."

termEnvironment::usage = "termEnvironment[term] gives the environment of the TypeTheoryTerm term, or the prelude if it has none."
heldTerm::usage = "heldTerm[term] gives HoldComplete[expr] for the TypeTheoryTerm term holding expr."
termSyntax::usage = "termSyntax[term] gives the syntax tree of the TypeTheoryTerm term."
declarationOf::usage = "declarationOf[environment, HoldComplete[name], mode] gives the declaration that introduced the constant name, \
its terms read back for display (mode \"Display\") or exactly (mode \"Exact\")."


(* ::Section:: *)
(*Function Definitions*)


(* a term without an environment is in the prelude *)
termEnvironment[TypeTheoryTerm[_, environment_?environmentQ]] := environment
termEnvironment[TypeTheoryTerm[_]] := preludeEnvironment[]

heldTerm[TypeTheoryTerm[term_, ___]] := HoldComplete[term]

termSyntax[TypeTheoryTerm[term_, ___]] := toSyntax[term]

(* the environment two terms share: a term without one takes the other's, and two without one are in
   the prelude *)
sharedEnvironment[first_TypeTheoryTerm, second_TypeTheoryTerm] := Replace[{givenEnvironment[first], givenEnvironment[second]}, {
	{None, None} :> preludeEnvironment[],
	{environment_, None} | {None, environment_} :> environment,
	{environment_, environment_} :> environment,
	_ :> kernelFailure["DifferentEnvironments", "The terms carry different environments.", {}]
}]

givenEnvironment[TypeTheoryTerm[_, environment_?environmentQ]] := environment
givenEnvironment[TypeTheoryTerm[_]] := None

elaborateQueryTerm[environment_, term_TypeTheoryTerm, expected_, universeParameters_List] :=
	elaborateClosedTerm[environment, heldTerm[term], expected, universeParameters]


TypeTheoryTerm /: TypeOf[term : TypeTheoryTerm[_, ___]] := TypeTheoryCheck[term]
TypeTheoryTerm /: TypeOf[TypeTheoryTerm[term_], environment_?environmentQ] := TypeTheoryCheck[TypeTheoryTerm[term, environment]]


(* a constant on its own has its declared type, with its implicit arguments and universe parameters *)
TypeTheoryCheck[term_TypeTheoryTerm] := catchKernelFailure @ With[{environment = termEnvironment[term]},
	coreToTypeTheoryTerm[environment, <||>, betaNormalize @ Replace[aliasResolvedName[environment, heldFromSyntax[termSyntax[term]]], {
		name_ /; And[constantDeclaredQ[environment, name], ! overloadedNameQ[environment, name], constantRecord[environment, name]["Kind"] =!= "RewriteRule"] :>
			constantRecord[environment, name]["Type"],
		_ :> Last @ elaborateQueryTerm[environment, term, None, universeParameterNames[{termSyntax[term]}]]
	}]]
]

TypeTheoryCheck[term_TypeTheoryTerm, type_TypeTheoryTerm] := catchKernelFailure @ With[
	{environment = sharedEnvironment[term, type], universeParameters = universeParameterNames[{termSyntax[term], termSyntax[type]}]},
	{expected = elaborateClosedType[environment, heldTerm[type], universeParameters]},
	elaborateQueryTerm[environment, term, expected, universeParameters];
	Success["TypeChecked", <|"MessageTemplate" -> "`1` has type `2`.", "MessageParameters" -> {term, type}, "Term" -> term, "Type" -> type|>]
]


DefinitionallyEqualQ[first_TypeTheoryTerm, second_TypeTheoryTerm] := TrueQ @ catchKernelFailure @ With[
	{environment = sharedEnvironment[first, second], universeParameters = universeParameterNames[{termSyntax[first], termSyntax[second]}]},
	definitionallyEqualQ[
		environment,
		<||>,
		First @ elaborateQueryTerm[environment, first, None, universeParameters],
		First @ elaborateQueryTerm[environment, second, None, universeParameters]
	]
]


WeakHeadNormalForm[term_TypeTheoryTerm] := catchKernelFailure @ With[{environment = termEnvironment[term]},
	coreToTypeTheoryTerm[
		environment,
		<||>,
		weakHeadNormalForm[environment, <||>, First @ elaborateQueryTerm[environment, term, None, universeParameterNames[{termSyntax[term]}]]]
	]
]


(* ::Subsection:: *)
(*Environments as associations*)


(environment : TypeTheoryEnvironment[_Symbol])[name_] /; environmentQ[environment] := declarationOf[environment, HoldComplete[name], "Display"]

TypeTheoryEnvironment /: Keys[environment : TypeTheoryEnvironment[_Symbol]?environmentQ] := ReleaseHold /@ environmentNames[environment]
TypeTheoryEnvironment /: Length[environment : TypeTheoryEnvironment[_Symbol]?environmentQ] := Length[environmentNames[environment]]
TypeTheoryEnvironment /: KeyExistsQ[environment : TypeTheoryEnvironment[_Symbol]?environmentQ, name_] := constantDeclaredQ[environment, HoldComplete[name]]

(* the declarations, in order; constructors and recursors come with their inductive type *)
TypeTheoryEnvironment /: Normal[environment : TypeTheoryEnvironment[_Symbol]?environmentQ] := catchKernelFailure @ With[
	{primary = primaryNames[environment]},
	Replace[naturalNumberSettings[environment], {
		settings_Association :> withRegistrations[Function[name, declarationOf[environment, name, "Exact"]] /@ primary, primary, settings],
		None :> Function[name, declarationOf[environment, name, "Exact"]] /@ primary
	}]
]

(* constructors and recursors come with their type, and the types of a block with its first *)
primaryNames[environment_] := Select[environmentNames[environment], Function[name, ! generatedQ[constantRecord[environment, name], name]]]

generatedQ[record_, name_] := MatchQ[record["Kind"], "Constructor" | "Recursor"] || (record["Kind"] === "InductiveType" && First[record["Block"]] =!= name)

(* each registration of the natural numbers, or of operations on them, comes right after the last constant
   it names, and after the registration before it *)
withRegistrations[declarations_List, primary_List, settings_Association] := With[
	{positions = Rest @ FoldList[Max, 0, MapIndexed[
		Function[{roles, index}, Max[Flatten[Position[primary, Alternatives @@ registrationNames[settings, First[index]], {1}]]]],
		settings["Registrations"]
	]]},
	Catenate @ MapIndexed[
		Function[{declaration, index}, Prepend[
			Function[registration, registrationDeclaration[settings, registration]] /@ Flatten[Position[positions, First[index]]],
			declaration
		]],
		declarations
	]
]

(* the constants a registration names: the first also names the natural numbers themselves *)
registrationNames[settings_Association, 1] := Join[Lookup[settings, {"Type", "Zero", "Successor"}], Lookup[settings["Operations"], First[settings["Registrations"]]]]
registrationNames[settings_Association, index_Integer] := Lookup[settings["Operations"], settings["Registrations"][[index]]]

registrationOf[settings_Association, index_Integer] := <|
	KeyTake[settings, {"Type", "Zero", "Successor"}],
	"Operations" -> KeyTake[settings["Operations"], settings["Registrations"][[index]]]
|>

registrationDeclaration[settings_Association, index_Integer] := ReleaseHold @ heldFromSyntax @ syntaxHead[
	TypeTheoryNaturalNumbers,
	Join[
		toSyntax @@@ Lookup[settings, {"Type", "Zero", "Successor"}],
		Replace[KeyTake[settings["Operations"], settings["Registrations"][[index]]], {
			<||> -> {},
			operations_ :> {syntaxHead[Association, KeyValueMap[Function[{role, name}, syntaxHead[Rule, {syntaxString[role], toSyntax @@ name}]], operations]]}
		}]
	]
]

TypeTheoryEnvironment /: Information[environment : TypeTheoryEnvironment[_Symbol]?environmentQ, property_String] := environmentInformation[environment, property]

environmentInformation[_, "Properties"] := {"Constants", "Kinds", "Axioms", "RewriteRules", "NaturalNumbers", "Rules"}
environmentInformation[environment_, "Constants"] := Keys[environment]
environmentInformation[environment_, "Kinds"] := Counts[Function[name, constantRecord[environment, name]["Kind"]] /@ environmentNames[environment]]
environmentInformation[environment_, "Axioms"] :=
	ReleaseHold /@ Select[environmentNames[environment], Function[name, constantRecord[environment, name]["Kind"] === "Axiom"]]
environmentInformation[environment_, "RewriteRules"] :=
	ReleaseHold /@ Select[environmentNames[environment], Function[name, constantRecord[environment, name]["Kind"] === "RewriteRule"]]
environmentInformation[environment_, "NaturalNumbers"] := Replace[
	naturalNumberSettings[environment],
	settings_Association :> <|Map[ReleaseHold, KeyTake[settings, {"Type", "Zero", "Successor"}]], "Operations" -> Map[ReleaseHold, settings["Operations"]]|>
]
environmentInformation[environment_, "Rules"] := environmentRules[environment]


(* ::Subsection:: *)
(*Declarations read back*)


declarationOf[environment_, name_HoldComplete, mode_String] := If[ ! constantDeclaredQ[environment, name],
	Missing["KeyAbsent", ReleaseHold[name]],
	Replace[constantRecord[environment, name], {
		record : KeyValuePattern["Kind" -> "Constructor" | "Recursor"] :> declarationOf[environment, record["InductiveType"], mode],
		record_ :> ReleaseHold @ heldFromSyntax @ declarationSyntax[environment, name, record, mode]
	}]
]

(* a rewrite rule reads back as ForAll[binders, lhs -> rhs], with the binders its two sides share *)
declarationSyntax[environment_, name_, record : KeyValuePattern["Kind" -> "RewriteRule"], mode_] := syntaxHead[TypeTheoryRewriteRule, Join[
	{
		toSyntax @@ name,
		ruleSyntax[readBack[environment, record["LeftHandSide"], mode], readBack[environment, record["RightHandSide"], mode], record["NumberOfVariables"]]
	},
	universeOptionSyntax[record]
]]

declarationSyntax[environment_, name_, record_, mode_] := With[
	{
		nameSyntax = toSyntax @@ name,
		typeSyntax = readBack[environment, record["Type"], mode],
		universeOption = universeOptionSyntax[record]
	},
	Replace[record["Kind"], {
		"InductiveType" /; Length[record["Block"]] > 1 :> syntaxHead[TypeTheoryInductiveType, Join[
			{
				syntaxHead[List, Function[member,
					syntaxHead[Rule, {toSyntax @@ member, readBack[environment, constantRecord[environment, member]["Type"], mode]}]
				] /@ record["Block"]],
				syntaxHead[List, Function[constructor,
					syntaxHead[Rule, {toSyntax @@ constructor, readBack[environment, constantRecord[environment, constructor]["Type"], mode]}]
				] /@ Catenate[Function[member, constantRecord[environment, member]["Constructors"]] /@ record["Block"]]],
				syntaxHead[Rule, {syntaxString["Parameters"], syntaxInteger[record["NumberOfParameters"]]}]
			},
			universeOption
		]],
		"Axiom" :> syntaxHead[TypeTheoryAxiom, Join[{nameSyntax, typeSyntax}, universeOption]],
		"Definition" :> syntaxHead[TypeTheoryDefinition, Join[{nameSyntax, syntaxHead[Typed, {readBack[environment, record["Value"], mode], typeSyntax}]}, universeOption]],
		"Theorem" :> syntaxHead[TypeTheoryTheorem, Join[{nameSyntax, typeSyntax, readBack[environment, record["Value"], mode]}, universeOption]],
		"InductiveType" :> syntaxHead[TypeTheoryInductiveType, Join[
			{
				nameSyntax,
				typeSyntax,
				syntaxHead[List, Function[constructor,
					syntaxHead[Rule, {toSyntax @@ constructor, readBack[environment, constantRecord[environment, constructor]["Type"], mode]}]
				] /@ record["Constructors"]],
				syntaxHead[Rule, {syntaxString["Parameters"], syntaxInteger[record["NumberOfParameters"]]}]
			},
			universeOption
		]]
	}]
]

universeOptionSyntax[record_] := Replace[record["UniverseParameters"], {
	{} -> {},
	parameters_List :> {syntaxHead[Rule, {syntaxString["UniverseParameters"], syntaxHead[List, toSyntax @@@ parameters]}]}
}]

ruleSyntax[left_, right_, 0] := syntaxHead[Rule, {left, right}]
ruleSyntax[syntaxApplication[syntaxSymbol[HoldComplete[Function]], {binders_, leftBody_}], syntaxApplication[syntaxSymbol[HoldComplete[Function]], {_, rightBody_}], _] :=
	syntaxHead[ForAll, {binders, syntaxHead[Rule, {leftBody, rightBody}]}]

readBack[environment_, term_, "Display"] := delaborate[environment, <||>, term]
readBack[environment_, term_, "Exact"] := Block[{$exactReadBack = True}, delaborate[environment, <||>, term]]


(* ::Subsection:: *)
(*Checking an environment*)


TypeTheoryCheck[environment_?environmentQ] := withStoreCleanup @ catchKernelFailure @ With[
	{
		replayed = Fold[
			Function[{partial, name}, replayDeclaration[environment, partial, name -> constantRecord[environment, name]]],
			emptyEnvironmentOf[environmentRules[environment]],
			environmentNames[environment]
		]
	},
	If[ naturalNumberSettings[replayed] =!= naturalNumberSettings[environment],
		kernelFailure["DeclarationMismatch", "The natural numbers of the environment do not match its declarations.", {}]
	];
	Success["EnvironmentChecked", <|
		"MessageTemplate" -> "All `1` constants of the environment check again from their declarations.",
		"MessageParameters" -> {Length[environmentNames[environment]]},
		"Constants" -> Length[environmentNames[environment]]
	|>]
]

(* Constructors and recursors are generated with their inductive type, which comes before them; every
   record must come out of the replay exactly as it is in the environment. *)
replayDeclaration[original_, replayed_, name_ -> record_] := With[
	{extended = If[generatedQ[record, name], replayed, redeclare[original, replayed, name, record]]},
	If[ ! constantDeclaredQ[extended, name] || constantRecord[extended, name] =!= record,
		kernelFailure["DeclarationMismatch", "The record of `1` does not match the record that checking its declaration gives.", {HoldForm @@ name}]
	];
	registerWhenDeclared[extended, naturalNumberSettings[original]]
]

redeclare[original_, replayed_, name_, record_] := Replace[record["Kind"], {
	"Axiom" :> declareAxiom[replayed, name, record["UniverseParameters"], record["Type"]],
	"Definition" :> declareDefinition[replayed, name, record["UniverseParameters"], record["Type"], record["Value"]],
	"Theorem" :> declareTheorem[replayed, name, record["UniverseParameters"], record["Type"], record["Value"]],
	"RewriteRule" :> declareRewriteRule[replayed, name, record["UniverseParameters"], record["NumberOfVariables"], record["LeftHandSide"], record["RightHandSide"]],
	"InductiveType" :> declareInductiveTypes[
		replayed,
		record["UniverseParameters"],
		record["NumberOfParameters"],
		Function[member, member -> constantRecord[original, member]["Type"]] /@ record["Block"],
		Function[constructor, constructor -> constantRecord[original, constructor]["Type"]] /@ Catenate[Function[member, constantRecord[original, member]["Constructors"]] /@ record["Block"]]
	],
	kind_ :> kernelFailure["UnknownDeclaration", "The record of `1` has the unknown kind `2`.", {HoldForm @@ name, kind}]
}]

(* each registration of the natural numbers is replayed as soon as the constants it names are declared *)
registerWhenDeclared[replayed_, settings_Association] := With[
	{next = Replace[naturalNumberSettings[replayed], {registered_Association :> Length[registered["Registrations"]] + 1, None -> 1}]},
	If[ next <= Length[settings["Registrations"]] && AllTrue[registrationNames[settings, next], Function[name, constantDeclaredQ[replayed, name]]],
		registerWhenDeclared[registerNaturalNumbers[replayed, registrationOf[settings, next]], settings],
		replayed
	]
]
registerWhenDeclared[replayed_, None] := replayed
