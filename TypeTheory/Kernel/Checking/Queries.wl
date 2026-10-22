(* ::Package:: *)

(*
Questions about terms and environments.

TypeTheoryTerm[term, environment] carries the environment its constants come from; TypeTheoryTerm[term]
without one is read in the default environment, $TypeTheoryEnvironment, or, beside a term that has one, in that term's. A term's universe parameters are the symbols and strings
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

TypeTheoryTranslate[environment, rules] replays the declarations the same way on the empty environment
of other rules, whose kernel checks each of them again: a translation is trusted no more than the
declarations it gives. Where the rules lose Prop, Prop becomes the lowest universe of types, Type, and the
other universes stay: a level l becomes max(l, 1), which commutes with instantiating universe parameters.
A recursor's motive goes into Sort u with Prop and into Sort (u + 1) without it, so the universe level a
recursor is applied at moves down by one where the rules lose Prop, and up by one where they gain it,
and a recursor that eliminates into Prop alone gets the level 0; a declaration whose motives go into
Prop itself, as a proof that 0 is no successor does, is tried again with the levels kept. An inductive
proposition lives in the universe of its largest field, as Exists does. What needs Prop's impredicativity
or proof irrelevance, or a recursor at a universe parameter that may be 0, then fails to check, and is
left out with every declaration that mentions it. A theorem of rules without Prop states a type, so where
the rules gain Prop it becomes a definition. Where the rules lose quantities, every binder loses its
quantity; where they gain them, the kernel gives the constructors and recursors theirs.
*)


(* ::Section:: *)
(*PackageExported*)


PackageExported[TypeTheoryCheck]
PackageExported[TypeTheoryTranslate]
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
TypeTheoryTranslate::usage = "TypeTheoryTranslate[environment, rules] translates the declarations of the TypeTheoryEnvironment environment to the \
TypeTheoryRules rules, whose kernel checks them again, and gives a Success whose \"Environment\" is the environment of rules with each declaration that \
checks there, and whose \"Failures\" gives the failure of each declaration left out, those that mention one included.\n\
Where rules have no Prop, Prop becomes the lowest universe of types, Type. Axioms are left out, since one that holds of propositions need not hold of \
types, as propositional extensionality does not; the option \"Axioms\" -> True keeps them."
DefinitionallyEqualQ::usage = "DefinitionallyEqualQ[term1, term2] gives True if the TypeTheoryTerm expressions term1 and term2 are equal by computation \
in their environment, and False otherwise."
WeakHeadNormalForm::usage = "WeakHeadNormalForm[term] reduces the TypeTheoryTerm term until its head can no longer reduce."

termEnvironment::usage = "termEnvironment[term] gives the environment of the TypeTheoryTerm term, or the default environment if it has none."
heldTerm::usage = "heldTerm[term] gives HoldComplete[expr] for the TypeTheoryTerm term holding expr."
termSyntax::usage = "termSyntax[term] gives the syntax tree of the TypeTheoryTerm term."
declarationOf::usage = "declarationOf[environment, HoldComplete[name], mode] gives the declaration that introduced the constant name, \
its terms read back for display (mode \"Display\") or exactly (mode \"Exact\")."


(* ::Section:: *)
(*Function Definitions*)


(* a term without an environment is in the default environment *)
termEnvironment[TypeTheoryTerm[_, environment_?environmentQ]] := environment
termEnvironment[TypeTheoryTerm[_]] := defaultEnvironment[]

heldTerm[TypeTheoryTerm[term_, ___]] := HoldComplete[term]

termSyntax[TypeTheoryTerm[term_, ___]] := toSyntax[term]

(* the environment two terms share: a term without one takes the other's, and two without one are in
   the default environment *)
sharedEnvironment[first_TypeTheoryTerm, second_TypeTheoryTerm] := Replace[{givenEnvironment[first], givenEnvironment[second]}, {
	{None, None} :> defaultEnvironment[],
	{environment_, None} | {None, environment_} :> environment,
	{environment_, environment_} :> environment,
	_ :> kernelFailure["DifferentEnvironments", "The terms carry different environments.", {}]
}]

givenEnvironment[TypeTheoryTerm[_, environment_?environmentQ]] := environment
givenEnvironment[TypeTheoryTerm[_]] := None

elaborateQueryTerm[environment_, term_TypeTheoryTerm, expected_, universeParameters_List] :=
	elaborateClosedTerm[environment, heldTerm[term], expected, universeParameters]

(* a term checks under rules with quantities only if its functions use their variables as their quantities allow *)
checkedQueryTerm[environment_, term_TypeTheoryTerm, expected_, universeParameters_List] := With[
	{elaborated = elaborateQueryTerm[environment, term, expected, universeParameters]},
	If[rulesSetting[environment, "Quantities"], withKernelCaches[checkLiveUses[environment, First[elaborated]]]];
	elaborated
]


TypeTheoryTerm /: TypeOf[term : TypeTheoryTerm[_, ___]] := TypeTheoryCheck[term]
TypeTheoryTerm /: TypeOf[TypeTheoryTerm[term_], environment_?environmentQ] := TypeTheoryCheck[TypeTheoryTerm[term, environment]]


(* a constant on its own has its declared type, with its implicit arguments and universe parameters *)
TypeTheoryCheck[term_TypeTheoryTerm] := catchKernelFailure @ With[{environment = termEnvironment[term]},
	coreToTypeTheoryTerm[environment, <||>, betaNormalize @ Replace[aliasResolvedName[environment, heldFromSyntax[termSyntax[term]]], {
		name_ /; And[constantDeclaredQ[environment, name], ! overloadedNameQ[environment, name], constantRecord[environment, name]["Kind"] =!= "RewriteRule"] :>
			constantRecord[environment, name]["Type"],
		_ :> Last @ checkedQueryTerm[environment, term, None, universeParameterNames[{termSyntax[term]}]]
	}]]
]

TypeTheoryCheck[term_TypeTheoryTerm, type_TypeTheoryTerm] := catchKernelFailure @ With[
	{environment = sharedEnvironment[term, type], universeParameters = universeParameterNames[{termSyntax[term], termSyntax[type]}]},
	{expected = elaborateClosedType[environment, heldTerm[type], universeParameters]},
	checkedQueryTerm[environment, term, expected, universeParameters];
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

generatedQ[record_, name_] := Or[
	MatchQ[record["Kind"], "Constructor" | "Recursor"],
	record["Kind"] === "InductiveType" && First[record["Block"]] =!= name,
	record["Kind"] === "Quotient" && record["QuotientType"] =!= name
]

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


(* the quotient constants come from one declaration, written short with the prelude's names *)
quotientDeclaration[record_] := Replace[{record["Equality"], record["QuotientNames"]}, {
	{HoldComplete[Equal], HoldComplete /@ Unevaluated[{QuotientType, QuotientIntroduction, QuotientLift, QuotientInduction}]} :> TypeTheoryQuotients[],
	{HoldComplete[equality_], names_List} :> (TypeTheoryQuotients[equality, names] /. HoldComplete[name_] :> name)
}]

declarationOf[environment_, name_HoldComplete, mode_String] := If[ ! constantDeclaredQ[environment, name],
	Missing["KeyAbsent", ReleaseHold[name]],
	Replace[constantRecord[environment, name], {
		record : KeyValuePattern["Kind" -> "Constructor" | "Recursor"] :> declarationOf[environment, record["InductiveType"], mode],
		record : KeyValuePattern["Kind" -> "Quotient"] :> quotientDeclaration[record],
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
		"Definition" :> syntaxHead[TypeTheoryDefinition, Join[
			{nameSyntax, syntaxHead[Typed, {readBack[environment, record["Value"], mode], typeSyntax}]},
			universeOption,
			Function[role, syntaxHead[Rule, {syntaxString[role], syntaxSymbol[HoldComplete[True]]}]] /@ Select[{"Instance", "Coercion"}, Function[role, TrueQ[record[role]]]]
		]],
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
	"Definition" :> declareDefinition[replayed, name, record["UniverseParameters"], record["Type"], record["Value"], KeyTake[record, {"Instance", "Coercion"}]],
	"Theorem" :> declareTheorem[replayed, name, record["UniverseParameters"], record["Type"], record["Value"]],
	"RewriteRule" :> declareRewriteRule[replayed, name, record["UniverseParameters"], record["NumberOfVariables"], record["LeftHandSide"], record["RightHandSide"]],
	"Quotient" :> declareQuotients[replayed, record["Equality"], record["QuotientNames"]],
	"InductiveType" :> declareInductiveTypes[
		replayed,
		record["UniverseParameters"],
		record["NumberOfParameters"],
		Function[member, member -> constantRecord[original, member]["Type"]] /@ record["Block"],
		Function[constructor, constructor -> constantRecord[original, constructor]["Type"]] /@ Catenate[Function[member, constantRecord[original, member]["Constructors"]] /@ record["Block"]]
	],
	kind_ :> kernelFailure["UnknownDeclaration", "The record of `1` has the unknown kind `2`.", {HoldForm @@ name, kind}]
}]

(* ::Subsection:: *)
(*Translations between rules*)


Options[TypeTheoryTranslate] = {"Axioms" -> False}

TypeTheoryTranslate[environment_?environmentQ, rules_?rulesQ, OptionsPattern[]] := withStoreCleanup @ catchKernelFailure @ With[
	{
		direction = Replace[{TrueQ[rulesSetting[environment, "Prop"]], TrueQ[rules["Prop"]]}, {{True, False} -> "LoseProp", {False, True} -> "GainProp", _ -> "SameProp"}],
		axiomsQ = TrueQ[OptionValue["Axioms"]],
		primary = primaryNames[environment]
	},
	{
		result = Fold[
			Function[{state, name}, translateDeclaration[environment, state, name, direction, axiomsQ]],
			<|"Environment" -> emptyEnvironmentOf[rules], "Failures" -> <||>|>,
			primary
		]
	},
	Success["Translated", <|
		"MessageTemplate" -> "`1` of the `2` declarations translate to the rules `3`.",
		"MessageParameters" -> {Length[primary] - Length[result["Failures"]], Length[primary], rules["Name"]},
		"Environment" -> result["Environment"],
		"Failures" -> KeyMap[ReleaseHold, result["Failures"]]
	|>]
]

(* the declaration of name redeclared in the environment of the other rules, or its failure recorded *)
translateDeclaration[original_, state_Association, name_, direction_String, axiomsQ_] := With[{record = constantRecord[original, name]},
	If[ record["Kind"] === "Axiom" && ! axiomsQ,
		Append[state, "Failures" -> Append[state["Failures"], name -> Failure["AxiomLeftOut", <|
			"MessageTemplate" -> "`1` is an axiom, which a translation keeps only with \"Axioms\" -> True.",
			"MessageParameters" -> {HoldForm @@ name}
		|>]]],
		Replace[catchKernelFailure[translatedDeclaration[original, state["Environment"], name, record, direction]], {
			failure_Failure :> Append[state, "Failures" -> Append[state["Failures"], name -> failure]],
			extended_ :> Append[state, "Environment" -> Replace[catchKernelFailure[registerWhenDeclared[extended, naturalNumberSettings[original]]], _Failure -> extended]]
		}]
	]
]

(* the recursors' levels lowered, or else kept, where the rules lose Prop *)
translatedDeclaration[original_, target_, name_, record_, direction_String] := With[
	{attempt = Function[mode, catchKernelFailure[translatedRecord[original, target, name, record, direction, Function[term, translatedTerm[original, target, direction, mode, term]]]]]},
	Replace[attempt["Lowered"], failure_Failure /; direction === "LoseProp" :> Replace[attempt["Kept"], _Failure -> failure]]
]

translatedRecord[original_, target_, name_, record_, direction_, translate_] := Replace[record["Kind"], {
	"Axiom" :> declareAxiom[target, name, record["UniverseParameters"], translate[record["Type"]]],
	"Definition" :> declareDefinition[target, name, record["UniverseParameters"], translate[record["Type"]], translate[record["Value"]], KeyTake[record, {"Instance", "Coercion"}]],
	"Theorem" /; direction === "GainProp" :> declareDefinition[target, name, record["UniverseParameters"], translate[record["Type"]], translate[record["Value"]]],
	"Theorem" :> declareTheorem[target, name, record["UniverseParameters"], translate[record["Type"]], translate[record["Value"]]],
	"RewriteRule" :> declareRewriteRule[target, name, record["UniverseParameters"], record["NumberOfVariables"], translate[record["LeftHandSide"]], translate[record["RightHandSide"]]],
	"Quotient" :> declareQuotients[target, record["Equality"], record["QuotientNames"]],
	"InductiveType" :> With[
		{
			constructorTypes = Function[constructor, constructor -> translate[constantRecord[original, constructor]["Type"]]] /@
				Catenate[Function[member, constantRecord[original, member]["Constructors"]] /@ record["Block"]]
		},
		declareInductiveTypes[
			target,
			record["UniverseParameters"],
			record["NumberOfParameters"],
			Function[member, member -> raisedProposition[original, target, direction, record, constructorTypes, member, translate[constantRecord[original, member]["Type"]]]] /@ record["Block"],
			constructorTypes
		]
	],
	kind_ :> kernelFailure["UnknownDeclaration", "The record of `1` has the unknown kind `2`.", {HoldForm @@ name}]
}]

(* an inductive proposition, where the rules lose Prop, lives in the universe of its largest field that is
   not of a type of its block, and in Type at least *)
raisedProposition[original_, target_, "LoseProp", record_, constructorTypes_List, member_, type_] /; conclusionSort[constantRecord[original, member]["Type"]] === universeSort[0] :=
	withConclusion[type, universeSort[normalizeLevel[levelMaximum @@ Prepend[
		Catenate[Function[constructor, fieldLevels[target, <||>, record["NumberOfParameters"], record["Block"], Last[constructor], {}]] /@ constructorTypes],
		1
	]]]]
raisedProposition[_, _, _, _, _, _, type_] := type

conclusionSort[dependentFunctionType[_, _, codomain_, _]] := conclusionSort[codomain]
conclusionSort[sort_] := sort

withConclusion[dependentFunctionType[name_, domain_, codomain_, binder_], sort_] := dependentFunctionType[name, domain, withConclusion[codomain, sort], binder]
withConclusion[_, sort_] := sort

(* the universes of a constructor's fields, its parameters skipped *)
fieldLevels[target_, context_, skipped_Integer, block_List, dependentFunctionType[name_, domain_, codomain_, binder_], levels_List] := With[{id = freshFreeVariable[]},
	fieldLevels[
		target,
		extendContext[context, id, name, domain, binder],
		Max[skipped - 1, 0],
		block,
		instantiateBoundVariable[codomain, freeVariable[id]],
		If[ skipped > 0 || ! FreeQ[domain, constantReference[Alternatives @@ block, _]], levels, Append[levels, sortLevel[target, context, domain]]]
	]
]
fieldLevels[_, _, _, _, _, levels_List] := levels

(* Where the rules lose Prop, Prop becomes Type, the lowest universe of types, and every other sort stays: a
   level l becomes max(l, 1), so a constant keeps its universe levels, its own sorts lifted the same way. A
   recursor's level moves with the meaning of its motive's universe. *)
translatedTerm[original_, target_, direction_, mode_, term_] := ReplaceAll[If[TrueQ[rulesSetting[target, "Quantities"]], term, withoutQuantities[term]], {
	universeSort[level_] /; direction === "LoseProp" :> universeSort[normalizeLevel[levelMaximum[level, 1]]],
	constantReference[name : HoldComplete[_InductiveRecursor], levels_List] :> constantReference[name, recursorLevels[original, target, direction, mode, name, levels]]
}]

(* the levels of a recursor in the other rules: its first is the universe its motive goes into, if it has one *)
recursorLevels[original_, target_, direction_, mode_, name_, levels_List] := With[
	{
		sourceUniverse = TrueQ[constantRecord[original, name]["EliminationUniverse"]],
		targetUniverse = constantDeclaredQ[target, name] && TrueQ[constantRecord[target, name]["EliminationUniverse"]]
	},
	Which[
		direction === "LoseProp" && sourceUniverse && targetUniverse && mode === "Lowered", Prepend[Rest[levels], loweredUniverse[First[levels]]],
		direction === "LoseProp" && ! sourceUniverse && targetUniverse, Prepend[levels, 0],
		direction === "GainProp" && sourceUniverse && targetUniverse, Prepend[Rest[levels], normalizeLevel[levelSuccessor[First[levels], 1]]],
		True, levels
	]
]

(* the level u with Sort (u + 1) the translation of Sort l, max(l, 1): l less one, or 0 for Prop; a universe
   parameter that may be 0 has none, and stays, so what uses it fails to check *)
loweredUniverse[level_Integer] := Max[level, 1] - 1
loweredUniverse[levelSuccessor[base_, k_Integer]] /; k >= 1 := normalizeLevel[levelSuccessor[base, k - 1]]
loweredUniverse[level_] := level

(* each registration of the natural numbers is replayed as soon as the constants it names are declared *)
registerWhenDeclared[replayed_, settings_Association] := With[
	{next = Replace[naturalNumberSettings[replayed], {registered_Association :> Length[registered["Registrations"]] + 1, None -> 1}]},
	If[ next <= Length[settings["Registrations"]] && AllTrue[registrationNames[settings, next], Function[name, constantDeclaredQ[replayed, name]]],
		registerWhenDeclared[registerNaturalNumbers[replayed, registrationOf[settings, next]], settings],
		replayed
	]
]
registerWhenDeclared[replayed_, None] := replayed
