(* ::Package:: *)

(*
Declarations: axioms, definitions, theorems and inductive types.

Each Declare function elaborates its surface terms and has the kernel check the result. If the check
succeeds it sets $TypeTheoryEnvironment to the extended environment and gives it; if anything fails it
gives a Failure and leaves $TypeTheoryEnvironment as it was. To declare into another environment
without touching the default, bind it:

	Block[{$TypeTheoryEnvironment = environment}, DeclareAxiom[name, type]]

gives environment extended with the axiom.

The arguments are held, so a declaration reads like mathematics and nothing in it evaluates. A name is
any expression, usually a symbol; the prelude's names are built-in symbols such as Equal and Plus.

Universe parameters are the symbols in universe levels, such as u in TypeUniverse[u], in the order
they first appear; the option "UniverseParameters" lists them explicitly instead.

The core functions declareAxiom, declareDefinition and declareTheorem take core terms. Like
declareInductiveType they check everything themselves and throw a kernel failure when a check fails, so
an environment built only through them holds only checked constants.
*)


(* ::Section:: *)
(*PackageExported*)


PackageExported[DeclareAxiom]
PackageExported[DeclareDefinition]
PackageExported[DeclareTheorem]
PackageExported[DeclareInductiveType]


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[declareAxiom]
PackageScoped[declareDefinition]
PackageScoped[declareTheorem]
PackageScoped[declarationUniverseParameters]
PackageScoped[universeParameterNames]
PackageScoped[heldOptionValue]
PackageScoped[updateEnvironment]


(* ::Section:: *)
(*Usage Messages*)


DeclareAxiom::usage = "DeclareAxiom[name, type] declares name as an axiom of the given type in $TypeTheoryEnvironment and gives the new environment.\n\
The option \"UniverseParameters\" -> {u, ...} lists the universe parameters; Automatic takes the symbols in universe levels in the order they appear."
DeclareDefinition::usage = "DeclareDefinition[name, value] declares name as a definition with the given value in $TypeTheoryEnvironment and gives the new environment.\n\
DeclareDefinition[name, Typed[value, type]] declares name with the given type.\n\
The option \"UniverseParameters\" -> {u, ...} lists the universe parameters; Automatic takes the symbols in universe levels in the order they appear."
DeclareTheorem::usage = "DeclareTheorem[name, statement, proof] checks that proof proves statement and declares name as a theorem in $TypeTheoryEnvironment, giving the new environment.\n\
DeclareTheorem[name, proof] declares the statement of the finished TypeTheoryProof proof.\n\
proof is a term, a TypeTheoryTerm or a finished TypeTheoryProof. The option \"UniverseParameters\" -> {u, ...} lists the universe parameters; \
Automatic takes the symbols in universe levels in the order they appear."
DeclareInductiveType::usage = "DeclareInductiveType[name, type, {constructor1 -> type1, ...}] declares the inductive type name with the given \
constructors, and its recursor InductiveRecursor[name], in $TypeTheoryEnvironment and gives the new environment.\n\
The option \"Parameters\" -> n makes the first n arguments of name parameters, which every constructor takes first and passes on unchanged; Automatic takes as many as every constructor allows. \
The option \"UniverseParameters\" -> {u, ...} lists the universe parameters; Automatic takes the symbols in universe levels in the order they appear."

declareAxiom::usage = "declareAxiom[environment, HoldComplete[name], {HoldComplete[u], ...}, type] checks the core type and gives environment with the axiom name added."
declareDefinition::usage = "declareDefinition[environment, HoldComplete[name], {HoldComplete[u], ...}, type, value] checks the core value against the \
core type and gives environment with the definition name added."
declareTheorem::usage = "declareTheorem[environment, HoldComplete[name], {HoldComplete[u], ...}, statement, proof] checks that statement is a \
proposition and proof proves it, and gives environment with the theorem name added."
declarationUniverseParameters::usage = "declarationUniverseParameters[function, Hold[options], {syntax, ...}] gives the universe parameters \
{HoldComplete[u], ...} of a declaration from its \"UniverseParameters\" option, or from the universe levels in the syntax trees."
universeParameterNames::usage = "universeParameterNames[{syntax, ...}] gives the symbols in universe levels of the syntax trees, as {HoldComplete[u], ...} in the order they first appear."
heldOptionValue::usage = "heldOptionValue[function, Hold[options], name] gives HoldComplete[value] for the option name among the held options, or among the defaults Options[function]."
updateEnvironment::usage = "updateEnvironment[environment] sets $TypeTheoryEnvironment to environment and gives it; updateEnvironment[failure] gives failure."


(* ::Section:: *)
(*Function Definitions*)


Options[DeclareAxiom] = {"UniverseParameters" -> Automatic}
Options[DeclareDefinition] = {"UniverseParameters" -> Automatic}
Options[DeclareTheorem] = {"UniverseParameters" -> Automatic}
Options[DeclareInductiveType] = {"Parameters" -> Automatic, "UniverseParameters" -> Automatic}

SetAttributes[{DeclareAxiom, DeclareDefinition, DeclareTheorem, DeclareInductiveType}, HoldAll]


updateEnvironment[environment_TypeTheoryEnvironment] := ($TypeTheoryEnvironment = environment)
updateEnvironment[failure_Failure] := failure


DeclareAxiom[name_, type_, options : OptionsPattern[]] := updateEnvironment @ catchKernelFailure @ With[
	{environment = $TypeTheoryEnvironment, universeParameters = declarationUniverseParameters[DeclareAxiom, Hold[options], {toSyntax[type]}]},
	declareAxiom[environment, HoldComplete[name], universeParameters, elaborateClosedType[environment, HoldComplete[type], universeParameters]]
]

DeclareDefinition[name_, value_, options : OptionsPattern[]] := updateEnvironment @ catchKernelFailure @ With[
	{environment = $TypeTheoryEnvironment, universeParameters = declarationUniverseParameters[DeclareDefinition, Hold[options], {toSyntax[value]}]},
	{elaborated = elaborateClosedTerm[environment, HoldComplete[value], None, universeParameters]},
	declareDefinition[environment, HoldComplete[name], universeParameters, betaNormalize[Last[elaborated]], First[elaborated]]
]

DeclareTheorem[name_, statement_, proof_, options : OptionsPattern[]] := updateEnvironment @ catchKernelFailure @ With[
	{
		environment = $TypeTheoryEnvironment,
		universeParameters = declarationUniverseParameters[DeclareTheorem, Hold[options], {toSyntax[statement], toSyntax[proof]}]
	},
	{type = elaborateClosedType[environment, HoldComplete[statement], universeParameters]},
	declareTheorem[environment, HoldComplete[name], universeParameters, type, theoremValue[environment, HoldComplete[proof], type, universeParameters]]
]

(* the statement and universe parameters come from the proof *)
DeclareTheorem[name_, proof_, options : OptionsPattern[]] := updateEnvironment @ catchKernelFailure @ Replace[proof, {
	state : TypeTheoryProof[_Association] :>
		declareTheorem[$TypeTheoryEnvironment, HoldComplete[name], proofUniverseParameters[state], proofStatement[state], completedProofTerm[state]],
	failure_Failure :> throwFailure[failure],
	other_ :> kernelFailure["ProofExpected", "`1` is not a TypeTheoryProof.", {Short[other]}]
}]

(* A proof written as TypeTheoryProof[statement, tactics] runs here; any other proof is a term, which may
   also name a finished proof stored in a symbol. *)
theoremValue[environment_, HoldComplete[proof_TypeTheoryProof], _, _] := Replace[proof, {
	state : TypeTheoryProof[_Association] :> completedProofTerm[state],
	failure_Failure :> throwFailure[failure]
}]
theoremValue[environment_, held_HoldComplete, type_, universeParameters_List] := First[elaborateClosedTerm[environment, held, type, universeParameters]]


DeclareInductiveType[name_, type_, constructors_List, options : OptionsPattern[]] := updateEnvironment @ catchKernelFailure @ Module[
	{environment = $TypeTheoryEnvironment, parsedConstructors, universeParameters, typeCore, provisional, constructorCores},
	parsedConstructors = constructorSpecifications[constructors];
	universeParameters = declarationUniverseParameters[
		DeclareInductiveType,
		Hold[options],
		Prepend[Function[pair, toSyntax @@ Last[pair]] /@ parsedConstructors, toSyntax[type]]
	];
	typeCore = elaborateClosedType[environment, HoldComplete[type], universeParameters];
	(* the constructor types may mention the type being declared *)
	provisional = addConstantRecords[environment, <|HoldComplete[name] -> <|
		"Kind" -> "InductiveType",
		"Type" -> typeCore,
		"UniverseParameters" -> universeParameters,
		"NumberOfParameters" -> 0,
		"NumberOfIndices" -> 0,
		"Constructors" -> {},
		"LargeElimination" -> False
	|>|>];
	constructorCores = Function[pair, First[pair] -> elaborateClosedType[provisional, Last[pair], universeParameters]] /@ parsedConstructors;
	declareInductiveType[
		environment,
		HoldComplete[name],
		universeParameters,
		Replace[heldOptionValue[DeclareInductiveType, Hold[options], "Parameters"], {
			HoldComplete[Automatic] :> sharedParameterCount[provisional, typeCore, Last /@ constructorCores],
			HoldComplete[n_Integer?NonNegative] :> n,
			HoldComplete[other_] :> kernelFailure["InvalidOption", "The value of the option \"Parameters\" must be a non-negative integer or Automatic, not `1`.", {HoldForm[other]}]
		}],
		typeCore,
		constructorCores
	]
]

(* {constructor -> type, ...}, held, as {{HoldComplete[constructor], HoldComplete[type]}, ...} *)
SetAttributes[constructorSpecifications, HoldFirst]
constructorSpecifications[constructors_] := With[
	{parsed = Cases[Unevaluated[constructors], (Rule | RuleDelayed)[constructor_, type_] :> {HoldComplete[constructor], HoldComplete[type]}]},
	If[ Length[parsed] =!= Length[Unevaluated[constructors]],
		kernelFailure["ConstructorSpecification", "Each constructor must be given as constructor -> type.", {}],
		parsed
	]
]


(* ::Subsection:: *)
(*Parameters*)


(* The largest n such that every constructor takes the type's first n binders first, with the same
   types, and passes them on unchanged to its result. *)
sharedParameterCount[environment_, typeCore_, constructorTypes_List] := Module[{typeContext, typeIds, resultType},
	{typeContext, typeIds, resultType} = typeTelescope[environment, <||>, typeCore];
	Min[Length[typeIds], Function[constructorType, constructorParameterCount[environment, typeContext, typeIds, constructorType]] /@ constructorTypes]
]

constructorParameterCount[environment_, typeContext_, typeIds_List, constructorType_] := Module[{matched, remaining, conclusion},
	{matched, remaining} = matchLeadingBinders[environment, typeContext, typeIds, constructorType, 0];
	conclusion = Last @ typeTelescope[environment, typeContext, remaining];
	commonPrefixLength[Last @ applicationSpine[conclusion], freeVariable /@ Take[typeIds, matched]]
]

matchLeadingBinders[_, _, {}, constructorType_, count_Integer] := {count, constructorType}
matchLeadingBinders[environment_, typeContext_, {id_, rest___}, constructorType_, count_Integer] := Replace[
	weakHeadNormalForm[environment, typeContext, constructorType],
	{
		dependentFunctionType[_, domain_, codomain_, _] /; definitionallyEqualQ[environment, typeContext, domain, typeContext[id]["Type"]] :>
			matchLeadingBinders[environment, typeContext, {rest}, instantiateBoundVariable[codomain, freeVariable[id]], count + 1],
		other_ :> {count, other}
	}
]

commonPrefixLength[first_List, second_List] := With[{length = Min[Length[first], Length[second]]},
	LengthWhile[Transpose[{Take[first, length], Take[second, length]}], Apply[SameQ]]
]


(* ::Subsection:: *)
(*Options and universe parameters*)


heldOptionValue[function_Symbol, Hold[options___], name_String] := First[Cases[
	Join[Hold[options], Hold @@ Options[function]],
	(Rule | RuleDelayed)[name, value_] :> HoldComplete[value],
	{1, 2}
]]

declarationUniverseParameters[function_Symbol, heldOptions_Hold, syntaxes_List] := Replace[heldOptionValue[function, heldOptions, "UniverseParameters"], {
	HoldComplete[Automatic] :> universeParameterNames[syntaxes],
	HoldComplete[{parameters___Symbol}] :> HoldComplete /@ Unevaluated[{parameters}],
	HoldComplete[other_] :> kernelFailure["InvalidOption", "The value of the option \"UniverseParameters\" must be a list of symbols or Automatic, not `1`.", {HoldForm[other]}]
}]

universeParameterNames[syntaxes_List] := DeleteDuplicates @ Catenate[levelParameterNames /@ Join[
	Cases[syntaxes, syntaxApplication[syntaxSymbol[HoldComplete[TypeUniverse]], {level_}] :> level, {0, Infinity}],
	Catenate @ Cases[syntaxes, syntaxApplication[syntaxSymbol[HoldComplete[Subscript]], {_, levels__}] :> {levels}, {0, Infinity}]
]]

(* the symbols of a level, leaving out the heads Plus, Max and ImpredicativeMaximum *)
levelParameterNames[syntaxSymbol[held_]] := {held}
levelParameterNames[syntaxApplication[_, arguments_List]] := Catenate[levelParameterNames /@ arguments]
levelParameterNames[_] := {}


(* ::Subsection:: *)
(*Core declarations*)


declareAxiom[environment_, name_HoldComplete, universeParameters_List, type_] := (
	checkUniverseParameters[name, universeParameters, {type}];
	sortLevel[environment, <||>, type];
	addConstantRecords[environment, <|name -> <|"Kind" -> "Axiom", "Type" -> type, "UniverseParameters" -> universeParameters|>|>]
)

declareDefinition[environment_, name_HoldComplete, universeParameters_List, type_, value_] := (
	checkUniverseParameters[name, universeParameters, {type, value}];
	sortLevel[environment, <||>, type];
	checkHasType[environment, <||>, value, type];
	addConstantRecords[environment, <|name -> <|"Kind" -> "Definition", "Type" -> type, "UniverseParameters" -> universeParameters, "Value" -> value|>|>]
)

(* a theorem is a proposition, and its proof is never unfolded *)
declareTheorem[environment_, name_HoldComplete, universeParameters_List, type_, value_] := (
	checkUniverseParameters[name, universeParameters, {type, value}];
	If[ ! levelEquivalentQ[sortLevel[environment, <||>, type], 0],
		kernelFailure["PropositionExpected", "The statement of the theorem `1` must be a proposition.", {HoldForm @@ name}]
	];
	checkHasType[environment, <||>, value, type];
	addConstantRecords[environment, <|name -> <|"Kind" -> "Theorem", "Type" -> type, "UniverseParameters" -> universeParameters, "Value" -> value|>|>]
)
