(* ::Package:: *)

(*
Declarations: the constructors TypeTheoryAxiom, TypeTheoryDefinition, TypeTheoryTheorem,
TypeTheoryInductiveType and TypeTheoryNaturalNumbers, and the environments built from them.

A declaration is inert data. Its arguments are held, so it reads like mathematics and nothing in it
evaluates, and it means nothing until it is added to an environment:

	TypeTheoryAxiom[name, type]
	TypeTheoryDefinition[name, value]                           value may be Typed[v, type]
	TypeTheoryTheorem[name, statement, proof]
	TypeTheoryTheorem[name, proof]                              proof a finished TypeTheoryProof
	TypeTheoryInductiveType[name, type, {constructor -> type, ...}]
	TypeTheoryNaturalNumbers[type, zero, successor]            the literals 0, 1, 2, ... become elements of type
	TypeTheoryNaturalNumbers[type, zero, successor, addition]   and adding two literals computes

TypeTheoryEnvironment[environment, {declaration, ...}] elaborates each declaration's terms in the
environment so far, has the kernel check them, and gives the extended environment, or a Failure for the
first declaration that does not check. Append[environment, declaration] adds one declaration.

A name is any expression: a symbol, or a string for a constant imported from elsewhere. Universe
parameters are the symbols and strings in universe levels, in the order they first appear; the option
"UniverseParameters" lists them explicitly.

The core functions declareAxiom, declareDefinition and declareTheorem take core terms. Like
declareInductiveType and registerNaturalNumbers, they check everything themselves and throw a kernel
failure when a check fails.
*)


(* ::Section:: *)
(*PackageExported*)


PackageExported[TypeTheoryAxiom]
PackageExported[TypeTheoryDefinition]
PackageExported[TypeTheoryTheorem]
PackageExported[TypeTheoryInductiveType]
PackageExported[TypeTheoryNaturalNumbers]


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[declareAxiom]
PackageScoped[declareDefinition]
PackageScoped[declareTheorem]
PackageScoped[addDeclaration]
PackageScoped[declarationQ]
PackageScoped[declarationUniverseParameters]
PackageScoped[universeParameterNames]
PackageScoped[heldOptionValue]
PackageScoped[$emptyEnvironment]


(* ::Section:: *)
(*Usage Messages*)


TypeTheoryAxiom::usage = "TypeTheoryAxiom[name, type] declares name as an axiom of the given type, when added to a TypeTheoryEnvironment.\n\
The option \"UniverseParameters\" -> {u, ...} lists the universe parameters; Automatic takes the symbols and strings in universe levels in the order they appear."
TypeTheoryDefinition::usage = "TypeTheoryDefinition[name, value] declares name as a definition with the given value, when added to a TypeTheoryEnvironment.\n\
TypeTheoryDefinition[name, Typed[value, type]] gives the definition the given type.\n\
The option \"UniverseParameters\" -> {u, ...} lists the universe parameters; Automatic takes the symbols and strings in universe levels in the order they appear."
TypeTheoryTheorem::usage = "TypeTheoryTheorem[name, statement, proof] declares name as a theorem: proof must prove statement when it is added to a TypeTheoryEnvironment.\n\
TypeTheoryTheorem[name, proof] declares the statement of the finished TypeTheoryProof proof.\n\
proof is a term, a TypeTheoryTerm or a finished TypeTheoryProof. The option \"UniverseParameters\" -> {u, ...} lists the universe parameters."
TypeTheoryInductiveType::usage = "TypeTheoryInductiveType[name, type, {constructor1 -> type1, ...}] declares the inductive type name with the given constructors, \
and its recursor InductiveRecursor[name], when added to a TypeTheoryEnvironment.\n\
The option \"Parameters\" -> n makes the first n arguments of name parameters, which every constructor takes first and passes on unchanged; \
Automatic takes as many as every constructor allows. The option \"UniverseParameters\" -> {u, ...} lists the universe parameters."
TypeTheoryNaturalNumbers::usage = "TypeTheoryNaturalNumbers[type, zero, successor] registers the inductive type type, with the constructors zero and successor, \
as the natural numbers, so the literals 0, 1, 2, ... are elements of type.\n\
TypeTheoryNaturalNumbers[type, zero, successor, addition] also adds two literals by integer addition; addition must be defined by recursion on its second argument."

declareAxiom::usage = "declareAxiom[environment, HoldComplete[name], {HoldComplete[u], ...}, type] checks the core type and gives environment with the axiom name added."
declareDefinition::usage = "declareDefinition[environment, HoldComplete[name], {HoldComplete[u], ...}, type, value] checks the core value against the core type \
and gives environment with the definition name added."
declareTheorem::usage = "declareTheorem[environment, HoldComplete[name], {HoldComplete[u], ...}, statement, proof] checks that statement is a proposition and \
proof proves it, and gives environment with the theorem name added."
addDeclaration::usage = "addDeclaration[environment, declaration] elaborates and checks the declaration and gives the extended environment, or throws a kernel failure."
declarationQ::usage = "declarationQ[expr] gives True if expr is a declaration: TypeTheoryAxiom, TypeTheoryDefinition, TypeTheoryTheorem, TypeTheoryInductiveType \
or TypeTheoryNaturalNumbers."
declarationUniverseParameters::usage = "declarationUniverseParameters[head, Hold[options], {syntax, ...}] gives the universe parameters {HoldComplete[u], ...} \
of a declaration from its \"UniverseParameters\" option, or from the universe levels in the syntax trees."
universeParameterNames::usage = "universeParameterNames[{syntax, ...}] gives the symbols and strings in universe levels of the syntax trees, \
as {HoldComplete[u], ...} in the order they first appear."
heldOptionValue::usage = "heldOptionValue[head, Hold[options], name] gives HoldComplete[value] for the option name among the held options, or among the defaults Options[head]."
$emptyEnvironment::usage = "$emptyEnvironment is the environment with no constants, in which a TypeTheoryTerm without an environment is checked."


(* ::Section:: *)
(*Function Definitions*)


Options[TypeTheoryAxiom] = {"UniverseParameters" -> Automatic}
Options[TypeTheoryDefinition] = {"UniverseParameters" -> Automatic}
Options[TypeTheoryTheorem] = {"UniverseParameters" -> Automatic}
Options[TypeTheoryInductiveType] = {"Parameters" -> Automatic, "UniverseParameters" -> Automatic}

SetAttributes[{TypeTheoryAxiom, TypeTheoryDefinition, TypeTheoryTheorem, TypeTheoryInductiveType, TypeTheoryNaturalNumbers}, HoldAll]

declarationQ[_TypeTheoryAxiom | _TypeTheoryDefinition | _TypeTheoryTheorem | _TypeTheoryInductiveType | _TypeTheoryNaturalNumbers] := True
declarationQ[_] := False


(* ::Subsection:: *)
(*Environments from declarations*)


TypeTheoryEnvironment[] := $emptyEnvironment
TypeTheoryEnvironment["Prelude"] := preludeEnvironment[]
TypeTheoryEnvironment[declarations_List] := TypeTheoryEnvironment[$emptyEnvironment, declarations]
TypeTheoryEnvironment[environment_?environmentQ, declaration_?declarationQ] := TypeTheoryEnvironment[environment, {declaration}]

(* the stores of the steps in between are removed, and so are all of them when a declaration fails *)
TypeTheoryEnvironment[environment_?environmentQ, declarations_List] := withStoreCleanup @ catchKernelFailure @ Fold[addDeclaration, environment, declarations]

TypeTheoryEnvironment /: Append[environment : TypeTheoryEnvironment[_Symbol]?environmentQ, declaration_] := TypeTheoryEnvironment[environment, {declaration}]


addDeclaration[environment_, TypeTheoryAxiom[name_, type_, options : OptionsPattern[]]] := With[
	{universeParameters = declarationUniverseParameters[TypeTheoryAxiom, Hold[options], {toSyntax[type]}]},
	declareAxiom[environment, HoldComplete[name], universeParameters, elaborateClosedType[environment, HoldComplete[type], universeParameters]]
]

(* a definition keeps the type it is given, implicit binders included, and its value only has to have
   that type: Lean's projections, for one, take their parameters explicitly in the value *)
addDeclaration[environment_, TypeTheoryDefinition[name_, Typed[value_, type_], options : OptionsPattern[]]] := With[
	{universeParameters = declarationUniverseParameters[TypeTheoryDefinition, Hold[options], {toSyntax[Typed[value, type]]}]},
	{typeCore = elaborateClosedType[environment, HoldComplete[type], universeParameters]},
	declareDefinition[environment, HoldComplete[name], universeParameters, typeCore, First[elaborateClosedTerm[environment, HoldComplete[value], typeCore, universeParameters]]]
]

addDeclaration[environment_, TypeTheoryDefinition[name_, value_, options : OptionsPattern[]]] := With[
	{universeParameters = declarationUniverseParameters[TypeTheoryDefinition, Hold[options], {toSyntax[value]}]},
	{elaborated = elaborateClosedTerm[environment, HoldComplete[value], None, universeParameters]},
	declareDefinition[environment, HoldComplete[name], universeParameters, betaNormalize[Last[elaborated]], First[elaborated]]
]

addDeclaration[environment_, TypeTheoryTheorem[name_, statement_, proof_, options : OptionsPattern[]]] := With[
	{universeParameters = declarationUniverseParameters[TypeTheoryTheorem, Hold[options], {toSyntax[statement], toSyntax[proof]}]},
	{type = elaborateClosedType[environment, HoldComplete[statement], universeParameters]},
	declareTheorem[environment, HoldComplete[name], universeParameters, type, theoremValue[environment, HoldComplete[proof], type, universeParameters]]
]

(* the statement and universe parameters come from the proof, which is evaluated *)
addDeclaration[environment_, TypeTheoryTheorem[name_, proof_, options : OptionsPattern[]]] := Replace[proof, {
	state : TypeTheoryProof[_Association] :>
		declareTheorem[environment, HoldComplete[name], proofUniverseParameters[state], proofStatement[state], completedProofTerm[state]],
	failure_Failure :> throwFailure[failure],
	other_ :> kernelFailure["ProofExpected", "`1` is not a TypeTheoryProof.", {Short[other]}]
}]

addDeclaration[environment_, TypeTheoryInductiveType[name_, type_, constructors_List, options : OptionsPattern[]]] := Module[
	{parsedConstructors, universeParameters, typeCore, provisional, constructorCores},
	parsedConstructors = constructorSpecifications[constructors];
	universeParameters = declarationUniverseParameters[
		TypeTheoryInductiveType,
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
		"LargeElimination" -> False,
		"Recursive" -> False
	|>|>];
	constructorCores = Function[pair, First[pair] -> elaborateClosedType[provisional, Last[pair], universeParameters]] /@ parsedConstructors;
	declareInductiveType[
		environment,
		HoldComplete[name],
		universeParameters,
		Replace[heldOptionValue[TypeTheoryInductiveType, Hold[options], "Parameters"], {
			HoldComplete[Automatic] :> sharedParameterCount[provisional, typeCore, Last /@ constructorCores],
			HoldComplete[n_Integer?NonNegative] :> n,
			HoldComplete[other_] :> kernelFailure["InvalidOption", "The value of the option \"Parameters\" must be a non-negative integer or Automatic, not `1`.", {HoldForm[other]}]
		}],
		typeCore,
		constructorCores
	]
]

addDeclaration[environment_, TypeTheoryNaturalNumbers[type_, zero_, successor_]] :=
	registerNaturalNumbers[environment, <|"Type" -> HoldComplete[type], "Zero" -> HoldComplete[zero], "Successor" -> HoldComplete[successor], "Addition" -> None|>]

addDeclaration[environment_, TypeTheoryNaturalNumbers[type_, zero_, successor_, addition_]] := registerNaturalNumbers[
	environment,
	<|"Type" -> HoldComplete[type], "Zero" -> HoldComplete[zero], "Successor" -> HoldComplete[successor], "Addition" -> HoldComplete[addition]|>
]

addDeclaration[_, other_] := kernelFailure["DeclarationExpected", "`1` is not a declaration.", {Short[other]}]


(* A proof written as TypeTheoryProof[...] runs here; any other proof is a term, which may also name a
   finished proof stored in a symbol. *)
theoremValue[environment_, HoldComplete[proof_TypeTheoryProof], _, _] := Replace[proof, {
	state : TypeTheoryProof[_Association] :> completedProofTerm[state],
	failure_Failure :> throwFailure[failure]
}]
theoremValue[environment_, held_HoldComplete, type_, universeParameters_List] := First[elaborateClosedTerm[environment, held, type, universeParameters]]

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


heldOptionValue[head_Symbol, Hold[options___], name_String] := First[Cases[
	Join[Hold[options], Hold @@ Options[head]],
	(Rule | RuleDelayed)[name, value_] :> HoldComplete[value],
	{1, 2}
]]

declarationUniverseParameters[head_Symbol, heldOptions_Hold, syntaxes_List] := Replace[heldOptionValue[head, heldOptions, "UniverseParameters"], {
	HoldComplete[Automatic] :> universeParameterNames[syntaxes],
	HoldComplete[{parameters___}] /; AllTrue[Unevaluated[{parameters}], Function[parameter, MatchQ[Unevaluated[parameter], _Symbol | _String], HoldAll]] :>
		HoldComplete /@ Unevaluated[{parameters}],
	HoldComplete[other_] :> kernelFailure[
		"InvalidOption",
		"The value of the option \"UniverseParameters\" must be a list of symbols or strings, or Automatic, not `1`.",
		{HoldForm[other]}
	]
}]

universeParameterNames[syntaxes_List] := DeleteDuplicates @ Catenate[levelParameterNames /@ Join[
	Cases[syntaxes, syntaxApplication[syntaxSymbol[HoldComplete[TypeUniverse]], {level_}] :> level, {0, Infinity}],
	Catenate @ Cases[syntaxes, syntaxApplication[syntaxSymbol[HoldComplete[Subscript]], {_, levels__}] :> {levels}, {0, Infinity}]
]]

(* the symbols and strings of a level, leaving out the heads Plus, Max and ImpredicativeMaximum *)
levelParameterNames[syntaxSymbol[held_]] := {held}
levelParameterNames[syntaxString[name_]] := {HoldComplete[name]}
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
