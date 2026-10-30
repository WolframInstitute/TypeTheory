(* ::Package:: *)

(*
Declarations: the constructors TypeTheoryAxiom, TypeTheoryDefinition, TypeTheoryTheorem,
TypeTheoryInductiveType, TypeTheoryNaturalNumbers, TypeTheoryRewriteRule and TypeTheoryQuotients, and the
environments built from them.

A declaration is inert data. Its arguments are held, so it reads like mathematics and nothing in it
evaluates, and it means nothing until it is added to an environment:

	TypeTheoryAxiom[name, type]
	TypeTheoryDefinition[name, value]                           value may be Typed[v, type]
	TypeTheoryDefinition[name, value, "Opaque" -> True]         checked as a definition, but never unfolded
	TypeTheoryTheorem[name, statement, proof]
	TypeTheoryTheorem[name, proof]                              proof a finished TypeTheoryProof
	TypeTheoryInductiveType[name, type, {constructor -> type, ...}]
	TypeTheoryInductiveType[{name -> type, ...}, {constructor -> type, ...}]
	                                                            mutually inductive types
	TypeTheoryNaturalNumbers[type, zero, successor]            the literals 0, 1, 2, ... become elements of type
	TypeTheoryNaturalNumbers[type, zero, successor, <|role -> operation, ...|>]
	                                                            and the operations compute on literals
	TypeTheoryNaturalNumbers[type, zero, successor, addition]   the same, with addition the only operation
	TypeTheoryRewriteRule[name, ForAll[binders, lhs -> rhs]]    lhs, an axiom applied to arguments, computes to rhs
	TypeTheoryQuotients[]                                       the quotient types of Lean's kernel (Quotients.wl)
	TypeTheoryQuotients[equality, {type, introduction, lift, induction}]
	                                                            the same under other names, with another equality
	TypeTheoryCubical[sum]                                      the interval, paths, transport and composition of cubical
	                                                            type theory (Cubical.wl)

TypeTheoryEnvironment[environment, {declaration, ...}] elaborates each declaration's terms in the
environment so far, has the kernel check them, and gives the extended environment, or a Failure for the
first declaration that does not check. Append[environment, declaration] adds one declaration.

TypeTheoryEnvironment[rules] starts an environment with no constants that follows the TypeTheoryRules
rules; every environment made from it follows them too. Rewrite rules may only be declared where the
rules allow them, and under rules without Prop a theorem may state any type. Under rules with
quantities, the value of a definition, the proof of a theorem and the right side of a rewrite rule pass
the live check of Quantities.wl.

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
PackageExported[TypeTheoryRewriteRule]
PackageExported[TypeTheoryQuotients]


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[declareAxiom]
PackageScoped[declareDefinition]
PackageScoped[declareTheorem]
PackageScoped[declareRewriteRule]
PackageScoped[emptyEnvironmentOf]
PackageScoped[addDeclaration]
PackageScoped[declarationQ]
PackageScoped[declarationUniverseParameters]
PackageScoped[universeParameterNames]
PackageScoped[heldOptionValue]
PackageScoped[$emptyEnvironment]
PackageScoped[$deferKernelChecks]


(* ::Section:: *)
(*Usage Messages*)


TypeTheoryAxiom::usage = "TypeTheoryAxiom[name, type] declares name as an axiom of the given type, when added to a TypeTheoryEnvironment.\n\
The option \"UniverseParameters\" -> {u, ...} lists the universe parameters; Automatic takes the symbols and strings in universe levels in the order they appear."
TypeTheoryDefinition::usage = "TypeTheoryDefinition[name, value] declares name as a definition with the given value, when added to a TypeTheoryEnvironment.\n\
TypeTheoryDefinition[name, Typed[value, type]] gives the definition the given type.\n\
The option \"UniverseParameters\" -> {u, ...} lists the universe parameters; Automatic takes the symbols and strings in universe levels in the order they appear. \
The option \"Instance\" -> True makes the definition an instance of its type's class, the constant its type applies at the end, which elaboration finds \
for an argument of an instance-implicit binder. The option \"Coercion\" -> True makes a function of one explicit argument a coercion, which elaboration \
applies to a term whose type is the function's domain where its codomain is expected. The option \"Opaque\" -> True makes the definition opaque, \
as Lean's opaque constants are: its value is checked against its type, but it never unfolds, so it equals only itself."
TypeTheoryTheorem::usage = "TypeTheoryTheorem[name, statement, proof] declares name as a theorem: proof must prove statement when it is added to a TypeTheoryEnvironment. \
statement must be a proposition, or under rules without Prop any type; a theorem is never unfolded.\n\
TypeTheoryTheorem[name, proof] declares the statement of the finished TypeTheoryProof proof.\n\
proof is a term, a TypeTheoryTerm or a finished TypeTheoryProof. The option \"UniverseParameters\" -> {u, ...} lists the universe parameters."
TypeTheoryInductiveType::usage = "TypeTheoryInductiveType[name, type, {constructor1 -> type1, ...}] declares the inductive type name with the given constructors, \
and its recursor InductiveRecursor[name], when added to a TypeTheoryEnvironment.\n\
The option \"Parameters\" -> n makes the first n arguments of name parameters, which every constructor takes first and passes on unchanged; \
Automatic takes as many as every constructor allows. The option \"UniverseParameters\" -> {u, ...} lists the universe parameters."
TypeTheoryRewriteRule::usage = "TypeTheoryRewriteRule[name, ForAll[{Typed[x, type], ...}, lhs -> rhs]] declares that lhs computes to rhs for every \
x, ..., when added to a TypeTheoryEnvironment whose rules allow rewrite rules.\n\
lhs must be an axiom applied to arguments in which each variable occurs, and rhs must have the type of lhs. Like an axiom, a rewrite rule is \
trusted: it may make the theory inconsistent, or computation endless. The option \"UniverseParameters\" -> {u, ...} lists the universe parameters."
TypeTheoryQuotients::usage = "TypeTheoryQuotients[] declares the quotient types of Lean's kernel, QuotientType, QuotientIntroduction, QuotientLift and \
QuotientInduction, when added to a TypeTheoryEnvironment whose rules have quotients and whose Equal is the equality of the prelude: \
QuotientLift[f, h, QuotientIntroduction[r, a]] computes to f[a].\n\
TypeTheoryQuotients[equality, {type, introduction, lift, induction}] declares them under the given names, with the inductive type equality as the equality."
TypeTheoryNaturalNumbers::usage = "TypeTheoryNaturalNumbers[type, zero, successor] registers the inductive type type, with the constructors zero and successor, \
as the natural numbers, so the literals 0, 1, 2, ... are elements of type.\n\
TypeTheoryNaturalNumbers[type, zero, successor, <|role -> operation, ...|>] also registers operations that the kernel computes on literals with integers, \
trusting that each computes what its role names: \"Addition\", \"Subtraction\", \"Multiplication\", \"Power\", \"Quotient\", \"Remainder\", \"GCD\", \"Log2\", \
\"BitAnd\", \"BitOr\", \"BitXor\", \"ShiftLeft\", \"ShiftRight\", and \"Equal\" and \"LessEqual\", which give Booleans. A later registration of the same \
natural numbers adds operations.\n\
TypeTheoryNaturalNumbers[type, zero, successor, addition] registers addition as the only operation."

declareAxiom::usage = "declareAxiom[environment, HoldComplete[name], {HoldComplete[u], ...}, type] checks the core type and gives environment with the axiom name added."
declareDefinition::usage = "declareDefinition[environment, HoldComplete[name], {HoldComplete[u], ...}, type, value] checks the core value against the core type \
and gives environment with the definition name added.\n\
declareDefinition[environment, HoldComplete[name], {HoldComplete[u], ...}, type, value, <|\"Instance\" -> True, \"Coercion\" -> True|>] adds it as an instance or \
a coercion for elaboration, which the kernel checks as any definition. With \"Opaque\" -> True its record is of the kind \"Opaque\", which never unfolds."
declareTheorem::usage = "declareTheorem[environment, HoldComplete[name], {HoldComplete[u], ...}, statement, proof] checks that statement is a proposition, or \
under rules without Prop a type, and that proof proves it, and gives environment with the theorem name added."
declareRewriteRule::usage = "declareRewriteRule[environment, HoldComplete[name], {HoldComplete[u], ...}, numberOfVariables, left, right] checks the rewrite rule \
whose sides are the core functions left and right of its variables, and gives environment with it added."
emptyEnvironmentOf::usage = "emptyEnvironmentOf[rules] gives the environment with no constants that follows rules, the same one each time."
addDeclaration::usage = "addDeclaration[environment, declaration] elaborates and checks the declaration and gives the extended environment, or throws a kernel failure."
declarationQ::usage = "declarationQ[expr] gives True if expr is a declaration: TypeTheoryAxiom, TypeTheoryDefinition, TypeTheoryTheorem, TypeTheoryInductiveType, \
TypeTheoryNaturalNumbers, TypeTheoryRewriteRule, TypeTheoryQuotients or TypeTheoryCubical."
declarationUniverseParameters::usage = "declarationUniverseParameters[head, Hold[options], {syntax, ...}] gives the universe parameters {HoldComplete[u], ...} \
of a declaration from its \"UniverseParameters\" option, or from the universe levels in the syntax trees."
universeParameterNames::usage = "universeParameterNames[{syntax, ...}] gives the symbols and strings in universe levels of the syntax trees, \
as {HoldComplete[u], ...} in the order they first appear."
heldOptionValue::usage = "heldOptionValue[head, Hold[options], name] gives HoldComplete[value] for the option name among the held options, or among the defaults Options[head]."
$emptyEnvironment::usage = "$emptyEnvironment is the environment with no constants, in which a TypeTheoryTerm without an environment is checked."
$deferKernelChecks::usage = "$deferKernelChecks is True while declarations are added for the compiled kernel to check them all at once: axioms, definitions, \
theorems and holes are added without the kernel's checks, inductive types with them."


(* ::Section:: *)
(*Function Definitions*)


Options[TypeTheoryAxiom] = {"UniverseParameters" -> Automatic, "Annotation" -> None, "Overloads" -> None}
Options[TypeTheoryDefinition] = {"UniverseParameters" -> Automatic, "Instance" -> False, "Coercion" -> False, "Opaque" -> False, "Overloads" -> None}
Options[TypeTheoryTheorem] = {"UniverseParameters" -> Automatic, "Annotation" -> None}
Options[TypeTheoryInductiveType] = {"Parameters" -> Automatic, "UniverseParameters" -> Automatic}
Options[TypeTheoryRewriteRule] = {"UniverseParameters" -> Automatic}

SetAttributes[{TypeTheoryAxiom, TypeTheoryDefinition, TypeTheoryTheorem, TypeTheoryInductiveType, TypeTheoryNaturalNumbers, TypeTheoryRewriteRule, TypeTheoryQuotients, TypeTheoryCubical}, HoldAll]

declarationQ[_TypeTheoryAxiom | _TypeTheoryDefinition | _TypeTheoryTheorem | _TypeTheoryInductiveType | _TypeTheoryNaturalNumbers | _TypeTheoryRewriteRule] := True
declarationQ[TypeTheoryQuotients[] | TypeTheoryQuotients[_, {_, _, _, _}] | TypeTheoryCubical[_]] := True
declarationQ[_] := False


(* ::Subsection:: *)
(*Environments from declarations*)


(* without an environment to extend, declarations extend the default environment; TypeTheoryEnvironment[] has none *)
TypeTheoryEnvironment[] := $emptyEnvironment
TypeTheoryEnvironment[rules_TypeTheoryRules?rulesQ] := emptyEnvironmentOf[rules]
TypeTheoryEnvironment[rules_TypeTheoryRules?rulesQ, declarations : (_List | _?declarationQ)] := TypeTheoryEnvironment[emptyEnvironmentOf[rules], declarations]
TypeTheoryEnvironment["Prelude"] := preludeEnvironment[]
TypeTheoryEnvironment["Constructive"] := constructiveEnvironment[]
TypeTheoryEnvironment["HomotopyTypeTheory"] := homotopyTypeTheoryEnvironment[]
TypeTheoryEnvironment["Integers"] := integersEnvironment[]
TypeTheoryEnvironment["Rationals"] := rationalsEnvironment[]
TypeTheoryEnvironment["Cubical"] := cubicalEnvironment[]
TypeTheoryEnvironment[declarations_List] := TypeTheoryEnvironment[defaultEnvironment[], declarations]
TypeTheoryEnvironment[declaration_?declarationQ] := TypeTheoryEnvironment[defaultEnvironment[], {declaration}]
TypeTheoryEnvironment[environment_?environmentQ, declaration_?declarationQ] := TypeTheoryEnvironment[environment, {declaration}]

Options[TypeTheoryEnvironment] = {Method -> Automatic}

(* the stores of the steps in between are removed, and so are all of them when a declaration fails; with
   Method -> "Compiled" the compiled kernel checks the declarations at once, after they are all added *)
TypeTheoryEnvironment[environment_?environmentQ, declarations_List, OptionsPattern[]] := withStoreCleanup @ catchKernelFailure @ If[
	OptionValue[Method] === "Compiled" && compiledKernelAvailableQ[],
	compiledDeclarations[environment, declarations],
	Fold[addDeclaration, environment, declarations]
]

(* Axioms, definitions, theorems and holes are added without the kernel's checks, and inductive types with them;
   then the compiled kernel checks every declaration added, in order. Where adding one fails, or the compiled kernel
   does not handle the environment, the declarations are added again with each one checked, so that a failure is
   that of the first declaration in order that does not check. *)
compiledDeclarations[environment_, declarations_List] := Replace[
	catchKernelFailure[Block[{$deferKernelChecks = True}, Fold[addDeclaration, environment, declarations]]],
	{
		_Failure :> Fold[addDeclaration, environment, declarations],
		extended_ :> Replace[compiledKernelCheck[extended, Length[environmentNames[environment]]], {
			failure_Failure :> throwFailure[Failure[failure["Tag"], KeyDrop[Last[failure], "Position"]]],
			None :> Fold[addDeclaration, environment, declarations],
			_Success :> extended
		}]
	}
]

$deferKernelChecks = False

TypeTheoryEnvironment /: Append[environment : TypeTheoryEnvironment[_Symbol]?environmentQ, declaration_] := TypeTheoryEnvironment[environment, {declaration}]

(* one empty environment per rules, kept for the session *)
emptyEnvironmentOf[rules_] /; rules === $defaultRules := $emptyEnvironment
emptyEnvironmentOf[rules_] := Lookup[$emptyEnvironments, Key[rules], $emptyEnvironments[rules] = withoutStoreTracking[emptyEnvironment[rules]]]

$emptyEnvironments = <||>


addDeclaration[environment_, TypeTheoryAxiom[name_, type_, options : OptionsPattern[]]] := With[
	{universeParameters = declarationUniverseParameters[TypeTheoryAxiom, Hold[options], {toSyntax[type]}]},
	declareAxiom[environment, HoldComplete[name], universeParameters, closedType[environment, HoldComplete[type], universeParameters], declarationAnnotation[Hold[options]], declarationOverloads[Hold[options]]]
]

(* the operation an "Overloads" option names, one of those whose meanings elaboration chooses by the types *)
declarationOverloads[Hold[options___]] := Replace[Cases[Hold[options], HoldPattern["Overloads" -> operation_] :> HoldComplete[operation], {1}], {
	{} -> None,
	{HoldComplete[None], ___} -> None,
	{operation : HoldComplete[Plus | Times | Subtract | Power | Minus | LessEqual | Less | GreaterEqual | Greater], ___} :> operation,
	{other_, ___} :> kernelFailure[
		"OverloadedOperation",
		"`1` cannot be overloaded: \"Overloads\" takes Plus, Times, Subtract, Power, Minus, LessEqual, Less, GreaterEqual or Greater.",
		{HoldForm @@ other}
	]
}]

overloadsField[None] := <||>
overloadsField[operation_HoldComplete] := <|"Overloads" -> operation|>

(* the "Annotation" given, evaluated, kept in the record as it is; None for none *)
declarationAnnotation[Hold[options___]] := Replace[Cases[Hold[options], HoldPattern["Annotation" -> annotation_] :> annotation, {1}], {{} -> None, {annotation_, ___} :> annotation}]

annotationField[None] := <||>
annotationField[annotation_] := <|"Annotation" -> annotation|>

(* a definition keeps the type it is given, implicit binders included, and its value only has to have
   that type: Lean's projections, for one, take their parameters explicitly in the value *)
addDeclaration[environment_, TypeTheoryDefinition[name_, Typed[value_, type_], options : OptionsPattern[]]] := With[
	{universeParameters = declarationUniverseParameters[TypeTheoryDefinition, Hold[options], {toSyntax[Typed[value, type]]}]},
	{typeCore = closedType[environment, HoldComplete[type], universeParameters]},
	declareDefinition[
		environment, HoldComplete[name], universeParameters, typeCore, closedValue[environment, HoldComplete[value], typeCore, universeParameters],
		Join[definitionRoles[Hold[options], typeCore], overloadsField[declarationOverloads[Hold[options]]]]
	]
]

addDeclaration[environment_, TypeTheoryDefinition[name_, value_, options : OptionsPattern[]]] := With[
	{universeParameters = declarationUniverseParameters[TypeTheoryDefinition, Hold[options], {toSyntax[value]}]},
	{elaborated = elaborateClosedTerm[environment, HoldComplete[value], None, universeParameters]},
	declareDefinition[
		environment, HoldComplete[name], universeParameters, betaNormalize[Last[elaborated]], First[elaborated],
		Join[definitionRoles[Hold[options], betaNormalize[Last[elaborated]]], overloadsField[declarationOverloads[Hold[options]]]]
	]
]

(* the roles the options give a definition: for elaboration, an instance's type, under its binders, is a
   constant applied to arguments, its class, and a coercion's type, under its implicit binders, is a
   function of an explicit argument; for the kernel, a definition of any type may be opaque *)
definitionRoles[heldOptions_Hold, type_] := Select[
	<|
		"Instance" -> roleOption[heldOptions, "Instance", MatchQ[First @ applicationSpine[functionTypeConclusion[type]], _constantReference],
			"InstanceTypeExpected", "The type of an instance must be a class, a constant applied to arguments, under its binders."],
		"Coercion" -> roleOption[heldOptions, "Coercion", MatchQ[explicitFunctionType[type], dependentFunctionType[_, _, _, binder_ /; binderKind[binder] === "Explicit"]],
			"CoercionTypeExpected", "The type of a coercion must be a function of an explicit argument, under its implicit binders."],
		"Opaque" -> roleOption[heldOptions, "Opaque"]
	|>,
	TrueQ
]

roleOption[heldOptions_Hold, option_String] := roleOption[heldOptions, option, True, None, None]
roleOption[heldOptions_Hold, option_String, fitsQ_, tag_, message_] := Replace[heldOptionValue[TypeTheoryDefinition, heldOptions, option], {
	HoldComplete[False] -> False,
	HoldComplete[True] /; fitsQ -> True,
	HoldComplete[True] :> kernelFailure[tag, message, {}],
	HoldComplete[other_] :> kernelFailure["InvalidOption", "The value of the option `1` must be True or False, not `2`.", {option, HoldForm[other]}]
}]

functionTypeConclusion[dependentFunctionType[_, _, codomain_, _]] := functionTypeConclusion[codomain]
functionTypeConclusion[type_] := type

explicitFunctionType[dependentFunctionType[_, _, codomain_, binder_]] /; binderKind[binder] =!= "Explicit" := explicitFunctionType[codomain]
explicitFunctionType[type_] := type

(* a proof with holes declares a constant for each before the theorem (Holes.wl); the statement has none *)
addDeclaration[environment_, TypeTheoryTheorem[name_, statement_, proof_, options : OptionsPattern[]]] := With[
	{universeParameters = declarationUniverseParameters[TypeTheoryTheorem, Hold[options], {toSyntax[statement], toSyntax[proof]}]},
	{type = closedType[environment, HoldComplete[statement], universeParameters]},
	Block[{$elaboratedHoles = {}},
		declareTheoremWithHoles[
			environment, HoldComplete[name], universeParameters, type, theoremValue[environment, HoldComplete[proof], type, universeParameters],
			declarationAnnotation[Hold[options]]
		]
	]
]

(* the statement and universe parameters come from the proof, which is evaluated *)
addDeclaration[environment_, TypeTheoryTheorem[name_, proof_, options : OptionsPattern[]]] := Replace[proof, {
	state : TypeTheoryProof[_Association] :> Block[{$elaboratedHoles = {}},
		declareTheoremWithHoles[environment, HoldComplete[name], proofUniverseParameters[state], proofStatement[state], completedProofTerm[state], declarationAnnotation[Hold[options]]]
	],
	failure_Failure :> throwFailure[failure],
	other_ :> kernelFailure["ProofExpected", "`1` is not a TypeTheoryProof.", {Short[other]}]
}]

declareTheoremWithHoles[environment_, name_, universeParameters_, type_, value_, annotation_] := If[ $elaboratedHoles === {},
	declareTheorem[environment, name, universeParameters, type, value, annotation],
	declareWithHoles[
		environment, name, universeParameters, value, $elaboratedHoles,
		Function[{extended, closedValue}, declareTheorem[extended, name, universeParameters, type, closedValue, annotation]]
	]
]

addDeclaration[environment_, TypeTheoryInductiveType[name_, type_, constructors_List, options : OptionsPattern[]]] :=
	inductiveBlock[environment, {{HoldComplete[name], HoldComplete[type]}}, constructorSpecifications[constructors], Hold[options]]

(* mutually inductive types: their types, then the constructors of all of them *)
addDeclaration[environment_, TypeTheoryInductiveType[types : {(_Rule | _RuleDelayed) ..}, constructors_List, options : OptionsPattern[]]] :=
	inductiveBlock[environment, constructorSpecifications[types], constructorSpecifications[constructors], Hold[options]]

inductiveBlock[environment_, parsedTypes_List, parsedConstructors_List, heldOptions_Hold] := Module[
	{universeParameters, typeCores, provisional, constructorCores},
	universeParameters = declarationUniverseParameters[TypeTheoryInductiveType, heldOptions, Function[pair, toSyntax @@ Last[pair]] /@ Join[parsedTypes, parsedConstructors]];
	typeCores = Function[pair, First[pair] -> closedType[environment, Last[pair], universeParameters]] /@ parsedTypes;
	(* the constructor types may mention the types being declared *)
	provisional = addConstantRecords[environment, Association[Function[typeCore, First[typeCore] -> <|
		"Kind" -> "InductiveType",
		"Type" -> Last[typeCore],
		"UniverseParameters" -> universeParameters,
		"NumberOfParameters" -> 0,
		"NumberOfIndices" -> 0,
		"Constructors" -> {},
		"LargeElimination" -> False,
		"Recursive" -> False,
		"Block" -> Keys[typeCores]
	|>] /@ typeCores]];
	constructorCores = Function[pair, First[pair] -> closedType[provisional, Last[pair], universeParameters]] /@ parsedConstructors;
	declareInductiveTypes[
		environment,
		universeParameters,
		Replace[heldOptionValue[TypeTheoryInductiveType, heldOptions, "Parameters"], {
			HoldComplete[Automatic] :> sharedParameterCount[provisional, Values[typeCores], Values[constructorCores]],
			HoldComplete[n_Integer?NonNegative] :> n,
			HoldComplete[other_] :> kernelFailure["InvalidOption", "The value of the option \"Parameters\" must be a non-negative integer or Automatic, not `1`.", {HoldForm[other]}]
		}],
		typeCores,
		constructorCores
	]
]

addDeclaration[environment_, TypeTheoryNaturalNumbers[type_, zero_, successor_]] :=
	naturalNumbersRegistration[environment, HoldComplete[type], HoldComplete[zero], HoldComplete[successor], <||>]

addDeclaration[environment_, TypeTheoryNaturalNumbers[type_, zero_, successor_, operations_Association]] :=
	naturalNumbersRegistration[environment, HoldComplete[type], HoldComplete[zero], HoldComplete[successor], heldOperations[operations]]

addDeclaration[environment_, TypeTheoryNaturalNumbers[type_, zero_, successor_, addition_]] :=
	naturalNumbersRegistration[environment, HoldComplete[type], HoldComplete[zero], HoldComplete[successor], <|"Addition" -> HoldComplete[addition]|>]

(* the operations' names stay held, as every name in a declaration does *)
SetAttributes[heldOperations, HoldAllComplete]
heldOperations[Association[rules___]] := Association @ Cases[HoldComplete[rules], (Rule | RuleDelayed)[role_, name_] :> (role -> HoldComplete[name])]

(* an alias names its constant here too, as Naturals does NonNegativeIntegers *)
naturalNumbersRegistration[environment_, type_, zero_, successor_, operations_] := registerNaturalNumbers[
	environment,
	<|
		"Type" -> aliasResolvedName[environment, type],
		"Zero" -> aliasResolvedName[environment, zero],
		"Successor" -> aliasResolvedName[environment, successor],
		"Operations" -> Map[Function[name, aliasResolvedName[environment, name]], operations]
	|>
]

(* the two sides are elaborated as functions of the rule's variables, the right one against the type of the left *)
addDeclaration[environment_, TypeTheoryRewriteRule[name_, rule_, options : OptionsPattern[]]] := With[
	{
		universeParameters = declarationUniverseParameters[TypeTheoryRewriteRule, Hold[options], {toSyntax[rule]}],
		sides = rewriteRuleSides[HoldComplete[rule]]
	},
	If[ ! rulesSetting[environment, "RewriteRules"],
		kernelFailure["RewriteRulesNotAllowed", "The rules of the environment do not allow the rewrite rule `1`.", {HoldForm[name]}]
	];
	With[{left = elaborateClosedTerm[environment, sides["Left"], None, universeParameters]},
		declareRewriteRule[
			environment,
			HoldComplete[name],
			universeParameters,
			sides["NumberOfVariables"],
			First[left],
			First[elaborateClosedTerm[environment, sides["Right"], Last[left], universeParameters]]
		]
	]
]

addDeclaration[environment_, TypeTheoryQuotients[]] := addDeclaration[environment, TypeTheoryQuotients[Equal, {QuotientType, QuotientIntroduction, QuotientLift, QuotientInduction}]]
addDeclaration[environment_, TypeTheoryQuotients[equality_, {type_, introduction_, lift_, induction_}]] :=
	declareQuotients[environment, HoldComplete[equality], HoldComplete /@ Unevaluated[{type, introduction, lift, induction}]]

addDeclaration[environment_, TypeTheoryCubical[sum_]] := declareCubical[environment, HoldComplete[sum]]

addDeclaration[_, other_] := kernelFailure["DeclarationExpected", "`1` is not a declaration.", {Short[other]}]

rewriteRuleSides[HoldComplete[ForAll[binders_, Rule[left_, right_]]]] :=
	<|"Left" -> HoldComplete[Function[binders, left]], "Right" -> HoldComplete[Function[binders, right]], "NumberOfVariables" -> Length[listElements[toSyntax[binders]]]|>
rewriteRuleSides[HoldComplete[Rule[left_, right_]]] := <|"Left" -> HoldComplete[left], "Right" -> HoldComplete[right], "NumberOfVariables" -> 0|>
rewriteRuleSides[HoldComplete[other_]] := kernelFailure["RewriteRuleSpecification", "`1` is not a rewrite rule: write ForAll[{Typed[x, type], ...}, lhs -> rhs].", {HoldForm[other]}]


(* A proof written as TypeTheoryProof[...] runs here; any other proof is a term, which may also name a
   finished proof stored in a symbol. *)
theoremValue[environment_, HoldComplete[proof_TypeTheoryProof], _, _] := Replace[proof, {
	state : TypeTheoryProof[_Association] :> completedProofTerm[state],
	failure_Failure :> throwFailure[failure]
}]
theoremValue[environment_, held_HoldComplete, type_, universeParameters_List] := closedValue[environment, held, type, universeParameters]

(* A type or value given in full, every argument and universe level written out, as an import writes it,
   goes into the declaration without elaboration: the kernel checks the declaration all the same. *)
closedType[environment_, held_HoldComplete, universeParameters_List] :=
	Replace[explicitTerm[environment, held, universeParameters], None :> elaborateClosedType[environment, held, universeParameters]]

closedValue[environment_, held_HoldComplete, type_, universeParameters_List] :=
	Replace[explicitTerm[environment, held, universeParameters], None :> First[elaborateClosedTerm[environment, held, type, universeParameters]]]

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


(* The largest n such that every type of the block takes the first type's first n binders first, and every
   constructor takes them first, with the same types, and passes them on unchanged to its result. *)
sharedParameterCount[environment_, typeCores_List, constructorTypes_List] := Module[{typeContext, typeIds, resultType},
	{typeContext, typeIds, resultType} = typeTelescope[environment, <||>, First[typeCores]];
	Min[
		Length[typeIds],
		Function[typeCore, First[matchLeadingBinders[environment, typeContext, typeIds, typeCore, 0]]] /@ Rest[typeCores],
		Function[constructorType, constructorParameterCount[environment, typeContext, typeIds, constructorType]] /@ constructorTypes
	]
]

constructorParameterCount[environment_, typeContext_, typeIds_List, constructorType_] := Module[{matched, remaining, conclusion},
	{matched, remaining} = matchLeadingBinders[environment, typeContext, typeIds, constructorType, 0];
	conclusion = Last @ typeTelescope[environment, typeContext, remaining];
	commonPrefixLength[Last @ applicationSpine[conclusion], freeVariable /@ Take[typeIds, matched]]
]

(* the types are elaborated and checked (closedType), but compared outside the block's check, so the type
   queries of the comparison check *)
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

(* the syntax trees are worked out only when the universe parameters are not given: an import gives them,
   with terms too large to walk for nothing *)
SetAttributes[declarationUniverseParameters, HoldRest]
declarationUniverseParameters[head_Symbol, heldOptions_Hold, syntaxes_] := Replace[heldOptionValue[head, heldOptions, "UniverseParameters"], {
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


(* A declaration's type is checked before its value, so every comparison in its check is of checked terms or
   their reducts, where definitional equality infers the types it asks without checking (withCheckedTerms). *)
declareAxiom[environment_, name_HoldComplete, universeParameters_List, type_, annotation_ : None, overloads_ : None] := withCheckedTerms[
	checkUniverseParameters[name, universeParameters, {type}];
	If[! $deferKernelChecks, sortLevel[environment, <||>, type]];
	addConstantRecords[environment, <|name -> Join[<|"Kind" -> "Axiom", "Type" -> type, "UniverseParameters" -> universeParameters|>, annotationField[annotation], overloadsField[overloads]]|>]
]

(* An instance or a coercion is a definition the elaborator may apply; the kernel checks it as any other.
   An opaque definition is checked as any other too, but its record is of the kind "Opaque", which
   nothing unfolds: like an axiom it equals only itself, and unlike one its type has an element. A
   definition that unfolds has a height, which decides which of two definitions unfolds first when the
   kernel compares them (TypeChecking.wl), and a projection function is an abbreviation, which unfolds
   before the others, as Lean's hints have it. *)
declareDefinition[environment_, name_HoldComplete, universeParameters_List, type_, value_, roles_Association : <||>] := withCheckedTerms[
	checkUniverseParameters[name, universeParameters, {type, value}];
	If[ ! $deferKernelChecks,
		sortLevel[environment, <||>, type];
		checkHasType[environment, <||>, value, type];
		If[rulesSetting[environment, "Quantities"], checkLiveUses[environment, value]]
	];
	addConstantRecords[environment, <|name -> Join[
		<|"Kind" -> If[TrueQ[roles["Opaque"]], "Opaque", "Definition"], "Type" -> type, "UniverseParameters" -> universeParameters, "Value" -> value|>,
		If[TrueQ[roles["Opaque"]], <||>, <|"Height" -> definitionHeight[environment, value]|>],
		If[! TrueQ[roles["Opaque"]] && projectionFunctionQ[value], <|"Hint" -> "Abbreviation"|>, <||>],
		Select[KeyTake[roles, {"Instance", "Coercion"}], TrueQ],
		KeyTake[roles, {"Overloads"}]
	]|>]
]

(* a definition's height, as Lean's: one more than the greatest height of the definitions its value
   mentions, so a definition is higher than each definition it is defined by *)
definitionHeight[environment_, value_] := 1 + Max[0, Function[constant, Lookup[constantRecord[environment, constant], "Height", 0]] /@
	DeleteDuplicates[Cases[value, constantReference[name_, _] :> name, {0, Infinity}]]
]

(* a theorem is a proposition, or under rules without Prop a type, and its proof is never unfolded *)
declareTheorem[environment_, name_HoldComplete, universeParameters_List, type_, value_, annotation_ : None] := withCheckedTerms[
	checkUniverseParameters[name, universeParameters, {type, value}];
	If[ ! $deferKernelChecks,
		If[ ! levelEquivalentQ[sortLevel[environment, <||>, type], 0] && rulesSetting[environment, "Prop"],
			kernelFailure["PropositionExpected", "The statement of the theorem `1` must be a proposition.", {HoldForm @@ name}]
		];
		checkHasType[environment, <||>, value, type];
		If[rulesSetting[environment, "Quantities"], checkLiveUses[environment, value]]
	];
	addConstantRecords[environment, <|name -> Join[<|"Kind" -> "Theorem", "Type" -> type, "UniverseParameters" -> universeParameters, "Value" -> value|>, annotationField[annotation]]|>]
]

(* The left side is an axiom applied to a pattern: each argument is a variable of the rule, a term
   without variables, or a constant applied to such arguments. Every variable occurs in it, and every
   universe parameter is a level of the axiom, so a match determines the right side. *)
declareRewriteRule[environment_, name_HoldComplete, universeParameters_List, numberOfVariables_Integer, left_, right_] := Module[
	{body, head, headLevels},
	checkUniverseParameters[name, universeParameters, {left, right}];
	checkHasType[environment, <||>, right, inferType[environment, <||>, left]];
	body = functionBody[left, numberOfVariables];
	{head, headLevels} = Replace[First @ applicationSpine[body], {
		constantReference[axiom_, levels_List] /; constantRecord[environment, axiom]["Kind"] === "Axiom" :> {axiom, levels},
		_ :> kernelFailure["RewriteRuleHead", "The left side of the rewrite rule `1` must be an axiom applied to arguments.", {HoldForm @@ name}]
	}];
	If[ ! AllTrue[Last @ applicationSpine[body], Function[argument, patternQ[argument, numberOfVariables]]],
		kernelFailure["RewriteRulePattern", "The left side of the rewrite rule `1` is not a pattern: a variable occurs inside a function or under a head that is not a constant.", {HoldForm @@ name}]
	];
	If[ ! AllTrue[Range[0, numberOfVariables - 1], Function[index, boundVariableOccursQ[body, index]]],
		kernelFailure["RewriteRuleVariable", "Every variable of the rewrite rule `1` must occur in its left side.", {HoldForm @@ name}]
	];
	If[ ! SubsetQ[Cases[headLevels, levelParameter[parameter_] :> parameter], universeParameters],
		kernelFailure["RewriteRuleUniverse", "Every universe parameter of the rewrite rule `1` must be a universe level of its head.", {HoldForm @@ name}]
	];
	If[rulesSetting[environment, "Quantities"], checkRewriteRuleUses[environment, name, numberOfVariables, left, right]];
	addRewriteRuleRecord[environment, name, <|
		"Kind" -> "RewriteRule",
		"Type" -> None,
		"UniverseParameters" -> universeParameters,
		"Head" -> head,
		"NumberOfVariables" -> numberOfVariables,
		"LeftHandSide" -> left,
		"RightHandSide" -> right
	|>]
]

functionBody[term_, 0] := term
functionBody[lambdaAbstraction[_, _, body_, _], n_Integer?Positive] := functionBody[body, n - 1]
functionBody[_, _] := kernelFailure["RewriteRuleSpecification", "The sides of a rewrite rule must be functions of its variables.", {}]

patternQ[boundVariable[index_], numberOfVariables_] := index < numberOfVariables
patternQ[term_, numberOfVariables_] /; NoneTrue[Range[0, numberOfVariables - 1], Function[index, boundVariableOccursQ[term, index]]] := True
patternQ[term_, numberOfVariables_] := With[{spine = applicationSpine[term]},
	MatchQ[First[spine], _constantReference] && Last[spine] =!= {} && AllTrue[Last[spine], Function[argument, patternQ[argument, numberOfVariables]]]
]
