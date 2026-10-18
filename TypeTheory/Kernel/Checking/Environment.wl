(* ::Package:: *)

(*
Environments: the declared constants a term may mention, with their records.

An environment is a handle, TypeTheoryEnvironment[store], to a symbol of its own whose definitions hold
the environment's contents. That is the Wolfram Language's own way of storing named definitions:

	store[HoldComplete[name]]    the record of the constant name, or None if name is not declared
	store["Names"]               {HoldComplete[name], ...}, in the order the constants were declared
	store["NaturalNumbers"]      None | <|"Type" -> HoldComplete[type], "Zero" -> HoldComplete[zero],
	                                "Successor" -> HoldComplete[successor], "Operations" -> <|role -> HoldComplete[operation]|>,
	                                "Roles" -> <|HoldComplete[operation] -> role|>, "Registrations" -> {{role, ...}, ...}|>,
	                                as Checking/NaturalNumbers.wl describes
	store["Identifier"]          a positive integer, marking store as an environment's store
	store["Rules"]               the TypeTheoryRules the environment follows, set when it is started
	store["RewriteRuleIndex"]    <|HoldComplete[axiom] -> {HoldComplete[rule], ...}|>: the rewrite rules of each axiom

An environment never changes. Adding constants gives a new environment, whose store holds a copy of the
old definitions and the new ones, and leaves the old environment as it was, so a proof can branch or be
undone without bookkeeping. The handle is small, so terms and proofs carry their environment with them.
A store lives for the session: Normal[environment] gives the declarations to rebuild it from.

A record is an Association with "Kind" (one of "Axiom", "Definition", "Theorem", "InductiveType",
"Constructor", "Recursor", "RewriteRule"), "Type" (a core term, or None for a rewrite rule, which is not a
term), "UniverseParameters" ({HoldComplete[u], ...}) and the fields of its kind:
	Definition, Theorem    "Value"
	InductiveType          "NumberOfParameters", "NumberOfIndices", "Constructors", "LargeElimination", "Recursive",
	                       "Block" (the types declared together with it, itself among them, in order)
	Constructor            "InductiveType", "ConstructorIndex", "NumberOfParameters", "NumberOfFields"
	Recursor               "InductiveType" (the type of its major premise), "NumberOfParameters", "NumberOfMotives",
	                       "NumberOfIndices", "NumberOfMinors",
	                       "Rules" (<|HoldComplete[constructor] -> <|"NumberOfParameters", "NumberOfFields", "RightHandSide"|>|>),
	                       "EliminationUniverse", "KLike"
	RewriteRule            "Head", "NumberOfVariables", "LeftHandSide", "RightHandSide": the two sides as
	                       functions of the rule's variables

A symbol with definitions outlives its last reference, so stores are never collected by themselves. A
batch of declarations therefore runs inside withStoreCleanup, which removes the stores the batch created
except those of the environments it gives back.

The kernel reports a failure by throwing a Failure with the tag $kernelFailureTag; every exported function
catches it with catchKernelFailure and returns it.
*)


(* ::Section:: *)
(*PackageExported*)


PackageExported[TypeTheoryEnvironment]


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[emptyEnvironment]
PackageScoped[environmentRules]
PackageScoped[addRewriteRuleRecord]
PackageScoped[rewriteRuleRecords]
PackageScoped[environmentQ]
PackageScoped[constantRecord]
PackageScoped[constantDeclaredQ]
PackageScoped[addConstantRecords]
PackageScoped[environmentNames]
PackageScoped[naturalNumberSettings]
PackageScoped[setNaturalNumberSettings]
PackageScoped[withStoreCleanup]
PackageScoped[withoutStoreTracking]
PackageScoped[checkUniverseParameters]
PackageScoped[kernelFailure]
PackageScoped[throwFailure]
PackageScoped[catchKernelFailure]
PackageScoped[$kernelFailureTag]


(* ::Section:: *)
(*Usage Messages*)


TypeTheoryEnvironment::usage = "TypeTheoryEnvironment[] gives the environment with no constants.\n\
TypeTheoryEnvironment[\"Prelude\"] gives the prelude: classical logic, equality, the natural numbers and the Booleans.\n\
TypeTheoryEnvironment[\"Constructive\"] gives the prelude without its axioms and the theorems proved from them.\n\
TypeTheoryEnvironment[\"HomotopyTypeTheory\"] gives homotopy type theory: paths, univalence and the circle, under rules without Prop.\n\
TypeTheoryEnvironment[{declaration1, declaration2, ...}] checks the declarations in turn and gives the prelude extended with them.\n\
TypeTheoryEnvironment[environment, {declaration1, ...}] gives environment extended with the declarations; Append[environment, declaration] adds one.\n\
TypeTheoryEnvironment[rules] gives the environment with no constants that follows the TypeTheoryRules rules, and TypeTheoryEnvironment[rules, {declaration1, ...}] extends it.\n\
environment[name] gives the declaration that introduced the constant name. Keys, Length, KeyExistsQ, Normal and Information[environment, property] also work."

emptyEnvironment::usage = "emptyEnvironment[] gives an environment with no constants and the default rules; emptyEnvironment[rules] gives one with the given rules."
environmentRules::usage = "environmentRules[environment] gives the TypeTheoryRules environment follows."
addRewriteRuleRecord::usage = "addRewriteRuleRecord[environment, HoldComplete[name], record] gives a new environment with the rewrite rule name added to the rules of its head."
rewriteRuleRecords::usage = "rewriteRuleRecords[environment, HoldComplete[axiom]] gives the records of the rewrite rules of axiom, in the order they were declared."
environmentQ::usage = "environmentQ[expr] gives True if expr is a TypeTheoryEnvironment handle to a store."
constantRecord::usage = "constantRecord[environment, HoldComplete[name]] gives the record of the constant name, or throws a kernel failure if it is not declared."
constantDeclaredQ::usage = "constantDeclaredQ[environment, HoldComplete[name]] gives True if name is declared in environment."
addConstantRecords::usage = "addConstantRecords[environment, <|HoldComplete[name] -> record, ...|>] gives a new environment with the records added; \
it throws a kernel failure if a name is already declared."
environmentNames::usage = "environmentNames[environment] gives the names {HoldComplete[name], ...} of the constants of environment, in the order they were declared."
naturalNumberSettings::usage = "naturalNumberSettings[environment] gives the registered natural numbers of environment, or None."
setNaturalNumberSettings::usage = "setNaturalNumberSettings[environment, settings] gives a new environment with settings as its natural numbers."
withStoreCleanup::usage = "withStoreCleanup[body] evaluates body and removes every store created meanwhile except the stores of the environments in its value."
withoutStoreTracking::usage = "withoutStoreTracking[expr] evaluates expr without reporting the stores it keeps to an enclosing withStoreCleanup, as for a cached environment."
checkUniverseParameters::usage = "checkUniverseParameters[HoldComplete[name], {HoldComplete[u], ...}, {term, ...}] throws a kernel failure unless the \
universe parameters are distinct and include every universe parameter the core terms mention."
kernelFailure::usage = "kernelFailure[tag, template, {parameter, ...}] throws a Failure with the given tag and message, to be caught by catchKernelFailure."
throwFailure::usage = "throwFailure[failure] throws failure, to be caught by catchKernelFailure."
catchKernelFailure::usage = "catchKernelFailure[expr] evaluates expr and gives its value, or the Failure a kernel function threw."
$kernelFailureTag::usage = "$kernelFailureTag is the tag kernel failures are thrown with."


(* ::Section:: *)
(*Function Definitions*)


$storeCounter = 0


environmentQ[TypeTheoryEnvironment[store_Symbol]] := IntegerQ[store["Identifier"]]
environmentQ[_] := False


(* A fresh store: the definitions of an existing store (with $storePlaceholder for its symbol) and the
   new records. Callers have checked the names, records and settings. *)
newEnvironment[baseDownValues_List, names_List, records_Association, naturalNumbers_] := Module[{store},
	DownValues[store] = ReplaceAll[baseDownValues, $storePlaceholder -> store];
	KeyValueMap[Function[{name, record}, store[name] = record], records];
	store["Names"] = names;
	store["NaturalNumbers"] = naturalNumbers;
	store["Identifier"] = ++$storeCounter;
	Sow[store, $storeTag];
	TypeTheoryEnvironment[store]
]

(* every store answers None for a name it does not declare *)
$emptyDownValues = {HoldPattern[$storePlaceholder[_HoldComplete]] :> None}

storeDownValues[store_Symbol] := ReplaceAll[DownValues[store], store -> $storePlaceholder]

emptyEnvironment[] := emptyEnvironment[$defaultRules]

(* a new store is filled in before anyone sees it, and the environments made from it copy these entries *)
emptyEnvironment[rules_TypeTheoryRules] := With[{environment = newEnvironment[$emptyDownValues, {}, <||>, None]},
	With[{store = First[environment]},
		store["Rules"] = rules;
		store["RewriteRuleIndex"] = <||>
	];
	environment
]

environmentRules[TypeTheoryEnvironment[store_Symbol]] := store["Rules"]


constantRecord[TypeTheoryEnvironment[store_Symbol], name_HoldComplete] := Replace[
	store[name],
	None :> kernelFailure["UnknownConstant", "`1` is not declared.", {HoldForm @@ name}]
]

constantDeclaredQ[TypeTheoryEnvironment[store_Symbol], name_HoldComplete] := store[name] =!= None

environmentNames[TypeTheoryEnvironment[store_Symbol]] := store["Names"]


addConstantRecords[environment : TypeTheoryEnvironment[store_Symbol], records_Association] := With[
	{clash = Select[Keys[records], Function[name, constantDeclaredQ[environment, name]]]},
	If[ clash =!= {},
		kernelFailure["AlreadyDeclared", "`1` is already declared.", {HoldForm @@ First[clash]}],
		newEnvironment[storeDownValues[store], Join[store["Names"], Keys[records]], records, store["NaturalNumbers"]]
	]
]


(* a rewrite rule is a record of its own, in the order of declarations, and listed under its head *)
addRewriteRuleRecord[environment : TypeTheoryEnvironment[store_Symbol], name_HoldComplete, record_Association] := With[
	{extended = addConstantRecords[environment, <|name -> record|>]},
	With[{newStore = First[extended]},
		newStore["RewriteRuleIndex"] = Merge[{store["RewriteRuleIndex"], <|record["Head"] -> {name}|>}, Apply[Join]]
	];
	extended
]

rewriteRuleRecords[TypeTheoryEnvironment[store_Symbol], head_HoldComplete] := Function[name, store[name]] /@ Lookup[store["RewriteRuleIndex"], Key[head], {}]


naturalNumberSettings[TypeTheoryEnvironment[store_Symbol]] := store["NaturalNumbers"]

setNaturalNumberSettings[TypeTheoryEnvironment[store_Symbol], settings_] := newEnvironment[storeDownValues[store], store["Names"], <||>, settings]


(* The stores body created become unreachable once body is done, except through its value, so the
   others are removed. The kept ones are reported to an enclosing withStoreCleanup in turn. *)
SetAttributes[withStoreCleanup, HoldFirst]
withStoreCleanup[body_] := Module[{result, created, kept},
	{result, created} = Reap[body, $storeTag];
	kept = Cases[result, TypeTheoryEnvironment[store_Symbol] :> store, {0, Infinity}];
	Scan[Remove, Complement[Flatten[created], kept]];
	Scan[Function[store, Sow[store, $storeTag]], Intersection[Flatten[created], kept]];
	result
]

SetAttributes[withoutStoreTracking, HoldFirst]
withoutStoreTracking[expr_] := First @ Reap[expr, $storeTag]


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


TypeTheoryEnvironment /: MakeBoxes[environment : TypeTheoryEnvironment[store_Symbol], format : StandardForm] /; environmentQ[environment] := With[
	{records = store /@ store["Names"], naturalNumbers = store["NaturalNumbers"]},
	BoxForm`ArrangeSummaryBox[
		TypeTheoryEnvironment,
		environment,
		None,
		{
			BoxForm`SummaryItem[{"Constants: ", Length[records]}],
			BoxForm`SummaryItem[{"Theorems: ", Count[records, KeyValuePattern["Kind" -> "Theorem"]]}]
		},
		{
			BoxForm`SummaryItem[{"Inductive types: ", Count[records, KeyValuePattern["Kind" -> "InductiveType"]]}],
			BoxForm`SummaryItem[{"Axioms: ", Count[records, KeyValuePattern["Kind" -> "Axiom"]]}],
			BoxForm`SummaryItem[{"Natural numbers: ", If[naturalNumbers === None, "none", HoldForm @@ naturalNumbers["Type"]]}],
			BoxForm`SummaryItem[{"Rules: ", First[store["Rules"]]["Name"]}]
		},
		format,
		"Interpretable" -> Automatic
	]
]
