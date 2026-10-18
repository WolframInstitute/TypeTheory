(* ::Package:: *)

(*
Questions about terms and environments: type checking, definitional equality, reduction, and checking a
whole environment again from scratch.

A TypeTheoryTerm is elaborated in $TypeTheoryEnvironment, or in an environment given as the first
argument, with the symbols in its universe levels as universe parameters. Answers are TypeTheoryTerm
expressions again, read back from the core terms.

An environment is an ordinary expression, which anyone can write by hand. TypeTheoryCheck[environment]
is how to trust one that did not come from the Declare functions: it replays every declaration in
order on an empty environment with the core declaration functions, and compares each record with the
one the replay produces. Axioms are taken on trust, as their name says.
*)


(* ::Section:: *)
(*PackageExported*)


PackageExported[TypeTheoryCheck]
PackageExported[DefinitionallyEqualQ]
PackageExported[WeakHeadNormalForm]


(* ::Section:: *)
(*Usage Messages*)


TypeTheoryCheck::usage = "TypeTheoryCheck[term] gives the type of the TypeTheoryTerm term in $TypeTheoryEnvironment, or a Failure if it does not type-check.\n\
TypeTheoryCheck[term, type] gives True if term has the given type, and a Failure otherwise.\n\
TypeTheoryCheck[environment, term] and TypeTheoryCheck[environment, term, type] use the TypeTheoryEnvironment environment.\n\
TypeTheoryCheck[environment] checks every declaration of environment again from scratch and gives True, or a Failure for the first declaration that does not check."
DefinitionallyEqualQ::usage = "DefinitionallyEqualQ[term1, term2] gives True if the TypeTheoryTerm expressions term1 and term2 are equal by \
computation in $TypeTheoryEnvironment, and False otherwise.\n\
DefinitionallyEqualQ[environment, term1, term2] uses the TypeTheoryEnvironment environment."
WeakHeadNormalForm::usage = "WeakHeadNormalForm[term] reduces the TypeTheoryTerm term in $TypeTheoryEnvironment until its head can no longer reduce.\n\
WeakHeadNormalForm[environment, term] uses the TypeTheoryEnvironment environment."


(* ::Section:: *)
(*Function Definitions*)


TypeTheoryTerm /: TypeOf[term_TypeTheoryTerm] := TypeTheoryCheck[term]
TypeTheoryTerm /: TypeOf[term_TypeTheoryTerm, environment_TypeTheoryEnvironment] := TypeTheoryCheck[environment, term]


queryUniverseParameters[terms_List] := universeParameterNames[Function[term, toSyntax @@ term] /@ terms]

elaborateQueryTerm[environment_, term_TypeTheoryTerm, expected_, universeParameters_List] :=
	elaborateClosedTerm[environment, HoldComplete @@ term, expected, universeParameters]


TypeTheoryCheck[term_TypeTheoryTerm] := TypeTheoryCheck[$TypeTheoryEnvironment, term]
TypeTheoryCheck[term_TypeTheoryTerm, type_TypeTheoryTerm] := TypeTheoryCheck[$TypeTheoryEnvironment, term, type]

(* a constant on its own has its declared type, with its implicit arguments and universe parameters *)
TypeTheoryCheck[environment_TypeTheoryEnvironment, term_TypeTheoryTerm] := catchKernelFailure @ coreToTypeTheoryTerm[
	environment,
	<||>,
	betaNormalize @ Replace[heldFromSyntax[toSyntax @@ term], {
		name_ /; constantDeclaredQ[environment, name] :> constantRecord[environment, name]["Type"],
		_ :> Last @ elaborateQueryTerm[environment, term, None, queryUniverseParameters[{term}]]
	}]
]

TypeTheoryCheck[environment_TypeTheoryEnvironment, term_TypeTheoryTerm, type_TypeTheoryTerm] := catchKernelFailure @ With[
	{universeParameters = queryUniverseParameters[{term, type}]},
	{expected = elaborateClosedType[environment, HoldComplete @@ type, universeParameters]},
	elaborateQueryTerm[environment, term, expected, universeParameters];
	True
]


DefinitionallyEqualQ[first_TypeTheoryTerm, second_TypeTheoryTerm] := DefinitionallyEqualQ[$TypeTheoryEnvironment, first, second]
DefinitionallyEqualQ[environment_TypeTheoryEnvironment, first_TypeTheoryTerm, second_TypeTheoryTerm] := TrueQ @ catchKernelFailure @ With[
	{universeParameters = queryUniverseParameters[{first, second}]},
	definitionallyEqualQ[
		environment,
		<||>,
		First @ elaborateQueryTerm[environment, first, None, universeParameters],
		First @ elaborateQueryTerm[environment, second, None, universeParameters]
	]
]


WeakHeadNormalForm[term_TypeTheoryTerm] := WeakHeadNormalForm[$TypeTheoryEnvironment, term]
WeakHeadNormalForm[environment_TypeTheoryEnvironment, term_TypeTheoryTerm] := catchKernelFailure @ coreToTypeTheoryTerm[
	environment,
	<||>,
	weakHeadNormalForm[environment, <||>, First @ elaborateQueryTerm[environment, term, None, queryUniverseParameters[{term}]]]
]


(* ::Subsection:: *)
(*Checking an environment*)


TypeTheoryCheck[environment : TypeTheoryEnvironment[data_Association]] := catchKernelFailure @ With[
	{
		replayed = Fold[
			Function[{partial, declaration}, replayDeclaration[environment, partial, declaration]],
			emptyEnvironment[],
			Normal[data["Constants"]]
		]
	},
	If[ naturalNumberSettings[replayed] =!= naturalNumberSettings[environment],
		kernelFailure["DeclarationMismatch", "The natural numbers of the environment do not match its declarations.", {}]
	];
	True
]

(* Constructors and recursors are generated with their inductive type, which comes before them; every
   record must come out of the replay exactly as it is in the environment. *)
replayDeclaration[original_, replayed_, name_ -> record_] := With[
	{extended = If[MatchQ[record["Kind"], "Constructor" | "Recursor"], replayed, redeclare[original, replayed, name, record]]},
	If[ ! constantDeclaredQ[extended, name] || constantRecord[extended, name] =!= record,
		kernelFailure["DeclarationMismatch", "The record of `1` does not match the record that checking its declaration gives.", {HoldForm @@ name}]
	];
	registerWhenDeclared[extended, naturalNumberSettings[original]]
]

redeclare[original_, replayed_, name_, record_] := Replace[record["Kind"], {
	"Axiom" :> declareAxiom[replayed, name, record["UniverseParameters"], record["Type"]],
	"Definition" :> declareDefinition[replayed, name, record["UniverseParameters"], record["Type"], record["Value"]],
	"Theorem" :> declareTheorem[replayed, name, record["UniverseParameters"], record["Type"], record["Value"]],
	"InductiveType" :> declareInductiveType[
		replayed,
		name,
		record["UniverseParameters"],
		record["NumberOfParameters"],
		record["Type"],
		Function[constructor, constructor -> constantRecord[original, constructor]["Type"]] /@ record["Constructors"]
	],
	kind_ :> kernelFailure["UnknownDeclaration", "The record of `1` has the unknown kind `2`.", {HoldForm @@ name, kind}]
}]

(* the natural numbers are registered as soon as the constants they name are declared *)
registerWhenDeclared[replayed_, settings_Association] /; naturalNumberSettings[replayed] === None && AllTrue[
	DeleteCases[Values[settings], None],
	Function[name, constantDeclaredQ[replayed, name]]
] := registerNaturalNumbers[replayed, settings]
registerWhenDeclared[replayed_, _] := replayed
