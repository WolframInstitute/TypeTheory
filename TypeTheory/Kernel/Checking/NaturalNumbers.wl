(* ::Package:: *)

(*
Natural numbers: registering an inductive type as the natural numbers lets terms use natural number
literals, which the kernel reads as constructor applications, and lets the kernel compute the registered
operations on literals with Wolfram Language integers.

	<|"Type" -> HoldComplete[type], "Zero" -> HoldComplete[zero], "Successor" -> HoldComplete[successor],
		"Operations" -> <|role -> HoldComplete[operation], ...|>,
		"Roles" -> <|HoldComplete[operation] -> role, ...|>,
		"Registrations" -> {{role, ...}, ...}|>

registerNaturalNumbers is part of the trusted kernel. It checks that type is an inductive type in Type
with no parameters, indices or universe parameters, whose constructors are exactly zero : type and
successor : type -> type. Then the literal 2 means successor[successor[zero]].

An operation is registered for one of the roles of $naturalNumberOperations, and must have the type the
role asks for: type -> type -> type, type -> type for "Log2", and type -> type -> B for "Equal" and
"LessEqual", where B is an inductive type with two constructors without fields, false and true in that
order, as Lean's Bool and the prelude's Booleans. The kernel trusts that the operation computes on
literals what the role's function computes on integers, as Lean's kernel trusts GMP for its Nat
operations; a constant registered for a role it does not compute makes the environment inconsistent.

The natural numbers are registered once. A later registration with the same type, zero and successor
adds operations; "Registrations" keeps the roles each registration added, in order, so Normal and the
replay of TypeTheoryCheck register them again where they were.
*)


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[registerNaturalNumbers]
PackageScoped[literalOperationResult]
PackageScoped[naturalNumberOperationRoles]


(* ::Section:: *)
(*Usage Messages*)


registerNaturalNumbers::usage = "registerNaturalNumbers[environment, registration] checks that registration describes natural numbers declared in environment, \
or operations on its natural numbers, and gives environment with them registered; it throws a kernel failure otherwise."
literalOperationResult::usage = "literalOperationResult[environment, context, HoldComplete[name], arguments] gives what the registered operation name computes \
from arguments that reduce to literals, or None."
naturalNumberOperationRoles::usage = "naturalNumberOperationRoles[] gives the roles an operation on natural numbers can be registered for."


(* ::Section:: *)
(*Function Definitions*)


(* the arity of each role and the function it computes on integers, or None where the kernel unfolds the
   operation instead; Lean's kernel does not compute powers and shifts by 2^24 or more either *)
$naturalNumberOperations = <|
	"Addition" -> {2, Function[{m, n}, m + n]},
	"Subtraction" -> {2, Function[{m, n}, Max[m - n, 0]]},
	"Multiplication" -> {2, Function[{m, n}, m * n]},
	"Power" -> {2, Function[{m, n}, Which[n == 0, 1, n < $largestExponent, m^n, True, None]]},
	"Quotient" -> {2, Function[{m, n}, If[n == 0, 0, Quotient[m, n]]]},
	"Remainder" -> {2, Function[{m, n}, If[n == 0, m, Mod[m, n]]]},
	"GCD" -> {2, Function[{m, n}, GCD[m, n]]},
	"Log2" -> {1, Function[{n}, If[n == 0, 0, BitLength[n] - 1]]},
	"BitAnd" -> {2, Function[{m, n}, BitAnd[m, n]]},
	"BitOr" -> {2, Function[{m, n}, BitOr[m, n]]},
	"BitXor" -> {2, Function[{m, n}, BitXor[m, n]]},
	"ShiftLeft" -> {2, Function[{m, n}, If[n < $largestExponent, BitShiftLeft[m, n], None]]},
	"ShiftRight" -> {2, Function[{m, n}, BitShiftRight[m, n]]},
	"Equal" -> {2, Function[{m, n}, m == n]},
	"LessEqual" -> {2, Function[{m, n}, m <= n]}
|>

$largestExponent = 2^24

$comparisonRoles = {"Equal", "LessEqual"}

naturalNumberOperationRoles[] := Keys[$naturalNumberOperations]


(* ::Subsection:: *)
(*Registration*)


registerNaturalNumbers[
	environment_TypeTheoryEnvironment,
	KeyValuePattern[{"Type" -> type_HoldComplete, "Zero" -> zero_HoldComplete, "Successor" -> successor_HoldComplete, "Operations" -> operations_Association}]
] := With[{settings = naturalNumberSettings[environment]},
	Which[
		settings === None && naturalNumbersValidQ[environment, type, zero, successor],
			setNaturalNumberSettings[environment, withOperations[
				environment,
				<|"Type" -> type, "Zero" -> zero, "Successor" -> successor, "Operations" -> <||>, "Roles" -> <||>, "Registrations" -> {}|>,
				operations
			]],
		settings === None,
			kernelFailure["InvalidNaturalNumbers", "`1` cannot be registered as the natural numbers.", {HoldForm @@ type}],
		operations === <||> || Lookup[settings, {"Type", "Zero", "Successor"}] =!= {type, zero, successor},
			kernelFailure["NaturalNumbersRegistered", "The environment already has natural numbers.", {}],
		True,
			setNaturalNumberSettings[environment, withOperations[environment, settings, operations]]
	]
]

naturalNumbersValidQ[environment_, type_, zero_, successor_] := With[{natural = constantReference[type, {}]},
	And[
		AllTrue[{type, zero, successor}, Function[name, constantDeclaredQ[environment, name]]],
		MatchQ[
			constantRecord[environment, type],
			KeyValuePattern[{
				"Kind" -> "InductiveType",
				"Type" -> universeSort[1],
				"UniverseParameters" -> {},
				"NumberOfParameters" -> 0,
				"NumberOfIndices" -> 0,
				"Constructors" -> {zero, successor}
			}]
		],
		constantRecord[environment, zero]["Type"] === natural,
		MatchQ[constantRecord[environment, successor]["Type"], dependentFunctionType[_, natural, natural, "Explicit"]]
	]
]

withOperations[environment_, settings_, operations_] := (
	KeyValueMap[Function[{role, name}, checkOperation[environment, settings, role, name]], operations];
	If[ ! DuplicateFreeQ[Values[operations]],
		kernelFailure["InvalidNaturalNumberOperation", "A constant can be registered for one operation on natural numbers only.", {}]
	];
	<|
		settings,
		"Operations" -> Join[settings["Operations"], operations],
		"Roles" -> Join[settings["Roles"], AssociationThread[Values[operations], Keys[operations]]],
		"Registrations" -> Append[settings["Registrations"], Keys[operations]]
	|>
)

checkOperation[environment_, settings_, role_, name_] := Which[
	! KeyExistsQ[$naturalNumberOperations, role],
		kernelFailure[
			"InvalidNaturalNumberOperation",
			"`1` is not an operation on natural numbers; the operations are `2`.",
			{role, Keys[$naturalNumberOperations]}
		],
	KeyExistsQ[settings["Operations"], role] || KeyExistsQ[settings["Roles"], name],
		kernelFailure["InvalidNaturalNumberOperation", "The natural numbers already have `1`, or `2` is registered already.", {role, HoldForm @@ name}],
	! (constantDeclaredQ[environment, name] && MatchQ[constantRecord[environment, name], KeyValuePattern[{"Kind" -> "Definition" | "Axiom", "UniverseParameters" -> {}}]]),
		kernelFailure["InvalidNaturalNumberOperation", "`1` must be a definition or an axiom without universe parameters to be registered as `2`.", {HoldForm @@ name, role}],
	! operationTypeQ[environment, settings["Type"], role, constantRecord[environment, name]["Type"]],
		kernelFailure["InvalidNaturalNumberOperation", "`1` does not have the type of `2` on `3`.", {HoldForm @@ name, role, HoldForm @@ settings["Type"]}],
	True,
		Null
]

operationTypeQ[environment_, type_, role_, operationType_] := With[{natural = constantReference[type, {}]},
	Which[
		role === "Log2",
			MatchQ[operationType, dependentFunctionType[_, natural, natural, "Explicit"]],
		MemberQ[$comparisonRoles, role],
			MatchQ[operationType, dependentFunctionType[_, natural, dependentFunctionType[_, natural, constantReference[_?(booleansQ[environment, #] &), {}], "Explicit"], "Explicit"]],
		True,
			MatchQ[operationType, dependentFunctionType[_, natural, dependentFunctionType[_, natural, natural, "Explicit"], "Explicit"]]
	]
]

(* an inductive type in Type with two constructors without fields, false and true in that order *)
booleansQ[environment_, name_HoldComplete] := And[
	MatchQ[
		constantRecord[environment, name],
		KeyValuePattern[{"Kind" -> "InductiveType", "Type" -> universeSort[1], "UniverseParameters" -> {}, "NumberOfParameters" -> 0, "NumberOfIndices" -> 0, "Constructors" -> {_, _}}]
	],
	AllTrue[constantRecord[environment, name]["Constructors"], Function[constructor, constantRecord[environment, constructor]["Type"] === constantReference[name, {}]]]
]
booleansQ[_, _] := False


(* ::Subsection:: *)
(*Computing on literals*)


(* The trusted literal extension: an operation registered for a role, applied to arguments that reduce
   to literals, gives what the role's function computes on their integers, instead of unfolding. *)
literalOperationResult[environment_, context_, name_HoldComplete, arguments_List] := literalOperationOf[environment, context, name, arguments, naturalNumberSettings[environment]]

literalOperationOf[environment_, context_, name_, arguments_, settings_Association] /; KeyExistsQ[settings["Roles"], name] :=
	operationResult[environment, context, settings, name, settings["Roles"][name], arguments]
literalOperationOf[_, _, _, _, _] := None

operationResult[environment_, context_, settings_, name_, role_, arguments_] := If[ Length[arguments] == First[$naturalNumberOperations[role]],
	Replace[literalValues[environment, context, settings, arguments], {
		values_List :> resultTerm[environment, name, Last[$naturalNumberOperations[role]] @@ values],
		None -> None
	}],
	None
]

(* the integers of the arguments, or None as soon as one does not reduce to a literal *)
literalValues[environment_, context_, settings_, arguments_List] := Catch[
	Function[argument, Replace[literalValue[environment, context, settings, argument], None :> Throw[None, literalValues]]] /@ arguments,
	literalValues
]

resultTerm[_, _, None] := None
resultTerm[_, _, value_Integer] := naturalLiteral[value]
resultTerm[environment_, name_, value : True | False] := With[
	{constructors = constantRecord[environment, booleansOf[constantRecord[environment, name]["Type"]]]["Constructors"]},
	constantReference[If[value, Last[constructors], First[constructors]], {}]
]

booleansOf[dependentFunctionType[_, _, dependentFunctionType[_, _, constantReference[booleans_, {}], _], _]] := booleans

(* a literal, the zero, or successors of either *)
literalValue[environment_, context_, settings_, term_] := Block[
	{literalSuccessor = constantReference[settings["Successor"], {}], literalCurrent = weakHeadNormalForm[environment, context, term], literalSuccessors = 0},
	While[MatchQ[literalCurrent, application[successor_, _] /; successor === literalSuccessor],
		literalSuccessors++;
		literalCurrent = weakHeadNormalForm[environment, context, Last[literalCurrent]]
	];
	Replace[literalCurrent, {
		naturalLiteral[n_Integer] :> n + literalSuccessors,
		constantReference[settings["Zero"], {}] :> literalSuccessors,
		_ :> None
	}]
]
