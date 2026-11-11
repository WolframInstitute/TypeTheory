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
order, as the prelude's Booleans. An operation whose role has defining equations is
checked against them by computation, for variables. The kernel reads terms through addition, so an
operation of the roles of $refusedRoles that fails them is refused; one of quotient or remainder that
fails them, as any function defined by well-founded recursion, which does not compute on a
variable, is accepted and trusted, as is an operation of a role without equations. The kernel trusts
that a trusted operation computes on literals what the role's function computes on integers,
and TypeTheoryAxiomClosure names it wherever a term rests on
it. A constant trusted for a role it does not compute makes the environment inconsistent.

The natural numbers are registered once. A later registration with the same type, zero and successor
adds operations; "Registrations" keeps the roles each registration added, in order, so Normal and the
replay of TypeTheoryCheck register them again where they were.
*)


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[registerNaturalNumbers]
PackageScoped[literalOperationResult]
PackageScoped[naturalNumberOperationRoles]
PackageScoped[naturalOffsetsEqualQ]
PackageScoped[registeredAdditionQ]
PackageScoped[uncheckedRegistrationQ]
PackageScoped[additionReduct]
PackageScoped[$foldedAddition]
PackageScoped[$naturalOffsetRule]
PackageScoped[$deferRegistrationEquations]
PackageScoped[registrationEquationRecords]


(* ::Section:: *)
(*Usage Messages*)


registerNaturalNumbers::usage = "registerNaturalNumbers[environment, registration] checks that registration describes natural numbers declared in environment, \
or operations on its natural numbers, and gives environment with them registered; it throws a kernel failure otherwise."
literalOperationResult::usage = "literalOperationResult[environment, context, HoldComplete[name], arguments] gives what the registered operation name computes \
from arguments that reduce to literals, or None."
naturalNumberOperationRoles::usage = "naturalNumberOperationRoles[] gives the roles an operation on natural numbers can be registered for."
naturalOffsetsEqualQ::usage = "naturalOffsetsEqualQ[environment, context, a, b] decides whether a and b are definitionally equal by their offsets, the successors \
read off each without reducing: True or False, or None where the offsets do not decide it."
uncheckedRegistrationQ::usage = "uncheckedRegistrationQ[environment, HoldComplete[name]] gives True if name is registered for an operation on natural numbers that has no defining equations to check, which the kernel trusts as it trusts an axiom."
registeredAdditionQ::usage = "registeredAdditionQ[environment, HoldComplete[name]] gives True if name is the registered addition of the natural numbers of environment."
additionReduct::usage = "additionReduct[environment, context, term, HoldComplete[name], t, s] reduces the registered addition t + s by its defining equations: t where s reduces to zero, the successor of t + s' where s reduces to a successor of s' or a positive literal, and term where s is stuck."
$foldedAddition::usage = "$foldedAddition is True where the registered addition reduces by its defining equations, its recursion folded; False unfolds its definition, for the agreement test."
$naturalOffsetRule::usage = "$naturalOffsetRule is True where definitional equality compares natural numbers by their offsets; False compares them by unfolding alone."
$deferRegistrationEquations::usage = "$deferRegistrationEquations is True where the compiled kernel checks the equations of the registrations that have a variable in every application of an \
operation: while a list of declarations is added before the compiled kernel checks it, the list being kept only where the check succeeds, and while an environment is declared again after the \
compiled kernel has checked it. A registration then compares only the equations left to it."
registrationEquationRecords::usage = "registrationEquationRecords[environment, first] gives {{role, HoldComplete[name], statement, record}, ...} for the registrations of environment from the \
first on: for each equation the compiled kernel checks, the record of a theorem whose check is the equation."


(* ::Section:: *)
(*Function Definitions*)


(* the arity of each role and the function it computes on integers, or None where the kernel unfolds the
   operation instead: a power or a shift by 2^24 or more is not computed, since its result would
   have millions of digits *)
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
	KeyValueMap[Function[{role, name}, checkOperation[environment, settings, operations, role, name]], operations];
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

checkOperation[environment_, settings_, operations_, role_, name_] := Which[
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
	(* an operation whose equations do not refuse it, a quotient or a remainder, is not compared here: it is trusted
	   where they fail, which is decided where it is asked (uncheckedRegistrationQ) *)
	MemberQ[$refusedRoles, role],
		checkRoleEquations[environment, settings, Join[settings["Operations"], operations], role, name],
	True,
		Null
]

(* An operation with defining equations must satisfy them by computation, for variables t and s, as its definition in
   the prelude does: the kernel computes it on literals by the Wolfram Language, and the offset rule and literal values
   read terms through the addition. Computing on literals right implies none of them on open terms: an addition by
   recursion on its first argument computes the literals right and fails the second of its equations. The equations
   are stated with the constructors alone, as the first registration has no literals yet, and an operation another's
   equations use, as the addition is in the multiplication's, must be registered too. The environment checked has none
   of the operations of the registration, so the offset rule does not read through them here. An operation without
   defining equations, as the greatest common divisor, is trusted, as an axiom is, and the axiom closure names its
   registration wherever a proof rests on it. *)
$roleEquations = <|
	"Addition" -> Function[terms, {
		{terms["Operation"][terms["t"], terms["Zero"]], terms["t"], "t + zero == t"},
		{terms["Operation"][terms["t"], terms["Successor"][terms["s"]]], terms["Successor"][terms["Operation"][terms["t"], terms["s"]]], "t + successor[s] == successor[t + s]"}
	}],
	"Multiplication" -> Function[terms, {
		{terms["Operation"][terms["t"], terms["Zero"]], terms["Zero"], "t * zero == zero"},
		{terms["Operation"][terms["t"], terms["Successor"][terms["s"]]], terms["Addition"][terms["Operation"][terms["t"], terms["s"]], terms["t"]], "t * successor[s] == t * s + t"}
	}],
	"Power" -> Function[terms, {
		{terms["Operation"][terms["t"], terms["Zero"]], terms["Successor"][terms["Zero"]], "t ^ zero == successor[zero]"},
		{terms["Operation"][terms["t"], terms["Successor"][terms["s"]]], terms["Multiplication"][terms["Operation"][terms["t"], terms["s"]], terms["t"]], "t ^ successor[s] == t ^ s * t"}
	}],
	"Subtraction" -> Function[terms, {
		{terms["Operation"][terms["t"], terms["Zero"]], terms["t"], "t - zero == t"},
		{terms["Operation"][terms["t"], terms["Successor"][terms["s"]]], terms["Predecessor"][terms["Operation"][terms["t"], terms["s"]]], "t - successor[s] == predecessor[t - s]"}
	}],
	"Equal" -> Function[terms, {
		{terms["Operation"][terms["Zero"], terms["Zero"]], terms["True"], "equal[zero, zero] == true"},
		{terms["Operation"][terms["Zero"], terms["Successor"][terms["s"]]], terms["False"], "equal[zero, successor[s]] == false"},
		{terms["Operation"][terms["Successor"][terms["t"]], terms["Zero"]], terms["False"], "equal[successor[t], zero] == false"},
		{terms["Operation"][terms["Successor"][terms["t"]], terms["Successor"][terms["s"]]], terms["Operation"][terms["t"], terms["s"]], "equal[successor[t], successor[s]] == equal[t, s]"}
	}],
	"LessEqual" -> Function[terms, {
		{terms["Operation"][terms["Zero"], terms["s"]], terms["True"], "lessEqual[zero, s] == true"},
		{terms["Operation"][terms["Successor"][terms["t"]], terms["Zero"]], terms["False"], "lessEqual[successor[t], zero] == false"},
		{terms["Operation"][terms["Successor"][terms["t"]], terms["Successor"][terms["s"]]], terms["Operation"][terms["t"], terms["s"]], "lessEqual[successor[t], successor[s]] == lessEqual[t, s]"}
	}],
	(* by recursion on the dividend with the divisor s fixed, the remainder counted up to s and back to zero, so that
	   n % 0 = n and n / 0 = 0: with s zero, the remainder plus one is never s *)
	"Remainder" -> Function[terms, {
		{terms["Operation"][terms["Zero"], terms["s"]], terms["Zero"], "remainder[zero, s] == zero"},
		{
			terms["Operation"][terms["Successor"][terms["t"]], terms["s"]],
			terms["If"][terms["Equal"][terms["Successor"][terms["Operation"][terms["t"], terms["s"]]], terms["s"]], terms["Zero"], terms["Successor"][terms["Operation"][terms["t"], terms["s"]]]],
			"remainder[successor[t], s] == if equal[successor[remainder[t, s]], s] then zero else successor[remainder[t, s]]"
		}
	}],
	"Quotient" -> Function[terms, {
		{terms["Operation"][terms["Zero"], terms["s"]], terms["Zero"], "quotient[zero, s] == zero"},
		{
			terms["Operation"][terms["Successor"][terms["t"]], terms["s"]],
			terms["If"][terms["Equal"][terms["Successor"][terms["Remainder"][terms["t"], terms["s"]]], terms["s"]], terms["Successor"][terms["Operation"][terms["t"], terms["s"]]], terms["Operation"][terms["t"], terms["s"]]],
			"quotient[successor[t], s] == if equal[successor[remainder[t, s]], s] then successor[quotient[t, s]] else quotient[t, s]"
		}
	}]
|>

(* the operations another's equations use *)
$roleRequirements = <|"Multiplication" -> {"Addition"}, "Power" -> {"Multiplication"}, "Remainder" -> {"Equal"}, "Quotient" -> {"Remainder", "Equal"}|>

(* an operation whose equations fail is refused where its role is one of $refusedRoles, and accepted, to be trusted,
   otherwise *)
checkRoleEquations[environment_, settings_, operations_, role_, name_] := Replace[roleEquationFailure[environment, settings, operations, role, name], {
	{template_String, parameters_List} /; MemberQ[$refusedRoles, role] :> kernelFailure["InvalidNaturalNumberOperation", template, parameters],
	_ -> Null
}]

(* the roles the kernel reads terms through, or whose equations any definition of them by recursion meets, refused where
   their equations fail; quotient and remainder are trusted then, as functions defined by
   well-founded recursion have to be *)
$refusedRoles = {"Addition", "Multiplication", "Power", "Subtraction", "Equal", "LessEqual"}

(* None, or the message and parameters of what fails: an operation the equations use not registered, or an equation
   that does not hold by computation. The comparison of an equation's sides remembers its steps, as a check does:
   without them it repeats the comparisons of the parts, 160 ms of each check of a cone of Mathlib. Where the compiled
   kernel checks the equations ($deferRegistrationEquations), those it checks are not compared here. *)
roleEquationFailure[environment_, settings_, operations_, role_, name_] := Replace[
	SelectFirst[Lookup[$roleRequirements, role, {}], Function[required, ! KeyExistsQ[operations, required]], None],
	{
		required_String :> {"`1` cannot be registered as `2` without an operation registered as `3`, which its equations use.", {HoldForm @@ name, role, required}},
		None :> With[
			{
				natural = constantReference[settings["Type"], {}],
				first = freshFreeVariable[],
				second = freshFreeVariable[]
			},
			With[{context = extendContext[extendContext[<||>, first, HoldComplete["t"], natural, "Explicit"], second, HoldComplete["s"], natural, "Explicit"]},
				Replace[
					SelectFirst[
						$roleEquations[role][equationTerms[environment, settings, operations, name, freeVariable[first], freeVariable[second]]],
						Apply[Function[{left, right, statement}, And[
							! (TrueQ[$deferRegistrationEquations] && compiledEquationQ[operations, role, left, right]),
							! withKernelCaches[definitionallyEqualQ[environment, context, left, right]]
						]]],
						None
					],
					{
						{_, _, statement_String} :> {"`1` cannot be registered as `2`: `3` does not hold by computation.", {HoldForm @@ name, role, statement}},
						None -> None
					}
				]
			]
		]
	}
]

$deferRegistrationEquations = False

(* The equations the compiled kernel checks: those of a role that refuses, with a variable in every application of a
   registered operation. The compiled kernel has the roles of an environment for its whole run, and computes a
   registered operation where every argument is a literal: an equation with a closed application of an operation, as
   equal[zero, zero] == true is, it would compute by the very registration the equation is to justify, so that one is
   compared here, in an environment without the registration. An application with a variable in it the compiled kernel
   reduces by unfolding the operation's definition alone, having no rule that reads a sum by its offset. Both facts
   are held by tests that offer a different function for each role to the compiled kernel alone and ask that it
   refuse (Tests/Checking/NaturalNumbers.wlt): a compiled kernel that computed a role on an open term, or read through
   the registered addition, would accept one. *)
compiledEquationQ[operations_, role_, left_, right_] := MemberQ[$refusedRoles, role] && With[{names = Values[operations]},
	FreeQ[
		{left, right},
		closed : application[application[constantReference[operation_, {}], _], _] /; MemberQ[names, operation] && FreeQ[closed, _freeVariable],
		{0, Infinity}
	]
]

(* For each registration from the first on and each equation of it that the compiled kernel checks, a theorem's record
   whose check is the equation: for sides l and r in the variables t and s of a type A, the natural numbers or the
   Booleans of a comparison, the statement that every predicate P on A that holds of l holds of r,
   ForAll[{t, s, P}, P[l] -> P[r]], proved by the function that gives its hypothesis back. That function has the type
   P[l] -> P[l], so the record checks exactly where l and r are equal by computation. The operations an equation is
   written with are those registered up to its registration, as the comparison here takes them. *)
registrationEquationRecords[environment_, firstRegistration_Integer] := Replace[naturalNumberSettings[environment], {
	settings_Association :> Catenate[Map[
		Function[index, registrationRecords[
			environment,
			settings,
			KeyTake[settings["Operations"], Catenate[Take[settings["Registrations"], index]]],
			Last[Take[settings["Registrations"], index]]
		]],
		Range[firstRegistration, Length[settings["Registrations"]]]
	]],
	_ -> {}
}]

registrationRecords[environment_, settings_, operations_Association, roles_List] := Catenate[Map[
	Function[role, With[
		{
			name = operations[role],
			natural = constantReference[settings["Type"], {}],
			first = freshFreeVariable[],
			second = freshFreeVariable[]
		},
		If[ MemberQ[$refusedRoles, role] && AllTrue[Lookup[$roleRequirements, role, {}], Function[required, KeyExistsQ[operations, required]]],
			Map[
				Apply[Function[{left, right, statement}, {role, name, statement, equationRecord[environment, natural, name, role, first, second, left, right]}]],
				Select[
					$roleEquations[role][equationTerms[environment, settings, operations, name, freeVariable[first], freeVariable[second]]],
					Apply[Function[{left, right, statement}, compiledEquationQ[operations, role, left, right]]]
				]
			],
			{}
		]
	]],
	roles
]]

equationRecord[environment_, natural_, name_, role_, first_, second_, left_, right_] := With[
	{
		sides = If[MemberQ[{"Equal", "LessEqual"}, role], constantReference[booleansOf[constantRecord[environment, name]["Type"]], {}], natural],
		predicate = freshFreeVariable[],
		hypothesis = freshFreeVariable[]
	},
	With[
		{
			context = extendContext[
				extendContext[
					extendContext[extendContext[<||>, first, HoldComplete["t"], natural, "Explicit"], second, HoldComplete["s"], natural, "Explicit"],
					predicate,
					HoldComplete["P"],
					dependentFunctionType[HoldComplete["x"], sides, universeSort[0], "Explicit"],
					"Explicit"
				],
				hypothesis,
				HoldComplete["h"],
				application[freeVariable[predicate], left],
				"Explicit"
			]
		},
		<|
			"Kind" -> "Theorem",
			"UniverseParameters" -> {},
			"Type" -> makeDependentFunctionType[context, {first, second, predicate, hypothesis}, application[freeVariable[predicate], right]],
			"Value" -> makeLambda[context, {first, second, predicate, hypothesis}, freeVariable[hypothesis]]
		|>
	]
]

(* the terms the equations are written in: the constructors, the operation and those its equations use as functions of
   their arguments, the predecessor as the recursor that gives it, the Booleans of a comparison, and a choice by the
   Booleans the registered equality gives, by their recursor; each composite term is built from parts computed first *)
equationTerms[environment_, settings_, operations_, name_, t_, s_] := With[
	{
		zero = constantReference[settings["Zero"], {}],
		successor = constantReference[settings["Successor"], {}],
		natural = constantReference[settings["Type"], {}],
		applier = Function[constant, With[{head = constantReference[constant, {}]}, Function[arguments, makeApplication[head, arguments]]]]
	},
	With[{booleans = Replace[constantRecord[environment, name]["Type"], {
		type : dependentFunctionType[_, _, dependentFunctionType[_, _, constantReference[_, {}], _], _] /; booleansQ[environment, booleansOf[type]] :>
			constantRecord[environment, booleansOf[type]]["Constructors"],
		_ -> {}
	}]},
		<|
			"t" -> t,
			"s" -> s,
			"Zero" -> zero,
			"Successor" -> Function[argument, application[successor, argument]],
			"Operation" -> Function[{left, right}, applier[name][{left, right}]],
			"Addition" -> Function[{left, right}, applier[Lookup[operations, "Addition"]][{left, right}]],
			"Multiplication" -> Function[{left, right}, applier[Lookup[operations, "Multiplication"]][{left, right}]],
			"Predecessor" -> Function[argument, predecessorTerm[settings, zero, natural, argument]],
			"True" -> If[booleans === {}, None, constantReference[Last[booleans], {}]],
			"False" -> If[booleans === {}, None, constantReference[First[booleans], {}]],
			"Equal" -> Function[{left, right}, applier[Lookup[operations, "Equal"]][{left, right}]],
			"Remainder" -> Function[{left, right}, applier[Lookup[operations, "Remainder"]][{left, right}]],
			"If" -> Function[{condition, then, else}, choiceTerm[environment, natural, Lookup[operations, "Equal"], condition, then, else]]
		|>
	]
]

(* the predecessor of a term, by the recursor of the natural numbers: zero for zero, and k for successor[k] *)
predecessorTerm[settings_, zero_, natural_, argument_] := With[
	{
		recursor = constantReference[Replace[settings["Type"], HoldComplete[type_] :> HoldComplete[InductiveRecursor[type]]], {1}],
		motive = lambdaAbstraction[HoldComplete["t"], natural, natural, "Explicit"],
		step = With[{inner = lambdaAbstraction[HoldComplete["r"], natural, boundVariable[1], "Explicit"]}, lambdaAbstraction[HoldComplete["k"], natural, inner, "Explicit"]]
	},
	makeApplication[recursor, {motive, zero, step, argument}]
]

(* if condition then a else b, of natural numbers, by the recursor of the Booleans the equality gives: its cases in the
   order of their constructors, false and true *)
choiceTerm[environment_, natural_, equality_HoldComplete, condition_, then_, else_] := With[
	{booleans = booleansOf[constantRecord[environment, equality]["Type"]]},
	With[
		{
			recursor = constantReference[Replace[booleans, HoldComplete[type_] :> HoldComplete[InductiveRecursor[type]]], {1}],
			motive = lambdaAbstraction[HoldComplete["b"], constantReference[booleans, {}], natural, "Explicit"]
		},
		makeApplication[recursor, {motive, else, then, condition}]
	]
]

(* a registration the kernel trusts without a check: of an operation whose role has no defining equations, or that fails
   those of quotient or remainder in the environment; decided where it is asked, so the natural numbers an environment
   stores, and the environments saved, keep their form *)
uncheckedRegistrationQ[environment_, name_HoldComplete] := Replace[naturalNumberSettings[environment], {
	settings_Association /; KeyExistsQ[settings["Roles"], name] :> With[{role = settings["Roles"][name]},
		! KeyExistsQ[$roleEquations, role] || (! MemberQ[$refusedRoles, role] && roleEquationFailure[environment, settings, settings["Operations"], role, name] =!= None)
	],
	_ -> False
}]

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
literalValues[environment_, context_, settings_, arguments_List] /; AnyTrue[arguments, Function[argument, stuckQ[context, settings, argument]]] := None
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

(* the number a term reduces to: its offset read first, k successors of a base, as the offset rule reads it, then the
   base reduced and read again, in a loop, as many times as a reduction exposes successors; None as soon as a base is no
   literal, zero or successor, and reduces no further *)
literalValue[environment_, context_, settings_, term_] := Block[{literalBase, literalOffset, literalReduced},
	{literalBase, literalOffset} = naturalOffset[settings, term];
	While[ ! zeroBaseQ[settings, literalBase] && (literalReduced = weakHeadNormalForm[environment, context, literalBase]) =!= literalBase,
		With[{read = naturalOffset[settings, literalReduced]},
			literalBase = First[read];
			literalOffset += Last[read]
		]
	];
	If[zeroBaseQ[settings, literalBase], literalOffset, None]
]


(* ::Subsection:: *)
(*Offsets*)


(* The offset rule: x + k is compared with y + k' without k steps of unfolding.
   A term of the natural numbers is read as {base, k}, k successors of base, without reducing: a literal n is
   {zero, n}; successor[t] is t's offset with one more; the registered addition t + s, where s is k successors of a
   base b, is {t + b, k} for k > 0, and t's offset with k more where b is zero; anything else is {term, 0}. Each reading
   is a step the kernel takes itself: a literal n + 1 is successor[n], and the addition's defining equations,
   t + zero == t and t + successor[s] == successor[t + s], hold by computation, as registration checks.

   Two sides with positive offsets are k successors of each, so they are equal exactly where what is left once the
   smaller offset is stripped is, by constructor injectivity. Two literals, or successors of zero, are equal where their
   numbers are. Otherwise the offsets decide nothing, None, and the comparison goes on as it would without the rule: a
   side with offset 0 over a base that is not zero reduces, and the rule applies again once it is a successor. The
   arithmetic is on the offsets only, Wolfram Language integers. *)
$naturalOffsetRule = True

naturalOffsetsEqualQ[environment_, context_, a_, b_] := If[ TrueQ[$naturalOffsetRule],
	Replace[naturalNumberSettings[environment], {
		settings_Association :> offsetsEqualQ[environment, context, settings, naturalOffset[settings, a], naturalOffset[settings, b]],
		_ -> None
	}],
	None
]

naturalOffset[settings_, naturalLiteral[n_Integer]] := {constantReference[settings["Zero"], {}], n}
naturalOffset[settings_, application[constantReference[successor_, {}], argument_]] /; successor === settings["Successor"] :=
	offsetAdded[naturalOffset[settings, argument], 1]
naturalOffset[settings_, term : application[application[constantReference[addition_, {}], left_], right_]] /; addition === Lookup[settings["Operations"], "Addition"] :=
	With[{offset = naturalOffset[settings, right]}, Which[
		zeroBaseQ[settings, First[offset]],
			offsetAdded[naturalOffset[settings, left], Last[offset]],
		Last[offset] > 0,
			{makeApplication[constantReference[addition, {}], {left, First[offset]}], Last[offset]},
		True,
			{term, 0}
	]]
naturalOffset[_, term_] := {term, 0}

offsetAdded[{base_, offset_Integer}, more_Integer] := {base, offset + more}

(* a term no literal can be, read without reducing: a variable of the context without a value, a successor of one, or a
   sum by the registered addition with one, as a sum is a literal only where both its sides are.
   This reading and naturalOffset's visit a term as a tree, a shared subterm once for each place it stands, so on sums and
   products that share their parts level after level they cost the size of the tree, which doubles where the shared
   graph grows by a few nodes. Closed arithmetic no longer builds such terms: a beta reduction computes each operation on
   literals as its substitution builds it (TypeChecking.wl, literalFolded). A symbolic part used twice is still read so;
   no blow-up of that kind has been measured (docs/notes/EvaluationCosts.md). *)
stuckQ[context_, _, freeVariable[id_]] := ! KeyExistsQ[Lookup[context, id, <||>], "Value"]
stuckQ[context_, settings_, application[constantReference[successor_, {}], argument_]] /; successor === settings["Successor"] := stuckQ[context, settings, argument]
stuckQ[context_, settings_, application[application[constantReference[addition_, {}], left_], right_]] /; addition === Lookup[settings["Operations"], "Addition"] :=
	stuckQ[context, settings, left] || stuckQ[context, settings, right]
(* a product, a power or a difference by a registered operation, read by the defining equations its registration checked:
   t s and t^s are stuck where s is, and where t is and s a positive literal, as t (k + 1) == t k + t and t^(k + 1) ==
   t^k t leave t in the sum or the product, while t 0 == 0 and t^0 == 1 are literals; t - s is stuck where either is,
   as t - (k + 1) == predecessor[t - k]. A product of a variable by a literal is so no literal at once, where reading
   its value would unfold it one step for each unit of the literal *)
stuckQ[context_, settings_, application[application[constantReference[operation_, {}], left_], right_]] /; MemberQ[{"Multiplication", "Power"}, Lookup[settings["Roles"], Key[operation]]] :=
	stuckQ[context, settings, right] || (stuckQ[context, settings, left] && MatchQ[right, naturalLiteral[_Integer ? Positive]])
stuckQ[context_, settings_, application[application[constantReference[operation_, {}], left_], right_]] /; Lookup[settings["Roles"], Key[operation]] === "Subtraction" :=
	stuckQ[context, settings, left] || stuckQ[context, settings, right]
stuckQ[_, _, _] := False

zeroBaseQ[settings_, base_] := base === constantReference[settings["Zero"], {}]

(* the rule in a loop, at one depth however many rounds it takes: both offsets positive, the smaller is stripped; one
   offset 0 over a base that is not zero against a positive one, that base is reduced and its offset read again; two
   numerals are decided by their numbers. Once neither side has an offset left to strip, what is left is compared by
   general definitional equality, once, or, where the round made no progress, the rule decides nothing *)
offsetsEqualQ[environment_, context_, settings_, first_List, second_List] := Block[
	{offsetFirst = first, offsetSecond = second, offsetProgress = False, offsetDone = False, offsetDecision = None, offsetReduced},
	While[ ! offsetDone,
		Which[
			zeroBaseQ[settings, First[offsetFirst]] && zeroBaseQ[settings, First[offsetSecond]],
				offsetDecision = Last[offsetFirst] == Last[offsetSecond];
				offsetDone = True,
			Last[offsetFirst] > 0 && Last[offsetSecond] > 0,
				With[{common = Min[Last[offsetFirst], Last[offsetSecond]]},
					offsetFirst = {First[offsetFirst], Last[offsetFirst] - common};
					offsetSecond = {First[offsetSecond], Last[offsetSecond] - common}
				];
				offsetProgress = True,
			Last[offsetFirst] == 0 && Last[offsetSecond] > 0 && (offsetReduced = weakHeadNormalForm[environment, context, First[offsetFirst]]) =!= First[offsetFirst],
				offsetFirst = naturalOffset[settings, offsetReduced];
				offsetProgress = True,
			Last[offsetSecond] == 0 && Last[offsetFirst] > 0 && (offsetReduced = weakHeadNormalForm[environment, context, First[offsetSecond]]) =!= First[offsetSecond],
				offsetSecond = naturalOffset[settings, offsetReduced];
				offsetProgress = True,
			offsetProgress,
				offsetDecision = definitionallyEqualQ[
					environment,
					context,
					offsetTerm[settings, First[offsetFirst], Last[offsetFirst]],
					offsetTerm[settings, First[offsetSecond], Last[offsetSecond]]
				];
				offsetDone = True,
			True,
				offsetDone = True
		]
	];
	offsetDecision
]

(* k successors of base written back: the base itself, a literal over zero, base + k by the registered addition, or k
   successors, where no addition is registered and so k is no more than the successors read *)
offsetTerm[_, base_, 0] := base
offsetTerm[settings_, base_, offset_Integer] /; zeroBaseQ[settings, base] := naturalLiteral[offset]
offsetTerm[settings_, base_, offset_Integer] /; KeyExistsQ[settings["Operations"], "Addition"] :=
	makeApplication[constantReference[settings["Operations"]["Addition"], {}], {base, naturalLiteral[offset]}]
offsetTerm[settings_, base_, offset_Integer] := With[{successor = constantReference[settings["Successor"], {}]},
	Nest[Function[term, application[successor, term]], base, offset]
]

$foldedAddition = True

registeredAdditionQ[environment_, name_HoldComplete] := Replace[naturalNumberSettings[environment], {
	settings_Association :> Lookup[settings["Operations"], "Addition"] === name,
	_ -> False
}]

additionReduct[environment_, context_, term_, name_, left_, right_] := With[
	{settings = naturalNumberSettings[environment], reduced = weakHeadNormalForm[environment, context, right]},
	With[{successor = constantReference[settings["Successor"], {}], addition = constantReference[name, {}]},
		Replace[reduced, {
			naturalLiteral[0] :> left,
			constantReference[zero_, {}] /; zero === settings["Zero"] :> left,
			naturalLiteral[n_Integer?Positive] :> With[{sum = makeApplication[addition, {left, naturalLiteral[n - 1]}]}, application[successor, sum]],
			application[constantReference[head_, {}], predecessor_] /; head === settings["Successor"] :> With[{sum = makeApplication[addition, {left, predecessor}]}, application[successor, sum]],
			_ :> term
		}]
	]
]
