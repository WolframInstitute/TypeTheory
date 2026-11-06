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
PackageScoped[naturalOffsetsEqualQ]
PackageScoped[registeredAdditionQ]
PackageScoped[additionReduct]
PackageScoped[$foldedAddition]
PackageScoped[$naturalOffsetRule]


(* ::Section:: *)
(*Usage Messages*)


registerNaturalNumbers::usage = "registerNaturalNumbers[environment, registration] checks that registration describes natural numbers declared in environment, \
or operations on its natural numbers, and gives environment with them registered; it throws a kernel failure otherwise."
literalOperationResult::usage = "literalOperationResult[environment, context, HoldComplete[name], arguments] gives what the registered operation name computes \
from arguments that reduce to literals, or None."
naturalNumberOperationRoles::usage = "naturalNumberOperationRoles[] gives the roles an operation on natural numbers can be registered for."
naturalOffsetsEqualQ::usage = "naturalOffsetsEqualQ[environment, context, a, b] decides whether a and b are definitionally equal by their offsets, the successors \
read off each without reducing, as Lean's kernel does: True or False, or None where the offsets do not decide it."
registeredAdditionQ::usage = "registeredAdditionQ[environment, HoldComplete[name]] gives True if name is the registered addition of the natural numbers of environment."
additionReduct::usage = "additionReduct[environment, context, term, HoldComplete[name], t, s] reduces the registered addition t + s by its defining equations: t where s reduces to zero, the successor of t + s' where s reduces to a successor of s' or a positive literal, and term where s is stuck."
$foldedAddition::usage = "$foldedAddition is True where the registered addition reduces by its defining equations, its recursion folded; False unfolds its definition, for the agreement test."
$naturalOffsetRule::usage = "$naturalOffsetRule is True where definitional equality compares natural numbers by their offsets; False compares them by unfolding alone."


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
	role === "Addition",
		checkAdditionEquations[environment, settings, name],
	True,
		Null
]

(* An addition must satisfy its two defining equations, t + zero == t and t + successor[s] == successor[t + s], by
   computation, for variables t and s: the offset rule reads a term through the addition by them. Computing on
   literals as integer addition does implies neither on open terms: an addition by recursion on its first argument
   computes the literals right and fails the second. The environment checked has no addition registered yet, so the
   offset rule does not read through it here. *)
checkAdditionEquations[environment_, settings_, name_] := With[
	{
		zero = constantReference[settings["Zero"], {}],
		successor = constantReference[settings["Successor"], {}],
		addition = constantReference[name, {}],
		first = freshFreeVariable[],
		second = freshFreeVariable[]
	},
	With[
		{
			context = extendContext[
				extendContext[<||>, first, HoldComplete["t"], constantReference[settings["Type"], {}], "Explicit"],
				second, HoldComplete["s"], constantReference[settings["Type"], {}], "Explicit"
			],
			t = freeVariable[first],
			s = freeVariable[second],
			sum = makeApplication[addition, {freeVariable[first], freeVariable[second]}]
		},
		Scan[
			Function[equation, If[ ! definitionallyEqualQ[environment, context, equation["Left"], equation["Right"]],
				kernelFailure[
					"InvalidNaturalNumberOperation",
					"`1` cannot be registered as the addition: `2` does not hold by computation.",
					{HoldForm @@ name, equation["Equation"]}
				]
			]],
			{
				<|"Left" -> makeApplication[addition, {t, zero}], "Right" -> t, "Equation" -> "t + zero == t"|>,
				<|
					"Left" -> makeApplication[addition, {t, application[successor, s]}],
					"Right" -> application[successor, sum],
					"Equation" -> "t + successor[s] == successor[t + s]"
				|>
			}
		]
	]
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


(* The offset rule, as Lean's kernel compares x + k with y + k' (is_def_eq_offset_nat), without k steps of unfolding.
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
   sum by the registered addition with one, as a sum is a literal only where both its sides are *)
stuckQ[context_, _, freeVariable[id_]] := ! KeyExistsQ[Lookup[context, id, <||>], "Value"]
stuckQ[context_, settings_, application[constantReference[successor_, {}], argument_]] /; successor === settings["Successor"] := stuckQ[context, settings, argument]
stuckQ[context_, settings_, application[application[constantReference[addition_, {}], left_], right_]] /; addition === Lookup[settings["Operations"], "Addition"] :=
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
