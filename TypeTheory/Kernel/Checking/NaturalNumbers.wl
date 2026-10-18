(* ::Package:: *)

(*
Natural numbers: registering an inductive type as the natural numbers lets terms use natural number
literals, which the kernel reads as constructor applications and adds as Wolfram Language integers.

	<|"Type" -> HoldComplete[type], "Zero" -> HoldComplete[zero], "Successor" -> HoldComplete[successor],
		"Addition" -> None | HoldComplete[addition]|>

registerNaturalNumbers is part of the trusted kernel. It checks that type is an inductive type in Type
with no parameters, indices or universe parameters, whose constructors are exactly zero : type and
successor : type -> type, and that addition, if given, is defined by recursion on its second argument,
exactly as

	Function[{Typed[m, type], Typed[n, type]},
		InductiveRecursor[type][Function[{Typed[t, type]}, type], m, Function[{Typed[k, type], Typed[r, type]}, successor[r]], n]]

up to the names of its bound variables. Then the literal 2 means successor[successor[zero]], and adding
two literals as integers gives what unfolding addition would.
*)


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[registerNaturalNumbers]


(* ::Section:: *)
(*Usage Messages*)


registerNaturalNumbers::usage = "registerNaturalNumbers[environment, settings] checks that settings describe natural numbers declared in environment \
and gives environment with them registered; it throws a kernel failure otherwise."


(* ::Section:: *)
(*Function Definitions*)


registerNaturalNumbers[
	environment_TypeTheoryEnvironment,
	settings : KeyValuePattern[{"Type" -> type_HoldComplete, "Zero" -> zero_HoldComplete, "Successor" -> successor_HoldComplete, "Addition" -> addition_}]
] := Which[
	naturalNumberSettings[environment] =!= None,
		kernelFailure["NaturalNumbersRegistered", "The environment already has natural numbers.", {}],
	naturalNumbersValidQ[environment, type, zero, successor] && (addition === None || additionValidQ[environment, type, successor, addition]),
		setNaturalNumberSettings[environment, settings],
	True,
		kernelFailure["InvalidNaturalNumbers", "`1` cannot be registered as the natural numbers.", {HoldForm @@ type}]
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

additionValidQ[environment_, type_, successor_, addition_HoldComplete] := And[
	constantDeclaredQ[environment, addition],
	MatchQ[constantRecord[environment, addition], KeyValuePattern[{"Kind" -> "Definition", "UniverseParameters" -> {}}]],
	eraseBinderNames[constantRecord[environment, addition]["Value"]] === canonicalAddition[type, successor]
]

canonicalAddition[type_, successor_] := With[{natural = constantReference[type, {}], anonymous = HoldComplete[Null]},
	lambdaAbstraction[anonymous, natural, lambdaAbstraction[anonymous, natural, makeApplication[
		constantReference[recursorName[type], {1}],
		{
			lambdaAbstraction[anonymous, natural, natural, "Explicit"],
			boundVariable[1],
			lambdaAbstraction[anonymous, natural, lambdaAbstraction[anonymous, natural, application[constantReference[successor, {}], boundVariable[0]], "Explicit"], "Explicit"],
			boundVariable[0]
		}
	], "Explicit"], "Explicit"]
]

eraseBinderNames[term_] := ReplaceRepeated[term, {
	(head : lambdaAbstraction | dependentFunctionType)[Except[HoldComplete[Null]], domain_, body_, binder_] :> head[HoldComplete[Null], domain, body, binder],
	localDefinition[Except[HoldComplete[Null]], type_, value_, body_] :> localDefinition[HoldComplete[Null], type, value, body]
}]
