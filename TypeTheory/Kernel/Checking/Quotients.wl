(* ::Package:: *)

(*
Quotients: the quotient types of Lean's kernel, which the declaration TypeTheoryQuotients[] adds.

	QuotientType[r]                  the type of the classes of the relation r on a type α
	QuotientIntroduction[r, a]       the class of a
	QuotientLift[f, h, q]            f on classes, given h, a proof that f[a] == f[b] whenever r[a, b]
	QuotientInduction[premise, q]    a property P of every class, from premise, a proof of P of the class
	                                 of every element

	QuotientLift[f, h, QuotientIntroduction[r, a]]          computes to f[a]
	QuotientInduction[premise, QuotientIntroduction[r, a]]  computes to premise[a]

These two rules are all the kernel adds. That the classes of two related elements are equal is an axiom,
Lean's Quot.sound, which the prelude declares as QuotientSoundness. TypeTheoryQuotients[equality, {type,
introduction, lift, induction}] declares the four constants under other names, with another equality,
as LeanLink declares Lean's own: TypeTheoryQuotients["Eq", {"Quot", "Quot.mk", "Quot.lift", "Quot.ind"}].

declareQuotients is part of the trusted kernel. It writes the four types itself, as Lean's kernel does,
after checking that the rules have quotients and that the equality is the identity type: an inductive
type with one universe parameter of the type ForAll[{TypedImplicit[α, TypeUniverse[u]]}, α -> α -> Prop]
and one constructor of the type ForAll[{TypedImplicit[α, TypeUniverse[u]], Typed[x, α]}, equality[x, x]].
The type of the lift mentions the equality, and with any other a lift could tell apart elements that the
quotient identifies.
*)


(* ::Section:: *)
(*PackageExported*)


PackageExported[QuotientType]
PackageExported[QuotientIntroduction]
PackageExported[QuotientLift]
PackageExported[QuotientInduction]


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[declareQuotients]
PackageScoped[reduceQuotient]


(* ::Section:: *)
(*Usage Messages*)


QuotientType::usage = "QuotientType[r] is the type of the classes of the relation r on a type, Lean's Quot; TypeTheoryQuotients[] declares it."
QuotientIntroduction::usage = "QuotientIntroduction[r, a] is the class of a in QuotientType[r], Lean's Quot.mk."
QuotientLift::usage = "QuotientLift[f, h, q] applies the function f to the class q, given a proof h that f[a] == f[b] whenever r[a, b], as Lean's Quot.lift; \
QuotientLift[f, h, QuotientIntroduction[r, a]] computes to f[a]."
QuotientInduction::usage = "QuotientInduction[premise, q] proves P[q] for every class q from a proof premise of P[QuotientIntroduction[r, a]] for every a, \
as Lean's Quot.ind."

declareQuotients::usage = "declareQuotients[environment, HoldComplete[equality], {HoldComplete[type], HoldComplete[introduction], HoldComplete[lift], HoldComplete[induction]}] \
checks that the rules of environment have quotient types and that equality is the identity type, and gives environment with the four quotient constants \
added under the given names; it throws a kernel failure otherwise."
reduceQuotient::usage = "reduceQuotient[environment, context, term, record, arguments] gives term, a quotient constant of the given record applied to arguments, \
reduced one step if it is a lift or an induction applied to a class, and term otherwise."


(* ::Section:: *)
(*Function Definitions*)


(* ::Subsection:: *)
(*Declaration*)


declareQuotients[environment_, equality_HoldComplete, names : {_HoldComplete, _HoldComplete, _HoldComplete, _HoldComplete}] := withKernelCaches[
	If[ ! TrueQ[rulesSetting[environment, "Quotients"]] || ! TrueQ[rulesSetting[environment, "Prop"]],
		kernelFailure["QuotientsNotAllowed", "The rules of the environment do not have quotient types.", {}]
	];
	If[ ! equalityQ[environment, equality],
		kernelFailure[
			"EqualityExpected",
			"Quotient types need `1` declared as the identity type, of the type ForAll[{TypedImplicit[α, TypeUniverse[u]]}, α -> α -> Prop] with one constructor of the type ForAll[{TypedImplicit[α, TypeUniverse[u]], Typed[x, α]}, `1`[x, x]].",
			{HoldForm @@ equality}
		]
	];
	Fold[declareQuotientConstant, environment, quotientRecords[equality, names]]
]

(* each type is checked to be a type, with the constants before it declared *)
declareQuotientConstant[environment_, name_ -> record_] := (
	sortLevel[environment, <||>, record["Type"]];
	addConstantRecords[environment, <|name -> record|>]
)

equalityQ[environment_, equality_HoldComplete] := And[
	constantDeclaredQ[environment, equality],
	MatchQ[constantRecord[environment, equality], KeyValuePattern[{"Kind" -> "InductiveType", "UniverseParameters" -> {_}, "Constructors" -> {_}}]],
	With[
		{
			record = constantRecord[environment, equality],
			level = levelParameter[First[constantRecord[environment, equality]["UniverseParameters"]]]
		},
		(* under rules with quantities the constructor's parameters are erased, which changes nothing here *)
		And[
			definitionallyEqualQ[environment, <||>, withoutQuantities[record["Type"]], equalityType[level]],
			definitionallyEqualQ[environment, <||>, withoutQuantities[constantRecord[environment, First[record["Constructors"]]]["Type"]], reflexivityType[equality, level]]
		]
	]
]

(* ForAll[{TypedImplicit[α, TypeUniverse[u]]}, α -> α -> Prop] *)
equalityType[level_] := dependentFunctionType[HoldComplete[\[Alpha]], universeSort[level],
	dependentFunctionType[HoldComplete[x], boundVariable[0], dependentFunctionType[HoldComplete[y], boundVariable[1], universeSort[0], "Explicit"], "Explicit"],
	"Implicit"
]

(* ForAll[{TypedImplicit[α, TypeUniverse[u]], Typed[x, α]}, equality[x, x]] *)
reflexivityType[equality_, level_] := dependentFunctionType[HoldComplete[\[Alpha]], universeSort[level],
	dependentFunctionType[HoldComplete[x], boundVariable[0], makeApplication[constantReference[equality, {level}], {boundVariable[1], boundVariable[0], boundVariable[0]}], "Explicit"],
	"Implicit"
]


(* ::Subsection:: *)
(*The four constants*)


(* The types are written with bound variables counted from the innermost binder, as Lean's kernel writes
   them; each comment gives the type as a term would write it, with the prelude's names. Every record
   holds the names of all four and of the equality, which declare them again. *)
quotientRecords[equality_, names : {type_, introduction_, lift_, induction_}] := With[
	{
		firstLevel = levelParameter[HoldComplete[u]],
		secondLevel = levelParameter[HoldComplete[v]],
		record = Function[{role, universeParameters, recordType}, quotientRecord[role, universeParameters, recordType, equality, names]]
	},
	{
		type -> record["Type", {HoldComplete[u]}, quotientTypeType[firstLevel]],
		introduction -> record["Introduction", {HoldComplete[u]}, introductionType[type, firstLevel]],
		lift -> record["Lift", {HoldComplete[u], HoldComplete[v]}, liftType[type, equality, firstLevel, secondLevel]],
		induction -> record["Induction", {HoldComplete[u]}, inductionType[type, introduction, firstLevel]]
	}
]

quotientRecord[role_String, universeParameters_List, type_, equality_, names : {typeName_, introductionName_, _, _}] := <|
	"Kind" -> "Quotient",
	"QuotientRole" -> role,
	"Type" -> type,
	"UniverseParameters" -> universeParameters,
	"Equality" -> equality,
	"QuotientNames" -> names,
	"QuotientType" -> typeName,
	"Introduction" -> introductionName
|>

(* alpha -> alpha -> Prop, alpha a term where the binder starts *)
relationType[alpha_] := dependentFunctionType[HoldComplete[a], alpha, dependentFunctionType[HoldComplete[b], liftBoundVariables[alpha, 1, 0], universeSort[0], "Explicit"], "Explicit"]

quotientOf[type_, level_, alpha_, relation_] := makeApplication[constantReference[type, {level}], {alpha, relation}]

(* ForAll[{TypedImplicit[α, TypeUniverse[u]], Typed[r, α -> α -> Prop]}, TypeUniverse[u]] *)
quotientTypeType[u_] := dependentFunctionType[HoldComplete[\[Alpha]], universeSort[u],
	dependentFunctionType[HoldComplete[r], relationType[boundVariable[0]], universeSort[u], "Explicit"],
	"Implicit"
]

(* ForAll[{TypedImplicit[α, TypeUniverse[u]], Typed[r, α -> α -> Prop], Typed[a, α]}, QuotientType[r]] *)
introductionType[type_, u_] := dependentFunctionType[HoldComplete[\[Alpha]], universeSort[u],
	dependentFunctionType[HoldComplete[r], relationType[boundVariable[0]],
		dependentFunctionType[HoldComplete[a], boundVariable[1], quotientOf[type, u, boundVariable[2], boundVariable[1]], "Explicit"],
		"Explicit"
	],
	"Implicit"
]

(* ForAll[{TypedImplicit[α, TypeUniverse[u]], TypedImplicit[r, α -> α -> Prop], TypedImplicit[β, TypeUniverse[v]], Typed[f, α -> β]},
	(ForAll[{Typed[a, α], Typed[b, α]}, Implies[r[a, b], f[a] == f[b]]]) -> QuotientType[r] -> β] *)
liftType[type_, equality_, u_, v_] := dependentFunctionType[HoldComplete[\[Alpha]], universeSort[u],
	dependentFunctionType[HoldComplete[r], relationType[boundVariable[0]],
		dependentFunctionType[HoldComplete[\[Beta]], universeSort[v],
			dependentFunctionType[HoldComplete[f], dependentFunctionType[HoldComplete[x], boundVariable[2], boundVariable[1], "Explicit"],
				dependentFunctionType[HoldComplete[h], respectsType[equality, v],
					dependentFunctionType[HoldComplete[q], quotientOf[type, u, boundVariable[4], boundVariable[3]], boundVariable[3], "Explicit"],
					"Explicit"
				],
				"Explicit"
			],
			"Implicit"
		],
		"Implicit"
	],
	"Implicit"
]

(* ForAll[{Typed[a, α], Typed[b, α]}, Implies[r[a, b], f[a] == f[b]]], under α, r, β and f *)
respectsType[equality_, v_] := dependentFunctionType[HoldComplete[a], boundVariable[3],
	dependentFunctionType[HoldComplete[b], boundVariable[4],
		dependentFunctionType[HoldComplete[e], makeApplication[boundVariable[4], {boundVariable[1], boundVariable[0]}],
			makeApplication[constantReference[equality, {v}], {boundVariable[4], application[boundVariable[3], boundVariable[2]], application[boundVariable[3], boundVariable[1]]}],
			"Explicit"
		],
		"Explicit"
	],
	"Explicit"
]

(* ForAll[{TypedImplicit[α, TypeUniverse[u]], TypedImplicit[r, α -> α -> Prop], TypedImplicit[β, QuotientType[r] -> Prop],
	Typed[premise, ForAll[{Typed[a, α]}, β[QuotientIntroduction[r, a]]]], Typed[q, QuotientType[r]]}, β[q]] *)
inductionType[type_, introduction_, u_] := dependentFunctionType[HoldComplete[\[Alpha]], universeSort[u],
	dependentFunctionType[HoldComplete[r], relationType[boundVariable[0]],
		dependentFunctionType[HoldComplete[\[Beta]], dependentFunctionType[HoldComplete[q], quotientOf[type, u, boundVariable[1], boundVariable[0]], universeSort[0], "Explicit"],
			dependentFunctionType[HoldComplete[premise],
				dependentFunctionType[HoldComplete[a], boundVariable[2],
					application[boundVariable[1], makeApplication[constantReference[introduction, {u}], {boundVariable[3], boundVariable[2], boundVariable[0]}]],
					"Explicit"
				],
				dependentFunctionType[HoldComplete[q], quotientOf[type, u, boundVariable[3], boundVariable[2]], application[boundVariable[2], boundVariable[0]], "Explicit"],
				"Explicit"
			],
			"Implicit"
		],
		"Implicit"
	],
	"Implicit"
]


(* ::Subsection:: *)
(*Reduction*)


(* a lift or an induction applied to a class takes the class's element, as Lean's kernel reduces them *)
reduceQuotient[environment_, context_, term_, record_, arguments_List] := Replace[{record["QuotientRole"], arguments}, {
	{"Lift", {_, _, _, function_, _, major_, rest___}} :> quotientComputation[environment, context, term, record, function, major, {rest}],
	{"Induction", {_, _, _, premise_, major_, rest___}} :> quotientComputation[environment, context, term, record, premise, major, {rest}],
	_ :> term
}]

quotientComputation[environment_, context_, term_, record_, function_, major_, rest_List] := Replace[
	applicationSpine[weakHeadNormalForm[environment, context, major]],
	{
		{constantReference[introduction_, _], {_, _, element_}} /; introduction === record["Introduction"] :> makeApplication[function, Prepend[rest, element]],
		_ :> term
	}
]
