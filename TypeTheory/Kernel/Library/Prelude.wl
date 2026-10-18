(* ::Package:: *)

(*
The prelude: logic, equality and the natural numbers, written as a list of declarations in the surface
syntax, so it doubles as an example of them. TypeTheoryEnvironment["Prelude"] gives its environment,
built and checked when the paclet loads.

The connectives are built-in symbols, so terms read as ordinary mathematics:

	True, False                propositions with one proof and with none
	Not[p]                     Implies[p, False], a definition
	And[p, q], Or[p, q]        with AndIntroduction, OrIntroductionLeft and OrIntroductionRight
	a == b                     Equal, with EqualityReflexivity
	Exists[{Typed[x, A]}, p]   Exists applied to a predicate, with ExistsIntroduction
	NonNegativeIntegers        the natural numbers, with NaturalNumberZero and NaturalNumberSuccessor,
	                           registered so that the literals 0, 1, 2, ... are natural numbers
	m + n                      Plus, by recursion on n

The theorems FalseElimination, AndEliminationLeft, AndEliminationRight, EqualitySymmetry,
EqualityTransitivity, EqualityCongruence and EqualitySubstitution are proved with the recursors.

Bound variables are Formal symbols, which have no values and cannot clash with a user's symbols.
*)


(* ::Section:: *)
(*PackageExported*)


PackageExported[TrueIntroduction]
PackageExported[AndIntroduction]
PackageExported[OrIntroductionLeft]
PackageExported[OrIntroductionRight]
PackageExported[EqualityReflexivity]
PackageExported[ExistsIntroduction]
PackageExported[NaturalNumberZero]
PackageExported[NaturalNumberSuccessor]
PackageExported[FalseElimination]
PackageExported[AndEliminationLeft]
PackageExported[AndEliminationRight]
PackageExported[EqualitySymmetry]
PackageExported[EqualityTransitivity]
PackageExported[EqualityCongruence]
PackageExported[EqualitySubstitution]


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[preludeEnvironment]
PackageScoped[$preludeDeclarations]
PackageScoped[$preludeEnvironment]


(* ::Section:: *)
(*Usage Messages*)


TrueIntroduction::usage = "TrueIntroduction is the proof of True."
AndIntroduction::usage = "AndIntroduction[p, q] proves And[a, b] from a proof p of a and a proof q of b."
OrIntroductionLeft::usage = "OrIntroductionLeft[p] proves Or[a, b] from a proof p of a."
OrIntroductionRight::usage = "OrIntroductionRight[q] proves Or[a, b] from a proof q of b."
EqualityReflexivity::usage = "EqualityReflexivity[x] proves x == x."
ExistsIntroduction::usage = "ExistsIntroduction[w, h] proves Exists[p] from a witness w and a proof h of p[w]."
NaturalNumberZero::usage = "NaturalNumberZero is the natural number zero, written 0."
NaturalNumberSuccessor::usage = "NaturalNumberSuccessor[n] is the natural number after n."
FalseElimination::usage = "FalseElimination[h] proves any proposition from a proof h of False."
AndEliminationLeft::usage = "AndEliminationLeft[h] proves a from a proof h of And[a, b]."
AndEliminationRight::usage = "AndEliminationRight[h] proves b from a proof h of And[a, b]."
EqualitySymmetry::usage = "EqualitySymmetry[h] proves y == x from a proof h of x == y."
EqualityTransitivity::usage = "EqualityTransitivity[h1, h2] proves x == z from proofs h1 of x == y and h2 of y == z."
EqualityCongruence::usage = "EqualityCongruence[f, h] proves f[x] == f[y] from a proof h of x == y."
EqualitySubstitution::usage = "EqualitySubstitution[h, p] proves P[y] from a proof h of x == y and a proof p of P[x]."

preludeEnvironment::usage = "preludeEnvironment[] gives the environment of the prelude, built and checked when the paclet loads."
$preludeDeclarations::usage = "$preludeDeclarations is the list of the prelude's declarations, in order."
$preludeEnvironment::usage = "$preludeEnvironment is the environment of the prelude."


(* ::Section:: *)
(*Function Definitions*)


$preludeDeclarations = {
	TypeTheoryInductiveType[True, TypeUniverse[0], {TrueIntroduction -> True}],
	TypeTheoryInductiveType[False, TypeUniverse[0], {}],
	TypeTheoryDefinition[Not, Function[{Typed[\[FormalA], TypeUniverse[0]]}, Implies[\[FormalA], False]]],
	TypeTheoryInductiveType[
		And,
		ForAll[{Typed[\[FormalA], TypeUniverse[0]], Typed[\[FormalB], TypeUniverse[0]]}, TypeUniverse[0]],
		{
			AndIntroduction -> ForAll[
				{
					Annotation[Typed[\[FormalA], TypeUniverse[0]], "Implicit"],
					Annotation[Typed[\[FormalB], TypeUniverse[0]], "Implicit"],
					Typed[\[FormalP], \[FormalA]],
					Typed[\[FormalQ], \[FormalB]]
				},
				And[\[FormalA], \[FormalB]]
			]
		}
	],
	TypeTheoryInductiveType[
		Or,
		ForAll[{Typed[\[FormalA], TypeUniverse[0]], Typed[\[FormalB], TypeUniverse[0]]}, TypeUniverse[0]],
		{
			OrIntroductionLeft -> ForAll[
				{Annotation[Typed[\[FormalA], TypeUniverse[0]], "Implicit"], Annotation[Typed[\[FormalB], TypeUniverse[0]], "Implicit"], Typed[\[FormalP], \[FormalA]]},
				Or[\[FormalA], \[FormalB]]
			],
			OrIntroductionRight -> ForAll[
				{Annotation[Typed[\[FormalA], TypeUniverse[0]], "Implicit"], Annotation[Typed[\[FormalB], TypeUniverse[0]], "Implicit"], Typed[\[FormalQ], \[FormalB]]},
				Or[\[FormalA], \[FormalB]]
			]
		}
	],
	TypeTheoryInductiveType[
		Equal,
		ForAll[{Annotation[Typed[\[FormalAlpha], TypeUniverse[\[FormalU]]], "Implicit"], Typed[\[FormalX], \[FormalAlpha]], Typed[\[FormalY], \[FormalAlpha]]}, TypeUniverse[0]],
		{
			EqualityReflexivity -> ForAll[
				{Annotation[Typed[\[FormalAlpha], TypeUniverse[\[FormalU]]], "Implicit"], Typed[\[FormalX], \[FormalAlpha]]},
				\[FormalX] == \[FormalX]
			]
		}
	],
	TypeTheoryInductiveType[
		Exists,
		ForAll[
			{Annotation[Typed[\[FormalAlpha], TypeUniverse[\[FormalU]]], "Implicit"], Typed[\[FormalCapitalP], TypeSpecifier[{\[FormalAlpha]} -> TypeUniverse[0]]]},
			TypeUniverse[0]
		],
		{
			ExistsIntroduction -> ForAll[
				{
					Annotation[Typed[\[FormalAlpha], TypeUniverse[\[FormalU]]], "Implicit"],
					Annotation[Typed[\[FormalCapitalP], TypeSpecifier[{\[FormalAlpha]} -> TypeUniverse[0]]], "Implicit"],
					Typed[\[FormalW], \[FormalAlpha]],
					Typed[\[FormalH], \[FormalCapitalP][\[FormalW]]]
				},
				Exists[\[FormalCapitalP]]
			]
		}
	],
	TypeTheoryInductiveType[
		NonNegativeIntegers,
		TypeUniverse[1],
		{
			NaturalNumberZero -> NonNegativeIntegers,
			NaturalNumberSuccessor -> ForAll[{Typed[\[FormalN], NonNegativeIntegers]}, NonNegativeIntegers]
		}
	],
	(* addition by recursion on the second argument, the form registerNaturalNumbers requires *)
	TypeTheoryDefinition[
		Plus,
		Typed[
			Function[{Typed[\[FormalM], NonNegativeIntegers], Typed[\[FormalN], NonNegativeIntegers]},
				InductiveRecursor[NonNegativeIntegers][
					Function[{Typed[\[FormalT], NonNegativeIntegers]}, NonNegativeIntegers],
					\[FormalM],
					Function[{Typed[\[FormalK], NonNegativeIntegers], Typed[\[FormalR], NonNegativeIntegers]}, NaturalNumberSuccessor[\[FormalR]]],
					\[FormalN]
				]
			],
			TypeSpecifier[{NonNegativeIntegers, NonNegativeIntegers} -> NonNegativeIntegers]
		]
	],
	TypeTheoryNaturalNumbers[NonNegativeIntegers, NaturalNumberZero, NaturalNumberSuccessor, Plus],
	TypeTheoryTheorem[
		FalseElimination,
		ForAll[{Annotation[Typed[\[FormalA], TypeUniverse[0]], "Implicit"]}, Implies[False, \[FormalA]]],
		Function[{Annotation[Typed[\[FormalA], TypeUniverse[0]], "Implicit"], Typed[\[FormalH], False]},
			InductiveRecursor[False][Function[{Typed[\[FormalT], False]}, \[FormalA]], \[FormalH]]
		]
	],
	TypeTheoryTheorem[
		AndEliminationLeft,
		ForAll[
			{Annotation[Typed[\[FormalA], TypeUniverse[0]], "Implicit"], Annotation[Typed[\[FormalB], TypeUniverse[0]], "Implicit"]},
			Implies[And[\[FormalA], \[FormalB]], \[FormalA]]
		],
		Function[
			{Annotation[Typed[\[FormalA], TypeUniverse[0]], "Implicit"], Annotation[Typed[\[FormalB], TypeUniverse[0]], "Implicit"], Typed[\[FormalH], And[\[FormalA], \[FormalB]]]},
			InductiveRecursor[And][
				Function[{Typed[\[FormalT], And[\[FormalA], \[FormalB]]]}, \[FormalA]],
				Function[{Typed[\[FormalP], \[FormalA]], Typed[\[FormalQ], \[FormalB]]}, \[FormalP]],
				\[FormalH]
			]
		]
	],
	TypeTheoryTheorem[
		AndEliminationRight,
		ForAll[
			{Annotation[Typed[\[FormalA], TypeUniverse[0]], "Implicit"], Annotation[Typed[\[FormalB], TypeUniverse[0]], "Implicit"]},
			Implies[And[\[FormalA], \[FormalB]], \[FormalB]]
		],
		Function[
			{Annotation[Typed[\[FormalA], TypeUniverse[0]], "Implicit"], Annotation[Typed[\[FormalB], TypeUniverse[0]], "Implicit"], Typed[\[FormalH], And[\[FormalA], \[FormalB]]]},
			InductiveRecursor[And][
				Function[{Typed[\[FormalT], And[\[FormalA], \[FormalB]]]}, \[FormalB]],
				Function[{Typed[\[FormalP], \[FormalA]], Typed[\[FormalQ], \[FormalB]]}, \[FormalQ]],
				\[FormalH]
			]
		]
	],
	TypeTheoryTheorem[
		EqualitySymmetry,
		ForAll[
			{
				Annotation[Typed[\[FormalAlpha], TypeUniverse[\[FormalU]]], "Implicit"],
				Annotation[Typed[\[FormalX], \[FormalAlpha]], "Implicit"],
				Annotation[Typed[\[FormalY], \[FormalAlpha]], "Implicit"]
			},
			Implies[\[FormalX] == \[FormalY], \[FormalY] == \[FormalX]]
		],
		Function[
			{
				Annotation[Typed[\[FormalAlpha], TypeUniverse[\[FormalU]]], "Implicit"],
				Annotation[Typed[\[FormalX], \[FormalAlpha]], "Implicit"],
				Annotation[Typed[\[FormalY], \[FormalAlpha]], "Implicit"],
				Typed[\[FormalH], \[FormalX] == \[FormalY]]
			},
			InductiveRecursor[Equal][
				Function[{Typed[\[FormalZ], \[FormalAlpha]], Typed[\[FormalE], \[FormalX] == \[FormalZ]]}, \[FormalZ] == \[FormalX]],
				EqualityReflexivity[\[FormalX]],
				\[FormalH]
			]
		]
	],
	TypeTheoryTheorem[
		EqualityTransitivity,
		ForAll[
			{
				Annotation[Typed[\[FormalAlpha], TypeUniverse[\[FormalU]]], "Implicit"],
				Annotation[Typed[\[FormalX], \[FormalAlpha]], "Implicit"],
				Annotation[Typed[\[FormalY], \[FormalAlpha]], "Implicit"],
				Annotation[Typed[\[FormalZ], \[FormalAlpha]], "Implicit"]
			},
			Implies[\[FormalX] == \[FormalY], Implies[\[FormalY] == \[FormalZ], \[FormalX] == \[FormalZ]]]
		],
		Function[
			{
				Annotation[Typed[\[FormalAlpha], TypeUniverse[\[FormalU]]], "Implicit"],
				Annotation[Typed[\[FormalX], \[FormalAlpha]], "Implicit"],
				Annotation[Typed[\[FormalY], \[FormalAlpha]], "Implicit"],
				Annotation[Typed[\[FormalZ], \[FormalAlpha]], "Implicit"],
				Typed[\[FormalH], \[FormalX] == \[FormalY]],
				Typed[\[FormalK], \[FormalY] == \[FormalZ]]
			},
			InductiveRecursor[Equal][
				Function[{Typed[\[FormalW], \[FormalAlpha]], Typed[\[FormalE], \[FormalY] == \[FormalW]]}, \[FormalX] == \[FormalW]],
				\[FormalH],
				\[FormalK]
			]
		]
	],
	TypeTheoryTheorem[
		EqualityCongruence,
		ForAll[
			{
				Annotation[Typed[\[FormalAlpha], TypeUniverse[\[FormalU]]], "Implicit"],
				Annotation[Typed[\[FormalBeta], TypeUniverse[\[FormalV]]], "Implicit"],
				Annotation[Typed[\[FormalX], \[FormalAlpha]], "Implicit"],
				Annotation[Typed[\[FormalY], \[FormalAlpha]], "Implicit"],
				Typed[\[FormalF], TypeSpecifier[{\[FormalAlpha]} -> \[FormalBeta]]]
			},
			Implies[\[FormalX] == \[FormalY], \[FormalF][\[FormalX]] == \[FormalF][\[FormalY]]]
		],
		Function[
			{
				Annotation[Typed[\[FormalAlpha], TypeUniverse[\[FormalU]]], "Implicit"],
				Annotation[Typed[\[FormalBeta], TypeUniverse[\[FormalV]]], "Implicit"],
				Annotation[Typed[\[FormalX], \[FormalAlpha]], "Implicit"],
				Annotation[Typed[\[FormalY], \[FormalAlpha]], "Implicit"],
				Typed[\[FormalF], TypeSpecifier[{\[FormalAlpha]} -> \[FormalBeta]]],
				Typed[\[FormalH], \[FormalX] == \[FormalY]]
			},
			InductiveRecursor[Equal][
				Function[{Typed[\[FormalZ], \[FormalAlpha]], Typed[\[FormalE], \[FormalX] == \[FormalZ]]}, \[FormalF][\[FormalX]] == \[FormalF][\[FormalZ]]],
				EqualityReflexivity[\[FormalF][\[FormalX]]],
				\[FormalH]
			]
		]
	],
	TypeTheoryTheorem[
		EqualitySubstitution,
		ForAll[
			{
				Annotation[Typed[\[FormalAlpha], TypeUniverse[\[FormalU]]], "Implicit"],
				Annotation[Typed[\[FormalCapitalP], TypeSpecifier[{\[FormalAlpha]} -> TypeUniverse[0]]], "Implicit"],
				Annotation[Typed[\[FormalX], \[FormalAlpha]], "Implicit"],
				Annotation[Typed[\[FormalY], \[FormalAlpha]], "Implicit"]
			},
			Implies[\[FormalX] == \[FormalY], Implies[\[FormalCapitalP][\[FormalX]], \[FormalCapitalP][\[FormalY]]]]
		],
		Function[
			{
				Annotation[Typed[\[FormalAlpha], TypeUniverse[\[FormalU]]], "Implicit"],
				Annotation[Typed[\[FormalCapitalP], TypeSpecifier[{\[FormalAlpha]} -> TypeUniverse[0]]], "Implicit"],
				Annotation[Typed[\[FormalX], \[FormalAlpha]], "Implicit"],
				Annotation[Typed[\[FormalY], \[FormalAlpha]], "Implicit"],
				Typed[\[FormalH], \[FormalX] == \[FormalY]],
				Typed[\[FormalP], \[FormalCapitalP][\[FormalX]]]
			},
			InductiveRecursor[Equal][
				Function[{Typed[\[FormalZ], \[FormalAlpha]], Typed[\[FormalE], \[FormalX] == \[FormalZ]]}, \[FormalCapitalP][\[FormalZ]]],
				\[FormalP],
				\[FormalH]
			]
		]
	]
}

preludeEnvironment[] := $preludeEnvironment
