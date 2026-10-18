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

Bound variables are plain symbols: a binder scopes its variable, so no value can reach it, and the
display shows each by its name.
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
	TypeTheoryDefinition[Not, Function[{Typed[a, TypeUniverse[0]]}, Implies[a, False]]],
	TypeTheoryInductiveType[
		And,
		ForAll[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]]}, TypeUniverse[0]],
		{
			AndIntroduction -> ForAll[
				{
					Annotation[Typed[a, TypeUniverse[0]], "Implicit"],
					Annotation[Typed[b, TypeUniverse[0]], "Implicit"],
					Typed[p, a],
					Typed[q, b]
				},
				And[a, b]
			]
		}
	],
	TypeTheoryInductiveType[
		Or,
		ForAll[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]]}, TypeUniverse[0]],
		{
			OrIntroductionLeft -> ForAll[
				{Annotation[Typed[a, TypeUniverse[0]], "Implicit"], Annotation[Typed[b, TypeUniverse[0]], "Implicit"], Typed[p, a]},
				Or[a, b]
			],
			OrIntroductionRight -> ForAll[
				{Annotation[Typed[a, TypeUniverse[0]], "Implicit"], Annotation[Typed[b, TypeUniverse[0]], "Implicit"], Typed[q, b]},
				Or[a, b]
			]
		}
	],
	TypeTheoryInductiveType[
		Equal,
		ForAll[{Annotation[Typed[\[Alpha], TypeUniverse[u]], "Implicit"], Typed[x, \[Alpha]], Typed[y, \[Alpha]]}, TypeUniverse[0]],
		{
			EqualityReflexivity -> ForAll[
				{Annotation[Typed[\[Alpha], TypeUniverse[u]], "Implicit"], Typed[x, \[Alpha]]},
				x == x
			]
		}
	],
	TypeTheoryInductiveType[
		Exists,
		ForAll[
			{Annotation[Typed[\[Alpha], TypeUniverse[u]], "Implicit"], Typed[P, TypeSpecifier[{\[Alpha]} -> TypeUniverse[0]]]},
			TypeUniverse[0]
		],
		{
			ExistsIntroduction -> ForAll[
				{
					Annotation[Typed[\[Alpha], TypeUniverse[u]], "Implicit"],
					Annotation[Typed[P, TypeSpecifier[{\[Alpha]} -> TypeUniverse[0]]], "Implicit"],
					Typed[w, \[Alpha]],
					Typed[h, P[w]]
				},
				Exists[P]
			]
		}
	],
	TypeTheoryInductiveType[
		NonNegativeIntegers,
		TypeUniverse[1],
		{
			NaturalNumberZero -> NonNegativeIntegers,
			NaturalNumberSuccessor -> ForAll[{Typed[n, NonNegativeIntegers]}, NonNegativeIntegers]
		}
	],
	(* addition by recursion on the second argument, the form registerNaturalNumbers requires *)
	TypeTheoryDefinition[
		Plus,
		Typed[
			Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]},
				InductiveRecursor[NonNegativeIntegers][
					Function[{Typed[t, NonNegativeIntegers]}, NonNegativeIntegers],
					m,
					Function[{Typed[k, NonNegativeIntegers], Typed[r, NonNegativeIntegers]}, NaturalNumberSuccessor[r]],
					n
				]
			],
			TypeSpecifier[{NonNegativeIntegers, NonNegativeIntegers} -> NonNegativeIntegers]
		]
	],
	TypeTheoryNaturalNumbers[NonNegativeIntegers, NaturalNumberZero, NaturalNumberSuccessor, Plus],
	TypeTheoryTheorem[
		FalseElimination,
		ForAll[{Annotation[Typed[a, TypeUniverse[0]], "Implicit"]}, Implies[False, a]],
		Function[{Annotation[Typed[a, TypeUniverse[0]], "Implicit"], Typed[h, False]},
			InductiveRecursor[False][Function[{Typed[t, False]}, a], h]
		]
	],
	TypeTheoryTheorem[
		AndEliminationLeft,
		ForAll[
			{Annotation[Typed[a, TypeUniverse[0]], "Implicit"], Annotation[Typed[b, TypeUniverse[0]], "Implicit"]},
			Implies[And[a, b], a]
		],
		Function[
			{Annotation[Typed[a, TypeUniverse[0]], "Implicit"], Annotation[Typed[b, TypeUniverse[0]], "Implicit"], Typed[h, And[a, b]]},
			InductiveRecursor[And][
				Function[{Typed[t, And[a, b]]}, a],
				Function[{Typed[p, a], Typed[q, b]}, p],
				h
			]
		]
	],
	TypeTheoryTheorem[
		AndEliminationRight,
		ForAll[
			{Annotation[Typed[a, TypeUniverse[0]], "Implicit"], Annotation[Typed[b, TypeUniverse[0]], "Implicit"]},
			Implies[And[a, b], b]
		],
		Function[
			{Annotation[Typed[a, TypeUniverse[0]], "Implicit"], Annotation[Typed[b, TypeUniverse[0]], "Implicit"], Typed[h, And[a, b]]},
			InductiveRecursor[And][
				Function[{Typed[t, And[a, b]]}, b],
				Function[{Typed[p, a], Typed[q, b]}, q],
				h
			]
		]
	],
	TypeTheoryTheorem[
		EqualitySymmetry,
		ForAll[
			{
				Annotation[Typed[\[Alpha], TypeUniverse[u]], "Implicit"],
				Annotation[Typed[x, \[Alpha]], "Implicit"],
				Annotation[Typed[y, \[Alpha]], "Implicit"]
			},
			Implies[x == y, y == x]
		],
		Function[
			{
				Annotation[Typed[\[Alpha], TypeUniverse[u]], "Implicit"],
				Annotation[Typed[x, \[Alpha]], "Implicit"],
				Annotation[Typed[y, \[Alpha]], "Implicit"],
				Typed[h, x == y]
			},
			InductiveRecursor[Equal][
				Function[{Typed[z, \[Alpha]], Typed[e, x == z]}, z == x],
				EqualityReflexivity[x],
				h
			]
		]
	],
	TypeTheoryTheorem[
		EqualityTransitivity,
		ForAll[
			{
				Annotation[Typed[\[Alpha], TypeUniverse[u]], "Implicit"],
				Annotation[Typed[x, \[Alpha]], "Implicit"],
				Annotation[Typed[y, \[Alpha]], "Implicit"],
				Annotation[Typed[z, \[Alpha]], "Implicit"]
			},
			Implies[x == y, Implies[y == z, x == z]]
		],
		Function[
			{
				Annotation[Typed[\[Alpha], TypeUniverse[u]], "Implicit"],
				Annotation[Typed[x, \[Alpha]], "Implicit"],
				Annotation[Typed[y, \[Alpha]], "Implicit"],
				Annotation[Typed[z, \[Alpha]], "Implicit"],
				Typed[h, x == y],
				Typed[k, y == z]
			},
			InductiveRecursor[Equal][
				Function[{Typed[w, \[Alpha]], Typed[e, y == w]}, x == w],
				h,
				k
			]
		]
	],
	TypeTheoryTheorem[
		EqualityCongruence,
		ForAll[
			{
				Annotation[Typed[\[Alpha], TypeUniverse[u]], "Implicit"],
				Annotation[Typed[\[Beta], TypeUniverse[v]], "Implicit"],
				Annotation[Typed[x, \[Alpha]], "Implicit"],
				Annotation[Typed[y, \[Alpha]], "Implicit"],
				Typed[f, TypeSpecifier[{\[Alpha]} -> \[Beta]]]
			},
			Implies[x == y, f[x] == f[y]]
		],
		Function[
			{
				Annotation[Typed[\[Alpha], TypeUniverse[u]], "Implicit"],
				Annotation[Typed[\[Beta], TypeUniverse[v]], "Implicit"],
				Annotation[Typed[x, \[Alpha]], "Implicit"],
				Annotation[Typed[y, \[Alpha]], "Implicit"],
				Typed[f, TypeSpecifier[{\[Alpha]} -> \[Beta]]],
				Typed[h, x == y]
			},
			InductiveRecursor[Equal][
				Function[{Typed[z, \[Alpha]], Typed[e, x == z]}, f[x] == f[z]],
				EqualityReflexivity[f[x]],
				h
			]
		]
	],
	TypeTheoryTheorem[
		EqualitySubstitution,
		ForAll[
			{
				Annotation[Typed[\[Alpha], TypeUniverse[u]], "Implicit"],
				Annotation[Typed[P, TypeSpecifier[{\[Alpha]} -> TypeUniverse[0]]], "Implicit"],
				Annotation[Typed[x, \[Alpha]], "Implicit"],
				Annotation[Typed[y, \[Alpha]], "Implicit"]
			},
			Implies[x == y, Implies[P[x], P[y]]]
		],
		Function[
			{
				Annotation[Typed[\[Alpha], TypeUniverse[u]], "Implicit"],
				Annotation[Typed[P, TypeSpecifier[{\[Alpha]} -> TypeUniverse[0]]], "Implicit"],
				Annotation[Typed[x, \[Alpha]], "Implicit"],
				Annotation[Typed[y, \[Alpha]], "Implicit"],
				Typed[h, x == y],
				Typed[p, P[x]]
			},
			InductiveRecursor[Equal][
				Function[{Typed[z, \[Alpha]], Typed[e, x == z]}, P[z]],
				p,
				h
			]
		]
	]
}

preludeEnvironment[] := $preludeEnvironment
