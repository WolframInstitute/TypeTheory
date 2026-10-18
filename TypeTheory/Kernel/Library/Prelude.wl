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

	Equivalent[p, q]           with EquivalentIntroduction, the two implications
	x != y                     Unequal, Not[x == y]
	Identity, Composition      the identity function and composition of functions
	m * n, m^n, Subtract[m, n] Times, Power and Subtract, the last stopping at 0, all by recursion on n
	m <= n                     LessEqual, inductive as in Lean, with Less, GreaterEqual and Greater

The theorems are proved by terms, mostly with the recursors: FalseElimination, AndEliminationLeft,
AndEliminationRight, EqualitySymmetry, EqualityTransitivity, EqualityCongruence and
EqualitySubstitution for logic and equality; the Equivalent theorems; and the laws of arithmetic and
order: commutativity, associativity and distributivity of addition and multiplication, cancellation,
injectivity of the successor, and the order's reflexivity, transitivity and antisymmetry.

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
PackageExported[EquivalentIntroduction]
PackageExported[EquivalentForward]
PackageExported[EquivalentBackward]
PackageExported[EquivalentReflexivity]
PackageExported[EquivalentSymmetry]
PackageExported[EquivalentTransitivity]
PackageExported[NaturalNumberPredecessor]
PackageExported[LessEqualReflexivity]
PackageExported[LessEqualStep]
PackageExported[AdditionZeroRight]
PackageExported[AdditionZeroLeft]
PackageExported[AdditionSuccessorRight]
PackageExported[AdditionSuccessorLeft]
PackageExported[AdditionCommutativity]
PackageExported[AdditionAssociativity]
PackageExported[MultiplicationZeroRight]
PackageExported[MultiplicationZeroLeft]
PackageExported[MultiplicationSuccessorRight]
PackageExported[MultiplicationOneRight]
PackageExported[MultiplicationOneLeft]
PackageExported[MultiplicationSuccessorLeft]
PackageExported[MultiplicationCommutativity]
PackageExported[MultiplicationDistributivityLeft]
PackageExported[MultiplicationDistributivityRight]
PackageExported[MultiplicationAssociativity]
PackageExported[SuccessorInjectivity]
PackageExported[SuccessorNotZero]
PackageExported[SubtractionZeroRight]
PackageExported[SubtractionZeroLeft]
PackageExported[SubtractionSuccessor]
PackageExported[SubtractionSelf]
PackageExported[AdditionSubtractionCancellation]
PackageExported[PowerZero]
PackageExported[PowerSuccessor]
PackageExported[PowerOne]
PackageExported[PowerAddition]
PackageExported[PredecessorLessEqual]
PackageExported[LessEqualZero]
PackageExported[LessEqualSuccessor]
PackageExported[LessEqualTransitivity]
PackageExported[LessEqualAddition]
PackageExported[SuccessorNotLessEqualZero]
PackageExported[LessEqualPredecessor]
PackageExported[LessIrreflexivity]
PackageExported[LessEqualAntisymmetry]


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
EquivalentIntroduction::usage = "EquivalentIntroduction[f, g] proves Equivalent[a, b] from a proof f of Implies[a, b] and a proof g of Implies[b, a]."
EquivalentForward::usage = "EquivalentForward[h] proves Implies[a, b] from a proof h of Equivalent[a, b]."
EquivalentBackward::usage = "EquivalentBackward[h] proves Implies[b, a] from a proof h of Equivalent[a, b]."
EquivalentReflexivity::usage = "EquivalentReflexivity[a] proves Equivalent[a, a]."
EquivalentSymmetry::usage = "EquivalentSymmetry[h] proves Equivalent[b, a] from a proof h of Equivalent[a, b]."
EquivalentTransitivity::usage = "EquivalentTransitivity[h1, h2] proves Equivalent[a, c] from proofs h1 of Equivalent[a, b] and h2 of Equivalent[b, c]."
NaturalNumberPredecessor::usage = "NaturalNumberPredecessor[n] is the natural number before n, and 0 before 0."
LessEqualReflexivity::usage = "LessEqualReflexivity proves n <= n."
LessEqualStep::usage = "LessEqualStep[h] proves n <= m + 1 from a proof h of n <= m."
AdditionZeroRight::usage = "AdditionZeroRight[n] proves n + 0 == n."
AdditionZeroLeft::usage = "AdditionZeroLeft[n] proves 0 + n == n."
AdditionSuccessorRight::usage = "AdditionSuccessorRight[m, n] proves m + (n + 1) == m + n + 1."
AdditionSuccessorLeft::usage = "AdditionSuccessorLeft[m, n] proves m + 1 + n == m + n + 1."
AdditionCommutativity::usage = "AdditionCommutativity[m, n] proves m + n == n + m."
AdditionAssociativity::usage = "AdditionAssociativity[a, b, c] proves a + b + c == a + (b + c)."
MultiplicationZeroRight::usage = "MultiplicationZeroRight[n] proves n * 0 == 0."
MultiplicationZeroLeft::usage = "MultiplicationZeroLeft[n] proves 0 * n == 0."
MultiplicationSuccessorRight::usage = "MultiplicationSuccessorRight[m, n] proves m * (n + 1) == m * n + m."
MultiplicationOneRight::usage = "MultiplicationOneRight[n] proves n * 1 == n."
MultiplicationOneLeft::usage = "MultiplicationOneLeft[n] proves 1 * n == n."
MultiplicationSuccessorLeft::usage = "MultiplicationSuccessorLeft[m, n] proves (m + 1) * n == m * n + n."
MultiplicationCommutativity::usage = "MultiplicationCommutativity[m, n] proves m * n == n * m."
MultiplicationDistributivityLeft::usage = "MultiplicationDistributivityLeft[a, b, c] proves a * (b + c) == a * b + a * c."
MultiplicationDistributivityRight::usage = "MultiplicationDistributivityRight[a, b, c] proves (a + b) * c == a * c + b * c."
MultiplicationAssociativity::usage = "MultiplicationAssociativity[a, b, c] proves a * b * c == a * (b * c)."
SuccessorInjectivity::usage = "SuccessorInjectivity[h] proves m == n from a proof h of m + 1 == n + 1."
SuccessorNotZero::usage = "SuccessorNotZero[n] proves n + 1 != 0."
SubtractionZeroRight::usage = "SubtractionZeroRight[n] proves n - 0 == n."
SubtractionZeroLeft::usage = "SubtractionZeroLeft[n] proves 0 - n == 0: subtraction of natural numbers stops at 0."
SubtractionSuccessor::usage = "SubtractionSuccessor[n, m] proves (n + 1) - (m + 1) == n - m."
SubtractionSelf::usage = "SubtractionSelf[n] proves n - n == 0."
AdditionSubtractionCancellation::usage = "AdditionSubtractionCancellation[n, m] proves (n + m) - m == n."
PowerZero::usage = "PowerZero[m] proves m^0 == 1."
PowerSuccessor::usage = "PowerSuccessor[m, n] proves m^(n + 1) == m^n * m."
PowerOne::usage = "PowerOne[m] proves m^1 == m."
PowerAddition::usage = "PowerAddition[m, a, b] proves m^(a + b) == m^a * m^b."
PredecessorLessEqual::usage = "PredecessorLessEqual[n] proves NaturalNumberPredecessor[n] <= n."
LessEqualZero::usage = "LessEqualZero[n] proves 0 <= n."
LessEqualSuccessor::usage = "LessEqualSuccessor[h] proves n + 1 <= m + 1 from a proof h of n <= m."
LessEqualTransitivity::usage = "LessEqualTransitivity[h1, h2] proves a <= c from proofs h1 of a <= b and h2 of b <= c."
LessEqualAddition::usage = "LessEqualAddition[n, m] proves n <= n + m."
SuccessorNotLessEqualZero::usage = "SuccessorNotLessEqualZero[n] proves Not[n + 1 <= 0]."
LessEqualPredecessor::usage = "LessEqualPredecessor[h] proves n <= m from a proof h of n + 1 <= m + 1."
LessIrreflexivity::usage = "LessIrreflexivity[n] proves Not[n < n]."
LessEqualAntisymmetry::usage = "LessEqualAntisymmetry[h1, h2] proves a == b from proofs h1 of a <= b and h2 of b <= a."

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
		Equivalent,
		ForAll[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]]}, TypeUniverse[0]],
		{
			EquivalentIntroduction -> ForAll[
				{Annotation[Typed[a, TypeUniverse[0]], "Implicit"], Annotation[Typed[b, TypeUniverse[0]], "Implicit"], Typed[f, Implies[a, b]], Typed[g, Implies[b, a]]},
				Equivalent[a, b]
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
	TypeTheoryDefinition[Unequal, Function[{Annotation[Typed[\[Alpha], TypeUniverse[u]], "Implicit"], Typed[x, \[Alpha]], Typed[y, \[Alpha]]}, Not[x == y]]],
	TypeTheoryDefinition[Identity, Function[{Annotation[Typed[\[Alpha], TypeUniverse[u]], "Implicit"], Typed[x, \[Alpha]]}, x]],
	TypeTheoryDefinition[
		Composition,
		Function[
			{
				Annotation[Typed[\[Alpha], TypeUniverse[u]], "Implicit"],
				Annotation[Typed[\[Beta], TypeUniverse[v]], "Implicit"],
				Annotation[Typed[\[Gamma], TypeUniverse[w]], "Implicit"],
				Typed[f, TypeSpecifier[{\[Beta]} -> \[Gamma]]],
				Typed[g, TypeSpecifier[{\[Alpha]} -> \[Beta]]]
			},
			Function[{Typed[x, \[Alpha]]}, f[g[x]]]
		]
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
	(* the number before n, and 0 before 0 *)
	TypeTheoryDefinition[
		NaturalNumberPredecessor,
		Typed[
			Function[{Typed[n, NonNegativeIntegers]},
				InductiveRecursor[NonNegativeIntegers][Function[{Typed[t, NonNegativeIntegers]}, NonNegativeIntegers], 0, Function[{Typed[k, NonNegativeIntegers], Typed[r, NonNegativeIntegers]}, k], n]
			],
			TypeSpecifier[{NonNegativeIntegers} -> NonNegativeIntegers]
		]
	],
	(* subtraction stops at 0, by recursion on the second argument, as Lean's *)
	TypeTheoryDefinition[
		Subtract,
		Typed[
			Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]},
				InductiveRecursor[NonNegativeIntegers][
					Function[{Typed[t, NonNegativeIntegers]}, NonNegativeIntegers],
					m,
					Function[{Typed[k, NonNegativeIntegers], Typed[r, NonNegativeIntegers]}, NaturalNumberPredecessor[r]],
					n
				]
			],
			TypeSpecifier[{NonNegativeIntegers, NonNegativeIntegers} -> NonNegativeIntegers]
		]
	],
	(* m (n + 1) is m n + m, as Lean's *)
	TypeTheoryDefinition[
		Times,
		Typed[
			Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]},
				InductiveRecursor[NonNegativeIntegers][
					Function[{Typed[t, NonNegativeIntegers]}, NonNegativeIntegers],
					0,
					Function[{Typed[k, NonNegativeIntegers], Typed[r, NonNegativeIntegers]}, r + m],
					n
				]
			],
			TypeSpecifier[{NonNegativeIntegers, NonNegativeIntegers} -> NonNegativeIntegers]
		]
	],
	TypeTheoryDefinition[
		Power,
		Typed[
			Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]},
				InductiveRecursor[NonNegativeIntegers][
					Function[{Typed[t, NonNegativeIntegers]}, NonNegativeIntegers],
					1,
					Function[{Typed[k, NonNegativeIntegers], Typed[r, NonNegativeIntegers]}, r * m],
					n
				]
			],
			TypeSpecifier[{NonNegativeIntegers, NonNegativeIntegers} -> NonNegativeIntegers]
		]
	],
	(* m <= n as Lean defines it: n is m, or the successor of a number m is at most *)
	TypeTheoryInductiveType[
		LessEqual,
		TypeSpecifier[{NonNegativeIntegers, NonNegativeIntegers} -> TypeUniverse[0]],
		{
			LessEqualReflexivity -> ForAll[{Annotation[Typed[n, NonNegativeIntegers], "Implicit"]}, n <= n],
			LessEqualStep -> ForAll[{Annotation[Typed[n, NonNegativeIntegers], "Implicit"], Annotation[Typed[m, NonNegativeIntegers], "Implicit"], Typed[h, n <= m]}, n <= NaturalNumberSuccessor[m]]
		}
	],
	TypeTheoryDefinition[Less, Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, m + 1 <= n]],
	TypeTheoryDefinition[GreaterEqual, Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, n <= m]],
	TypeTheoryDefinition[Greater, Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, n < m]],
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
	],
	TypeTheoryTheorem[
		EquivalentForward,
		ForAll[{Annotation[Typed[a, TypeUniverse[0]], "Implicit"], Annotation[Typed[b, TypeUniverse[0]], "Implicit"]}, Implies[Equivalent[a, b], Implies[a, b]]],
		Function[{Annotation[Typed[a, TypeUniverse[0]], "Implicit"], Annotation[Typed[b, TypeUniverse[0]], "Implicit"], Typed[h, Equivalent[a, b]]}, h[[1]]]
	],
	TypeTheoryTheorem[
		EquivalentBackward,
		ForAll[{Annotation[Typed[a, TypeUniverse[0]], "Implicit"], Annotation[Typed[b, TypeUniverse[0]], "Implicit"]}, Implies[Equivalent[a, b], Implies[b, a]]],
		Function[{Annotation[Typed[a, TypeUniverse[0]], "Implicit"], Annotation[Typed[b, TypeUniverse[0]], "Implicit"], Typed[h, Equivalent[a, b]]}, h[[2]]]
	],
	TypeTheoryTheorem[
		EquivalentReflexivity,
		ForAll[{Typed[a, TypeUniverse[0]]}, Equivalent[a, a]],
		Function[{Typed[a, TypeUniverse[0]]}, EquivalentIntroduction[Function[{Typed[p, a]}, p], Function[{Typed[p, a]}, p]]]
	],
	TypeTheoryTheorem[
		EquivalentSymmetry,
		ForAll[{Annotation[Typed[a, TypeUniverse[0]], "Implicit"], Annotation[Typed[b, TypeUniverse[0]], "Implicit"]}, Implies[Equivalent[a, b], Equivalent[b, a]]],
		Function[{Annotation[Typed[a, TypeUniverse[0]], "Implicit"], Annotation[Typed[b, TypeUniverse[0]], "Implicit"], Typed[h, Equivalent[a, b]]}, EquivalentIntroduction[h[[2]], h[[1]]]]
	],
	TypeTheoryTheorem[
		EquivalentTransitivity,
		ForAll[{Annotation[Typed[a, TypeUniverse[0]], "Implicit"], Annotation[Typed[b, TypeUniverse[0]], "Implicit"], Annotation[Typed[c, TypeUniverse[0]], "Implicit"]}, Implies[Equivalent[a, b], Implies[Equivalent[b, c], Equivalent[a, c]]]],
		Function[{Annotation[Typed[a, TypeUniverse[0]], "Implicit"], Annotation[Typed[b, TypeUniverse[0]], "Implicit"], Annotation[Typed[c, TypeUniverse[0]], "Implicit"], Typed[h, Equivalent[a, b]], Typed[k, Equivalent[b, c]]}, EquivalentIntroduction[Function[{Typed[p, a]}, k[[1]][h[[1]][p]]], Function[{Typed[r, c]}, h[[2]][k[[2]][r]]]]]
	],
	TypeTheoryTheorem[
		AdditionZeroRight,
		ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n],
		Function[{Typed[n, NonNegativeIntegers]}, EqualityReflexivity[n]]
	],
	TypeTheoryTheorem[
		AdditionZeroLeft,
		ForAll[{Typed[n, NonNegativeIntegers]}, 0 + n == n],
		Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, 0 + k == k], EqualityReflexivity[0], Function[{Typed[k, NonNegativeIntegers], Typed[ih, 0 + k == k]}, EqualityCongruence[NaturalNumberSuccessor, ih]], n]]
	],
	TypeTheoryTheorem[
		AdditionSuccessorRight,
		ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, m + (n + 1) == m + n + 1],
		Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, EqualityReflexivity[m + n + 1]]
	],
	TypeTheoryTheorem[
		AdditionSuccessorLeft,
		ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, m + 1 + n == m + n + 1],
		Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, m + 1 + k == m + k + 1], EqualityReflexivity[m + 1], Function[{Typed[k, NonNegativeIntegers], Typed[ih, m + 1 + k == m + k + 1]}, EqualityCongruence[NaturalNumberSuccessor, ih]], n]]
	],
	TypeTheoryTheorem[
		AdditionCommutativity,
		ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, m + n == n + m],
		Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, m + k == k + m], EqualitySymmetry[AdditionZeroLeft[m]], Function[{Typed[k, NonNegativeIntegers], Typed[ih, m + k == k + m]}, EqualityTransitivity[EqualityCongruence[NaturalNumberSuccessor, ih], EqualitySymmetry[AdditionSuccessorLeft[k, m]]]], n]]
	],
	TypeTheoryTheorem[
		AdditionAssociativity,
		ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers]}, a + b + c == a + (b + c)],
		Function[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, a + b + k == a + (b + k)], EqualityReflexivity[a + b], Function[{Typed[k, NonNegativeIntegers], Typed[ih, a + b + k == a + (b + k)]}, EqualityCongruence[NaturalNumberSuccessor, ih]], c]]
	],
	TypeTheoryTheorem[
		MultiplicationZeroRight,
		ForAll[{Typed[n, NonNegativeIntegers]}, n * 0 == 0],
		Function[{Typed[n, NonNegativeIntegers]}, EqualityReflexivity[0]]
	],
	TypeTheoryTheorem[
		MultiplicationZeroLeft,
		ForAll[{Typed[n, NonNegativeIntegers]}, 0 * n == 0],
		Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, 0 * k == 0], EqualityReflexivity[0], Function[{Typed[k, NonNegativeIntegers], Typed[ih, 0 * k == 0]}, ih], n]]
	],
	TypeTheoryTheorem[
		MultiplicationSuccessorRight,
		ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, m * (n + 1) == m * n + m],
		Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, EqualityReflexivity[m * n + m]]
	],
	TypeTheoryTheorem[
		MultiplicationOneRight,
		ForAll[{Typed[n, NonNegativeIntegers]}, n * 1 == n],
		Function[{Typed[n, NonNegativeIntegers]}, AdditionZeroLeft[n]]
	],
	TypeTheoryTheorem[
		MultiplicationOneLeft,
		ForAll[{Typed[n, NonNegativeIntegers]}, 1 * n == n],
		Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, 1 * k == k], EqualityReflexivity[0], Function[{Typed[k, NonNegativeIntegers], Typed[ih, 1 * k == k]}, EqualityCongruence[NaturalNumberSuccessor, ih]], n]]
	],
	TypeTheoryTheorem[
		MultiplicationSuccessorLeft,
		ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, (m + 1) * n == m * n + n],
		Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, (m + 1) * k == m * k + k], EqualityReflexivity[0], Function[{Typed[k, NonNegativeIntegers], Typed[ih, (m + 1) * k == m * k + k]}, EqualityCongruence[NaturalNumberSuccessor, EqualityTransitivity[EqualityCongruence[Function[{Typed[x, NonNegativeIntegers]}, x + m], ih], EqualityTransitivity[AdditionAssociativity[m * k, k, m], EqualityTransitivity[EqualityCongruence[Function[{Typed[x, NonNegativeIntegers]}, m * k + x], AdditionCommutativity[k, m]], EqualitySymmetry[AdditionAssociativity[m * k, m, k]]]]]]], n]]
	],
	TypeTheoryTheorem[
		MultiplicationCommutativity,
		ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, m * n == n * m],
		Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, m * k == k * m], EqualitySymmetry[MultiplicationZeroLeft[m]], Function[{Typed[k, NonNegativeIntegers], Typed[ih, m * k == k * m]}, EqualityTransitivity[EqualityCongruence[Function[{Typed[x, NonNegativeIntegers]}, x + m], ih], EqualitySymmetry[MultiplicationSuccessorLeft[k, m]]]], n]]
	],
	TypeTheoryTheorem[
		MultiplicationDistributivityLeft,
		ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers]}, a * (b + c) == a * b + a * c],
		Function[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, a * (b + k) == a * b + a * k], EqualityReflexivity[a * b], Function[{Typed[k, NonNegativeIntegers], Typed[ih, a * (b + k) == a * b + a * k]}, EqualityTransitivity[EqualityCongruence[Function[{Typed[x, NonNegativeIntegers]}, x + a], ih], AdditionAssociativity[a * b, a * k, a]]], c]]
	],
	TypeTheoryTheorem[
		MultiplicationDistributivityRight,
		ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers]}, (a + b) * c == a * c + b * c],
		Function[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers]}, EqualityTransitivity[MultiplicationCommutativity[a + b, c], EqualityTransitivity[MultiplicationDistributivityLeft[c, a, b], EqualityTransitivity[EqualityCongruence[Function[{Typed[x, NonNegativeIntegers]}, x + c * b], MultiplicationCommutativity[c, a]], EqualityCongruence[Function[{Typed[y, NonNegativeIntegers]}, a * c + y], MultiplicationCommutativity[c, b]]]]]]
	],
	TypeTheoryTheorem[
		MultiplicationAssociativity,
		ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers]}, a * b * c == a * (b * c)],
		Function[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, a * b * k == a * (b * k)], EqualityReflexivity[0], Function[{Typed[k, NonNegativeIntegers], Typed[ih, a * b * k == a * (b * k)]}, EqualityTransitivity[EqualityCongruence[Function[{Typed[x, NonNegativeIntegers]}, x + a * b], ih], EqualitySymmetry[MultiplicationDistributivityLeft[a, b * k, b]]]], c]]
	],
	TypeTheoryTheorem[
		SuccessorInjectivity,
		ForAll[{Annotation[Typed[m, NonNegativeIntegers], "Implicit"], Annotation[Typed[n, NonNegativeIntegers], "Implicit"]}, Implies[m + 1 == n + 1, m == n]],
		Function[{Annotation[Typed[m, NonNegativeIntegers], "Implicit"], Annotation[Typed[n, NonNegativeIntegers], "Implicit"], Typed[h, m + 1 == n + 1]}, EqualityCongruence[NaturalNumberPredecessor, h]]
	],
	TypeTheoryTheorem[
		SuccessorNotZero,
		ForAll[{Typed[n, NonNegativeIntegers]}, n + 1 != 0],
		Function[{Typed[n, NonNegativeIntegers], Typed[h, n + 1 == 0]}, Construct[EqualitySubstitution, NonNegativeIntegers, Function[{Typed[k, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[t, NonNegativeIntegers]}, TypeUniverse[0]], False, Function[{Typed[j, NonNegativeIntegers], Typed[r, TypeUniverse[0]]}, True], k]], n + 1, 0, h, TrueIntroduction]]
	],
	TypeTheoryTheorem[
		SubtractionZeroRight,
		ForAll[{Typed[n, NonNegativeIntegers]}, Subtract[n, 0] == n],
		Function[{Typed[n, NonNegativeIntegers]}, EqualityReflexivity[n]]
	],
	TypeTheoryTheorem[
		SubtractionZeroLeft,
		ForAll[{Typed[n, NonNegativeIntegers]}, Subtract[0, n] == 0],
		Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, Subtract[0, k] == 0], EqualityReflexivity[0], Function[{Typed[k, NonNegativeIntegers], Typed[ih, Subtract[0, k] == 0]}, EqualityCongruence[NaturalNumberPredecessor, ih]], n]]
	],
	TypeTheoryTheorem[
		SubtractionSuccessor,
		ForAll[{Typed[n, NonNegativeIntegers], Typed[m, NonNegativeIntegers]}, Subtract[n + 1, m + 1] == Subtract[n, m]],
		Function[{Typed[n, NonNegativeIntegers], Typed[m, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, Subtract[n + 1, k + 1] == Subtract[n, k]], EqualityReflexivity[n], Function[{Typed[k, NonNegativeIntegers], Typed[ih, Subtract[n + 1, k + 1] == Subtract[n, k]]}, EqualityCongruence[NaturalNumberPredecessor, ih]], m]]
	],
	TypeTheoryTheorem[
		SubtractionSelf,
		ForAll[{Typed[n, NonNegativeIntegers]}, Subtract[n, n] == 0],
		Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, Subtract[k, k] == 0], EqualityReflexivity[0], Function[{Typed[k, NonNegativeIntegers], Typed[ih, Subtract[k, k] == 0]}, EqualityTransitivity[SubtractionSuccessor[k, k], ih]], n]]
	],
	TypeTheoryTheorem[
		AdditionSubtractionCancellation,
		ForAll[{Typed[n, NonNegativeIntegers], Typed[m, NonNegativeIntegers]}, Subtract[n + m, m] == n],
		Function[{Typed[n, NonNegativeIntegers], Typed[m, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, Subtract[n + k, k] == n], EqualityReflexivity[n], Function[{Typed[k, NonNegativeIntegers], Typed[ih, Subtract[n + k, k] == n]}, EqualityTransitivity[SubtractionSuccessor[n + k, k], ih]], m]]
	],
	TypeTheoryTheorem[
		PowerZero,
		ForAll[{Typed[m, NonNegativeIntegers]}, m^0 == 1],
		Function[{Typed[m, NonNegativeIntegers]}, EqualityReflexivity[1]]
	],
	TypeTheoryTheorem[
		PowerSuccessor,
		ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, m^(n + 1) == m^n * m],
		Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, EqualityReflexivity[m^n * m]]
	],
	TypeTheoryTheorem[
		PowerOne,
		ForAll[{Typed[m, NonNegativeIntegers]}, m^1 == m],
		Function[{Typed[m, NonNegativeIntegers]}, MultiplicationOneLeft[m]]
	],
	TypeTheoryTheorem[
		PowerAddition,
		ForAll[{Typed[m, NonNegativeIntegers], Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, m^(a + b) == m^a * m^b],
		Function[{Typed[m, NonNegativeIntegers], Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, m^(a + k) == m^a * m^k], EqualitySymmetry[MultiplicationOneRight[m^a]], Function[{Typed[k, NonNegativeIntegers], Typed[ih, m^(a + k) == m^a * m^k]}, EqualityTransitivity[EqualityCongruence[Function[{Typed[x, NonNegativeIntegers]}, x * m], ih], MultiplicationAssociativity[m^a, m^k, m]]], b]]
	],
	TypeTheoryTheorem[
		PredecessorLessEqual,
		ForAll[{Typed[n, NonNegativeIntegers]}, NaturalNumberPredecessor[n] <= n],
		Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, NaturalNumberPredecessor[k] <= k], LessEqualReflexivity, Function[{Typed[k, NonNegativeIntegers], Typed[ih, NaturalNumberPredecessor[k] <= k]}, LessEqualStep[LessEqualReflexivity]], n]]
	],
	TypeTheoryTheorem[
		LessEqualZero,
		ForAll[{Typed[n, NonNegativeIntegers]}, 0 <= n],
		Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, 0 <= k], LessEqualReflexivity, Function[{Typed[k, NonNegativeIntegers], Typed[ih, 0 <= k]}, LessEqualStep[ih]], n]]
	],
	TypeTheoryTheorem[
		LessEqualSuccessor,
		ForAll[{Annotation[Typed[n, NonNegativeIntegers], "Implicit"], Annotation[Typed[m, NonNegativeIntegers], "Implicit"]}, Implies[n <= m, n + 1 <= m + 1]],
		Function[{Annotation[Typed[n, NonNegativeIntegers], "Implicit"], Annotation[Typed[m, NonNegativeIntegers], "Implicit"], Typed[h, n <= m]}, InductiveRecursor[LessEqual][Function[{Typed[j, NonNegativeIntegers], Typed[t, n <= j]}, n + 1 <= j + 1], LessEqualReflexivity, Function[{Typed[j, NonNegativeIntegers], Typed[t, n <= j], Typed[ih, n + 1 <= j + 1]}, LessEqualStep[ih]], h]]
	],
	TypeTheoryTheorem[
		LessEqualTransitivity,
		ForAll[{Annotation[Typed[a, NonNegativeIntegers], "Implicit"], Annotation[Typed[b, NonNegativeIntegers], "Implicit"], Annotation[Typed[c, NonNegativeIntegers], "Implicit"]}, Implies[a <= b, Implies[b <= c, a <= c]]],
		Function[{Annotation[Typed[a, NonNegativeIntegers], "Implicit"], Annotation[Typed[b, NonNegativeIntegers], "Implicit"], Annotation[Typed[c, NonNegativeIntegers], "Implicit"], Typed[h, a <= b], Typed[k, b <= c]}, InductiveRecursor[LessEqual][Function[{Typed[j, NonNegativeIntegers], Typed[t, b <= j]}, a <= j], h, Function[{Typed[j, NonNegativeIntegers], Typed[t, b <= j], Typed[ih, a <= j]}, LessEqualStep[ih]], k]]
	],
	TypeTheoryTheorem[
		LessEqualAddition,
		ForAll[{Typed[n, NonNegativeIntegers], Typed[m, NonNegativeIntegers]}, n <= n + m],
		Function[{Typed[n, NonNegativeIntegers], Typed[m, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, n <= n + k], LessEqualReflexivity, Function[{Typed[k, NonNegativeIntegers], Typed[ih, n <= n + k]}, LessEqualStep[ih]], m]]
	],
	TypeTheoryTheorem[
		SuccessorNotLessEqualZero,
		ForAll[{Typed[n, NonNegativeIntegers]}, Not[n + 1 <= 0]],
		Function[{Typed[n, NonNegativeIntegers], Typed[h, n + 1 <= 0]}, InductiveRecursor[LessEqual][Function[{Typed[j, NonNegativeIntegers], Typed[t, n + 1 <= j]}, Implies[j == 0, False]], SuccessorNotZero[n], Function[{Typed[j, NonNegativeIntegers], Typed[t, n + 1 <= j], Typed[ih, Implies[j == 0, False]]}, SuccessorNotZero[j]], h][EqualityReflexivity[0]]]
	],
	TypeTheoryTheorem[
		LessEqualPredecessor,
		ForAll[{Annotation[Typed[n, NonNegativeIntegers], "Implicit"], Annotation[Typed[m, NonNegativeIntegers], "Implicit"]}, Implies[n + 1 <= m + 1, n <= m]],
		Function[{Annotation[Typed[n, NonNegativeIntegers], "Implicit"], Annotation[Typed[m, NonNegativeIntegers], "Implicit"], Typed[h, n + 1 <= m + 1]}, InductiveRecursor[LessEqual][Function[{Typed[j, NonNegativeIntegers], Typed[t, n + 1 <= j]}, n <= NaturalNumberPredecessor[j]], LessEqualReflexivity, Function[{Typed[j, NonNegativeIntegers], Typed[t, n + 1 <= j], Typed[ih, n <= NaturalNumberPredecessor[j]]}, LessEqualTransitivity[ih, PredecessorLessEqual[j]]], h]]
	],
	TypeTheoryTheorem[
		LessIrreflexivity,
		ForAll[{Typed[n, NonNegativeIntegers]}, Not[n < n]],
		Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, Not[k < k]], SuccessorNotLessEqualZero[0], Function[{Typed[k, NonNegativeIntegers], Typed[ih, Not[k < k]], Typed[h, k + 1 < k + 1]}, ih[LessEqualPredecessor[h]]], n]]
	],
	TypeTheoryTheorem[
		LessEqualAntisymmetry,
		ForAll[{Annotation[Typed[a, NonNegativeIntegers], "Implicit"], Annotation[Typed[b, NonNegativeIntegers], "Implicit"]}, Implies[a <= b, Implies[b <= a, a == b]]],
		Function[{Annotation[Typed[a, NonNegativeIntegers], "Implicit"], Annotation[Typed[b, NonNegativeIntegers], "Implicit"], Typed[h, a <= b], Typed[k, b <= a]}, InductiveRecursor[LessEqual][Function[{Typed[j, NonNegativeIntegers], Typed[t, a <= j]}, Implies[j <= a, a == j]], Function[{Typed[r, a <= a]}, EqualityReflexivity[a]], Function[{Typed[j, NonNegativeIntegers], Typed[t, a <= j], Typed[ih, Implies[j <= a, a == j]], Typed[r, NaturalNumberSuccessor[j] <= a]}, FalseElimination[LessIrreflexivity[j][LessEqualTransitivity[r, t]]]], h][k]]
	]
}

preludeEnvironment[] := $preludeEnvironment
