(* ::Package:: *)

(*
The prelude: classical logic, equality and the natural numbers, written as lists of declarations in the
surface syntax, so it doubles as an example of them. TypeTheoryEnvironment["Prelude"] gives its
environment, built and checked when the paclet loads; TypeTheoryEnvironment["Constructive"] gives the
environment of the constructive declarations alone, without the axioms and what is proved from them.

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
	Booleans                   with BooleanFalse and BooleanTrue, and BooleanNot, BooleanAnd and BooleanOr;
	                           True, False, Not, And and Or stand for these where a Boolean is expected

	Nonempty[a], Subtype[P]    with NonemptyIntroduction, and SubtypeIntroduction, an element and its proof

The theorems are proved by terms, mostly with the recursors: FalseElimination, AndEliminationLeft,
AndEliminationRight, EqualitySymmetry, EqualityTransitivity, EqualityCongruence and
EqualitySubstitution for logic and equality; the Equivalent theorems; and the laws of arithmetic and
order: commutativity, associativity and distributivity of addition and multiplication, cancellation,
injectivity of the successor, and the order's reflexivity, transitivity and antisymmetry.

The classical declarations come last: the axioms PropositionalExtensionality, FunctionExtensionality and
Choice, ChosenWitness defined from Choice, and ExcludedMiddle and DoubleNegationElimination proved from
the axioms.

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
PackageExported[BooleanFalse]
PackageExported[BooleanTrue]
PackageExported[BooleanNot]
PackageExported[BooleanAnd]
PackageExported[BooleanOr]
PackageExported[NonemptyIntroduction]
PackageExported[SubtypeIntroduction]
PackageExported[Nonempty]
PackageExported[Subtype]
PackageExported[PropositionalExtensionality]
PackageExported[FunctionExtensionality]
PackageExported[Choice]
PackageExported[ChosenWitness]
PackageExported[ChosenWitnessProperty]
PackageExported[ExcludedMiddle]
PackageExported[DoubleNegationElimination]


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[preludeEnvironment]
PackageScoped[$constructiveDeclarations]
PackageScoped[$classicalDeclarations]
PackageScoped[constructiveEnvironment]
PackageScoped[$constructiveEnvironment]
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
BooleanFalse::usage = "BooleanFalse is the Boolean false, which False stands for where a Boolean is expected."
BooleanTrue::usage = "BooleanTrue is the Boolean true, which True stands for where a Boolean is expected."
BooleanNot::usage = "BooleanNot[a] is the negation of the Boolean a, which Not[a] and !a stand for when a is a Boolean."
BooleanAnd::usage = "BooleanAnd[a, b] is the conjunction of the Booleans a and b, which And[a, b] and a && b stand for when they are Booleans."
BooleanOr::usage = "BooleanOr[a, b] is the disjunction of the Booleans a and b, which Or[a, b] and a || b stand for when they are Booleans."
Nonempty::usage = "Nonempty[a] is the proposition that the type a has an element."
NonemptyIntroduction::usage = "NonemptyIntroduction[x] proves Nonempty[a] from an element x of a."
Subtype::usage = "Subtype[P] is the type of the elements x of a type with a proof of P[x]."
SubtypeIntroduction::usage = "SubtypeIntroduction[x, h] is the element x of Subtype[P], with h a proof of P[x]."
PropositionalExtensionality::usage = "PropositionalExtensionality[h] proves a == b from a proof h of Equivalent[a, b]: equivalent propositions are equal. It is an axiom of the prelude."
FunctionExtensionality::usage = "FunctionExtensionality[h] proves f == g from a proof h that f[x] == g[x] for every x. It is an axiom of the prelude."
Choice::usage = "Choice[h] is an element of the type a, chosen given a proof h of Nonempty[a]. It is an axiom of the prelude, so it does not compute."
ChosenWitness::usage = "ChosenWitness[h] is an element x with P[x], chosen from a proof h of Exists[P]."
ChosenWitnessProperty::usage = "ChosenWitnessProperty[h] proves P[ChosenWitness[h]] from a proof h of Exists[P]."
ExcludedMiddle::usage = "ExcludedMiddle[p] proves Or[p, Not[p]]. It is a theorem of the prelude, proved from its axioms."
DoubleNegationElimination::usage = "DoubleNegationElimination[p] proves Implies[Not[Not[p]], p]."

preludeEnvironment::usage = "preludeEnvironment[] gives the environment of the prelude, built and checked when the paclet loads."
$constructiveDeclarations::usage = "$constructiveDeclarations is the list of the declarations of the constructive environment, in order."
$classicalDeclarations::usage = "$classicalDeclarations is the list of the classical declarations the prelude adds to the constructive environment."
constructiveEnvironment::usage = "constructiveEnvironment[] gives the constructive environment: the prelude without its axioms and the theorems proved from them."
$constructiveEnvironment::usage = "$constructiveEnvironment is the constructive environment."
$preludeEnvironment::usage = "$preludeEnvironment is the environment of the prelude."


(* ::Section:: *)
(*Function Definitions*)


$constructiveDeclarations = {
	TypeTheoryInductiveType[True, TypeUniverse[0], {TrueIntroduction -> True}],
	TypeTheoryInductiveType[False, TypeUniverse[0], {}],
	TypeTheoryDefinition[Not, Function[{Typed[a, TypeUniverse[0]]}, Implies[a, False]]],
	TypeTheoryInductiveType[
		And,
		ForAll[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]]}, TypeUniverse[0]],
		{
			AndIntroduction -> ForAll[
				{
					TypedImplicit[a, TypeUniverse[0]],
					TypedImplicit[b, TypeUniverse[0]],
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
				{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]], Typed[p, a]},
				Or[a, b]
			],
			OrIntroductionRight -> ForAll[
				{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]], Typed[q, b]},
				Or[a, b]
			]
		}
	],
	TypeTheoryInductiveType[
		Equivalent,
		ForAll[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]]}, TypeUniverse[0]],
		{
			EquivalentIntroduction -> ForAll[
				{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]], Typed[f, Implies[a, b]], Typed[g, Implies[b, a]]},
				Equivalent[a, b]
			]
		}
	],
	TypeTheoryInductiveType[
		Equal,
		ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u]], Typed[x, \[Alpha]], Typed[y, \[Alpha]]}, TypeUniverse[0]],
		{
			EqualityReflexivity -> ForAll[
				{TypedImplicit[\[Alpha], TypeUniverse[u]], Typed[x, \[Alpha]]},
				x == x
			]
		}
	],
	TypeTheoryInductiveType[
		Exists,
		ForAll[
			{TypedImplicit[\[Alpha], TypeUniverse[u]], Typed[P, TypeSpecifier[{\[Alpha]} -> TypeUniverse[0]]]},
			TypeUniverse[0]
		],
		{
			ExistsIntroduction -> ForAll[
				{
					TypedImplicit[\[Alpha], TypeUniverse[u]],
					TypedImplicit[P, TypeSpecifier[{\[Alpha]} -> TypeUniverse[0]]],
					Typed[w, \[Alpha]],
					Typed[h, P[w]]
				},
				Exists[P]
			]
		}
	],
	TypeTheoryDefinition[Unequal, Function[{TypedImplicit[\[Alpha], TypeUniverse[u]], Typed[x, \[Alpha]], Typed[y, \[Alpha]]}, Not[x == y]]],
	TypeTheoryDefinition[Identity, Function[{TypedImplicit[\[Alpha], TypeUniverse[u]], Typed[x, \[Alpha]]}, x]],
	TypeTheoryDefinition[
		Composition,
		Function[
			{
				TypedImplicit[\[Alpha], TypeUniverse[u]],
				TypedImplicit[\[Beta], TypeUniverse[v]],
				TypedImplicit[\[Gamma], TypeUniverse[w]],
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
			LessEqualReflexivity -> ForAll[{TypedImplicit[n, NonNegativeIntegers]}, n <= n],
			LessEqualStep -> ForAll[{TypedImplicit[n, NonNegativeIntegers], TypedImplicit[m, NonNegativeIntegers], Typed[h, n <= m]}, n <= NaturalNumberSuccessor[m]]
		}
	],
	TypeTheoryDefinition[Less, Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, m + 1 <= n]],
	TypeTheoryDefinition[GreaterEqual, Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, n <= m]],
	TypeTheoryDefinition[Greater, Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, n < m]],
	TypeTheoryTheorem[
		FalseElimination,
		ForAll[{TypedImplicit[a, TypeUniverse[0]]}, Implies[False, a]],
		Function[{TypedImplicit[a, TypeUniverse[0]], Typed[h, False]},
			InductiveRecursor[False][Function[{Typed[t, False]}, a], h]
		]
	],
	TypeTheoryTheorem[
		AndEliminationLeft,
		ForAll[
			{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]]},
			Implies[And[a, b], a]
		],
		Function[
			{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]], Typed[h, And[a, b]]},
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
			{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]]},
			Implies[And[a, b], b]
		],
		Function[
			{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]], Typed[h, And[a, b]]},
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
				TypedImplicit[\[Alpha], TypeUniverse[u]],
				TypedImplicit[x, \[Alpha]],
				TypedImplicit[y, \[Alpha]]
			},
			Implies[x == y, y == x]
		],
		Function[
			{
				TypedImplicit[\[Alpha], TypeUniverse[u]],
				TypedImplicit[x, \[Alpha]],
				TypedImplicit[y, \[Alpha]],
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
				TypedImplicit[\[Alpha], TypeUniverse[u]],
				TypedImplicit[x, \[Alpha]],
				TypedImplicit[y, \[Alpha]],
				TypedImplicit[z, \[Alpha]]
			},
			Implies[x == y, Implies[y == z, x == z]]
		],
		Function[
			{
				TypedImplicit[\[Alpha], TypeUniverse[u]],
				TypedImplicit[x, \[Alpha]],
				TypedImplicit[y, \[Alpha]],
				TypedImplicit[z, \[Alpha]],
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
				TypedImplicit[\[Alpha], TypeUniverse[u]],
				TypedImplicit[\[Beta], TypeUniverse[v]],
				TypedImplicit[x, \[Alpha]],
				TypedImplicit[y, \[Alpha]],
				Typed[f, TypeSpecifier[{\[Alpha]} -> \[Beta]]]
			},
			Implies[x == y, f[x] == f[y]]
		],
		Function[
			{
				TypedImplicit[\[Alpha], TypeUniverse[u]],
				TypedImplicit[\[Beta], TypeUniverse[v]],
				TypedImplicit[x, \[Alpha]],
				TypedImplicit[y, \[Alpha]],
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
				TypedImplicit[\[Alpha], TypeUniverse[u]],
				TypedImplicit[P, TypeSpecifier[{\[Alpha]} -> TypeUniverse[0]]],
				TypedImplicit[x, \[Alpha]],
				TypedImplicit[y, \[Alpha]]
			},
			Implies[x == y, Implies[P[x], P[y]]]
		],
		Function[
			{
				TypedImplicit[\[Alpha], TypeUniverse[u]],
				TypedImplicit[P, TypeSpecifier[{\[Alpha]} -> TypeUniverse[0]]],
				TypedImplicit[x, \[Alpha]],
				TypedImplicit[y, \[Alpha]],
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
		ForAll[{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]]}, Implies[Equivalent[a, b], Implies[a, b]]],
		Function[{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]], Typed[h, Equivalent[a, b]]}, h[[1]]]
	],
	TypeTheoryTheorem[
		EquivalentBackward,
		ForAll[{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]]}, Implies[Equivalent[a, b], Implies[b, a]]],
		Function[{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]], Typed[h, Equivalent[a, b]]}, h[[2]]]
	],
	TypeTheoryTheorem[
		EquivalentReflexivity,
		ForAll[{Typed[a, TypeUniverse[0]]}, Equivalent[a, a]],
		Function[{Typed[a, TypeUniverse[0]]}, EquivalentIntroduction[Function[{Typed[p, a]}, p], Function[{Typed[p, a]}, p]]]
	],
	TypeTheoryTheorem[
		EquivalentSymmetry,
		ForAll[{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]]}, Implies[Equivalent[a, b], Equivalent[b, a]]],
		Function[{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]], Typed[h, Equivalent[a, b]]}, EquivalentIntroduction[h[[2]], h[[1]]]]
	],
	TypeTheoryTheorem[
		EquivalentTransitivity,
		ForAll[{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]], TypedImplicit[c, TypeUniverse[0]]}, Implies[Equivalent[a, b], Implies[Equivalent[b, c], Equivalent[a, c]]]],
		Function[{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]], TypedImplicit[c, TypeUniverse[0]], Typed[h, Equivalent[a, b]], Typed[k, Equivalent[b, c]]}, EquivalentIntroduction[Function[{Typed[p, a]}, k[[1]][h[[1]][p]]], Function[{Typed[r, c]}, h[[2]][k[[2]][r]]]]]
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
		ForAll[{TypedImplicit[m, NonNegativeIntegers], TypedImplicit[n, NonNegativeIntegers]}, Implies[m + 1 == n + 1, m == n]],
		Function[{TypedImplicit[m, NonNegativeIntegers], TypedImplicit[n, NonNegativeIntegers], Typed[h, m + 1 == n + 1]}, EqualityCongruence[NaturalNumberPredecessor, h]]
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
		ForAll[{TypedImplicit[n, NonNegativeIntegers], TypedImplicit[m, NonNegativeIntegers]}, Implies[n <= m, n + 1 <= m + 1]],
		Function[{TypedImplicit[n, NonNegativeIntegers], TypedImplicit[m, NonNegativeIntegers], Typed[h, n <= m]}, InductiveRecursor[LessEqual][Function[{Typed[j, NonNegativeIntegers], Typed[t, n <= j]}, n + 1 <= j + 1], LessEqualReflexivity, Function[{Typed[j, NonNegativeIntegers], Typed[t, n <= j], Typed[ih, n + 1 <= j + 1]}, LessEqualStep[ih]], h]]
	],
	TypeTheoryTheorem[
		LessEqualTransitivity,
		ForAll[{TypedImplicit[a, NonNegativeIntegers], TypedImplicit[b, NonNegativeIntegers], TypedImplicit[c, NonNegativeIntegers]}, Implies[a <= b, Implies[b <= c, a <= c]]],
		Function[{TypedImplicit[a, NonNegativeIntegers], TypedImplicit[b, NonNegativeIntegers], TypedImplicit[c, NonNegativeIntegers], Typed[h, a <= b], Typed[k, b <= c]}, InductiveRecursor[LessEqual][Function[{Typed[j, NonNegativeIntegers], Typed[t, b <= j]}, a <= j], h, Function[{Typed[j, NonNegativeIntegers], Typed[t, b <= j], Typed[ih, a <= j]}, LessEqualStep[ih]], k]]
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
		ForAll[{TypedImplicit[n, NonNegativeIntegers], TypedImplicit[m, NonNegativeIntegers]}, Implies[n + 1 <= m + 1, n <= m]],
		Function[{TypedImplicit[n, NonNegativeIntegers], TypedImplicit[m, NonNegativeIntegers], Typed[h, n + 1 <= m + 1]}, InductiveRecursor[LessEqual][Function[{Typed[j, NonNegativeIntegers], Typed[t, n + 1 <= j]}, n <= NaturalNumberPredecessor[j]], LessEqualReflexivity, Function[{Typed[j, NonNegativeIntegers], Typed[t, n + 1 <= j], Typed[ih, n <= NaturalNumberPredecessor[j]]}, LessEqualTransitivity[ih, PredecessorLessEqual[j]]], h]]
	],
	TypeTheoryTheorem[
		LessIrreflexivity,
		ForAll[{Typed[n, NonNegativeIntegers]}, Not[n < n]],
		Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, Not[k < k]], SuccessorNotLessEqualZero[0], Function[{Typed[k, NonNegativeIntegers], Typed[ih, Not[k < k]], Typed[h, k + 1 < k + 1]}, ih[LessEqualPredecessor[h]]], n]]
	],
	TypeTheoryTheorem[
		LessEqualAntisymmetry,
		ForAll[{TypedImplicit[a, NonNegativeIntegers], TypedImplicit[b, NonNegativeIntegers]}, Implies[a <= b, Implies[b <= a, a == b]]],
		Function[{TypedImplicit[a, NonNegativeIntegers], TypedImplicit[b, NonNegativeIntegers], Typed[h, a <= b], Typed[k, b <= a]}, InductiveRecursor[LessEqual][Function[{Typed[j, NonNegativeIntegers], Typed[t, a <= j]}, Implies[j <= a, a == j]], Function[{Typed[r, a <= a]}, EqualityReflexivity[a]], Function[{Typed[j, NonNegativeIntegers], Typed[t, a <= j], Typed[ih, Implies[j <= a, a == j]], Typed[r, NaturalNumberSuccessor[j] <= a]}, FalseElimination[LessIrreflexivity[j][LessEqualTransitivity[r, t]]]], h][k]]
	],

	(* the Booleans, with false before true and the operations by cases on the first argument, as Lean's
	   Bool; once they are declared, True, False, And, Or and Not stand for them where a Boolean is expected *)
	TypeTheoryInductiveType[Booleans, TypeUniverse[1], {BooleanFalse -> Booleans, BooleanTrue -> Booleans}],
	TypeTheoryDefinition[BooleanNot, Function[{Typed[a, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Booleans], BooleanTrue, BooleanFalse, a]]],
	TypeTheoryDefinition[BooleanAnd, Function[{Typed[a, Booleans], Typed[b, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Booleans], BooleanFalse, b, a]]],
	TypeTheoryDefinition[BooleanOr, Function[{Typed[a, Booleans], Typed[b, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Booleans], b, BooleanTrue, a]]]
}

(* The classical part of the prelude: Lean's axioms, propositional extensionality, choice and, since
   there are no quotients, function extensionality, with the excluded middle proved from them as Lean
   proves it, by Diaconescu's argument. TypeTheoryEnvironment["Constructive"] is the prelude without it. *)
$classicalDeclarations = {
	TypeTheoryInductiveType[
		Nonempty,
		ForAll[{Typed[\[Alpha], TypeUniverse[u]]}, TypeUniverse[0]],
		{NonemptyIntroduction -> ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u]], Typed[x, \[Alpha]]}, Nonempty[\[Alpha]]]}
	],
	TypeTheoryInductiveType[
		Subtype,
		ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u]], Typed[P, TypeSpecifier[{\[Alpha]} -> TypeUniverse[0]]]}, TypeUniverse[Max[1, u]]],
		{SubtypeIntroduction -> ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u]], TypedImplicit[P, TypeSpecifier[{\[Alpha]} -> TypeUniverse[0]]], Typed[x, \[Alpha]], Typed[h, P[x]]}, Subtype[P]]}
	],
	TypeTheoryAxiom[
		PropositionalExtensionality,
		ForAll[{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]]}, Implies[Equivalent[a, b], a == b]]
	],
	TypeTheoryAxiom[
		FunctionExtensionality,
		ForAll[
			{
				TypedImplicit[\[Alpha], TypeUniverse[u]],
				TypedImplicit[\[Beta], TypeSpecifier[{\[Alpha]} -> TypeUniverse[v]]],
				TypedImplicit[f, ForAll[{Typed[x, \[Alpha]]}, \[Beta][x]]],
				TypedImplicit[g, ForAll[{Typed[x, \[Alpha]]}, \[Beta][x]]]
			},
			Implies[ForAll[{Typed[x, \[Alpha]]}, f[x] == g[x]], f == g]
		]
	],
	TypeTheoryAxiom[Choice, ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u]], Typed[h, Nonempty[\[Alpha]]]}, \[Alpha]]],
	TypeTheoryDefinition[
		ChosenWitness,
		Function[
			{TypedImplicit[\[Alpha], TypeUniverse[u]], TypedImplicit[P, TypeSpecifier[{\[Alpha]} -> TypeUniverse[0]]], Typed[h, Exists[P]]},
			Choice[InductiveRecursor[Exists][
				Function[{Typed[t, Exists[P]]}, Nonempty[Subtype[P]]],
				Function[{Typed[w, \[Alpha]], Typed[k, P[w]]}, NonemptyIntroduction[SubtypeIntroduction[w, k]]],
				h
			]][[1]]
		]
	],
	TypeTheoryTheorem[
		ChosenWitnessProperty,
		ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u]], TypedImplicit[P, TypeSpecifier[{\[Alpha]} -> TypeUniverse[0]]], Typed[h, Exists[P]]}, P[ChosenWitness[h]]],
		Function[
			{TypedImplicit[\[Alpha], TypeUniverse[u]], TypedImplicit[P, TypeSpecifier[{\[Alpha]} -> TypeUniverse[0]]], Typed[h, Exists[P]]},
			Choice[InductiveRecursor[Exists][
				Function[{Typed[t, Exists[P]]}, Nonempty[Subtype[P]]],
				Function[{Typed[w, \[Alpha]], Typed[k, P[w]]}, NonemptyIntroduction[SubtypeIntroduction[w, k]]],
				h
			]][[2]]
		]
	],
	TypeTheoryTheorem[
		ExcludedMiddle,
		ForAll[{Typed[p, TypeUniverse[0]]}, Or[p, Not[p]]],
		Function[{Typed[p, TypeUniverse[0]]},
			With[
				{
					existsTrue = Typed[ExistsIntroduction[True, OrIntroductionLeft[EqualityReflexivity[True]]], Exists[Function[{Typed[x, TypeUniverse[0]]}, Or[x == True, p]]]],
					existsFalse = Typed[ExistsIntroduction[False, OrIntroductionLeft[EqualityReflexivity[False]]], Exists[Function[{Typed[x, TypeUniverse[0]]}, Or[x == False, p]]]]
				},
				With[
					{
						chosenTrue = ChosenWitness[existsTrue],
						chosenFalse = ChosenWitness[existsFalse],
						trueProperty = ChosenWitnessProperty[existsTrue],
						falseProperty = ChosenWitnessProperty[existsFalse]
					},
					With[
						{
							(* the two choices differ, unless p holds *)
							differentOrP = InductiveRecursor[Or][
								Function[{Typed[t, Or[chosenTrue == True, p]]}, Or[Not[chosenTrue == chosenFalse], p]],
								Function[{Typed[isTrue, chosenTrue == True]},
									InductiveRecursor[Or][
										Function[{Typed[t, Or[chosenFalse == False, p]]}, Or[Not[chosenTrue == chosenFalse], p]],
										Function[{Typed[isFalse, chosenFalse == False]},
											OrIntroductionLeft[Function[{Typed[e, chosenTrue == chosenFalse]},
												Construct[EqualitySubstitution, TypeUniverse[0], Function[{Typed[x, TypeUniverse[0]]}, x], True, False,
													EqualityTransitivity[EqualitySymmetry[isTrue], EqualityTransitivity[e, isFalse]],
													TrueIntroduction
												]
											]]
										],
										Function[{Typed[holds, p]}, OrIntroductionRight[holds]],
										falseProperty
									]
								],
								Function[{Typed[holds, p]}, OrIntroductionRight[holds]],
								trueProperty
							],
							(* if p holds, the two predicates are equal, and so are the choices *)
							sameIfP = Function[{Typed[holds, p]},
								Construct[EqualitySubstitution,
									TypeSpecifier[{TypeUniverse[0]} -> TypeUniverse[0]],
									Function[{Typed[W, TypeSpecifier[{TypeUniverse[0]} -> TypeUniverse[0]]]}, ForAll[{Typed[e, Exists[W]]}, chosenTrue == ChosenWitness[e]]],
									Function[{Typed[x, TypeUniverse[0]]}, Or[x == True, p]],
									Function[{Typed[x, TypeUniverse[0]]}, Or[x == False, p]],
									FunctionExtensionality[Function[{Typed[x, TypeUniverse[0]]},
										PropositionalExtensionality[EquivalentIntroduction[
											Function[{Typed[k, Or[x == True, p]]}, OrIntroductionRight[holds]],
											Function[{Typed[k, Or[x == False, p]]}, OrIntroductionRight[holds]]
										]]
									]],
									Function[{Typed[e, Exists[Function[{Typed[x, TypeUniverse[0]]}, Or[x == True, p]]]]}, EqualityReflexivity[chosenTrue]]
								][existsFalse]
							]
						},
						InductiveRecursor[Or][
							Function[{Typed[t, Or[Not[chosenTrue == chosenFalse], p]]}, Or[p, Not[p]]],
							Function[{Typed[different, Not[chosenTrue == chosenFalse]]}, OrIntroductionRight[Function[{Typed[holds, p]}, different[sameIfP[holds]]]]],
							Function[{Typed[holds, p]}, OrIntroductionLeft[holds]],
							differentOrP
						]
					]
				]
			]
		]
	],
	TypeTheoryTheorem[
		DoubleNegationElimination,
		ForAll[{Typed[p, TypeUniverse[0]]}, Implies[Not[Not[p]], p]],
		Function[{Typed[p, TypeUniverse[0]], Typed[h, Not[Not[p]]]},
			InductiveRecursor[Or][
				Function[{Typed[t, Or[p, Not[p]]]}, p],
				Function[{Typed[k, p]}, k],
				Function[{Typed[k, Not[p]]}, FalseElimination[h[k]]],
				ExcludedMiddle[p]
			]
		]
	]
}

preludeEnvironment[] := $preludeEnvironment

constructiveEnvironment[] := $constructiveEnvironment
