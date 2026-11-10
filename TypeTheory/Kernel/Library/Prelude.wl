(* ::Package:: *)

(*
The prelude: classical logic, equality, the natural numbers, decisions and lists, written as lists of
declarations in the surface syntax, so it doubles as an example of them. TypeTheoryEnvironment["Prelude"]
gives its environment, built and checked when the paclet loads; TypeTheoryEnvironment["Constructive"]
gives the environment of the constructive declarations alone, without the axioms and what is proved
from them.

The connectives are built-in symbols, so terms read as ordinary mathematics:

	True, False                propositions with one proof and with none
	Not[p]                     Implies[p, False], a definition
	And[p, q], Or[p, q]        with "andIntroduction", "orIntroductionLeft" and "orIntroductionRight"
	a == b                     Equal, with "equalityReflexivity"
	Exists[{Typed[x, A]}, p]   Exists applied to a predicate, with "existsIntroduction"
	NonNegativeIntegers        the natural numbers, with "zero" and "successor",
	                           registered so that the literals 0, 1, 2, ... are natural numbers
	m + n                      Plus, by recursion on n

	Equivalent[p, q]           with "equivalentIntroduction", the two implications
	x != y                     Unequal, Not[x == y]
	Identity, Composition      the identity function and composition of functions
	QuotientType[r]            the quotient types, with QuotientIntroduction, QuotientLift and
	                           QuotientInduction
	m * n, m^n, Subtract[m, n] Times, Power and Subtract, the last stopping at 0, all by recursion on n
	m <= n                     LessEqual, an inductive family, with Less, GreaterEqual and Greater
	Booleans                   with the constants "false" and "true", "not", "and" and "or", named by strings;
	                           True, False, Not, And and Or stand for these where a Boolean is expected
	"equal", "lessEqual"       the Boolean comparisons of natural numbers, which the kernel computes on literals
	Decidable[p]               decisions, with Decide, "decideSoundness", and the instances deciding == and <= of
	                           natural numbers, True, False, the connectives and == of Booleans, the last three
	                           named "trueDecidable", "falseDecidable" and "booleanEqualityDecidable"
	CartesianProductType, DisjointUnionType, Option, List
	                           pairs, sums, optional values and lists, with Join, Length, Map, Append and Reverse:
	                           {a}, List[a], is the type of lists of a where a type is expected, and a list elsewhere

	Nonempty[a], Subtype[P]    with "nonempty", and "subtype", an element and its proof

The theorems are proved by terms, mostly with the recursors: "falseElimination", "andEliminationLeft",
"andEliminationRight", "equalitySymmetry", "equalityTransitivity", "equalityCongruence" and
"equalitySubstitution" for logic and equality; the Equivalent theorems; and the laws of arithmetic and
order: commutativity, associativity and distributivity of addition and multiplication, cancellation,
injectivity of the successor, and the order's reflexivity, transitivity and antisymmetry.

The classical declarations come last: the axioms "propositionalExtensionality", "quotientSoundness" and
"choice", ChosenWitness defined from "choice", and "functionExtensionality", "excludedMiddle" and
"doubleNegationElimination" proved from the axioms.

Bound variables are plain symbols: a binder scopes its variable, so no value can reach it, and the
display shows each by its name.
*)


(* ::Section:: *)
(*PackageExported*)


PackageExported[Naturals]
PackageExported[NaturalNumberPredecessor]
PackageExported[Nonempty]
PackageExported[Subtype]
PackageExported[ChosenWitness]
PackageExported[Decidable]
PackageExported[Decide]
PackageExported[CartesianProductType]
PackageExported[DisjointUnionType]
PackageExported[Option]


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


Naturals::usage = "Naturals is NonNegativeIntegers, the natural numbers of the prelude, by a shorter name: in a term, a symbol whose \
value is a declared constant stands for that constant."
NaturalNumberPredecessor::usage = "NaturalNumberPredecessor[n] is the natural number before n, and 0 before 0."
Nonempty::usage = "Nonempty[a] is the proposition that the type a has an element."
Subtype::usage = "Subtype[P] is the type of the elements x of a type with a proof of P[x]; s[\"element\"] and s[\"proof\"] are the parts of one, s."
ChosenWitness::usage = "ChosenWitness[h] is an element x with P[x], chosen from a proof h of Exists[P]."
Decidable::usage = "Decidable[p] is the type of decisions of the proposition p: \"decidableFalse\" with a proof of Not[p], or \"decidableTrue\" with a proof of p."
Decide::usage = "Decide[p] is the Boolean that the decision of the proposition p computes, False for \"decidableFalse\" and True for \"decidableTrue\", \
the decision being the instance of Decidable[p] that elaboration finds."
CartesianProductType::usage = "CartesianProductType[a, b] is the type of the pairs of an element of the type a and one of the type b; p[\"first\"] and p[\"second\"] are the parts of a pair p, also p[[1]] and p[[2]]."
DisjointUnionType::usage = "DisjointUnionType[a, b] is the type of the elements of the type a or of the type b, each tagged with its side."
Option::usage = "Option[a] is the type of optional elements of the type a: \"none\", or \"some\"[x] with x of type a."

preludeEnvironment::usage = "preludeEnvironment[] gives the environment of the prelude, built and checked when the paclet loads."
$constructiveDeclarations::usage = "$constructiveDeclarations is the list of the declarations of the constructive environment, in order."
$classicalDeclarations::usage = "$classicalDeclarations is the list of the classical declarations the prelude adds to the constructive environment."
constructiveEnvironment::usage = "constructiveEnvironment[] gives the constructive environment: the prelude without its axioms and the theorems proved from them."
$constructiveEnvironment::usage = "$constructiveEnvironment is the constructive environment."
$preludeEnvironment::usage = "$preludeEnvironment is the environment of the prelude."


(* ::Section:: *)
(*Function Definitions*)


Naturals = NonNegativeIntegers

$constructiveDeclarations = {
	TypeTheoryInductiveType[True, TypeUniverse[0], {"trueIntroduction" -> True}],
	TypeTheoryInductiveType[False, TypeUniverse[0], {}],
	TypeTheoryDefinition[Not, Function[{Typed[a, TypeUniverse[0]]}, Implies[a, False]]],
	TypeTheoryInductiveType[
		And,
		ForAll[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]]}, TypeUniverse[0]],
		{
			"andIntroduction" -> ForAll[
				{
					TypedImplicit[a, TypeUniverse[0]],
					TypedImplicit[b, TypeUniverse[0]],
					Typed[left, a],
					Typed[right, b]
				},
				And[a, b]
			]
		}
	],
	TypeTheoryInductiveType[
		Or,
		ForAll[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]]}, TypeUniverse[0]],
		{
			"orIntroductionLeft" -> ForAll[
				{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]], Typed[p, a]},
				Or[a, b]
			],
			"orIntroductionRight" -> ForAll[
				{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]], Typed[q, b]},
				Or[a, b]
			]
		}
	],
	TypeTheoryInductiveType[
		Equivalent,
		ForAll[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]]}, TypeUniverse[0]],
		{
			"equivalentIntroduction" -> ForAll[
				{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]], Typed[forward, Implies[a, b]], Typed[backward, Implies[b, a]]},
				Equivalent[a, b]
			]
		}
	],
	TypeTheoryInductiveType[
		Equal,
		ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u]], Typed[x, \[Alpha]], Typed[y, \[Alpha]]}, TypeUniverse[0]],
		{
			"equalityReflexivity" -> ForAll[
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
			"existsIntroduction" -> ForAll[
				{
					TypedImplicit[\[Alpha], TypeUniverse[u]],
					TypedImplicit[P, TypeSpecifier[{\[Alpha]} -> TypeUniverse[0]]],
					Typed[witness, \[Alpha]],
					Typed[proof, P[witness]]
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
	(* the quotient types, whose lift computes on a class; that related elements have equal
	   classes is the axiom "quotientSoundness", among the classical declarations *)
	TypeTheoryQuotients[],
	TypeTheoryInductiveType[
		NonNegativeIntegers,
		TypeUniverse[1],
		{
			"zero" -> NonNegativeIntegers,
			"successor" -> ForAll[{Typed[n, NonNegativeIntegers]}, NonNegativeIntegers]
		}
	],
	(* addition by recursion on the second argument *)
	TypeTheoryDefinition[
		Plus,
		Typed[
			Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]},
				InductiveRecursor[NonNegativeIntegers][
					Function[{Typed[t, NonNegativeIntegers]}, NonNegativeIntegers],
					m,
					Function[{Typed[k, NonNegativeIntegers], Typed[r, NonNegativeIntegers]}, "successor"[r]],
					n
				]
			],
			TypeSpecifier[{NonNegativeIntegers, NonNegativeIntegers} -> NonNegativeIntegers]
		]
	],
	TypeTheoryNaturalNumbers[NonNegativeIntegers, "zero", "successor", Plus],
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
	(* subtraction stops at 0, by recursion on the second argument *)
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
	(* m (n + 1) is m n + m *)
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
	(* the kernel computes these on literals with integers *)
	TypeTheoryNaturalNumbers[NonNegativeIntegers, "zero", "successor", <|"Subtraction" -> Subtract, "Multiplication" -> Times, "Power" -> Power|>],
	(* m <= n, inductively: n is m, or the successor of a number m is at most *)
	TypeTheoryInductiveType[
		LessEqual,
		TypeSpecifier[{NonNegativeIntegers, NonNegativeIntegers} -> TypeUniverse[0]],
		{
			"lessEqualReflexivity" -> ForAll[{TypedImplicit[n, NonNegativeIntegers]}, n <= n],
			"lessEqualStep" -> ForAll[{TypedImplicit[n, NonNegativeIntegers], TypedImplicit[m, NonNegativeIntegers], Typed[h, n <= m]}, n <= "successor"[m]]
		}
	],
	TypeTheoryDefinition[Less, Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, m + 1 <= n]],
	TypeTheoryDefinition[GreaterEqual, Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, n <= m]],
	TypeTheoryDefinition[Greater, Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, n < m]],
	TypeTheoryTheorem[
		"falseElimination",
		ForAll[{TypedImplicit[a, TypeUniverse[0]]}, Implies[False, a]],
		Function[{TypedImplicit[a, TypeUniverse[0]], Typed[h, False]},
			InductiveRecursor[False][Function[{Typed[t, False]}, a], h]
		]
	],
	TypeTheoryTheorem[
		"andEliminationLeft",
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
		"andEliminationRight",
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
		"equalitySymmetry",
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
				"equalityReflexivity"[x],
				h
			]
		]
	],
	TypeTheoryTheorem[
		"equalityTransitivity",
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
		"equalityCongruence",
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
				"equalityReflexivity"[f[x]],
				h
			]
		]
	],
	TypeTheoryTheorem[
		"equalitySubstitution",
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
		"equivalentForward",
		ForAll[{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]]}, Implies[Equivalent[a, b], Implies[a, b]]],
		Function[{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]], Typed[h, Equivalent[a, b]]}, h[[1]]]
	],
	TypeTheoryTheorem[
		"equivalentBackward",
		ForAll[{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]]}, Implies[Equivalent[a, b], Implies[b, a]]],
		Function[{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]], Typed[h, Equivalent[a, b]]}, h[[2]]]
	],
	TypeTheoryTheorem[
		"equivalentReflexivity",
		ForAll[{Typed[a, TypeUniverse[0]]}, Equivalent[a, a]],
		Function[{Typed[a, TypeUniverse[0]]}, "equivalentIntroduction"[Function[{Typed[p, a]}, p], Function[{Typed[p, a]}, p]]]
	],
	TypeTheoryTheorem[
		"equivalentSymmetry",
		ForAll[{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]]}, Implies[Equivalent[a, b], Equivalent[b, a]]],
		Function[{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]], Typed[h, Equivalent[a, b]]}, "equivalentIntroduction"[h[[2]], h[[1]]]]
	],
	TypeTheoryTheorem[
		"equivalentTransitivity",
		ForAll[{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]], TypedImplicit[c, TypeUniverse[0]]}, Implies[Equivalent[a, b], Implies[Equivalent[b, c], Equivalent[a, c]]]],
		Function[{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]], TypedImplicit[c, TypeUniverse[0]], Typed[h, Equivalent[a, b]], Typed[k, Equivalent[b, c]]}, "equivalentIntroduction"[Function[{Typed[p, a]}, k[[1]][h[[1]][p]]], Function[{Typed[r, c]}, h[[2]][k[[2]][r]]]]]
	],
	TypeTheoryTheorem[
		"additionZeroRight",
		ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n],
		Function[{Typed[n, NonNegativeIntegers]}, "equalityReflexivity"[n]]
	],
	TypeTheoryTheorem[
		"additionZeroLeft",
		ForAll[{Typed[n, NonNegativeIntegers]}, 0 + n == n],
		Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, 0 + k == k], "equalityReflexivity"[0], Function[{Typed[k, NonNegativeIntegers], Typed[ih, 0 + k == k]}, "equalityCongruence"["successor", ih]], n]]
	],
	TypeTheoryTheorem[
		"additionSuccessorRight",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, m + (n + 1) == m + n + 1],
		Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, "equalityReflexivity"[m + n + 1]]
	],
	TypeTheoryTheorem[
		"additionSuccessorLeft",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, m + 1 + n == m + n + 1],
		Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, m + 1 + k == m + k + 1], "equalityReflexivity"[m + 1], Function[{Typed[k, NonNegativeIntegers], Typed[ih, m + 1 + k == m + k + 1]}, "equalityCongruence"["successor", ih]], n]]
	],
	TypeTheoryTheorem[
		"additionCommutativity",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, m + n == n + m],
		Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, m + k == k + m], "equalitySymmetry"["additionZeroLeft"[m]], Function[{Typed[k, NonNegativeIntegers], Typed[ih, m + k == k + m]}, "equalityTransitivity"["equalityCongruence"["successor", ih], "equalitySymmetry"["additionSuccessorLeft"[k, m]]]], n]]
	],
	TypeTheoryTheorem[
		"additionAssociativity",
		ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers]}, a + b + c == a + (b + c)],
		Function[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, a + b + k == a + (b + k)], "equalityReflexivity"[a + b], Function[{Typed[k, NonNegativeIntegers], Typed[ih, a + b + k == a + (b + k)]}, "equalityCongruence"["successor", ih]], c]]
	],
	TypeTheoryTheorem[
		"multiplicationZeroRight",
		ForAll[{Typed[n, NonNegativeIntegers]}, n * 0 == 0],
		Function[{Typed[n, NonNegativeIntegers]}, "equalityReflexivity"[0]]
	],
	TypeTheoryTheorem[
		"multiplicationZeroLeft",
		ForAll[{Typed[n, NonNegativeIntegers]}, 0 * n == 0],
		Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, 0 * k == 0], "equalityReflexivity"[0], Function[{Typed[k, NonNegativeIntegers], Typed[ih, 0 * k == 0]}, ih], n]]
	],
	TypeTheoryTheorem[
		"multiplicationSuccessorRight",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, m * (n + 1) == m * n + m],
		Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, "equalityReflexivity"[m * n + m]]
	],
	TypeTheoryTheorem[
		"multiplicationOneRight",
		ForAll[{Typed[n, NonNegativeIntegers]}, n * 1 == n],
		Function[{Typed[n, NonNegativeIntegers]}, "additionZeroLeft"[n]]
	],
	TypeTheoryTheorem[
		"multiplicationOneLeft",
		ForAll[{Typed[n, NonNegativeIntegers]}, 1 * n == n],
		Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, 1 * k == k], "equalityReflexivity"[0], Function[{Typed[k, NonNegativeIntegers], Typed[ih, 1 * k == k]}, "equalityCongruence"["successor", ih]], n]]
	],
	TypeTheoryTheorem[
		"multiplicationSuccessorLeft",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, (m + 1) * n == m * n + n],
		Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, (m + 1) * k == m * k + k], "equalityReflexivity"[0], Function[{Typed[k, NonNegativeIntegers], Typed[ih, (m + 1) * k == m * k + k]}, "equalityCongruence"["successor", "equalityTransitivity"["equalityCongruence"[Function[{Typed[x, NonNegativeIntegers]}, x + m], ih], "equalityTransitivity"["additionAssociativity"[m * k, k, m], "equalityTransitivity"["equalityCongruence"[Function[{Typed[x, NonNegativeIntegers]}, m * k + x], "additionCommutativity"[k, m]], "equalitySymmetry"["additionAssociativity"[m * k, m, k]]]]]]], n]]
	],
	TypeTheoryTheorem[
		"multiplicationCommutativity",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, m * n == n * m],
		Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, m * k == k * m], "equalitySymmetry"["multiplicationZeroLeft"[m]], Function[{Typed[k, NonNegativeIntegers], Typed[ih, m * k == k * m]}, "equalityTransitivity"["equalityCongruence"[Function[{Typed[x, NonNegativeIntegers]}, x + m], ih], "equalitySymmetry"["multiplicationSuccessorLeft"[k, m]]]], n]]
	],
	TypeTheoryTheorem[
		"multiplicationDistributivityLeft",
		ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers]}, a * (b + c) == a * b + a * c],
		Function[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, a * (b + k) == a * b + a * k], "equalityReflexivity"[a * b], Function[{Typed[k, NonNegativeIntegers], Typed[ih, a * (b + k) == a * b + a * k]}, "equalityTransitivity"["equalityCongruence"[Function[{Typed[x, NonNegativeIntegers]}, x + a], ih], "additionAssociativity"[a * b, a * k, a]]], c]]
	],
	TypeTheoryTheorem[
		"multiplicationDistributivityRight",
		ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers]}, (a + b) * c == a * c + b * c],
		Function[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers]}, "equalityTransitivity"["multiplicationCommutativity"[a + b, c], "equalityTransitivity"["multiplicationDistributivityLeft"[c, a, b], "equalityTransitivity"["equalityCongruence"[Function[{Typed[x, NonNegativeIntegers]}, x + c * b], "multiplicationCommutativity"[c, a]], "equalityCongruence"[Function[{Typed[y, NonNegativeIntegers]}, a * c + y], "multiplicationCommutativity"[c, b]]]]]]
	],
	TypeTheoryTheorem[
		"multiplicationAssociativity",
		ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers]}, a * b * c == a * (b * c)],
		Function[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, a * b * k == a * (b * k)], "equalityReflexivity"[0], Function[{Typed[k, NonNegativeIntegers], Typed[ih, a * b * k == a * (b * k)]}, "equalityTransitivity"["equalityCongruence"[Function[{Typed[x, NonNegativeIntegers]}, x + a * b], ih], "equalitySymmetry"["multiplicationDistributivityLeft"[a, b * k, b]]]], c]]
	],
	TypeTheoryTheorem[
		"successorInjectivity",
		ForAll[{TypedImplicit[m, NonNegativeIntegers], TypedImplicit[n, NonNegativeIntegers]}, Implies[m + 1 == n + 1, m == n]],
		Function[{TypedImplicit[m, NonNegativeIntegers], TypedImplicit[n, NonNegativeIntegers], Typed[h, m + 1 == n + 1]}, "equalityCongruence"[NaturalNumberPredecessor, h]]
	],
	TypeTheoryTheorem[
		"successorNotZero",
		ForAll[{Typed[n, NonNegativeIntegers]}, n + 1 != 0],
		Function[{Typed[n, NonNegativeIntegers], Typed[h, n + 1 == 0]}, Construct["equalitySubstitution", NonNegativeIntegers, Function[{Typed[k, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[t, NonNegativeIntegers]}, TypeUniverse[0]], False, Function[{Typed[j, NonNegativeIntegers], Typed[r, TypeUniverse[0]]}, True], k]], n + 1, 0, h, "trueIntroduction"]]
	],
	TypeTheoryTheorem[
		"subtractionZeroRight",
		ForAll[{Typed[n, NonNegativeIntegers]}, Subtract[n, 0] == n],
		Function[{Typed[n, NonNegativeIntegers]}, "equalityReflexivity"[n]]
	],
	TypeTheoryTheorem[
		"subtractionZeroLeft",
		ForAll[{Typed[n, NonNegativeIntegers]}, Subtract[0, n] == 0],
		Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, Subtract[0, k] == 0], "equalityReflexivity"[0], Function[{Typed[k, NonNegativeIntegers], Typed[ih, Subtract[0, k] == 0]}, "equalityCongruence"[NaturalNumberPredecessor, ih]], n]]
	],
	TypeTheoryTheorem[
		"subtractionSuccessor",
		ForAll[{Typed[n, NonNegativeIntegers], Typed[m, NonNegativeIntegers]}, Subtract[n + 1, m + 1] == Subtract[n, m]],
		Function[{Typed[n, NonNegativeIntegers], Typed[m, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, Subtract[n + 1, k + 1] == Subtract[n, k]], "equalityReflexivity"[n], Function[{Typed[k, NonNegativeIntegers], Typed[ih, Subtract[n + 1, k + 1] == Subtract[n, k]]}, "equalityCongruence"[NaturalNumberPredecessor, ih]], m]]
	],
	TypeTheoryTheorem[
		"subtractionSelf",
		ForAll[{Typed[n, NonNegativeIntegers]}, Subtract[n, n] == 0],
		Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, Subtract[k, k] == 0], "equalityReflexivity"[0], Function[{Typed[k, NonNegativeIntegers], Typed[ih, Subtract[k, k] == 0]}, "equalityTransitivity"["subtractionSuccessor"[k, k], ih]], n]]
	],
	TypeTheoryTheorem[
		"additionSubtractionCancellation",
		ForAll[{Typed[n, NonNegativeIntegers], Typed[m, NonNegativeIntegers]}, Subtract[n + m, m] == n],
		Function[{Typed[n, NonNegativeIntegers], Typed[m, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, Subtract[n + k, k] == n], "equalityReflexivity"[n], Function[{Typed[k, NonNegativeIntegers], Typed[ih, Subtract[n + k, k] == n]}, "equalityTransitivity"["subtractionSuccessor"[n + k, k], ih]], m]]
	],
	(* a product by a positive number determines the other factor *)
	TypeTheoryTheorem[
		"multiplicationCancellation",
		ForAll[{Typed[k, NonNegativeIntegers], Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, Implies[(k + 1) * a == (k + 1) * b, a == b]],
		Function[{Typed[k, NonNegativeIntegers], Typed[a, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
			Function[{Typed[t, NonNegativeIntegers]}, ForAll[{Typed[b, NonNegativeIntegers]}, Implies[(k + 1) * t == (k + 1) * b, t == b]]],
			Function[{Typed[b, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
				Function[{Typed[c, NonNegativeIntegers]}, Implies[(k + 1) * 0 == (k + 1) * c, 0 == c]],
				Function[{Typed[h, (k + 1) * 0 == (k + 1) * 0]}, "equalityReflexivity"[0]],
				Function[{Typed[c, NonNegativeIntegers], Typed[r, Implies[(k + 1) * 0 == (k + 1) * c, 0 == c]], Typed[h, (k + 1) * 0 == (k + 1) * (c + 1)]},
					"falseElimination"["successorNotZero"[(k + 1) * c + k]["equalitySymmetry"[h]]]
				],
				b
			]],
			Function[{Typed[t, NonNegativeIntegers], Typed[ih, ForAll[{Typed[b, NonNegativeIntegers]}, Implies[(k + 1) * t == (k + 1) * b, t == b]]]}, Function[{Typed[b, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
				Function[{Typed[c, NonNegativeIntegers]}, Implies[(k + 1) * (t + 1) == (k + 1) * c, t + 1 == c]],
				Function[{Typed[h, (k + 1) * (t + 1) == (k + 1) * 0]}, "falseElimination"["successorNotZero"[(k + 1) * t + k][h]]],
				Function[{Typed[c, NonNegativeIntegers], Typed[r, Implies[(k + 1) * (t + 1) == (k + 1) * c, t + 1 == c]], Typed[h, (k + 1) * (t + 1) == (k + 1) * (c + 1)]},
					"equalityCongruence"["successor", ih[c, "equalityTransitivity"[
						"equalitySymmetry"["additionSubtractionCancellation"[(k + 1) * t, k + 1]],
						"equalityTransitivity"[
							"equalityCongruence"[Function[{Typed[x, NonNegativeIntegers]}, Subtract[x, k + 1]], h],
							"additionSubtractionCancellation"[(k + 1) * c, k + 1]
						]
					]]]
				],
				b
			]]],
			a
		]]
	],
	TypeTheoryTheorem[
		"powerZero",
		ForAll[{Typed[m, NonNegativeIntegers]}, m^0 == 1],
		Function[{Typed[m, NonNegativeIntegers]}, "equalityReflexivity"[1]]
	],
	TypeTheoryTheorem[
		"powerSuccessor",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, m^(n + 1) == m^n * m],
		Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, "equalityReflexivity"[m^n * m]]
	],
	TypeTheoryTheorem[
		"powerOne",
		ForAll[{Typed[m, NonNegativeIntegers]}, m^1 == m],
		Function[{Typed[m, NonNegativeIntegers]}, "multiplicationOneLeft"[m]]
	],
	TypeTheoryTheorem[
		"powerAddition",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, m^(a + b) == m^a * m^b],
		Function[{Typed[m, NonNegativeIntegers], Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, m^(a + k) == m^a * m^k], "equalitySymmetry"["multiplicationOneRight"[m^a]], Function[{Typed[k, NonNegativeIntegers], Typed[ih, m^(a + k) == m^a * m^k]}, "equalityTransitivity"["equalityCongruence"[Function[{Typed[x, NonNegativeIntegers]}, x * m], ih], "multiplicationAssociativity"[m^a, m^k, m]]], b]]
	],
	TypeTheoryTheorem[
		"predecessorLessEqual",
		ForAll[{Typed[n, NonNegativeIntegers]}, NaturalNumberPredecessor[n] <= n],
		Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, NaturalNumberPredecessor[k] <= k], "lessEqualReflexivity", Function[{Typed[k, NonNegativeIntegers], Typed[ih, NaturalNumberPredecessor[k] <= k]}, "lessEqualStep"["lessEqualReflexivity"]], n]]
	],
	TypeTheoryTheorem[
		"lessEqualZero",
		ForAll[{Typed[n, NonNegativeIntegers]}, 0 <= n],
		Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, 0 <= k], "lessEqualReflexivity", Function[{Typed[k, NonNegativeIntegers], Typed[ih, 0 <= k]}, "lessEqualStep"[ih]], n]]
	],
	TypeTheoryTheorem[
		"lessEqualSuccessor",
		ForAll[{TypedImplicit[n, NonNegativeIntegers], TypedImplicit[m, NonNegativeIntegers]}, Implies[n <= m, n + 1 <= m + 1]],
		Function[{TypedImplicit[n, NonNegativeIntegers], TypedImplicit[m, NonNegativeIntegers], Typed[h, n <= m]}, InductiveRecursor[LessEqual][Function[{Typed[j, NonNegativeIntegers], Typed[t, n <= j]}, n + 1 <= j + 1], "lessEqualReflexivity", Function[{Typed[j, NonNegativeIntegers], Typed[t, n <= j], Typed[ih, n + 1 <= j + 1]}, "lessEqualStep"[ih]], h]]
	],
	TypeTheoryTheorem[
		"lessEqualTransitivity",
		ForAll[{TypedImplicit[a, NonNegativeIntegers], TypedImplicit[b, NonNegativeIntegers], TypedImplicit[c, NonNegativeIntegers]}, Implies[a <= b, Implies[b <= c, a <= c]]],
		Function[{TypedImplicit[a, NonNegativeIntegers], TypedImplicit[b, NonNegativeIntegers], TypedImplicit[c, NonNegativeIntegers], Typed[h, a <= b], Typed[k, b <= c]}, InductiveRecursor[LessEqual][Function[{Typed[j, NonNegativeIntegers], Typed[t, b <= j]}, a <= j], h, Function[{Typed[j, NonNegativeIntegers], Typed[t, b <= j], Typed[ih, a <= j]}, "lessEqualStep"[ih]], k]]
	],
	TypeTheoryTheorem[
		"lessEqualAddition",
		ForAll[{Typed[n, NonNegativeIntegers], Typed[m, NonNegativeIntegers]}, n <= n + m],
		Function[{Typed[n, NonNegativeIntegers], Typed[m, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, n <= n + k], "lessEqualReflexivity", Function[{Typed[k, NonNegativeIntegers], Typed[ih, n <= n + k]}, "lessEqualStep"[ih]], m]]
	],
	TypeTheoryTheorem[
		"successorNotLessEqualZero",
		ForAll[{Typed[n, NonNegativeIntegers]}, Not[n + 1 <= 0]],
		Function[{Typed[n, NonNegativeIntegers], Typed[h, n + 1 <= 0]}, InductiveRecursor[LessEqual][Function[{Typed[j, NonNegativeIntegers], Typed[t, n + 1 <= j]}, Implies[j == 0, False]], "successorNotZero"[n], Function[{Typed[j, NonNegativeIntegers], Typed[t, n + 1 <= j], Typed[ih, Implies[j == 0, False]]}, "successorNotZero"[j]], h]["equalityReflexivity"[0]]]
	],
	TypeTheoryTheorem[
		"lessEqualPredecessor",
		ForAll[{TypedImplicit[n, NonNegativeIntegers], TypedImplicit[m, NonNegativeIntegers]}, Implies[n + 1 <= m + 1, n <= m]],
		Function[{TypedImplicit[n, NonNegativeIntegers], TypedImplicit[m, NonNegativeIntegers], Typed[h, n + 1 <= m + 1]}, InductiveRecursor[LessEqual][Function[{Typed[j, NonNegativeIntegers], Typed[t, n + 1 <= j]}, n <= NaturalNumberPredecessor[j]], "lessEqualReflexivity", Function[{Typed[j, NonNegativeIntegers], Typed[t, n + 1 <= j], Typed[ih, n <= NaturalNumberPredecessor[j]]}, "lessEqualTransitivity"[ih, "predecessorLessEqual"[j]]], h]]
	],
	TypeTheoryTheorem[
		"lessIrreflexivity",
		ForAll[{Typed[n, NonNegativeIntegers]}, Not[n < n]],
		Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, Not[k < k]], "successorNotLessEqualZero"[0], Function[{Typed[k, NonNegativeIntegers], Typed[ih, Not[k < k]], Typed[h, k + 1 < k + 1]}, ih["lessEqualPredecessor"[h]]], n]]
	],
	TypeTheoryTheorem[
		"lessEqualAntisymmetry",
		ForAll[{TypedImplicit[a, NonNegativeIntegers], TypedImplicit[b, NonNegativeIntegers]}, Implies[a <= b, Implies[b <= a, a == b]]],
		Function[{TypedImplicit[a, NonNegativeIntegers], TypedImplicit[b, NonNegativeIntegers], Typed[h, a <= b], Typed[k, b <= a]}, InductiveRecursor[LessEqual][Function[{Typed[j, NonNegativeIntegers], Typed[t, a <= j]}, Implies[j <= a, a == j]], Function[{Typed[r, a <= a]}, "equalityReflexivity"[a]], Function[{Typed[j, NonNegativeIntegers], Typed[t, a <= j], Typed[ih, Implies[j <= a, a == j]], Typed[r, "successor"[j] <= a]}, "falseElimination"["lessIrreflexivity"[j]["lessEqualTransitivity"[r, t]]]], h][k]]
	],
	(* sums and products of inequalities *)
	TypeTheoryTheorem[
		"additionMonotonicity",
		ForAll[
			{TypedImplicit[a, NonNegativeIntegers], TypedImplicit[b, NonNegativeIntegers], TypedImplicit[c, NonNegativeIntegers], TypedImplicit[d, NonNegativeIntegers]},
			Implies[a <= b, Implies[c <= d, a + c <= b + d]]
		],
		Function[
			{TypedImplicit[a, NonNegativeIntegers], TypedImplicit[b, NonNegativeIntegers], TypedImplicit[c, NonNegativeIntegers], TypedImplicit[d, NonNegativeIntegers], Typed[h, a <= b], Typed[k, c <= d]},
			InductiveRecursor[LessEqual][
				Function[{Typed[t, NonNegativeIntegers], Typed[e, c <= t]}, a + c <= b + t],
				InductiveRecursor[LessEqual][
					Function[{Typed[t, NonNegativeIntegers], Typed[e, a <= t]}, a + c <= t + c],
					"lessEqualReflexivity",
					Function[{Typed[t, NonNegativeIntegers], Typed[e, a <= t], Typed[r, a + c <= t + c]},
						Construct["equalitySubstitution",
							NonNegativeIntegers,
							Function[{Typed[s, NonNegativeIntegers]}, a + c <= s],
							t + c + 1,
							t + 1 + c,
							"equalitySymmetry"["additionSuccessorLeft"[t, c]],
							"lessEqualStep"[r]
						]
					],
					h
				],
				Function[{Typed[t, NonNegativeIntegers], Typed[e, c <= t], Typed[r, a + c <= b + t]}, "lessEqualStep"[r]],
				k
			]
		]
	],
	TypeTheoryTheorem[
		"multiplicationMonotonicity",
		ForAll[{TypedImplicit[a, NonNegativeIntegers], TypedImplicit[b, NonNegativeIntegers], Typed[k, NonNegativeIntegers]}, Implies[a <= b, a * k <= b * k]],
		Function[{TypedImplicit[a, NonNegativeIntegers], TypedImplicit[b, NonNegativeIntegers], Typed[k, NonNegativeIntegers], Typed[h, a <= b]}, InductiveRecursor[NonNegativeIntegers][
			Function[{Typed[t, NonNegativeIntegers]}, a * t <= b * t],
			"lessEqualReflexivity",
			Function[{Typed[t, NonNegativeIntegers], Typed[r, a * t <= b * t]}, "additionMonotonicity"[r, h]],
			k
		]]
	],
	(* either m <= n or n < m *)
	TypeTheoryTheorem[
		"lessEqualTotality",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, Or[m <= n, n < m]],
		Function[{Typed[m, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
			Function[{Typed[a, NonNegativeIntegers]}, ForAll[{Typed[n, NonNegativeIntegers]}, Or[a <= n, n < a]]],
			Function[{Typed[n, NonNegativeIntegers]}, "orIntroductionLeft"["lessEqualZero"[n]]],
			Function[{Typed[a, NonNegativeIntegers], Typed[ih, ForAll[{Typed[n, NonNegativeIntegers]}, Or[a <= n, n < a]]]}, Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
				Function[{Typed[c, NonNegativeIntegers]}, Or[a + 1 <= c, c < a + 1]],
				"orIntroductionRight"["lessEqualSuccessor"["lessEqualZero"[a]]],
				Function[{Typed[c, NonNegativeIntegers], Typed[r, Or[a + 1 <= c, c < a + 1]]}, InductiveRecursor[Or][
					Function[{Typed[s, Or[a <= c, c < a]]}, Or[a + 1 <= c + 1, c + 1 < a + 1]],
					Function[{Typed[g, a <= c]}, "orIntroductionLeft"["lessEqualSuccessor"[g]]],
					Function[{Typed[g, c < a]}, "orIntroductionRight"["lessEqualSuccessor"[g]]],
					ih[c]
				]],
				n
			]]],
			m
		]]
	],

	(* the Booleans, with false before true and the operations by cases on the first argument;
	   the constants are named by strings, and once they are declared, True, False, And, Or and Not
	   stand for them where a Boolean is expected *)
	TypeTheoryInductiveType[Booleans, TypeUniverse[1], {"false" -> Booleans, "true" -> Booleans}],
	TypeTheoryDefinition["not", Function[{Typed[a, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Booleans], "true", "false", a]]],
	TypeTheoryDefinition["and", Function[{Typed[a, Booleans], Typed[b, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Booleans], "false", b, a]]],
	TypeTheoryDefinition["or", Function[{Typed[a, Booleans], Typed[b, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Booleans], b, "true", a]]],

	(* decidable propositions: a proof of Not[p] or of p, in that order, which Decide
	   turns into the Boolean it computes; Decide[p] finds the decision of p among the instances *)
	TypeTheoryInductiveType[
		Decidable,
		ForAll[{Typed[p, TypeUniverse[0]]}, TypeUniverse[1]],
		{
			"decidableFalse" -> ForAll[{TypedImplicit[p, TypeUniverse[0]], Typed[h, Not[p]]}, Decidable[p]],
			"decidableTrue" -> ForAll[{TypedImplicit[p, TypeUniverse[0]], Typed[h, p]}, Decidable[p]]
		}
	],
	TypeTheoryDefinition[
		Decide,
		Function[{Typed[p, TypeUniverse[0]], Annotation[Typed[d, Decidable[p]], "InstanceImplicit"]},
			InductiveRecursor[Decidable][Function[{Typed[t, Decidable[p]]}, Booleans], Function[{Typed[h, Not[p]]}, "false"], Function[{Typed[h, p]}, "true"], d]
		]
	],

	(* Decide[p] == True proves p; True, False, the connectives, and the
	   equality and order of the natural numbers, are decidable, by instances *)
	TypeTheoryTheorem[
		"decideSoundness",
		ForAll[{TypedImplicit[p, TypeUniverse[0]], Annotation[Typed[d, Decidable[p]], "InstanceImplicit"]}, Implies[Decide[p] == "true", p]],
		Function[{TypedImplicit[p, TypeUniverse[0]], Annotation[Typed[d, Decidable[p]], "InstanceImplicit"]}, InductiveRecursor[Decidable][
			Function[{Typed[t, Decidable[p]]}, Implies[Construct[Decide, p, t] == "true", p]],
			Function[{Typed[h, Not[p]], Typed[e, "false" == "true"]}, "falseElimination"[
				InductiveRecursor[Equal][
					Function[{Typed[y, Booleans], Typed[k, "false" == y]}, InductiveRecursor[Booleans][Function[{Typed[b, Booleans]}, TypeUniverse[0]], True, False, y]],
					"trueIntroduction",
					e
				]
			]],
			Function[{Typed[h, p], Typed[e, "true" == "true"]}, h],
			d
		]]
	],
	TypeTheoryDefinition["trueDecidable", Typed["decidableTrue"["trueIntroduction"], Decidable[True]], "Instance" -> True],
	TypeTheoryDefinition["falseDecidable", Typed["decidableFalse"[Function[{Typed[h, False]}, h]], Decidable[False]], "Instance" -> True],
	TypeTheoryDefinition[
		"notDecidable",
		Function[{TypedImplicit[p, TypeUniverse[0]], Annotation[Typed[d, Decidable[p]], "InstanceImplicit"]}, InductiveRecursor[Decidable][
			Function[{Typed[t, Decidable[p]]}, Decidable[Not[p]]],
			Function[{Typed[h, Not[p]]}, "decidableTrue"[h]],
			Function[{Typed[h, p]}, "decidableFalse"[Function[{Typed[k, Not[p]]}, k[h]]]],
			d
		]],
		"Instance" -> True
	],
	TypeTheoryDefinition[
		"andDecidable",
		Function[
			{TypedImplicit[p, TypeUniverse[0]], TypedImplicit[q, TypeUniverse[0]], Annotation[Typed[d, Decidable[p]], "InstanceImplicit"], Annotation[Typed[e, Decidable[q]], "InstanceImplicit"]},
			InductiveRecursor[Decidable][
				Function[{Typed[t, Decidable[p]]}, Decidable[And[p, q]]],
				Function[{Typed[h, Not[p]]}, "decidableFalse"[Function[{Typed[k, And[p, q]]}, h["andEliminationLeft"[k]]]]],
				Function[{Typed[h, p]}, InductiveRecursor[Decidable][
					Function[{Typed[t, Decidable[q]]}, Decidable[And[p, q]]],
					Function[{Typed[g, Not[q]]}, "decidableFalse"[Function[{Typed[k, And[p, q]]}, g["andEliminationRight"[k]]]]],
					Function[{Typed[g, q]}, "decidableTrue"["andIntroduction"[h, g]]],
					e
				]],
				d
			]
		],
		"Instance" -> True
	],
	TypeTheoryDefinition[
		"orDecidable",
		Function[
			{TypedImplicit[p, TypeUniverse[0]], TypedImplicit[q, TypeUniverse[0]], Annotation[Typed[d, Decidable[p]], "InstanceImplicit"], Annotation[Typed[e, Decidable[q]], "InstanceImplicit"]},
			InductiveRecursor[Decidable][
				Function[{Typed[t, Decidable[p]]}, Decidable[Or[p, q]]],
				Function[{Typed[h, Not[p]]}, InductiveRecursor[Decidable][
					Function[{Typed[t, Decidable[q]]}, Decidable[Or[p, q]]],
					Function[{Typed[g, Not[q]]}, "decidableFalse"[Function[{Typed[k, Or[p, q]]}, InductiveRecursor[Or][Function[{Typed[s, Or[p, q]]}, False], h, g, k]]]],
					Function[{Typed[g, q]}, "decidableTrue"["orIntroductionRight"[g]]],
					e
				]],
				Function[{Typed[h, p]}, "decidableTrue"["orIntroductionLeft"[h]]],
				d
			]
		],
		"Instance" -> True
	],
	(* two Booleans that differ, by the predicate true of one and false of the other *)
	TypeTheoryTheorem[
		"falseNotTrue",
		Not["false" == "true"],
		Function[{Typed[e, "false" == "true"]}, InductiveRecursor[Equal][
			Function[{Typed[y, Booleans], Typed[k, "false" == y]}, InductiveRecursor[Booleans][Function[{Typed[b, Booleans]}, TypeUniverse[0]], True, False, y]],
			"trueIntroduction",
			e
		]]
	],
	TypeTheoryTheorem[
		"trueNotFalse",
		Not["true" == "false"],
		Function[{Typed[e, "true" == "false"]}, InductiveRecursor[Equal][
			Function[{Typed[y, Booleans], Typed[k, "true" == y]}, InductiveRecursor[Booleans][Function[{Typed[b, Booleans]}, TypeUniverse[0]], False, True, y]],
			"trueIntroduction",
			e
		]]
	],
	(* the equality of Booleans is decidable, by cases on both *)
	TypeTheoryDefinition[
		"booleanEqualityDecidable",
		Function[{Typed[a, Booleans], Typed[b, Booleans]}, InductiveRecursor[Booleans][
			Function[{Typed[x, Booleans]}, Decidable[x == b]],
			InductiveRecursor[Booleans][Function[{Typed[y, Booleans]}, Decidable["false" == y]], "decidableTrue"["equalityReflexivity"["false"]], "decidableFalse"["falseNotTrue"], b],
			InductiveRecursor[Booleans][Function[{Typed[y, Booleans]}, Decidable["true" == y]], "decidableFalse"["trueNotFalse"], "decidableTrue"["equalityReflexivity"["true"]], b],
			a
		]],
		"Instance" -> True
	],

	(* the Boolean comparisons of natural numbers, by recursion on both; the
	   kernel computes them on literals *)
	TypeTheoryDefinition[
		"equal",
		Typed[
			Function[{Typed[m, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
				Function[{Typed[a, NonNegativeIntegers]}, TypeSpecifier[{NonNegativeIntegers} -> Booleans]],
				Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
					Function[{Typed[c, NonNegativeIntegers]}, Booleans],
					"true",
					Function[{Typed[c, NonNegativeIntegers], Typed[r, Booleans]}, "false"],
					n
				]],
				Function[{Typed[a, NonNegativeIntegers], Typed[ih, TypeSpecifier[{NonNegativeIntegers} -> Booleans]]}, Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
					Function[{Typed[c, NonNegativeIntegers]}, Booleans],
					"false",
					Function[{Typed[c, NonNegativeIntegers], Typed[r, Booleans]}, ih[c]],
					n
				]]],
				m
			]],
			TypeSpecifier[{NonNegativeIntegers, NonNegativeIntegers} -> Booleans]
		]
	],
	TypeTheoryDefinition[
		"lessEqual",
		Typed[
			Function[{Typed[m, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
				Function[{Typed[a, NonNegativeIntegers]}, TypeSpecifier[{NonNegativeIntegers} -> Booleans]],
				Function[{Typed[n, NonNegativeIntegers]}, "true"],
				Function[{Typed[a, NonNegativeIntegers], Typed[ih, TypeSpecifier[{NonNegativeIntegers} -> Booleans]]}, Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
					Function[{Typed[c, NonNegativeIntegers]}, Booleans],
					"false",
					Function[{Typed[c, NonNegativeIntegers], Typed[r, Booleans]}, ih[c]],
					n
				]]],
				m
			]],
			TypeSpecifier[{NonNegativeIntegers, NonNegativeIntegers} -> Booleans]
		]
	],
	TypeTheoryNaturalNumbers[NonNegativeIntegers, "zero", "successor", <|"Equal" -> "equal", "LessEqual" -> "lessEqual"|>],

	(* what the comparisons give says what holds *)
	TypeTheoryTheorem[
		"equalTrue",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, Implies["equal"[m, n] == "true", m == n]],
		Function[{Typed[m, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
			Function[{Typed[a, NonNegativeIntegers]}, ForAll[{Typed[n, NonNegativeIntegers]}, Implies["equal"[a, n] == "true", a == n]]],
			Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
				Function[{Typed[c, NonNegativeIntegers]}, Implies["equal"[0, c] == "true", 0 == c]],
				Function[{Typed[e, "equal"[0, 0] == "true"]}, "equalityReflexivity"[0]],
				Function[{Typed[c, NonNegativeIntegers], Typed[r, Implies["equal"[0, c] == "true", 0 == c]], Typed[e, "equal"[0, c + 1] == "true"]}, "falseElimination"["falseNotTrue"[e]]],
				n
			]],
			Function[{Typed[a, NonNegativeIntegers], Typed[ih, ForAll[{Typed[n, NonNegativeIntegers]}, Implies["equal"[a, n] == "true", a == n]]]}, Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
				Function[{Typed[c, NonNegativeIntegers]}, Implies["equal"[a + 1, c] == "true", a + 1 == c]],
				Function[{Typed[e, "equal"[a + 1, 0] == "true"]}, "falseElimination"["falseNotTrue"[e]]],
				Function[{Typed[c, NonNegativeIntegers], Typed[r, Implies["equal"[a + 1, c] == "true", a + 1 == c]], Typed[e, "equal"[a + 1, c + 1] == "true"]},
					"equalityCongruence"["successor", ih[c, e]]
				],
				n
			]]],
			m
		]]
	],
	TypeTheoryTheorem[
		"equalFalse",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, Implies["equal"[m, n] == "false", Not[m == n]]],
		Function[{Typed[m, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
			Function[{Typed[a, NonNegativeIntegers]}, ForAll[{Typed[n, NonNegativeIntegers]}, Implies["equal"[a, n] == "false", Not[a == n]]]],
			Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
				Function[{Typed[c, NonNegativeIntegers]}, Implies["equal"[0, c] == "false", Not[0 == c]]],
				Function[{Typed[e, "equal"[0, 0] == "false"]}, "falseElimination"["trueNotFalse"[e]]],
				Function[{Typed[c, NonNegativeIntegers], Typed[r, Implies["equal"[0, c] == "false", Not[0 == c]]], Typed[e, "equal"[0, c + 1] == "false"], Typed[k, 0 == c + 1]},
					"successorNotZero"[c]["equalitySymmetry"[k]]
				],
				n
			]],
			Function[{Typed[a, NonNegativeIntegers], Typed[ih, ForAll[{Typed[n, NonNegativeIntegers]}, Implies["equal"[a, n] == "false", Not[a == n]]]]}, Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
				Function[{Typed[c, NonNegativeIntegers]}, Implies["equal"[a + 1, c] == "false", Not[a + 1 == c]]],
				Function[{Typed[e, "equal"[a + 1, 0] == "false"], Typed[k, a + 1 == 0]}, "successorNotZero"[a][k]],
				Function[{Typed[c, NonNegativeIntegers], Typed[r, Implies["equal"[a + 1, c] == "false", Not[a + 1 == c]]], Typed[e, "equal"[a + 1, c + 1] == "false"], Typed[k, a + 1 == c + 1]},
					ih[c, e]["successorInjectivity"[k]]
				],
				n
			]]],
			m
		]]
	],
	TypeTheoryTheorem[
		"lessEqualTrue",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, Implies["lessEqual"[m, n] == "true", m <= n]],
		Function[{Typed[m, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
			Function[{Typed[a, NonNegativeIntegers]}, ForAll[{Typed[n, NonNegativeIntegers]}, Implies["lessEqual"[a, n] == "true", a <= n]]],
			Function[{Typed[n, NonNegativeIntegers], Typed[e, "lessEqual"[0, n] == "true"]}, "lessEqualZero"[n]],
			Function[{Typed[a, NonNegativeIntegers], Typed[ih, ForAll[{Typed[n, NonNegativeIntegers]}, Implies["lessEqual"[a, n] == "true", a <= n]]]}, Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
				Function[{Typed[c, NonNegativeIntegers]}, Implies["lessEqual"[a + 1, c] == "true", a + 1 <= c]],
				Function[{Typed[e, "lessEqual"[a + 1, 0] == "true"]}, "falseElimination"["falseNotTrue"[e]]],
				Function[{Typed[c, NonNegativeIntegers], Typed[r, Implies["lessEqual"[a + 1, c] == "true", a + 1 <= c]], Typed[e, "lessEqual"[a + 1, c + 1] == "true"]},
					"lessEqualSuccessor"[ih[c, e]]
				],
				n
			]]],
			m
		]]
	],
	TypeTheoryTheorem[
		"lessEqualFalse",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, Implies["lessEqual"[m, n] == "false", Not[m <= n]]],
		Function[{Typed[m, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
			Function[{Typed[a, NonNegativeIntegers]}, ForAll[{Typed[n, NonNegativeIntegers]}, Implies["lessEqual"[a, n] == "false", Not[a <= n]]]],
			Function[{Typed[n, NonNegativeIntegers], Typed[e, "lessEqual"[0, n] == "false"]}, "falseElimination"["trueNotFalse"[e]]],
			Function[{Typed[a, NonNegativeIntegers], Typed[ih, ForAll[{Typed[n, NonNegativeIntegers]}, Implies["lessEqual"[a, n] == "false", Not[a <= n]]]]}, Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
				Function[{Typed[c, NonNegativeIntegers]}, Implies["lessEqual"[a + 1, c] == "false", Not[a + 1 <= c]]],
				Function[{Typed[e, "lessEqual"[a + 1, 0] == "false"]}, "successorNotLessEqualZero"[a]],
				Function[{Typed[c, NonNegativeIntegers], Typed[r, Implies["lessEqual"[a + 1, c] == "false", Not[a + 1 <= c]]], Typed[e, "lessEqual"[a + 1, c + 1] == "false"], Typed[k, a + 1 <= c + 1]},
					ih[c, e]["lessEqualPredecessor"[k]]
				],
				n
			]]],
			m
		]]
	],

	(* a decision of m == n or m <= n is what the comparison gives, with the proof it gives,
	   an instance of each: on literals it is one step of the kernel, however
	   large they are *)
	TypeTheoryDefinition[
		"naturalNumberEqualityDecidable",
		Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, InductiveRecursor[Booleans][
			Function[{Typed[b, Booleans]}, Implies["equal"[m, n] == b, Decidable[m == n]]],
			Function[{Typed[e, "equal"[m, n] == "false"]}, "decidableFalse"["equalFalse"[m, n, e]]],
			Function[{Typed[e, "equal"[m, n] == "true"]}, "decidableTrue"["equalTrue"[m, n, e]]],
			"equal"[m, n]
		]["equalityReflexivity"["equal"[m, n]]]],
		"Instance" -> True
	],
	TypeTheoryDefinition[
		"lessEqualDecidable",
		Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, InductiveRecursor[Booleans][
			Function[{Typed[b, Booleans]}, Implies["lessEqual"[m, n] == b, Decidable[m <= n]]],
			Function[{Typed[e, "lessEqual"[m, n] == "false"]}, "decidableFalse"["lessEqualFalse"[m, n, e]]],
			Function[{Typed[e, "lessEqual"[m, n] == "true"]}, "decidableTrue"["lessEqualTrue"[m, n, e]]],
			"lessEqual"[m, n]
		]["equalityReflexivity"["lessEqual"[m, n]]]],
		"Instance" -> True
	],

	(* pairs, sums, optional values and lists *)
	TypeTheoryInductiveType[
		CartesianProductType,
		ForAll[{Typed[\[Alpha], TypeUniverse[u + 1]], Typed[\[Beta], TypeUniverse[v + 1]]}, TypeUniverse[Max[u, v] + 1]],
		{
			"pair" -> ForAll[
				{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], TypedImplicit[\[Beta], TypeUniverse[v + 1]], Typed[first, \[Alpha]], Typed[second, \[Beta]]},
				CartesianProductType[\[Alpha], \[Beta]]
			]
		}
	],
	TypeTheoryInductiveType[
		DisjointUnionType,
		ForAll[{Typed[\[Alpha], TypeUniverse[u + 1]], Typed[\[Beta], TypeUniverse[v + 1]]}, TypeUniverse[Max[u, v] + 1]],
		{
			"left" -> ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], TypedImplicit[\[Beta], TypeUniverse[v + 1]], Typed[x, \[Alpha]]}, DisjointUnionType[\[Alpha], \[Beta]]],
			"right" -> ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], TypedImplicit[\[Beta], TypeUniverse[v + 1]], Typed[y, \[Beta]]}, DisjointUnionType[\[Alpha], \[Beta]]]
		}
	],
	TypeTheoryInductiveType[
		Option,
		ForAll[{Typed[\[Alpha], TypeUniverse[u + 1]]}, TypeUniverse[u + 1]],
		{
			"none" -> ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]]}, Option[\[Alpha]]],
			"some" -> ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[x, \[Alpha]]}, Option[\[Alpha]]]
		}
	],
	TypeTheoryInductiveType[
		List,
		ForAll[{Typed[\[Alpha], TypeUniverse[u + 1]]}, TypeUniverse[u + 1]],
		{
			"{}" -> ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]]}, {\[Alpha]}],
			"Prepend" -> ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[x, \[Alpha]], Typed[l, {\[Alpha]}]}, {\[Alpha]}]
		}
	],

	(* the operations on lists, by recursion on the first list: Join, Length, Map, Append of one element at
	   the end, and Reverse, which appends each element to the reversed rest *)
	TypeTheoryDefinition[
		Join,
		Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[l, {\[Alpha]}], Typed[m, {\[Alpha]}]},
			InductiveRecursor[List][
				Function[{Typed[t, {\[Alpha]}]}, {\[Alpha]}],
				m,
				Function[{Typed[x, \[Alpha]], Typed[rest, {\[Alpha]}], Typed[r, {\[Alpha]}]}, Prepend[x][r]],
				l
			]
		]
	],
	TypeTheoryDefinition[
		Length,
		Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[l, {\[Alpha]}]},
			InductiveRecursor[List][
				Function[{Typed[t, {\[Alpha]}]}, NonNegativeIntegers],
				0,
				Function[{Typed[x, \[Alpha]], Typed[rest, {\[Alpha]}], Typed[r, NonNegativeIntegers]}, r + 1],
				l
			]
		]
	],
	TypeTheoryDefinition[
		Map,
		Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], TypedImplicit[\[Beta], TypeUniverse[v + 1]], Typed[f, TypeSpecifier[{\[Alpha]} -> \[Beta]]], Typed[l, {\[Alpha]}]},
			InductiveRecursor[List][
				Function[{Typed[t, {\[Alpha]}]}, {\[Beta]}],
				{},
				Function[{Typed[x, \[Alpha]], Typed[rest, {\[Alpha]}], Typed[r, {\[Beta]}]}, Prepend[f[x]][r]],
				l
			]
		]
	],
	TypeTheoryDefinition[
		Append,
		Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[l, {\[Alpha]}], Typed[x, \[Alpha]]}, Join[l, Prepend[x][{}]]]
	],
	TypeTheoryDefinition[
		Reverse,
		Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[l, {\[Alpha]}]},
			InductiveRecursor[List][
				Function[{Typed[t, {\[Alpha]}]}, {\[Alpha]}],
				{},
				Function[{Typed[x, \[Alpha]], Typed[rest, {\[Alpha]}], Typed[r, {\[Alpha]}]}, Append[r, x]],
				l
			]
		]
	],

	(* the laws of the operations on lists, each by recursion on a list *)
	TypeTheoryTheorem[
		"joinEmptyRight",
		ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[l, {\[Alpha]}]}, Join[l, {}] == l],
		Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[l, {\[Alpha]}]}, InductiveRecursor[List][
			Function[{Typed[t, {\[Alpha]}]}, Join[t, {}] == t],
			"equalityReflexivity"[{}],
			Function[{Typed[x, \[Alpha]], Typed[rest, {\[Alpha]}], Typed[ih, Join[rest, {}] == rest]},
				"equalityCongruence"[Function[{Typed[r, {\[Alpha]}]}, Prepend[x][r]], ih]
			],
			l
		]]
	],
	TypeTheoryTheorem[
		"joinAssociativity",
		ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[a, {\[Alpha]}], Typed[b, {\[Alpha]}], Typed[c, {\[Alpha]}]}, Join[Join[a, b], c] == Join[a, Join[b, c]]],
		Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[a, {\[Alpha]}], Typed[b, {\[Alpha]}], Typed[c, {\[Alpha]}]}, InductiveRecursor[List][
			Function[{Typed[t, {\[Alpha]}]}, Join[Join[t, b], c] == Join[t, Join[b, c]]],
			"equalityReflexivity"[Join[b, c]],
			Function[{Typed[x, \[Alpha]], Typed[rest, {\[Alpha]}], Typed[ih, Join[Join[rest, b], c] == Join[rest, Join[b, c]]]},
				"equalityCongruence"[Function[{Typed[r, {\[Alpha]}]}, Prepend[x][r]], ih]
			],
			a
		]]
	],
	TypeTheoryTheorem[
		"lengthJoin",
		ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[a, {\[Alpha]}], Typed[b, {\[Alpha]}]}, Length[Join[a, b]] == Length[a] + Length[b]],
		Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[a, {\[Alpha]}], Typed[b, {\[Alpha]}]}, InductiveRecursor[List][
			Function[{Typed[t, {\[Alpha]}]}, Length[Join[t, b]] == Length[t] + Length[b]],
			"equalitySymmetry"["additionZeroLeft"[Length[b]]],
			Function[{Typed[x, \[Alpha]], Typed[rest, {\[Alpha]}], Typed[ih, Length[Join[rest, b]] == Length[rest] + Length[b]]},
				"equalityTransitivity"["equalityCongruence"["successor", ih], "equalitySymmetry"["additionSuccessorLeft"[Length[rest], Length[b]]]]
			],
			a
		]]
	],
	TypeTheoryTheorem[
		"lengthMap",
		ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], TypedImplicit[\[Beta], TypeUniverse[v + 1]], Typed[f, TypeSpecifier[{\[Alpha]} -> \[Beta]]], Typed[l, {\[Alpha]}]}, Length[Map[f, l]] == Length[l]],
		Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], TypedImplicit[\[Beta], TypeUniverse[v + 1]], Typed[f, TypeSpecifier[{\[Alpha]} -> \[Beta]]], Typed[l, {\[Alpha]}]}, InductiveRecursor[List][
			Function[{Typed[t, {\[Alpha]}]}, Length[Map[f, t]] == Length[t]],
			"equalityReflexivity"[0],
			Function[{Typed[x, \[Alpha]], Typed[rest, {\[Alpha]}], Typed[ih, Length[Map[f, rest]] == Length[rest]]}, "equalityCongruence"["successor", ih]],
			l
		]]
	],
	TypeTheoryTheorem[
		"mapJoin",
		ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], TypedImplicit[\[Beta], TypeUniverse[v + 1]], Typed[f, TypeSpecifier[{\[Alpha]} -> \[Beta]]], Typed[a, {\[Alpha]}], Typed[b, {\[Alpha]}]}, Map[f, Join[a, b]] == Join[Map[f, a], Map[f, b]]],
		Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], TypedImplicit[\[Beta], TypeUniverse[v + 1]], Typed[f, TypeSpecifier[{\[Alpha]} -> \[Beta]]], Typed[a, {\[Alpha]}], Typed[b, {\[Alpha]}]}, InductiveRecursor[List][
			Function[{Typed[t, {\[Alpha]}]}, Map[f, Join[t, b]] == Join[Map[f, t], Map[f, b]]],
			"equalityReflexivity"[Map[f, b]],
			Function[{Typed[x, \[Alpha]], Typed[rest, {\[Alpha]}], Typed[ih, Map[f, Join[rest, b]] == Join[Map[f, rest], Map[f, b]]]},
				"equalityCongruence"[Function[{Typed[r, {\[Beta]}]}, Prepend[f[x]][r]], ih]
			],
			a
		]]
	],
	TypeTheoryTheorem[
		"mapComposition",
		ForAll[
			{
				TypedImplicit[\[Alpha], TypeUniverse[u + 1]], TypedImplicit[\[Beta], TypeUniverse[v + 1]], TypedImplicit[\[Gamma], TypeUniverse[w + 1]],
				Typed[f, TypeSpecifier[{\[Beta]} -> \[Gamma]]], Typed[g, TypeSpecifier[{\[Alpha]} -> \[Beta]]], Typed[l, {\[Alpha]}]
			},
			Map[f, Map[g, l]] == Map[Composition[f, g], l]
		],
		Function[
			{
				TypedImplicit[\[Alpha], TypeUniverse[u + 1]], TypedImplicit[\[Beta], TypeUniverse[v + 1]], TypedImplicit[\[Gamma], TypeUniverse[w + 1]],
				Typed[f, TypeSpecifier[{\[Beta]} -> \[Gamma]]], Typed[g, TypeSpecifier[{\[Alpha]} -> \[Beta]]], Typed[l, {\[Alpha]}]
			},
			InductiveRecursor[List][
				Function[{Typed[t, {\[Alpha]}]}, Map[f, Map[g, t]] == Map[Composition[f, g], t]],
				"equalityReflexivity"[{}],
				Function[{Typed[x, \[Alpha]], Typed[rest, {\[Alpha]}], Typed[ih, Map[f, Map[g, rest]] == Map[Composition[f, g], rest]]},
					"equalityCongruence"[Function[{Typed[r, {\[Gamma]}]}, Prepend[f[g[x]]][r]], ih]
				],
				l
			]
		]
	],
	TypeTheoryTheorem[
		"reverseJoin",
		ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[a, {\[Alpha]}], Typed[b, {\[Alpha]}]}, Reverse[Join[a, b]] == Join[Reverse[b], Reverse[a]]],
		Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[a, {\[Alpha]}], Typed[b, {\[Alpha]}]}, InductiveRecursor[List][
			Function[{Typed[t, {\[Alpha]}]}, Reverse[Join[t, b]] == Join[Reverse[b], Reverse[t]]],
			"equalitySymmetry"["joinEmptyRight"[Reverse[b]]],
			Function[{Typed[x, \[Alpha]], Typed[rest, {\[Alpha]}], Typed[ih, Reverse[Join[rest, b]] == Join[Reverse[b], Reverse[rest]]]},
				"equalityTransitivity"[
					"equalityCongruence"[Function[{Typed[r, {\[Alpha]}]}, Join[r, Prepend[x][{}]]], ih],
					"joinAssociativity"[Reverse[b], Reverse[rest], Prepend[x][{}]]
				]
			],
			a
		]]
	],
	TypeTheoryTheorem[
		"reverseReverse",
		ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[l, {\[Alpha]}]}, Reverse[Reverse[l]] == l],
		Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[l, {\[Alpha]}]}, InductiveRecursor[List][
			Function[{Typed[t, {\[Alpha]}]}, Reverse[Reverse[t]] == t],
			"equalityReflexivity"[{}],
			Function[{Typed[x, \[Alpha]], Typed[rest, {\[Alpha]}], Typed[ih, Reverse[Reverse[rest]] == rest]},
				"equalityTransitivity"[
					"reverseJoin"[Reverse[rest], Prepend[x][{}]],
					"equalityCongruence"[Function[{Typed[r, {\[Alpha]}]}, Join[Prepend[x][{}], r]], ih]
				]
			],
			l
		]]
	],
	TypeTheoryTheorem[
		"lengthReverse",
		ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[l, {\[Alpha]}]}, Length[Reverse[l]] == Length[l]],
		Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[l, {\[Alpha]}]}, InductiveRecursor[List][
			Function[{Typed[t, {\[Alpha]}]}, Length[Reverse[t]] == Length[t]],
			"equalityReflexivity"[0],
			Function[{Typed[x, \[Alpha]], Typed[rest, {\[Alpha]}], Typed[ih, Length[Reverse[rest]] == Length[rest]]},
				"equalityTransitivity"["lengthJoin"[Reverse[rest], Prepend[x][{}]], "equalityCongruence"["successor", ih]]
			],
			l
		]]
	]
}

(* The classical part of the prelude: three axioms, propositional extensionality, the soundness of
   quotients and choice, with function extensionality proved from the soundness of quotients and the
   excluded middle from all three, the second by Diaconescu's argument.
   TypeTheoryEnvironment["Constructive"] is the prelude without it. *)
$classicalDeclarations = {
	TypeTheoryInductiveType[
		Nonempty,
		ForAll[{Typed[\[Alpha], TypeUniverse[u]]}, TypeUniverse[0]],
		{"nonempty" -> ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u]], Typed[element, \[Alpha]]}, Nonempty[\[Alpha]]]}
	],
	TypeTheoryInductiveType[
		Subtype,
		ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u]], Typed[P, TypeSpecifier[{\[Alpha]} -> TypeUniverse[0]]]}, TypeUniverse[Max[1, u]]],
		{"subtype" -> ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u]], TypedImplicit[P, TypeSpecifier[{\[Alpha]} -> TypeUniverse[0]]], Typed[element, \[Alpha]], Typed[proof, P[element]]}, Subtype[P]]}
	],
	TypeTheoryAxiom[
		"propositionalExtensionality",
		ForAll[{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]]}, Implies[Equivalent[a, b], a == b]]
	],
	TypeTheoryAxiom[
		"quotientSoundness",
		ForAll[
			{
				TypedImplicit[\[Alpha], TypeUniverse[u]],
				TypedImplicit[r, TypeSpecifier[{\[Alpha], \[Alpha]} -> TypeUniverse[0]]],
				TypedImplicit[a, \[Alpha]],
				TypedImplicit[b, \[Alpha]]
			},
			Implies[r[a, b], QuotientIntroduction[r, a] == QuotientIntroduction[r, b]]
		]
	],
	(* two functions equal at every point are equal: they have the same class in the quotient of functions by
	   that relation, and applying a class to a point gives the value there *)
	TypeTheoryTheorem[
		"functionExtensionality",
		ForAll[
			{
				TypedImplicit[\[Alpha], TypeUniverse[u]],
				TypedImplicit[\[Beta], TypeSpecifier[{\[Alpha]} -> TypeUniverse[v]]],
				TypedImplicit[f, ForAll[{Typed[x, \[Alpha]]}, \[Beta][x]]],
				TypedImplicit[g, ForAll[{Typed[x, \[Alpha]]}, \[Beta][x]]]
			},
			Implies[ForAll[{Typed[x, \[Alpha]]}, f[x] == g[x]], f == g]
		],
		Function[
			{
				TypedImplicit[\[Alpha], TypeUniverse[u]],
				TypedImplicit[\[Beta], TypeSpecifier[{\[Alpha]} -> TypeUniverse[v]]],
				TypedImplicit[f, ForAll[{Typed[x, \[Alpha]]}, \[Beta][x]]],
				TypedImplicit[g, ForAll[{Typed[x, \[Alpha]]}, \[Beta][x]]],
				Typed[h, ForAll[{Typed[x, \[Alpha]]}, f[x] == g[x]]]
			},
			"equalityCongruence"[
				Function[
					{
						Typed[q, QuotientType[Function[{Typed[k, ForAll[{Typed[x, \[Alpha]]}, \[Beta][x]]], Typed[l, ForAll[{Typed[x, \[Alpha]]}, \[Beta][x]]]}, ForAll[{Typed[x, \[Alpha]]}, k[x] == l[x]]]]],
						Typed[x, \[Alpha]]
					},
					QuotientLift[
						Function[{Typed[k, ForAll[{Typed[y, \[Alpha]]}, \[Beta][y]]]}, k[x]],
						Function[{Typed[k, ForAll[{Typed[y, \[Alpha]]}, \[Beta][y]]], Typed[l, ForAll[{Typed[y, \[Alpha]]}, \[Beta][y]]], Typed[e, ForAll[{Typed[y, \[Alpha]]}, k[y] == l[y]]]}, e[x]],
						q
					]
				],
				"quotientSoundness"[h]
			]
		]
	],
	TypeTheoryAxiom["choice", ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u]], Typed[h, Nonempty[\[Alpha]]]}, \[Alpha]]],
	TypeTheoryDefinition[
		ChosenWitness,
		Function[
			{TypedImplicit[\[Alpha], TypeUniverse[u]], TypedImplicit[P, TypeSpecifier[{\[Alpha]} -> TypeUniverse[0]]], Typed[h, Exists[P]]},
			"choice"[InductiveRecursor[Exists][
				Function[{Typed[t, Exists[P]]}, Nonempty[Subtype[P]]],
				Function[{Typed[w, \[Alpha]], Typed[k, P[w]]}, "nonempty"["subtype"[w, k]]],
				h
			]][[1]]
		]
	],
	TypeTheoryTheorem[
		"chosenWitnessProperty",
		ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u]], TypedImplicit[P, TypeSpecifier[{\[Alpha]} -> TypeUniverse[0]]], Typed[h, Exists[P]]}, P[ChosenWitness[h]]],
		Function[
			{TypedImplicit[\[Alpha], TypeUniverse[u]], TypedImplicit[P, TypeSpecifier[{\[Alpha]} -> TypeUniverse[0]]], Typed[h, Exists[P]]},
			"choice"[InductiveRecursor[Exists][
				Function[{Typed[t, Exists[P]]}, Nonempty[Subtype[P]]],
				Function[{Typed[w, \[Alpha]], Typed[k, P[w]]}, "nonempty"["subtype"[w, k]]],
				h
			]][[2]]
		]
	],
	TypeTheoryTheorem[
		"excludedMiddle",
		ForAll[{Typed[p, TypeUniverse[0]]}, Or[p, Not[p]]],
		Function[{Typed[p, TypeUniverse[0]]},
			With[
				{
					existsTrue = Typed["existsIntroduction"[True, "orIntroductionLeft"["equalityReflexivity"[True]]], Exists[Function[{Typed[x, TypeUniverse[0]]}, Or[x == True, p]]]],
					existsFalse = Typed["existsIntroduction"[False, "orIntroductionLeft"["equalityReflexivity"[False]]], Exists[Function[{Typed[x, TypeUniverse[0]]}, Or[x == False, p]]]]
				},
				With[
					{
						chosenTrue = ChosenWitness[existsTrue],
						chosenFalse = ChosenWitness[existsFalse],
						trueProperty = "chosenWitnessProperty"[existsTrue],
						falseProperty = "chosenWitnessProperty"[existsFalse]
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
											"orIntroductionLeft"[Function[{Typed[e, chosenTrue == chosenFalse]},
												Construct["equalitySubstitution", TypeUniverse[0], Function[{Typed[x, TypeUniverse[0]]}, x], True, False,
													"equalityTransitivity"["equalitySymmetry"[isTrue], "equalityTransitivity"[e, isFalse]],
													"trueIntroduction"
												]
											]]
										],
										Function[{Typed[holds, p]}, "orIntroductionRight"[holds]],
										falseProperty
									]
								],
								Function[{Typed[holds, p]}, "orIntroductionRight"[holds]],
								trueProperty
							],
							(* if p holds, the two predicates are equal, and so are the choices *)
							sameIfP = Function[{Typed[holds, p]},
								Construct["equalitySubstitution",
									TypeSpecifier[{TypeUniverse[0]} -> TypeUniverse[0]],
									Function[{Typed[W, TypeSpecifier[{TypeUniverse[0]} -> TypeUniverse[0]]]}, ForAll[{Typed[e, Exists[W]]}, chosenTrue == ChosenWitness[e]]],
									Function[{Typed[x, TypeUniverse[0]]}, Or[x == True, p]],
									Function[{Typed[x, TypeUniverse[0]]}, Or[x == False, p]],
									"functionExtensionality"[Function[{Typed[x, TypeUniverse[0]]},
										"propositionalExtensionality"["equivalentIntroduction"[
											Function[{Typed[k, Or[x == True, p]]}, "orIntroductionRight"[holds]],
											Function[{Typed[k, Or[x == False, p]]}, "orIntroductionRight"[holds]]
										]]
									]],
									Function[{Typed[e, Exists[Function[{Typed[x, TypeUniverse[0]]}, Or[x == True, p]]]]}, "equalityReflexivity"[chosenTrue]]
								][existsFalse]
							]
						},
						InductiveRecursor[Or][
							Function[{Typed[t, Or[Not[chosenTrue == chosenFalse], p]]}, Or[p, Not[p]]],
							Function[{Typed[different, Not[chosenTrue == chosenFalse]]}, "orIntroductionRight"[Function[{Typed[holds, p]}, different[sameIfP[holds]]]]],
							Function[{Typed[holds, p]}, "orIntroductionLeft"[holds]],
							differentOrP
						]
					]
				]
			]
		]
	],
	TypeTheoryTheorem[
		"doubleNegationElimination",
		ForAll[{Typed[p, TypeUniverse[0]]}, Implies[Not[Not[p]], p]],
		Function[{Typed[p, TypeUniverse[0]], Typed[h, Not[Not[p]]]},
			InductiveRecursor[Or][
				Function[{Typed[t, Or[p, Not[p]]]}, p],
				Function[{Typed[k, p]}, k],
				Function[{Typed[k, Not[p]]}, "falseElimination"[h[k]]],
				"excludedMiddle"[p]
			]
		]
	]
}

preludeEnvironment[] := $preludeEnvironment

constructiveEnvironment[] := $constructiveEnvironment
