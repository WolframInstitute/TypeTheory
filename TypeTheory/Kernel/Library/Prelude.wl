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
	Booleans                   with the constants "false" and "true", "not", "and" and "or", named by strings;
	                           True, False, Not, And and Or stand for these where a Boolean is expected
	"equal", "lessEqual"       the Boolean comparisons of natural numbers, which the kernel computes on literals
	Decidable[p]               decisions, with Decide, DecideSoundness, and the decisions of ==, <= and the
	                           connectives
	CartesianProduct, DisjointUnion, Option, Lists
	                           pairs, sums, optional values and lists, with Join, Length, Map, Append and Reverse

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
PackageExported[Naturals]
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
PackageExported[Decidable]
PackageExported[DecidableFalse]
PackageExported[DecidableTrue]
PackageExported[Decide]
PackageExported[CartesianProduct]
PackageExported[Pair]
PackageExported[DisjointUnion]
PackageExported[LeftInjection]
PackageExported[RightInjection]
PackageExported[Option]
PackageExported[OptionNone]
PackageExported[OptionSome]
PackageExported[Lists]
PackageExported[EmptyList]
PackageExported[ListPrepend]
PackageExported[DecideSoundness]
PackageExported[NotDecidable]
PackageExported[AndDecidable]
PackageExported[OrDecidable]
PackageExported[NaturalNumberEqualityDecidable]
PackageExported[LessEqualDecidable]
PackageExported[JoinEmptyRight]
PackageExported[JoinAssociativity]
PackageExported[LengthJoin]
PackageExported[LengthMap]
PackageExported[MapJoin]
PackageExported[MapComposition]
PackageExported[ReverseJoin]
PackageExported[ReverseReverse]
PackageExported[LengthReverse]


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
Naturals::usage = "Naturals is NonNegativeIntegers, the natural numbers of the prelude, by a shorter name: in a term, a symbol whose \
value is a declared constant stands for that constant."
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
Decidable::usage = "Decidable[p] is the type of decisions of the proposition p: DecidableFalse with a proof of Not[p], or DecidableTrue with a proof of p."
DecidableFalse::usage = "DecidableFalse[h] decides p false, given a proof h of Not[p]."
DecidableTrue::usage = "DecidableTrue[h] decides p true, given a proof h of p."
Decide::usage = "Decide[d] is the Boolean that the decision d of Decidable[p] computes: False for DecidableFalse, True for DecidableTrue."
CartesianProduct::usage = "CartesianProduct[a, b] is the type of the pairs of an element of the type a and one of the type b; p[[1]] and p[[2]] project a pair p."
Pair::usage = "Pair[x, y] is the element of CartesianProduct[a, b] made of x of type a and y of type b."
DisjointUnion::usage = "DisjointUnion[a, b] is the type of the elements of the type a or of the type b, each tagged with its side."
LeftInjection::usage = "LeftInjection[x] is the element x of the type a in DisjointUnion[a, b]."
RightInjection::usage = "RightInjection[y] is the element y of the type b in DisjointUnion[a, b]."
Option::usage = "Option[a] is the type of optional elements of the type a: OptionNone, or OptionSome[x] with x of type a."
OptionNone::usage = "OptionNone is the element of Option[a] with no element of a."
OptionSome::usage = "OptionSome[x] is the element of Option[a] holding x of type a."
Lists::usage = "Lists[a] is the type of finite lists of elements of the type a, built from EmptyList by ListPrepend; Join, Length, Map, Append and Reverse operate on them."
EmptyList::usage = "EmptyList is the list with no elements, of type Lists[a]."
ListPrepend::usage = "ListPrepend[x, l] is the list l with x in front."
DecideSoundness::usage = "DecideSoundness[d, h] proves p from a decision d of Decidable[p] and a proof h of Decide[d] == True."
NotDecidable::usage = "NotDecidable[d] decides Not[p] from a decision d of Decidable[p]."
AndDecidable::usage = "AndDecidable[d, e] decides And[p, q] from decisions d of Decidable[p] and e of Decidable[q]."
OrDecidable::usage = "OrDecidable[d, e] decides Or[p, q] from decisions d of Decidable[p] and e of Decidable[q]."
NaturalNumberEqualityDecidable::usage = "NaturalNumberEqualityDecidable[m, n] decides m == n for natural numbers m and n."
LessEqualDecidable::usage = "LessEqualDecidable[m, n] decides m <= n for natural numbers m and n."
JoinEmptyRight::usage = "JoinEmptyRight[l] proves Join[l, EmptyList] == l."
JoinAssociativity::usage = "JoinAssociativity[a, b, c] proves Join[Join[a, b], c] == Join[a, Join[b, c]]."
LengthJoin::usage = "LengthJoin[a, b] proves Length[Join[a, b]] == Length[a] + Length[b]."
LengthMap::usage = "LengthMap[f, l] proves Length[Map[f, l]] == Length[l]."
MapJoin::usage = "MapJoin[f, a, b] proves Map[f, Join[a, b]] == Join[Map[f, a], Map[f, b]]."
MapComposition::usage = "MapComposition[f, g, l] proves Map[f, Map[g, l]] == Map[Composition[f, g], l]."
ReverseJoin::usage = "ReverseJoin[a, b] proves Reverse[Join[a, b]] == Join[Reverse[b], Reverse[a]]."
ReverseReverse::usage = "ReverseReverse[l] proves Reverse[Reverse[l]] == l."
LengthReverse::usage = "LengthReverse[l] proves Length[Reverse[l]] == Length[l]."

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
	(* addition by recursion on the second argument, as Lean's *)
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
	(* the kernel computes these on literals with integers, as Lean's kernel computes its own *)
	TypeTheoryNaturalNumbers[NonNegativeIntegers, NaturalNumberZero, NaturalNumberSuccessor, <|"Subtraction" -> Subtract, "Multiplication" -> Times, "Power" -> Power|>],
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
	   Bool; the constants are named by strings, and once they are declared, True, False, And, Or and Not
	   stand for them where a Boolean is expected *)
	TypeTheoryInductiveType[Booleans, TypeUniverse[1], {"false" -> Booleans, "true" -> Booleans}],
	TypeTheoryDefinition["not", Function[{Typed[a, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Booleans], "true", "false", a]]],
	TypeTheoryDefinition["and", Function[{Typed[a, Booleans], Typed[b, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Booleans], "false", b, a]]],
	TypeTheoryDefinition["or", Function[{Typed[a, Booleans], Typed[b, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Booleans], b, "true", a]]],

	(* decidable propositions, as Lean's Decidable: a proof of Not[p] or of p, in that order, which Decide
	   turns into the Boolean it computes *)
	TypeTheoryInductiveType[
		Decidable,
		ForAll[{Typed[p, TypeUniverse[0]]}, TypeUniverse[1]],
		{
			DecidableFalse -> ForAll[{TypedImplicit[p, TypeUniverse[0]], Typed[h, Not[p]]}, Decidable[p]],
			DecidableTrue -> ForAll[{TypedImplicit[p, TypeUniverse[0]], Typed[h, p]}, Decidable[p]]
		}
	],
	TypeTheoryDefinition[
		Decide,
		Function[{TypedImplicit[p, TypeUniverse[0]], Typed[d, Decidable[p]]},
			InductiveRecursor[Decidable][Function[{Typed[t, Decidable[p]]}, Booleans], Function[{Typed[h, Not[p]]}, "false"], Function[{Typed[h, p]}, "true"], d]
		]
	],

	(* Decide[d] == True proves p; the connectives, and the equality and order of the natural numbers, are
	   decidable *)
	TypeTheoryTheorem[
		DecideSoundness,
		ForAll[{TypedImplicit[p, TypeUniverse[0]], Typed[d, Decidable[p]]}, Implies[Decide[d] == "true", p]],
		Function[{TypedImplicit[p, TypeUniverse[0]], Typed[d, Decidable[p]]}, InductiveRecursor[Decidable][
			Function[{Typed[t, Decidable[p]]}, Implies[Decide[t] == "true", p]],
			Function[{Typed[h, Not[p]], Typed[e, "false" == "true"]}, FalseElimination[
				InductiveRecursor[Equal][
					Function[{Typed[y, Booleans], Typed[k, "false" == y]}, InductiveRecursor[Booleans][Function[{Typed[b, Booleans]}, TypeUniverse[0]], True, False, y]],
					TrueIntroduction,
					e
				]
			]],
			Function[{Typed[h, p], Typed[e, "true" == "true"]}, h],
			d
		]]
	],
	TypeTheoryDefinition[
		NotDecidable,
		Function[{TypedImplicit[p, TypeUniverse[0]], Typed[d, Decidable[p]]}, InductiveRecursor[Decidable][
			Function[{Typed[t, Decidable[p]]}, Decidable[Not[p]]],
			Function[{Typed[h, Not[p]]}, DecidableTrue[h]],
			Function[{Typed[h, p]}, DecidableFalse[Function[{Typed[k, Not[p]]}, k[h]]]],
			d
		]]
	],
	TypeTheoryDefinition[
		AndDecidable,
		Function[{TypedImplicit[p, TypeUniverse[0]], TypedImplicit[q, TypeUniverse[0]], Typed[d, Decidable[p]], Typed[e, Decidable[q]]}, InductiveRecursor[Decidable][
			Function[{Typed[t, Decidable[p]]}, Decidable[And[p, q]]],
			Function[{Typed[h, Not[p]]}, DecidableFalse[Function[{Typed[k, And[p, q]]}, h[AndEliminationLeft[k]]]]],
			Function[{Typed[h, p]}, InductiveRecursor[Decidable][
				Function[{Typed[t, Decidable[q]]}, Decidable[And[p, q]]],
				Function[{Typed[g, Not[q]]}, DecidableFalse[Function[{Typed[k, And[p, q]]}, g[AndEliminationRight[k]]]]],
				Function[{Typed[g, q]}, DecidableTrue[AndIntroduction[h, g]]],
				e
			]],
			d
		]]
	],
	TypeTheoryDefinition[
		OrDecidable,
		Function[{TypedImplicit[p, TypeUniverse[0]], TypedImplicit[q, TypeUniverse[0]], Typed[d, Decidable[p]], Typed[e, Decidable[q]]}, InductiveRecursor[Decidable][
			Function[{Typed[t, Decidable[p]]}, Decidable[Or[p, q]]],
			Function[{Typed[h, Not[p]]}, InductiveRecursor[Decidable][
				Function[{Typed[t, Decidable[q]]}, Decidable[Or[p, q]]],
				Function[{Typed[g, Not[q]]}, DecidableFalse[Function[{Typed[k, Or[p, q]]}, InductiveRecursor[Or][Function[{Typed[s, Or[p, q]]}, False], h, g, k]]]],
				Function[{Typed[g, q]}, DecidableTrue[OrIntroductionRight[g]]],
				e
			]],
			Function[{Typed[h, p]}, DecidableTrue[OrIntroductionLeft[h]]],
			d
		]]
	],
	(* two Booleans that differ, by the predicate true of one and false of the other *)
	TypeTheoryTheorem[
		"falseNotTrue",
		Not["false" == "true"],
		Function[{Typed[e, "false" == "true"]}, InductiveRecursor[Equal][
			Function[{Typed[y, Booleans], Typed[k, "false" == y]}, InductiveRecursor[Booleans][Function[{Typed[b, Booleans]}, TypeUniverse[0]], True, False, y]],
			TrueIntroduction,
			e
		]]
	],
	TypeTheoryTheorem[
		"trueNotFalse",
		Not["true" == "false"],
		Function[{Typed[e, "true" == "false"]}, InductiveRecursor[Equal][
			Function[{Typed[y, Booleans], Typed[k, "true" == y]}, InductiveRecursor[Booleans][Function[{Typed[b, Booleans]}, TypeUniverse[0]], False, True, y]],
			TrueIntroduction,
			e
		]]
	],

	(* the Boolean comparisons of natural numbers, by recursion on both, as Lean's Nat.beq and Nat.ble; the
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
	TypeTheoryNaturalNumbers[NonNegativeIntegers, NaturalNumberZero, NaturalNumberSuccessor, <|"Equal" -> "equal", "LessEqual" -> "lessEqual"|>],

	(* what the comparisons give says what holds *)
	TypeTheoryTheorem[
		"equalTrue",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, Implies["equal"[m, n] == "true", m == n]],
		Function[{Typed[m, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
			Function[{Typed[a, NonNegativeIntegers]}, ForAll[{Typed[n, NonNegativeIntegers]}, Implies["equal"[a, n] == "true", a == n]]],
			Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
				Function[{Typed[c, NonNegativeIntegers]}, Implies["equal"[0, c] == "true", 0 == c]],
				Function[{Typed[e, "equal"[0, 0] == "true"]}, EqualityReflexivity[0]],
				Function[{Typed[c, NonNegativeIntegers], Typed[r, Implies["equal"[0, c] == "true", 0 == c]], Typed[e, "equal"[0, c + 1] == "true"]}, FalseElimination["falseNotTrue"[e]]],
				n
			]],
			Function[{Typed[a, NonNegativeIntegers], Typed[ih, ForAll[{Typed[n, NonNegativeIntegers]}, Implies["equal"[a, n] == "true", a == n]]]}, Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
				Function[{Typed[c, NonNegativeIntegers]}, Implies["equal"[a + 1, c] == "true", a + 1 == c]],
				Function[{Typed[e, "equal"[a + 1, 0] == "true"]}, FalseElimination["falseNotTrue"[e]]],
				Function[{Typed[c, NonNegativeIntegers], Typed[r, Implies["equal"[a + 1, c] == "true", a + 1 == c]], Typed[e, "equal"[a + 1, c + 1] == "true"]},
					EqualityCongruence[NaturalNumberSuccessor, ih[c, e]]
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
				Function[{Typed[e, "equal"[0, 0] == "false"]}, FalseElimination["trueNotFalse"[e]]],
				Function[{Typed[c, NonNegativeIntegers], Typed[r, Implies["equal"[0, c] == "false", Not[0 == c]]], Typed[e, "equal"[0, c + 1] == "false"], Typed[k, 0 == c + 1]},
					SuccessorNotZero[c][EqualitySymmetry[k]]
				],
				n
			]],
			Function[{Typed[a, NonNegativeIntegers], Typed[ih, ForAll[{Typed[n, NonNegativeIntegers]}, Implies["equal"[a, n] == "false", Not[a == n]]]]}, Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
				Function[{Typed[c, NonNegativeIntegers]}, Implies["equal"[a + 1, c] == "false", Not[a + 1 == c]]],
				Function[{Typed[e, "equal"[a + 1, 0] == "false"], Typed[k, a + 1 == 0]}, SuccessorNotZero[a][k]],
				Function[{Typed[c, NonNegativeIntegers], Typed[r, Implies["equal"[a + 1, c] == "false", Not[a + 1 == c]]], Typed[e, "equal"[a + 1, c + 1] == "false"], Typed[k, a + 1 == c + 1]},
					ih[c, e][SuccessorInjectivity[k]]
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
			Function[{Typed[n, NonNegativeIntegers], Typed[e, "lessEqual"[0, n] == "true"]}, LessEqualZero[n]],
			Function[{Typed[a, NonNegativeIntegers], Typed[ih, ForAll[{Typed[n, NonNegativeIntegers]}, Implies["lessEqual"[a, n] == "true", a <= n]]]}, Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
				Function[{Typed[c, NonNegativeIntegers]}, Implies["lessEqual"[a + 1, c] == "true", a + 1 <= c]],
				Function[{Typed[e, "lessEqual"[a + 1, 0] == "true"]}, FalseElimination["falseNotTrue"[e]]],
				Function[{Typed[c, NonNegativeIntegers], Typed[r, Implies["lessEqual"[a + 1, c] == "true", a + 1 <= c]], Typed[e, "lessEqual"[a + 1, c + 1] == "true"]},
					LessEqualSuccessor[ih[c, e]]
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
			Function[{Typed[n, NonNegativeIntegers], Typed[e, "lessEqual"[0, n] == "false"]}, FalseElimination["trueNotFalse"[e]]],
			Function[{Typed[a, NonNegativeIntegers], Typed[ih, ForAll[{Typed[n, NonNegativeIntegers]}, Implies["lessEqual"[a, n] == "false", Not[a <= n]]]]}, Function[{Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
				Function[{Typed[c, NonNegativeIntegers]}, Implies["lessEqual"[a + 1, c] == "false", Not[a + 1 <= c]]],
				Function[{Typed[e, "lessEqual"[a + 1, 0] == "false"]}, SuccessorNotLessEqualZero[a]],
				Function[{Typed[c, NonNegativeIntegers], Typed[r, Implies["lessEqual"[a + 1, c] == "false", Not[a + 1 <= c]]], Typed[e, "lessEqual"[a + 1, c + 1] == "false"], Typed[k, a + 1 <= c + 1]},
					ih[c, e][LessEqualPredecessor[k]]
				],
				n
			]]],
			m
		]]
	],

	(* a decision of m == n or m <= n is what the comparison gives, with the proof it gives, as Lean's
	   Nat.decEq and Nat.decLe: on literals it is one step of the kernel, however large they are *)
	TypeTheoryDefinition[
		NaturalNumberEqualityDecidable,
		Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, InductiveRecursor[Booleans][
			Function[{Typed[b, Booleans]}, Implies["equal"[m, n] == b, Decidable[m == n]]],
			Function[{Typed[e, "equal"[m, n] == "false"]}, DecidableFalse["equalFalse"[m, n, e]]],
			Function[{Typed[e, "equal"[m, n] == "true"]}, DecidableTrue["equalTrue"[m, n, e]]],
			"equal"[m, n]
		][EqualityReflexivity["equal"[m, n]]]]
	],
	TypeTheoryDefinition[
		LessEqualDecidable,
		Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, InductiveRecursor[Booleans][
			Function[{Typed[b, Booleans]}, Implies["lessEqual"[m, n] == b, Decidable[m <= n]]],
			Function[{Typed[e, "lessEqual"[m, n] == "false"]}, DecidableFalse["lessEqualFalse"[m, n, e]]],
			Function[{Typed[e, "lessEqual"[m, n] == "true"]}, DecidableTrue["lessEqualTrue"[m, n, e]]],
			"lessEqual"[m, n]
		][EqualityReflexivity["lessEqual"[m, n]]]]
	],

	(* pairs, sums, optional values and lists, laid out as Lean's Prod, Sum, Option and List *)
	TypeTheoryInductiveType[
		CartesianProduct,
		ForAll[{Typed[\[Alpha], TypeUniverse[u + 1]], Typed[\[Beta], TypeUniverse[v + 1]]}, TypeUniverse[Max[u, v] + 1]],
		{
			Pair -> ForAll[
				{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], TypedImplicit[\[Beta], TypeUniverse[v + 1]], Typed[x, \[Alpha]], Typed[y, \[Beta]]},
				CartesianProduct[\[Alpha], \[Beta]]
			]
		}
	],
	TypeTheoryInductiveType[
		DisjointUnion,
		ForAll[{Typed[\[Alpha], TypeUniverse[u + 1]], Typed[\[Beta], TypeUniverse[v + 1]]}, TypeUniverse[Max[u, v] + 1]],
		{
			LeftInjection -> ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], TypedImplicit[\[Beta], TypeUniverse[v + 1]], Typed[x, \[Alpha]]}, DisjointUnion[\[Alpha], \[Beta]]],
			RightInjection -> ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], TypedImplicit[\[Beta], TypeUniverse[v + 1]], Typed[y, \[Beta]]}, DisjointUnion[\[Alpha], \[Beta]]]
		}
	],
	TypeTheoryInductiveType[
		Option,
		ForAll[{Typed[\[Alpha], TypeUniverse[u + 1]]}, TypeUniverse[u + 1]],
		{
			OptionNone -> ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]]}, Option[\[Alpha]]],
			OptionSome -> ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[x, \[Alpha]]}, Option[\[Alpha]]]
		}
	],
	TypeTheoryInductiveType[
		Lists,
		ForAll[{Typed[\[Alpha], TypeUniverse[u + 1]]}, TypeUniverse[u + 1]],
		{
			EmptyList -> ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]]}, Lists[\[Alpha]]],
			ListPrepend -> ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[x, \[Alpha]], Typed[l, Lists[\[Alpha]]]}, Lists[\[Alpha]]]
		}
	],

	(* the operations on lists, by recursion on the first list: Join, Length, Map, Append of one element at
	   the end, and Reverse, which appends each element to the reversed rest *)
	TypeTheoryDefinition[
		Join,
		Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[l, Lists[\[Alpha]]], Typed[m, Lists[\[Alpha]]]},
			InductiveRecursor[Lists][
				Function[{Typed[t, Lists[\[Alpha]]]}, Lists[\[Alpha]]],
				m,
				Function[{Typed[x, \[Alpha]], Typed[rest, Lists[\[Alpha]]], Typed[r, Lists[\[Alpha]]]}, ListPrepend[x, r]],
				l
			]
		]
	],
	TypeTheoryDefinition[
		Length,
		Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[l, Lists[\[Alpha]]]},
			InductiveRecursor[Lists][
				Function[{Typed[t, Lists[\[Alpha]]]}, NonNegativeIntegers],
				0,
				Function[{Typed[x, \[Alpha]], Typed[rest, Lists[\[Alpha]]], Typed[r, NonNegativeIntegers]}, r + 1],
				l
			]
		]
	],
	TypeTheoryDefinition[
		Map,
		Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], TypedImplicit[\[Beta], TypeUniverse[v + 1]], Typed[f, TypeSpecifier[{\[Alpha]} -> \[Beta]]], Typed[l, Lists[\[Alpha]]]},
			InductiveRecursor[Lists][
				Function[{Typed[t, Lists[\[Alpha]]]}, Lists[\[Beta]]],
				EmptyList,
				Function[{Typed[x, \[Alpha]], Typed[rest, Lists[\[Alpha]]], Typed[r, Lists[\[Beta]]]}, ListPrepend[f[x], r]],
				l
			]
		]
	],
	TypeTheoryDefinition[
		Append,
		Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[l, Lists[\[Alpha]]], Typed[x, \[Alpha]]}, Join[l, ListPrepend[x, EmptyList]]]
	],
	TypeTheoryDefinition[
		Reverse,
		Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[l, Lists[\[Alpha]]]},
			InductiveRecursor[Lists][
				Function[{Typed[t, Lists[\[Alpha]]]}, Lists[\[Alpha]]],
				EmptyList,
				Function[{Typed[x, \[Alpha]], Typed[rest, Lists[\[Alpha]]], Typed[r, Lists[\[Alpha]]]}, Append[r, x]],
				l
			]
		]
	],

	(* the laws of the operations on lists, each by recursion on a list *)
	TypeTheoryTheorem[
		JoinEmptyRight,
		ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[l, Lists[\[Alpha]]]}, Join[l, EmptyList] == l],
		Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[l, Lists[\[Alpha]]]}, InductiveRecursor[Lists][
			Function[{Typed[t, Lists[\[Alpha]]]}, Join[t, EmptyList] == t],
			EqualityReflexivity[EmptyList],
			Function[{Typed[x, \[Alpha]], Typed[rest, Lists[\[Alpha]]], Typed[ih, Join[rest, EmptyList] == rest]},
				EqualityCongruence[Function[{Typed[r, Lists[\[Alpha]]]}, ListPrepend[x, r]], ih]
			],
			l
		]]
	],
	TypeTheoryTheorem[
		JoinAssociativity,
		ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[a, Lists[\[Alpha]]], Typed[b, Lists[\[Alpha]]], Typed[c, Lists[\[Alpha]]]}, Join[Join[a, b], c] == Join[a, Join[b, c]]],
		Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[a, Lists[\[Alpha]]], Typed[b, Lists[\[Alpha]]], Typed[c, Lists[\[Alpha]]]}, InductiveRecursor[Lists][
			Function[{Typed[t, Lists[\[Alpha]]]}, Join[Join[t, b], c] == Join[t, Join[b, c]]],
			EqualityReflexivity[Join[b, c]],
			Function[{Typed[x, \[Alpha]], Typed[rest, Lists[\[Alpha]]], Typed[ih, Join[Join[rest, b], c] == Join[rest, Join[b, c]]]},
				EqualityCongruence[Function[{Typed[r, Lists[\[Alpha]]]}, ListPrepend[x, r]], ih]
			],
			a
		]]
	],
	TypeTheoryTheorem[
		LengthJoin,
		ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[a, Lists[\[Alpha]]], Typed[b, Lists[\[Alpha]]]}, Length[Join[a, b]] == Length[a] + Length[b]],
		Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[a, Lists[\[Alpha]]], Typed[b, Lists[\[Alpha]]]}, InductiveRecursor[Lists][
			Function[{Typed[t, Lists[\[Alpha]]]}, Length[Join[t, b]] == Length[t] + Length[b]],
			EqualitySymmetry[AdditionZeroLeft[Length[b]]],
			Function[{Typed[x, \[Alpha]], Typed[rest, Lists[\[Alpha]]], Typed[ih, Length[Join[rest, b]] == Length[rest] + Length[b]]},
				EqualityTransitivity[EqualityCongruence[NaturalNumberSuccessor, ih], EqualitySymmetry[AdditionSuccessorLeft[Length[rest], Length[b]]]]
			],
			a
		]]
	],
	TypeTheoryTheorem[
		LengthMap,
		ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], TypedImplicit[\[Beta], TypeUniverse[v + 1]], Typed[f, TypeSpecifier[{\[Alpha]} -> \[Beta]]], Typed[l, Lists[\[Alpha]]]}, Length[Map[f, l]] == Length[l]],
		Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], TypedImplicit[\[Beta], TypeUniverse[v + 1]], Typed[f, TypeSpecifier[{\[Alpha]} -> \[Beta]]], Typed[l, Lists[\[Alpha]]]}, InductiveRecursor[Lists][
			Function[{Typed[t, Lists[\[Alpha]]]}, Length[Map[f, t]] == Length[t]],
			EqualityReflexivity[0],
			Function[{Typed[x, \[Alpha]], Typed[rest, Lists[\[Alpha]]], Typed[ih, Length[Map[f, rest]] == Length[rest]]}, EqualityCongruence[NaturalNumberSuccessor, ih]],
			l
		]]
	],
	TypeTheoryTheorem[
		MapJoin,
		ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], TypedImplicit[\[Beta], TypeUniverse[v + 1]], Typed[f, TypeSpecifier[{\[Alpha]} -> \[Beta]]], Typed[a, Lists[\[Alpha]]], Typed[b, Lists[\[Alpha]]]}, Map[f, Join[a, b]] == Join[Map[f, a], Map[f, b]]],
		Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], TypedImplicit[\[Beta], TypeUniverse[v + 1]], Typed[f, TypeSpecifier[{\[Alpha]} -> \[Beta]]], Typed[a, Lists[\[Alpha]]], Typed[b, Lists[\[Alpha]]]}, InductiveRecursor[Lists][
			Function[{Typed[t, Lists[\[Alpha]]]}, Map[f, Join[t, b]] == Join[Map[f, t], Map[f, b]]],
			EqualityReflexivity[Map[f, b]],
			Function[{Typed[x, \[Alpha]], Typed[rest, Lists[\[Alpha]]], Typed[ih, Map[f, Join[rest, b]] == Join[Map[f, rest], Map[f, b]]]},
				EqualityCongruence[Function[{Typed[r, Lists[\[Beta]]]}, ListPrepend[f[x], r]], ih]
			],
			a
		]]
	],
	TypeTheoryTheorem[
		MapComposition,
		ForAll[
			{
				TypedImplicit[\[Alpha], TypeUniverse[u + 1]], TypedImplicit[\[Beta], TypeUniverse[v + 1]], TypedImplicit[\[Gamma], TypeUniverse[w + 1]],
				Typed[f, TypeSpecifier[{\[Beta]} -> \[Gamma]]], Typed[g, TypeSpecifier[{\[Alpha]} -> \[Beta]]], Typed[l, Lists[\[Alpha]]]
			},
			Map[f, Map[g, l]] == Map[Composition[f, g], l]
		],
		Function[
			{
				TypedImplicit[\[Alpha], TypeUniverse[u + 1]], TypedImplicit[\[Beta], TypeUniverse[v + 1]], TypedImplicit[\[Gamma], TypeUniverse[w + 1]],
				Typed[f, TypeSpecifier[{\[Beta]} -> \[Gamma]]], Typed[g, TypeSpecifier[{\[Alpha]} -> \[Beta]]], Typed[l, Lists[\[Alpha]]]
			},
			InductiveRecursor[Lists][
				Function[{Typed[t, Lists[\[Alpha]]]}, Map[f, Map[g, t]] == Map[Composition[f, g], t]],
				EqualityReflexivity[EmptyList],
				Function[{Typed[x, \[Alpha]], Typed[rest, Lists[\[Alpha]]], Typed[ih, Map[f, Map[g, rest]] == Map[Composition[f, g], rest]]},
					EqualityCongruence[Function[{Typed[r, Lists[\[Gamma]]]}, ListPrepend[f[g[x]], r]], ih]
				],
				l
			]
		]
	],
	TypeTheoryTheorem[
		ReverseJoin,
		ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[a, Lists[\[Alpha]]], Typed[b, Lists[\[Alpha]]]}, Reverse[Join[a, b]] == Join[Reverse[b], Reverse[a]]],
		Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[a, Lists[\[Alpha]]], Typed[b, Lists[\[Alpha]]]}, InductiveRecursor[Lists][
			Function[{Typed[t, Lists[\[Alpha]]]}, Reverse[Join[t, b]] == Join[Reverse[b], Reverse[t]]],
			EqualitySymmetry[JoinEmptyRight[Reverse[b]]],
			Function[{Typed[x, \[Alpha]], Typed[rest, Lists[\[Alpha]]], Typed[ih, Reverse[Join[rest, b]] == Join[Reverse[b], Reverse[rest]]]},
				EqualityTransitivity[
					EqualityCongruence[Function[{Typed[r, Lists[\[Alpha]]]}, Join[r, ListPrepend[x, EmptyList]]], ih],
					JoinAssociativity[Reverse[b], Reverse[rest], ListPrepend[x, EmptyList]]
				]
			],
			a
		]]
	],
	TypeTheoryTheorem[
		ReverseReverse,
		ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[l, Lists[\[Alpha]]]}, Reverse[Reverse[l]] == l],
		Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[l, Lists[\[Alpha]]]}, InductiveRecursor[Lists][
			Function[{Typed[t, Lists[\[Alpha]]]}, Reverse[Reverse[t]] == t],
			EqualityReflexivity[EmptyList],
			Function[{Typed[x, \[Alpha]], Typed[rest, Lists[\[Alpha]]], Typed[ih, Reverse[Reverse[rest]] == rest]},
				EqualityTransitivity[
					ReverseJoin[Reverse[rest], ListPrepend[x, EmptyList]],
					EqualityCongruence[Function[{Typed[r, Lists[\[Alpha]]]}, Join[ListPrepend[x, EmptyList], r]], ih]
				]
			],
			l
		]]
	],
	TypeTheoryTheorem[
		LengthReverse,
		ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[l, Lists[\[Alpha]]]}, Length[Reverse[l]] == Length[l]],
		Function[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[l, Lists[\[Alpha]]]}, InductiveRecursor[Lists][
			Function[{Typed[t, Lists[\[Alpha]]]}, Length[Reverse[t]] == Length[t]],
			EqualityReflexivity[0],
			Function[{Typed[x, \[Alpha]], Typed[rest, Lists[\[Alpha]]], Typed[ih, Length[Reverse[rest]] == Length[rest]]},
				EqualityTransitivity[LengthJoin[Reverse[rest], ListPrepend[x, EmptyList]], EqualityCongruence[NaturalNumberSuccessor, ih]]
			],
			l
		]]
	]
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
