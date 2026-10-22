(* ::Package:: *)

(* Tests for Library/Prelude.wl: the declarations of the prelude, the theorems proved from the
   recursors, the classical axioms and the constructive environment without them. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

prelude = TypeTheoryEnvironment["Prelude"]


VerificationTest[
	{Head[prelude], prelude === TypeTheoryEnvironment["Prelude"]},
	{TypeTheoryEnvironment, True},
	TestID -> "The-prelude-is-built-once"
]

VerificationTest[
	Complement[
		{
			True, False, Not, And, Or, Equal, Exists, NonNegativeIntegers, Plus,
			FalseElimination, AndEliminationLeft, AndEliminationRight,
			EqualitySymmetry, EqualityTransitivity, EqualityCongruence, EqualitySubstitution
		},
		Keys[prelude]
	],
	{},
	TestID -> "The-prelude-declares-logic-equality-and-the-natural-numbers"
]

VerificationTest[
	{
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[EqualitySymmetry[EqualityReflexivity[3]], prelude], TypeTheoryTerm[3 == 3]], _Success],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[h, False]}, FalseElimination[h]], prelude], TypeTheoryTerm[Implies[False, 1 == 2]]], _Success],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[AndEliminationRight[AndIntroduction[TrueIntroduction, EqualityReflexivity[2]]], prelude], TypeTheoryTerm[1 + 1 == 2]], _Success],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[EqualityCongruence[NaturalNumberSuccessor, EqualityReflexivity[2]], prelude], TypeTheoryTerm[3 == 3]], _Success],
		MatchQ[TypeTheoryCheck[
			TypeTheoryTerm[Function[{Typed[x, NonNegativeIntegers], Typed[h, x == 2]}, EqualitySubstitution[EqualitySymmetry[h], EqualityReflexivity[2]]], prelude],
			TypeTheoryTerm[ForAll[{Typed[x, NonNegativeIntegers]}, Implies[x == 2, x == 2]]]
		], _Success]
	},
	{True, True, True, True, True},
	TestID -> "The-prelude-theorems-apply"
]

VerificationTest[
	{
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[OrIntroductionLeft[TrueIntroduction], prelude], TypeTheoryTerm[Or[True, False]]], _Success],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[OrIntroductionRight[TrueIntroduction], prelude], TypeTheoryTerm[Or[False, True]]], _Success]
	},
	{True, True},
	TestID -> "Disjunction-introduction"
]

VerificationTest[
	{
		WeakHeadNormalForm[TypeTheoryTerm[3 * 4]] === TypeTheoryTerm[12, prelude],
		WeakHeadNormalForm[TypeTheoryTerm[2^5]] === TypeTheoryTerm[32, prelude],
		WeakHeadNormalForm[TypeTheoryTerm[Subtract[7, 5]]] === TypeTheoryTerm[2, prelude],
		WeakHeadNormalForm[TypeTheoryTerm[Subtract[5, 7]]] === TypeTheoryTerm[0, prelude],
		WeakHeadNormalForm[TypeTheoryTerm[7 - 5]] === TypeTheoryTerm[2, prelude],
		WeakHeadNormalForm[TypeTheoryTerm[NaturalNumberPredecessor[10]]] === TypeTheoryTerm[9, prelude]
	},
	{True, True, True, True, True, True},
	TestID -> "Multiplication-powers-and-subtraction-compute"
]

VerificationTest[
	{
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[AdditionCommutativity], TypeTheoryTerm[ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, a + b == b + a]]], _Success],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[AdditionAssociativity], TypeTheoryTerm[ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers]}, a + b + c == a + (b + c)]]], _Success],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[MultiplicationCommutativity], TypeTheoryTerm[ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, a * b == b * a]]], _Success],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[MultiplicationDistributivityRight], TypeTheoryTerm[ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers]}, (a + b) * c == a * c + b * c]]], _Success],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[PowerAddition], TypeTheoryTerm[ForAll[{Typed[m, NonNegativeIntegers], Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, m^(a + b) == m^a * m^b]]], _Success],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[AdditionSubtractionCancellation], TypeTheoryTerm[ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, (a + b) - b == a]]], _Success]
	},
	{True, True, True, True, True, True},
	TestID -> "The-laws-of-arithmetic-have-their-statements"
]

VerificationTest[
	{
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[MultiplicationCommutativity[3, 4]], TypeTheoryTerm[3 * 4 == 4 * 3]], _Success],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[SuccessorNotZero[4]], TypeTheoryTerm[5 != 0]], _Success],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[LessEqualStep[LessEqualStep[LessEqualStep[LessEqualReflexivity]]]], TypeTheoryTerm[2 <= 5]], _Success],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[LessEqualAddition[4, 2]], TypeTheoryTerm[3 < 6]], _Success],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[h, 3 <= 2]}, LessIrreflexivity[2][LessEqualTransitivity[h, LessEqualReflexivity]]]], TypeTheoryTerm[Not[3 <= 2]]], _Success],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[LessEqualZero[7]], TypeTheoryTerm[7 >= 0]], _Success]
	},
	{True, True, True, True, True, True},
	TestID -> "The-order-of-the-natural-numbers"
]

VerificationTest[
	{
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[EquivalentReflexivity[True]], TypeTheoryTerm[Equivalent[True, True]]], _Success],
		MatchQ[TypeTheoryCheck[
			TypeTheoryTerm[Function[{Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]], Typed[h, Equivalent[p, q]], Typed[x, q]}, EquivalentBackward[EquivalentSymmetry[EquivalentSymmetry[h]]][x]]],
			TypeTheoryTerm[ForAll[{Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]]}, Implies[Equivalent[p, q], Implies[q, p]]]]
		], _Success],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[Identity[3]], TypeTheoryTerm[NonNegativeIntegers]], _Success],
		WeakHeadNormalForm[TypeTheoryTerm[Composition[NaturalNumberSuccessor, NaturalNumberSuccessor][3]]] === TypeTheoryTerm[NaturalNumberSuccessor[NaturalNumberSuccessor[3]], prelude],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[AndIntroduction[TrueIntroduction, AndIntroduction[TrueIntroduction, TrueIntroduction]]], TypeTheoryTerm[True && True && True]], _Success]
	},
	{True, True, True, True, True},
	TestID -> "Equivalence-identity-composition-and-conjunctions"
]

VerificationTest[
	MatchQ[TypeTheoryCheck[prelude], _Success],
	True,
	TestID -> "The-expanded-prelude-replays"
]


(* === the classical part === *)

VerificationTest[
	With[{constructive = TypeTheoryEnvironment["Constructive"]},
		{
			Length[constructive],
			Information[constructive, "Axioms"],
			Take[Keys[prelude], Length[constructive]] === Keys[constructive],
			KeyExistsQ[constructive, ExcludedMiddle],
			Information[prelude, "Axioms"]
		}
	],
	{155, {}, True, False, {PropositionalExtensionality, QuotientSoundness, Choice}},
	TestID -> "The-constructive-environment-is-the-prelude-without-its-classical-part"
]

VerificationTest[
	{
		Head[prelude[ExcludedMiddle]],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[ExcludedMiddle[2 + 2 == 5]], TypeTheoryTerm[Or[2 + 2 == 5, Not[2 + 2 == 5]]]], _Success],
		MatchQ[TypeTheoryCheck[
			TypeTheoryTerm[Function[{Typed[p, TypeUniverse[0]], Typed[h, Not[Not[p]]]}, DoubleNegationElimination[p][h]]],
			TypeTheoryTerm[ForAll[{Typed[p, TypeUniverse[0]]}, Implies[Not[Not[p]], p]]]
		], _Success]
	},
	{TypeTheoryTheorem, True, True},
	TestID -> "The-excluded-middle-is-a-theorem"
]

VerificationTest[
	{
		MatchQ[TypeTheoryCheck[
			TypeTheoryTerm[PropositionalExtensionality[EquivalentIntroduction[Function[{Typed[h, True]}, AndIntroduction[h, h]], Function[{Typed[h, True && True]}, AndEliminationLeft[h]]]]],
			TypeTheoryTerm[Typed[True, TypeUniverse[0]] == (True && True)]
		], _Success],
		MatchQ[TypeTheoryCheck[
			TypeTheoryTerm[FunctionExtensionality[AdditionZeroLeft]],
			TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]}, 0 + n] == Function[{Typed[n, NonNegativeIntegers]}, n]]
		], _Success],
		MatchQ[TypeTheoryCheck[
			TypeTheoryTerm[Function[{Typed[h, Exists[Function[{Typed[n, NonNegativeIntegers]}, n + n == 6]]]}, ChosenWitnessProperty[h]]],
			TypeTheoryTerm[ForAll[{Typed[h, Exists[Function[{Typed[n, NonNegativeIntegers]}, n + n == 6]]]}, ChosenWitness[h] + ChosenWitness[h] == 6]]
		], _Success]
	},
	{True, True, True},
	TestID -> "Extensionality-and-choice"
]


(* === the Booleans === *)

VerificationTest[
	{
		WeakHeadNormalForm[TypeTheoryTerm[Typed[True && False, Booleans]]],
		WeakHeadNormalForm[TypeTheoryTerm[Typed[Not[False] || False, Booleans]]],
		WeakHeadNormalForm[TypeTheoryTerm[Typed[True && True && False, Booleans]]],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[EqualityReflexivity["true"]], TypeTheoryTerm[Not[Not[Typed[True, Booleans]]] == True]], _Success]
	},
	{TypeTheoryTerm["false", prelude], TypeTheoryTerm["true", prelude], TypeTheoryTerm["false", prelude], True},
	TestID -> "The-Booleans-compute"
]

VerificationTest[
	MatchQ[TypeTheoryCheck[
		TypeTheoryTerm[Function[{Typed[b, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Not[Not[t]] == t], EqualityReflexivity["false"], EqualityReflexivity["true"], b]]],
		TypeTheoryTerm[ForAll[{Typed[b, Booleans]}, Not[Not[b]] == b]]
	], _Success],
	True,
	TestID -> "A-statement-about-every-Boolean-proved-by-cases"
]

(* decisions, pairs, sums, optional values and lists *)

VerificationTest[
	{
		WeakHeadNormalForm[TypeTheoryTerm[Decide[3 + 4 == 7], prelude]],
		WeakHeadNormalForm[TypeTheoryTerm[Decide[5 <= 2], prelude]],
		WeakHeadNormalForm[TypeTheoryTerm[Decide[Not[1 == 2] && (3 <= 1 || 1 <= 3)], prelude]],
		WeakHeadNormalForm[TypeTheoryTerm[Decide[2 < 3 && 4 != 5 && True && Not[False]], prelude]],
		WeakHeadNormalForm[TypeTheoryTerm[Construct[Decide, 5 <= 2, LessEqualDecidable[5, 2]], prelude]]
	},
	{TypeTheoryTerm["true", prelude], TypeTheoryTerm["false", prelude], TypeTheoryTerm["true", prelude], TypeTheoryTerm["true", prelude], TypeTheoryTerm["false", prelude]},
	TestID -> "Decisions-are-found-among-the-instances-and-compute-to-Booleans"
]

VerificationTest[
	MatchQ[TypeTheoryCheck[TypeTheoryTerm[DecideSoundness[EqualityReflexivity[True]], prelude], TypeTheoryTerm[3 + 4 == 7, prelude]], _Success],
	True,
	TestID -> "A-decision-that-computes-to-True-proves-its-proposition"
]

VerificationTest[
	{
		TypeOf[TypeTheoryTerm[Pair[1, "true"][[2]], prelude]],
		TypeOf[TypeTheoryTerm[Typed[LeftInjection[3], DisjointUnion[NonNegativeIntegers, Booleans]], prelude]],
		TypeOf[TypeTheoryTerm[OptionSome[5], prelude]],
		TypeOf[TypeTheoryTerm[ListPrepend[1, EmptyList], prelude]]
	},
	{
		TypeTheoryTerm[Booleans, prelude],
		TypeTheoryTerm[DisjointUnion[NonNegativeIntegers, Booleans], prelude],
		TypeTheoryTerm[Option[NonNegativeIntegers], prelude],
		TypeTheoryTerm[Lists[NonNegativeIntegers], prelude]
	},
	TestID -> "Pairs-sums-optional-values-and-lists-have-their-types"
]

VerificationTest[
	{
		WeakHeadNormalForm[TypeTheoryTerm[Length[Join[ListPrepend[1, ListPrepend[2, EmptyList]], ListPrepend[3, EmptyList]]], prelude]],
		MatchQ[TypeTheoryCheck[
			TypeTheoryTerm[EqualityReflexivity[ListPrepend[3, ListPrepend[2, ListPrepend[1, EmptyList]]]], prelude],
			TypeTheoryTerm[Reverse[ListPrepend[1, ListPrepend[2, ListPrepend[3, EmptyList]]]] == ListPrepend[3, ListPrepend[2, ListPrepend[1, EmptyList]]], prelude]
		], _Success],
		MatchQ[TypeTheoryCheck[
			TypeTheoryTerm[ReverseReverse[ListPrepend[1, EmptyList]], prelude],
			TypeTheoryTerm[Reverse[Reverse[ListPrepend[1, EmptyList]]] == ListPrepend[1, EmptyList], prelude]
		], _Success]
	},
	{TypeTheoryTerm[3, prelude], True, True},
	TestID -> "The-operations-on-lists-compute-and-their-laws-apply"
]
