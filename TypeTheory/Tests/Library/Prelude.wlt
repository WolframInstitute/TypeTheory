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
		TypeTheoryCheck[TypeTheoryTerm[EqualitySymmetry[EqualityReflexivity[3]], prelude], TypeTheoryTerm[3 == 3]],
		TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[h, False]}, FalseElimination[h]], prelude], TypeTheoryTerm[Implies[False, 1 == 2]]],
		TypeTheoryCheck[TypeTheoryTerm[AndEliminationRight[AndIntroduction[TrueIntroduction, EqualityReflexivity[2]]], prelude], TypeTheoryTerm[1 + 1 == 2]],
		TypeTheoryCheck[TypeTheoryTerm[EqualityCongruence[NaturalNumberSuccessor, EqualityReflexivity[2]], prelude], TypeTheoryTerm[3 == 3]],
		TypeTheoryCheck[
			TypeTheoryTerm[Function[{Typed[x, NonNegativeIntegers], Typed[h, x == 2]}, EqualitySubstitution[EqualitySymmetry[h], EqualityReflexivity[2]]], prelude],
			TypeTheoryTerm[ForAll[{Typed[x, NonNegativeIntegers]}, Implies[x == 2, x == 2]]]
		]
	},
	{True, True, True, True, True},
	TestID -> "The-prelude-theorems-apply"
]

VerificationTest[
	{
		TypeTheoryCheck[TypeTheoryTerm[OrIntroductionLeft[TrueIntroduction], prelude], TypeTheoryTerm[Or[True, False]]],
		TypeTheoryCheck[TypeTheoryTerm[OrIntroductionRight[TrueIntroduction], prelude], TypeTheoryTerm[Or[False, True]]]
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
		TypeTheoryCheck[TypeTheoryTerm[AdditionCommutativity], TypeTheoryTerm[ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, a + b == b + a]]],
		TypeTheoryCheck[TypeTheoryTerm[AdditionAssociativity], TypeTheoryTerm[ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers]}, a + b + c == a + (b + c)]]],
		TypeTheoryCheck[TypeTheoryTerm[MultiplicationCommutativity], TypeTheoryTerm[ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, a * b == b * a]]],
		TypeTheoryCheck[TypeTheoryTerm[MultiplicationDistributivityRight], TypeTheoryTerm[ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers]}, (a + b) * c == a * c + b * c]]],
		TypeTheoryCheck[TypeTheoryTerm[PowerAddition], TypeTheoryTerm[ForAll[{Typed[m, NonNegativeIntegers], Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, m^(a + b) == m^a * m^b]]],
		TypeTheoryCheck[TypeTheoryTerm[AdditionSubtractionCancellation], TypeTheoryTerm[ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, (a + b) - b == a]]]
	},
	{True, True, True, True, True, True},
	TestID -> "The-laws-of-arithmetic-have-their-statements"
]

VerificationTest[
	{
		TypeTheoryCheck[TypeTheoryTerm[MultiplicationCommutativity[3, 4]], TypeTheoryTerm[3 * 4 == 4 * 3]],
		TypeTheoryCheck[TypeTheoryTerm[SuccessorNotZero[4]], TypeTheoryTerm[5 != 0]],
		TypeTheoryCheck[TypeTheoryTerm[LessEqualStep[LessEqualStep[LessEqualStep[LessEqualReflexivity]]]], TypeTheoryTerm[2 <= 5]],
		TypeTheoryCheck[TypeTheoryTerm[LessEqualAddition[4, 2]], TypeTheoryTerm[3 < 6]],
		TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[h, 3 <= 2]}, LessIrreflexivity[2][LessEqualTransitivity[h, LessEqualReflexivity]]]], TypeTheoryTerm[Not[3 <= 2]]],
		TypeTheoryCheck[TypeTheoryTerm[LessEqualZero[7]], TypeTheoryTerm[7 >= 0]]
	},
	{True, True, True, True, True, True},
	TestID -> "The-order-of-the-natural-numbers"
]

VerificationTest[
	{
		TypeTheoryCheck[TypeTheoryTerm[EquivalentReflexivity[True]], TypeTheoryTerm[Equivalent[True, True]]],
		TypeTheoryCheck[
			TypeTheoryTerm[Function[{Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]], Typed[h, Equivalent[p, q]], Typed[x, q]}, EquivalentBackward[EquivalentSymmetry[EquivalentSymmetry[h]]][x]]],
			TypeTheoryTerm[ForAll[{Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]]}, Implies[Equivalent[p, q], Implies[q, p]]]]
		],
		TypeTheoryCheck[TypeTheoryTerm[Identity[3]], TypeTheoryTerm[NonNegativeIntegers]],
		WeakHeadNormalForm[TypeTheoryTerm[Composition[NaturalNumberSuccessor, NaturalNumberSuccessor][3]]] === TypeTheoryTerm[NaturalNumberSuccessor[NaturalNumberSuccessor[3]], prelude],
		TypeTheoryCheck[TypeTheoryTerm[AndIntroduction[TrueIntroduction, AndIntroduction[TrueIntroduction, TrueIntroduction]]], TypeTheoryTerm[True && True && True]]
	},
	{True, True, True, True, True},
	TestID -> "Equivalence-identity-composition-and-conjunctions"
]

VerificationTest[
	TypeTheoryCheck[prelude],
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
	{96, {}, True, False, {PropositionalExtensionality, FunctionExtensionality, Choice}},
	TestID -> "The-constructive-environment-is-the-prelude-without-its-classical-part"
]

VerificationTest[
	{
		Head[prelude[ExcludedMiddle]],
		TypeTheoryCheck[TypeTheoryTerm[ExcludedMiddle[2 + 2 == 5]], TypeTheoryTerm[Or[2 + 2 == 5, Not[2 + 2 == 5]]]],
		TypeTheoryCheck[
			TypeTheoryTerm[Function[{Typed[p, TypeUniverse[0]], Typed[h, Not[Not[p]]]}, DoubleNegationElimination[p][h]]],
			TypeTheoryTerm[ForAll[{Typed[p, TypeUniverse[0]]}, Implies[Not[Not[p]], p]]]
		]
	},
	{TypeTheoryTheorem, True, True},
	TestID -> "The-excluded-middle-is-a-theorem"
]

VerificationTest[
	{
		TypeTheoryCheck[
			TypeTheoryTerm[PropositionalExtensionality[EquivalentIntroduction[Function[{Typed[h, True]}, AndIntroduction[h, h]], Function[{Typed[h, True && True]}, AndEliminationLeft[h]]]]],
			TypeTheoryTerm[Typed[True, TypeUniverse[0]] == (True && True)]
		],
		TypeTheoryCheck[
			TypeTheoryTerm[FunctionExtensionality[AdditionZeroLeft]],
			TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]}, 0 + n] == Function[{Typed[n, NonNegativeIntegers]}, n]]
		],
		TypeTheoryCheck[
			TypeTheoryTerm[Function[{Typed[h, Exists[Function[{Typed[n, NonNegativeIntegers]}, n + n == 6]]]}, ChosenWitnessProperty[h]]],
			TypeTheoryTerm[ForAll[{Typed[h, Exists[Function[{Typed[n, NonNegativeIntegers]}, n + n == 6]]]}, ChosenWitness[h] + ChosenWitness[h] == 6]]
		]
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
		TypeTheoryCheck[TypeTheoryTerm[EqualityReflexivity[BooleanTrue]], TypeTheoryTerm[Not[Not[Typed[True, Booleans]]] == True]]
	},
	{TypeTheoryTerm[BooleanFalse, prelude], TypeTheoryTerm[BooleanTrue, prelude], TypeTheoryTerm[BooleanFalse, prelude], True},
	TestID -> "The-Booleans-compute"
]

VerificationTest[
	TypeTheoryCheck[
		TypeTheoryTerm[Function[{Typed[b, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Not[Not[t]] == t], EqualityReflexivity[BooleanFalse], EqualityReflexivity[BooleanTrue], b]]],
		TypeTheoryTerm[ForAll[{Typed[b, Booleans]}, Not[Not[b]] == b]]
	],
	True,
	TestID -> "A-statement-about-every-Boolean-proved-by-cases"
]
