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
			"falseElimination", "andEliminationLeft", "andEliminationRight",
			"equalitySymmetry", "equalityTransitivity", "equalityCongruence", "equalitySubstitution"
		},
		Keys[prelude]
	],
	{},
	TestID -> "The-prelude-declares-logic-equality-and-the-natural-numbers"
]

VerificationTest[
	{
		MatchQ[TypeTheoryCheck[TypeTheoryTerm["equalitySymmetry"["equalityReflexivity"[3]], prelude], TypeTheoryTerm[3 == 3]], _Success],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[h, False]}, "falseElimination"[h]], prelude], TypeTheoryTerm[Implies[False, 1 == 2]]], _Success],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm["andEliminationRight"["andIntroduction"["trueIntroduction", "equalityReflexivity"[2]]], prelude], TypeTheoryTerm[1 + 1 == 2]], _Success],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm["equalityCongruence"["successor", "equalityReflexivity"[2]], prelude], TypeTheoryTerm[3 == 3]], _Success],
		MatchQ[TypeTheoryCheck[
			TypeTheoryTerm[Function[{Typed[x, NonNegativeIntegers], Typed[h, x == 2]}, "equalitySubstitution"["equalitySymmetry"[h], "equalityReflexivity"[2]]], prelude],
			TypeTheoryTerm[ForAll[{Typed[x, NonNegativeIntegers]}, Implies[x == 2, x == 2]]]
		], _Success]
	},
	{True, True, True, True, True},
	TestID -> "The-prelude-theorems-apply"
]

VerificationTest[
	{
		MatchQ[TypeTheoryCheck[TypeTheoryTerm["orIntroductionLeft"["trueIntroduction"], prelude], TypeTheoryTerm[Or[True, False]]], _Success],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm["orIntroductionRight"["trueIntroduction"], prelude], TypeTheoryTerm[Or[False, True]]], _Success]
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
		MatchQ[TypeTheoryCheck[TypeTheoryTerm["additionCommutativity"], TypeTheoryTerm[ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, a + b == b + a]]], _Success],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm["additionAssociativity"], TypeTheoryTerm[ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers]}, a + b + c == a + (b + c)]]], _Success],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm["multiplicationCommutativity"], TypeTheoryTerm[ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, a * b == b * a]]], _Success],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm["multiplicationDistributivityRight"], TypeTheoryTerm[ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers]}, (a + b) * c == a * c + b * c]]], _Success],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm["powerAddition"], TypeTheoryTerm[ForAll[{Typed[m, NonNegativeIntegers], Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, m^(a + b) == m^a * m^b]]], _Success],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm["additionSubtractionCancellation"], TypeTheoryTerm[ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, (a + b) - b == a]]], _Success]
	},
	{True, True, True, True, True, True},
	TestID -> "The-laws-of-arithmetic-have-their-statements"
]

VerificationTest[
	{
		MatchQ[TypeTheoryCheck[TypeTheoryTerm["multiplicationCommutativity"[3, 4]], TypeTheoryTerm[3 * 4 == 4 * 3]], _Success],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm["successorNotZero"[4]], TypeTheoryTerm[5 != 0]], _Success],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm["lessEqualStep"["lessEqualStep"["lessEqualStep"["lessEqualReflexivity"]]]], TypeTheoryTerm[2 <= 5]], _Success],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm["lessEqualAddition"[4, 2]], TypeTheoryTerm[3 < 6]], _Success],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[h, 3 <= 2]}, "lessIrreflexivity"[2]["lessEqualTransitivity"[h, "lessEqualReflexivity"]]]], TypeTheoryTerm[Not[3 <= 2]]], _Success],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm["lessEqualZero"[7]], TypeTheoryTerm[7 >= 0]], _Success]
	},
	{True, True, True, True, True, True},
	TestID -> "The-order-of-the-natural-numbers"
]

VerificationTest[
	{
		MatchQ[TypeTheoryCheck[TypeTheoryTerm["equivalentReflexivity"[True]], TypeTheoryTerm[Equivalent[True, True]]], _Success],
		MatchQ[TypeTheoryCheck[
			TypeTheoryTerm[Function[{Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]], Typed[h, Equivalent[p, q]], Typed[x, q]}, "equivalentBackward"["equivalentSymmetry"["equivalentSymmetry"[h]]][x]]],
			TypeTheoryTerm[ForAll[{Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]]}, Implies[Equivalent[p, q], Implies[q, p]]]]
		], _Success],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[Identity[3]], TypeTheoryTerm[NonNegativeIntegers]], _Success],
		WeakHeadNormalForm[TypeTheoryTerm[Composition["successor", "successor"][3]]] === TypeTheoryTerm["successor"["successor"[3]], prelude],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm["andIntroduction"["trueIntroduction", "andIntroduction"["trueIntroduction", "trueIntroduction"]]], TypeTheoryTerm[True && True && True]], _Success]
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
			KeyExistsQ[constructive, "excludedMiddle"],
			Information[prelude, "Axioms"]
		}
	],
	{155, {}, True, False, {"propositionalExtensionality", "quotientSoundness", "choice"}},
	TestID -> "The-constructive-environment-is-the-prelude-without-its-classical-part"
]

VerificationTest[
	{
		Head[prelude["excludedMiddle"]],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm["excludedMiddle"[2 + 2 == 5]], TypeTheoryTerm[Or[2 + 2 == 5, Not[2 + 2 == 5]]]], _Success],
		MatchQ[TypeTheoryCheck[
			TypeTheoryTerm[Function[{Typed[p, TypeUniverse[0]], Typed[h, Not[Not[p]]]}, "doubleNegationElimination"[p][h]]],
			TypeTheoryTerm[ForAll[{Typed[p, TypeUniverse[0]]}, Implies[Not[Not[p]], p]]]
		], _Success]
	},
	{TypeTheoryTheorem, True, True},
	TestID -> "The-excluded-middle-is-a-theorem"
]

VerificationTest[
	{
		MatchQ[TypeTheoryCheck[
			TypeTheoryTerm["propositionalExtensionality"["equivalentIntroduction"[Function[{Typed[h, True]}, "andIntroduction"[h, h]], Function[{Typed[h, True && True]}, "andEliminationLeft"[h]]]]],
			TypeTheoryTerm[Typed[True, TypeUniverse[0]] == (True && True)]
		], _Success],
		MatchQ[TypeTheoryCheck[
			TypeTheoryTerm["functionExtensionality"["additionZeroLeft"]],
			TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]}, 0 + n] == Function[{Typed[n, NonNegativeIntegers]}, n]]
		], _Success],
		MatchQ[TypeTheoryCheck[
			TypeTheoryTerm[Function[{Typed[h, Exists[Function[{Typed[n, NonNegativeIntegers]}, n + n == 6]]]}, "chosenWitnessProperty"[h]]],
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
		MatchQ[TypeTheoryCheck[TypeTheoryTerm["equalityReflexivity"["true"]], TypeTheoryTerm[Not[Not[Typed[True, Booleans]]] == True]], _Success]
	},
	{TypeTheoryTerm["false", prelude], TypeTheoryTerm["true", prelude], TypeTheoryTerm["false", prelude], True},
	TestID -> "The-Booleans-compute"
]

VerificationTest[
	MatchQ[TypeTheoryCheck[
		TypeTheoryTerm[Function[{Typed[b, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Not[Not[t]] == t], "equalityReflexivity"["false"], "equalityReflexivity"["true"], b]]],
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
		WeakHeadNormalForm[TypeTheoryTerm[Construct[Decide, 5 <= 2, "lessEqualDecidable"[5, 2]], prelude]]
	},
	{TypeTheoryTerm["true", prelude], TypeTheoryTerm["false", prelude], TypeTheoryTerm["true", prelude], TypeTheoryTerm["true", prelude], TypeTheoryTerm["false", prelude]},
	TestID -> "Decisions-are-found-among-the-instances-and-compute-to-Booleans"
]

VerificationTest[
	MatchQ[TypeTheoryCheck[TypeTheoryTerm["decideSoundness"["equalityReflexivity"[True]], prelude], TypeTheoryTerm[3 + 4 == 7, prelude]], _Success],
	True,
	TestID -> "A-decision-that-computes-to-True-proves-its-proposition"
]

VerificationTest[
	{
		TypeTheoryType[TypeTheoryTerm["pair"[1, "true"][[2]], prelude]],
		TypeTheoryType[TypeTheoryTerm[Typed["left"[3], DisjointUnionType[NonNegativeIntegers, Booleans]], prelude]],
		TypeTheoryType[TypeTheoryTerm["some"[5], prelude]],
		TypeTheoryType[TypeTheoryTerm[Prepend[1][{}], prelude]]
	},
	{
		TypeTheoryTerm[Booleans, prelude],
		TypeTheoryTerm[DisjointUnionType[NonNegativeIntegers, Booleans], prelude],
		TypeTheoryTerm[Option[NonNegativeIntegers], prelude],
		TypeTheoryTerm[{NonNegativeIntegers}, prelude]
	},
	TestID -> "Pairs-sums-optional-values-and-lists-have-their-types"
]

VerificationTest[
	{
		WeakHeadNormalForm[TypeTheoryTerm[Length[Join[Prepend[1][Prepend[2][{}]], Prepend[3][{}]]], prelude]],
		MatchQ[TypeTheoryCheck[
			TypeTheoryTerm["equalityReflexivity"[Prepend[3][Prepend[2][Prepend[1][{}]]]], prelude],
			TypeTheoryTerm[Reverse[Prepend[1][Prepend[2][Prepend[3][{}]]]] == Prepend[3][Prepend[2][Prepend[1][{}]]], prelude]
		], _Success],
		MatchQ[TypeTheoryCheck[
			TypeTheoryTerm["reverseReverse"[Prepend[1][{}]], prelude],
			TypeTheoryTerm[Reverse[Reverse[Prepend[1][{}]]] == Prepend[1][{}], prelude]
		], _Success]
	},
	{TypeTheoryTerm[3, prelude], True, True},
	TestID -> "The-operations-on-lists-compute-and-their-laws-apply"
]
