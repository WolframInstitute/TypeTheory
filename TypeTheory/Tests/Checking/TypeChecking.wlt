(* ::Package:: *)

(* Tests for Checking/TypeChecking.wl, the trusted kernel: type inference, reduction, definitional
   equality and projections, through the public queries. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

prelude = TypeTheoryEnvironment["Prelude"]

pairs = TypeTheoryEnvironment[prelude, {
	TypeTheoryInductiveType[NaturalPair, TypeUniverse[1], {NaturalPairIntroduction -> ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, NaturalPair]}],
	TypeTheoryInductiveType[Witness, TypeUniverse[0], {WitnessIntroduction -> ForAll[{Typed[a, NonNegativeIntegers], Typed[h, a == a]}, Witness]}]
}]


(* === inference === *)

VerificationTest[
	{TypeOf[TypeTheoryTerm[TypeUniverse[0]]], TypeOf[TypeTheoryTerm[TypeUniverse[1]]], TypeOf[TypeTheoryTerm[1 == 1, prelude]]},
	{TypeTheoryTerm[TypeUniverse[1], prelude], TypeTheoryTerm[TypeUniverse[2], prelude], TypeTheoryTerm[TypeUniverse[0], prelude]},
	TestID -> "Prop-is-in-Type-and-Type-is-in-the-next-universe"
]

VerificationTest[
	TypeOf[TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[1]]}, TypeSpecifier[{A} -> A]]]],
	TypeTheoryTerm[TypeUniverse[2], prelude],
	TestID -> "A-dependent-function-type-lives-in-the-larger-universe"
]

VerificationTest[
	TypeOf[TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[1]]}, Implies[True, True]], prelude]],
	TypeTheoryTerm[TypeUniverse[0], prelude],
	TestID -> "Prop-is-impredicative"
]

VerificationTest[
	FailureQ[TypeTheoryCheck[TypeTheoryTerm[TypeUniverse[1]], TypeTheoryTerm[TypeUniverse[1]]]],
	True,
	TestID -> "Type-is-not-in-Type"
]

VerificationTest[
	First @ TypeOf[TypeTheoryTerm[NaturalNumberSuccessor[True], prelude]],
	"TypeMismatch",
	TestID -> "An-argument-of-the-wrong-type-is-rejected"
]

VerificationTest[
	{TypeOf[TypeTheoryTerm[2 + 3]] === TypeTheoryTerm[NonNegativeIntegers, prelude], First @ TypeOf[TypeTheoryTerm[2 + 3, TypeTheoryEnvironment[]]]},
	{True, "ElaborationFailed"},
	TestID -> "A-term-without-an-environment-is-in-the-prelude"
]


(* === reduction and definitional equality === *)

VerificationTest[
	WeakHeadNormalForm[TypeTheoryTerm[Function[{Typed[x, NonNegativeIntegers]}, x + 1][41], prelude]],
	TypeTheoryTerm[42, prelude],
	TestID -> "Beta-reduction-and-literal-addition"
]

VerificationTest[
	WeakHeadNormalForm[TypeTheoryTerm[With[{x = 2}, x + x], prelude]],
	TypeTheoryTerm[4, prelude],
	TestID -> "With-binds-a-value"
]

VerificationTest[
	WeakHeadNormalForm[TypeTheoryTerm[Not[1 == 2], prelude]],
	TypeTheoryTerm[Implies[1 == 2, False], prelude],
	TestID -> "Definitions-unfold"
]

VerificationTest[
	{DefinitionallyEqualQ[TypeTheoryTerm[2 + 3, prelude], TypeTheoryTerm[5, prelude]], DefinitionallyEqualQ[TypeTheoryTerm[2 + 3, prelude], TypeTheoryTerm[6, prelude]]},
	{True, False},
	TestID -> "Literals-compute"
]

VerificationTest[
	DefinitionallyEqualQ[TypeTheoryTerm[NaturalNumberSuccessor[NaturalNumberSuccessor[NaturalNumberZero]], prelude], TypeTheoryTerm[2]],
	True,
	TestID -> "A-literal-is-its-constructor-form"
]

VerificationTest[
	DefinitionallyEqualQ[TypeTheoryTerm[NaturalNumberSuccessor[2] + 1, prelude], TypeTheoryTerm[4]],
	True,
	TestID -> "Addition-unfolds-on-a-constructor"
]

VerificationTest[
	DefinitionallyEqualQ[TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]}, NaturalNumberSuccessor[n]], prelude], TypeTheoryTerm[NaturalNumberSuccessor]],
	True,
	TestID -> "Eta-equality"
]

VerificationTest[
	MatchQ[TypeTheoryCheck[
		TypeTheoryTerm[Function[{Typed[p, TypeUniverse[0]], Typed[h, p], Typed[k, p]}, EqualityReflexivity[h]], prelude],
		TypeTheoryTerm[ForAll[{Typed[p, TypeUniverse[0]], Typed[h, p], Typed[k, p]}, h == k]]
	], _Success],
	True,
	TestID -> "Two-proofs-of-a-proposition-are-equal"
]


(* === projections === *)

VerificationTest[
	{TypeOf[TypeTheoryTerm[Function[{Typed[p, NaturalPair]}, p[[2]]], pairs]], WeakHeadNormalForm[TypeTheoryTerm[NaturalPairIntroduction[3, 4][[2]], pairs]]},
	{TypeTheoryTerm[TypeSpecifier[{NaturalPair} -> NonNegativeIntegers], pairs], TypeTheoryTerm[4, pairs]},
	TestID -> "A-projection-has-the-field-type-and-reduces-on-the-constructor"
]

VerificationTest[
	DefinitionallyEqualQ[
		TypeTheoryTerm[Function[{Typed[p, NaturalPair]}, NaturalPairIntroduction[p[[1]], p[[2]]]], pairs],
		TypeTheoryTerm[Function[{Typed[p, NaturalPair]}, p]]
	],
	True,
	TestID -> "Eta-for-structures"
]

VerificationTest[
	{
		First @ TypeOf[TypeTheoryTerm[Function[{Typed[w, Witness]}, w[[1]]], pairs]],
		First @ TypeOf[TypeTheoryTerm[Function[{Typed[w, Witness]}, w[[2]]], pairs]],
		TypeOf[TypeTheoryTerm[Function[{Typed[h, And[True, False]]}, h[[2]]], pairs]]
	},
	{"ProjectionFromProof", "ProjectionFromProof", TypeTheoryTerm[Implies[True && False, False], pairs]},
	TestID -> "Only-proofs-independent-of-data-are-projected-out-of-a-proof"
]

VerificationTest[
	First @ TypeOf[TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]}, n[[1]]], prelude]],
	"ElaborationFailed",
	TestID -> "Only-a-structure-has-fields"
]

VerificationTest[
	{
		DefinitionallyEqualQ[TypeTheoryTerm[TypeUniverse[ImpredicativeMaximum[1, u]]], TypeTheoryTerm[TypeUniverse[u]]],
		DefinitionallyEqualQ[TypeTheoryTerm[TypeUniverse[ImpredicativeMaximum[u, v]]], TypeTheoryTerm[TypeUniverse[v]]]
	},
	{True, False},
	TestID -> "The-impredicative-maximum-of-1-and-u-is-u"
]
