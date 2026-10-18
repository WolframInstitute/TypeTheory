(* ::Package:: *)

(* Tests for Checking/TypeChecking.wl, the trusted kernel: type inference, reduction and definitional
   equality, through the public queries. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]


(* === inference === *)

VerificationTest[
	{TypeOf[TypeTheoryTerm[TypeUniverse[0]]], TypeOf[TypeTheoryTerm[TypeUniverse[1]]], TypeOf[TypeTheoryTerm[True]]},
	{TypeTheoryTerm[TypeUniverse[1]], TypeTheoryTerm[TypeUniverse[2]], TypeTheoryTerm[TypeUniverse[0]]},
	TestID -> "Prop-is-in-Type-and-Type-is-in-the-next-universe"
]

VerificationTest[
	TypeOf[TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[1]]}, TypeSpecifier[{A} -> A]]]],
	TypeTheoryTerm[TypeUniverse[2]],
	TestID -> "A-dependent-function-type-lives-in-the-larger-universe"
]

VerificationTest[
	TypeOf[TypeTheoryTerm[ForAll[{Typed[A, TypeUniverse[1]]}, Implies[True, True]]]],
	TypeTheoryTerm[TypeUniverse[0]],
	TestID -> "Prop-is-impredicative"
]

VerificationTest[
	FailureQ[TypeTheoryCheck[TypeTheoryTerm[TypeUniverse[1]], TypeTheoryTerm[TypeUniverse[1]]]],
	True,
	TestID -> "Type-is-not-in-Type"
]

VerificationTest[
	First @ TypeOf[TypeTheoryTerm[NaturalNumberSuccessor[True]]],
	"TypeMismatch",
	TestID -> "An-argument-of-the-wrong-type-is-rejected"
]

VerificationTest[
	First @ TypeOf[TypeTheoryTerm[2[3]]],
	"ElaborationFailed",
	TestID -> "Applying-a-non-function-is-rejected"
]


(* === reduction and definitional equality === *)

VerificationTest[
	WeakHeadNormalForm[TypeTheoryTerm[Function[{Typed[x, NonNegativeIntegers]}, x + 1][41]]],
	TypeTheoryTerm[42],
	TestID -> "Beta-reduction-and-literal-addition"
]

VerificationTest[
	WeakHeadNormalForm[TypeTheoryTerm[With[{x = 2}, x + x]]],
	TypeTheoryTerm[4],
	TestID -> "With-binds-a-value"
]

VerificationTest[
	WeakHeadNormalForm[TypeTheoryTerm[Not[True]]],
	TypeTheoryTerm[Implies[True, False]],
	TestID -> "Definitions-unfold"
]

VerificationTest[
	{DefinitionallyEqualQ[TypeTheoryTerm[2 + 3], TypeTheoryTerm[5]], DefinitionallyEqualQ[TypeTheoryTerm[2 + 3], TypeTheoryTerm[6]]},
	{True, False},
	TestID -> "Literals-compute"
]

VerificationTest[
	DefinitionallyEqualQ[TypeTheoryTerm[NaturalNumberSuccessor[NaturalNumberSuccessor[NaturalNumberZero]]], TypeTheoryTerm[2]],
	True,
	TestID -> "A-literal-is-its-constructor-form"
]

VerificationTest[
	DefinitionallyEqualQ[TypeTheoryTerm[NaturalNumberSuccessor[2] + 1], TypeTheoryTerm[4]],
	True,
	TestID -> "Addition-unfolds-on-a-constructor"
]

VerificationTest[
	DefinitionallyEqualQ[TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]}, NaturalNumberSuccessor[n]]], TypeTheoryTerm[NaturalNumberSuccessor]],
	True,
	TestID -> "Eta-equality"
]

VerificationTest[
	TypeTheoryCheck[
		TypeTheoryTerm[Function[{Typed[p, TypeUniverse[0]], Typed[h, p], Typed[k, p]}, EqualityReflexivity[h]]],
		TypeTheoryTerm[ForAll[{Typed[p, TypeUniverse[0]], Typed[h, p], Typed[k, p]}, h == k]]
	],
	True,
	TestID -> "Two-proofs-of-a-proposition-are-equal"
]
