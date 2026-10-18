(* ::Package:: *)

(* Tests for Checking/InductiveTypes.wl: declaring inductive families, the checks that reject unsound
   ones, and the generated recursors. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

prelude = TypeTheoryEnvironment["Prelude"]


(* === accepted declarations === *)

VerificationTest[
	With[
		{
			lists = TypeTheoryEnvironment[prelude, {
				TypeTheoryInductiveType[NaturalList, TypeUniverse[1], {EmptyList -> NaturalList, ConsList -> ForAll[{Typed[h, NonNegativeIntegers], Typed[t, NaturalList]}, NaturalList]}],
				TypeTheoryDefinition[
					ListLength,
					Typed[
						Function[{Typed[l, NaturalList]},
							InductiveRecursor[NaturalList][
								Function[{Typed[x, NaturalList]}, NonNegativeIntegers],
								0,
								Function[{Typed[h, NonNegativeIntegers], Typed[t, NaturalList], Typed[r, NonNegativeIntegers]}, r + 1],
								l
							]
						],
						TypeSpecifier[{NaturalList} -> NonNegativeIntegers]
					]
				]
			}]
		},
		WeakHeadNormalForm[TypeTheoryTerm[ListLength[ConsList[5, ConsList[6, ConsList[7, EmptyList]]]], lists]] === TypeTheoryTerm[3, lists]
	],
	True,
	TestID -> "A-recursor-computes-on-constructors"
]

VerificationTest[
	With[
		{
			lists = Append[prelude, TypeTheoryInductiveType[
				PolymorphicList,
				ForAll[{Typed[A, TypeUniverse[u + 1]]}, TypeUniverse[u + 1]],
				{
					PolymorphicEmpty -> ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, PolymorphicList[A]],
					PolymorphicCons -> ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[h, A], Typed[t, PolymorphicList[A]]}, PolymorphicList[A]]
				}
			]]
		},
		TypeOf[TypeTheoryTerm[PolymorphicCons[1, PolymorphicEmpty], lists]] === TypeTheoryTerm[PolymorphicList[NonNegativeIntegers], lists]
	],
	True,
	TestID -> "A-parameter-is-found-and-inferred-at-each-use"
]

VerificationTest[
	With[
		{
			vectors = Append[prelude, TypeTheoryInductiveType[
				NaturalVector,
				ForAll[{Typed[n, NonNegativeIntegers]}, TypeUniverse[1]],
				{
					VectorEmpty -> NaturalVector[0],
					VectorCons -> ForAll[{TypedImplicit[n, NonNegativeIntegers], Typed[h, NonNegativeIntegers], Typed[t, NaturalVector[n]]}, NaturalVector[n + 1]]
				}
			]]
		},
		{
			TypeTheoryCheck[TypeTheoryTerm[VectorCons[1, VectorCons[2, VectorEmpty]], vectors], TypeTheoryTerm[NaturalVector[2]]],
			FailureQ @ TypeTheoryCheck[TypeTheoryTerm[VectorCons[1, VectorEmpty], vectors], TypeTheoryTerm[NaturalVector[2]]]
		}
	],
	{True, True},
	TestID -> "An-index-is-checked-by-computation"
]


(* === rejected declarations === *)

VerificationTest[
	First @ Append[prelude, TypeTheoryInductiveType[Bad, TypeUniverse[1], {BadIntroduction -> ForAll[{Typed[f, TypeSpecifier[{Bad} -> False]]}, Bad]}]],
	"NonPositiveOccurrence",
	TestID -> "A-negative-occurrence-is-rejected"
]

VerificationTest[
	First @ Append[prelude, TypeTheoryInductiveType[Big, TypeUniverse[1], {BigIntroduction -> ForAll[{Typed[t, TypeUniverse[1]]}, Big]}]],
	"UniverseTooLarge",
	TestID -> "A-field-in-a-larger-universe-is-rejected"
]

VerificationTest[
	First @ Append[prelude, TypeTheoryInductiveType[Odd, TypeUniverse[1], {OddIntroduction -> NonNegativeIntegers}]],
	"ConstructorResult",
	TestID -> "A-constructor-must-build-its-own-type"
]

VerificationTest[
	First @ Append[prelude, TypeTheoryInductiveType[Twice, TypeUniverse[1], {TwiceIntroduction -> Twice, TwiceIntroduction -> Twice}]],
	"DuplicateConstructor",
	TestID -> "Constructor-names-must-be-distinct"
]


(* === elimination === *)

VerificationTest[
	First @ TypeTheoryCheck[TypeTheoryTerm[InductiveRecursor[Or][
		Function[{Typed[t, Or[True, True]]}, NonNegativeIntegers],
		Function[{Typed[p, True]}, 0],
		Function[{Typed[q, True]}, 1],
		OrIntroductionLeft[TrueIntroduction]
	], prelude]],
	"TypeMismatch",
	TestID -> "A-proof-of-a-disjunction-cannot-choose-a-number"
]

VerificationTest[
	WeakHeadNormalForm[TypeTheoryTerm[InductiveRecursor[And][
		Function[{Typed[t, And[True, True]]}, NonNegativeIntegers],
		Function[{Typed[p, True], Typed[q, True]}, 7],
		AndIntroduction[TrueIntroduction, TrueIntroduction]
	], prelude]],
	TypeTheoryTerm[7, prelude],
	TestID -> "A-conjunction-eliminates-into-any-universe"
]

VerificationTest[
	TypeTheoryCheck[
		TypeTheoryTerm[Function[{Typed[h, 2 + 2 == 4]}, InductiveRecursor[Equal][Function[{Typed[y, NonNegativeIntegers], Typed[e, 4 == y]}, NonNegativeIntegers], 7, h]], prelude],
		TypeTheoryTerm[TypeSpecifier[{2 + 2 == 4} -> NonNegativeIntegers]]
	],
	True,
	TestID -> "Equality-eliminates-into-any-universe"
]

VerificationTest[
	DefinitionallyEqualQ[
		TypeTheoryTerm[Function[{Typed[h, 4 == 4]}, InductiveRecursor[Equal][Function[{Typed[y, NonNegativeIntegers], Typed[e, 4 == y]}, NonNegativeIntegers], 7, h]], prelude],
		TypeTheoryTerm[Function[{Typed[h, 4 == 4]}, 7]]
	],
	True,
	TestID -> "The-equality-recursor-reduces-on-any-proof"
]
