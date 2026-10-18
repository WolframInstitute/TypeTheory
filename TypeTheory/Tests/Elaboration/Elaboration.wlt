(* ::Package:: *)

(* Tests for Elaboration/Elaboration.wl: implicit arguments, universe levels, binder types taken from
   the expected type, explicit application with Construct, string names, and the errors elaboration
   reports. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

prelude = TypeTheoryEnvironment["Prelude"]


VerificationTest[
	TypeOf[TypeTheoryTerm[EqualityReflexivity[TrueIntroduction], prelude]],
	TypeTheoryTerm[TrueIntroduction == TrueIntroduction, prelude],
	TestID -> "An-implicit-type-argument-is-inferred"
]

VerificationTest[
	TypeOf[TypeTheoryTerm[EqualityReflexivity[NonNegativeIntegers], prelude]],
	TypeTheoryTerm[NonNegativeIntegers == NonNegativeIntegers, prelude],
	TestID -> "A-universe-level-is-inferred"
]

VerificationTest[
	{TypeOf[TypeTheoryTerm[Subscript[EqualityReflexivity, 1][3], prelude]], First @ TypeOf[TypeTheoryTerm[Subscript[EqualityReflexivity, 0][3], prelude]]},
	{TypeTheoryTerm[3 == 3, prelude], "TypeMismatch"},
	TestID -> "Explicit-universe-levels-with-Subscript"
]

VerificationTest[
	TypeOf[TypeTheoryTerm[Construct[EqualityReflexivity, NonNegativeIntegers, 3], prelude]],
	TypeTheoryTerm[3 == 3, prelude],
	TestID -> "Construct-gives-every-argument-explicitly"
]

VerificationTest[
	TypeOf[TypeTheoryTerm[Typed[Function[{x}, x + 1], TypeSpecifier[{NonNegativeIntegers} -> NonNegativeIntegers]], prelude]],
	TypeTheoryTerm[TypeSpecifier[{NonNegativeIntegers} -> NonNegativeIntegers], prelude],
	TestID -> "A-binder-takes-its-type-from-the-expected-type"
]

VerificationTest[
	TypeOf[TypeTheoryTerm[NonNegativeIntegers -> TypeUniverse[0], prelude]],
	TypeTheoryTerm[TypeUniverse[1], prelude],
	TestID -> "A-rule-is-a-function-type"
]

VerificationTest[
	TypeOf[TypeTheoryTerm[1 + 2 + 3 + 4, prelude]],
	TypeTheoryTerm[NonNegativeIntegers, prelude],
	TestID -> "A-sum-of-several-terms-is-read-left-to-right"
]

VerificationTest[
	{
		TypeOf[TypeTheoryTerm[Exists[{Typed[n, NonNegativeIntegers]}, n + n == 4], prelude]],
		TypeTheoryCheck[TypeTheoryTerm[ExistsIntroduction[2, EqualityReflexivity[4]], prelude], TypeTheoryTerm[Exists[{Typed[n, NonNegativeIntegers]}, n + n == 4]]]
	},
	{TypeTheoryTerm[TypeUniverse[0], prelude], True},
	TestID -> "A-witness-proves-an-existential-statement"
]

VerificationTest[
	With[{booleans = TypeTheoryEnvironment[{TypeTheoryInductiveType["Bool", TypeUniverse[1], {"Bool.false" -> "Bool", "Bool.true" -> "Bool"}]}]},
		TypeOf[TypeTheoryTerm[Function[{Typed["b", "Bool"]}, "b"], booleans]] === TypeTheoryTerm[TypeSpecifier[{"Bool"} -> "Bool"], booleans]
	],
	True,
	TestID -> "Strings-name-constants-and-variables"
]

VerificationTest[
	First /@ {
		TypeOf[TypeTheoryTerm[Unknown, prelude]],
		TypeOf[TypeTheoryTerm[Function[{x}, x], prelude]],
		TypeOf[TypeTheoryTerm[Function[{Typed[x, NonNegativeIntegers]}, EqualityReflexivity], prelude]],
		TypeOf[TypeTheoryTerm[NaturalNumberZero[1], prelude]]
	},
	{"ElaborationFailed", "ElaborationFailed", "UnsolvedImplicitArgument", "ElaborationFailed"},
	TestID -> "Elaboration-errors-are-Failures"
]

VerificationTest[
	TypeTheoryCheck[
		TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]},
			InductiveRecursor[NonNegativeIntegers][
				Function[{Typed[k, NonNegativeIntegers]}, Or[True, k == k]],
				OrIntroductionLeft[TrueIntroduction],
				Function[{Typed[k, NonNegativeIntegers], Typed[ih, Or[True, k == k]]}, OrIntroductionLeft[TrueIntroduction]],
				n
			]
		], prelude],
		TypeTheoryTerm[ForAll[{Typed[n, NonNegativeIntegers]}, Or[True, n == n]]]
	],
	True,
	TestID -> "An-implicit-argument-solved-by-the-expected-type-stays-inside-its-binder"
]

VerificationTest[
	TypeTheoryCheck[
		TypeTheoryTerm[
			Function[
				{
					Typed[f, ForAll[{Typed[h, Exists[Function[{Typed[x, TypeUniverse[0]]}, x]]]}, NonNegativeIntegers]],
					Typed[e1, Exists[Function[{Typed[x, TypeUniverse[0]]}, x]]],
					Typed[e2, Exists[Function[{Typed[x, TypeUniverse[0]]}, x]]]
				},
				Typed[EqualityReflexivity[f[e1]], f[e1] == f[e2]]
			],
			prelude
		],
		TypeTheoryTerm[ForAll[
			{
				Typed[f, ForAll[{Typed[h, Exists[Function[{Typed[x, TypeUniverse[0]]}, x]]]}, NonNegativeIntegers]],
				Typed[e1, Exists[Function[{Typed[x, TypeUniverse[0]]}, x]]],
				Typed[e2, Exists[Function[{Typed[x, TypeUniverse[0]]}, x]]]
			},
			f[e1] == f[e2]
		]]
	],
	True,
	TestID -> "A-binder-type-enters-the-context-with-the-implicit-arguments-solved-in-it"
]

VerificationTest[
	TypeTheoryCheck[
		TypeTheoryTerm[
			Function[{TypedImplicit[A, TypeUniverse[u]], Typed[P, TypeSpecifier[{A} -> TypeUniverse[0]]], Typed[h, Exists[P]]},
				InductiveRecursor[Exists][
					Function[{Typed[t, Exists[P]]}, And[True, Exists[P]]],
					Function[{Typed[w, A], Typed[k, P[w]]}, AndIntroduction[TrueIntroduction, ExistsIntroduction[w, k]]],
					h
				][[2]]
			],
			prelude
		],
		TypeTheoryTerm[ForAll[{Annotation[Typed[A, TypeUniverse[u]], "Implicit"], Typed[P, TypeSpecifier[{A} -> TypeUniverse[0]]], Typed[h, Exists[P]]}, Exists[P]]]
	],
	True,
	TestID -> "A-projection-from-a-term-with-solved-implicit-arguments"
]


(* === overloaded names === *)

VerificationTest[
	{
		TypeOf[TypeTheoryTerm[Typed[True, Booleans]]],
		TypeTheoryCheck[TypeTheoryTerm[TrueIntroduction], TypeTheoryTerm[True]],
		TypeOf[TypeTheoryTerm[Function[{Typed[b, Booleans]}, b && True]]],
		TypeOf[TypeTheoryTerm[Not[1 == 2]]]
	},
	{TypeTheoryTerm[Booleans, prelude], True, TypeTheoryTerm[TypeSpecifier[{Booleans} -> Booleans], prelude], TypeTheoryTerm[TypeUniverse[0], prelude]},
	TestID -> "True-and-the-connectives-take-the-meaning-their-type-or-arguments-give"
]

VerificationTest[
	{
		TypeOf[TypeTheoryTerm[Typed[True, Booleans] == False]],
		TypeOf[TypeTheoryTerm[Typed[Identity[Not[False]], Booleans]]],
		TypeOf[TypeTheoryTerm[With[{t = True}, Typed[t, Booleans]]]],
		TypeTheoryCheck[
			TypeTheoryTerm[Function[{Typed[x, TypeUniverse[0]]}, EqualityReflexivity[True]]],
			TypeTheoryTerm[ForAll[{Typed[x, TypeUniverse[0]]}, Typed[True, TypeUniverse[0]] == True]]
		]
	},
	{TypeTheoryTerm[TypeUniverse[0], prelude], TypeTheoryTerm[Booleans, prelude], TypeTheoryTerm[Booleans, prelude], True},
	TestID -> "A-name-waits-until-a-later-type-decides-it"
]

VerificationTest[
	First /@ {TypeOf[TypeTheoryTerm[True]], TypeOf[TypeTheoryTerm[True == False]], TypeOf[TypeTheoryTerm[Identity[Not[False]]]], TypeOf[TypeTheoryTerm[And]]},
	{"Ambiguous", "Ambiguous", "Ambiguous", "Ambiguous"},
	TestID -> "A-name-both-meanings-fit-is-ambiguous"
]

VerificationTest[
	TypeOf[TypeTheoryTerm[
		Function[{Typed[B, TypeUniverse[v + 1]]}, Wrapped[B]],
		TypeTheoryEnvironment[TypeTheoryEnvironment[], {
			TypeTheoryInductiveType[Wrapped, ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[x, A]}, TypeUniverse[u + 1]], {
				WrappedIntroduction -> ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[x, A]}, Wrapped[x]]
			}]
		}]
	]][[1]],
	TypeSpecifier[{TypeUniverse[v + 1]} -> TypeUniverse[v + 2]],
	TestID -> "A-universe-level-unifies-with-a-larger-successor"
]
