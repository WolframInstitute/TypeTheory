(* ::Package:: *)

(* Tests for Elaboration/Elaboration.wl: implicit arguments, universe levels, binder types taken from
   the expected type, explicit application with Construct, string names, and the errors elaboration
   reports. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

prelude = TypeTheoryEnvironment["Prelude"]


VerificationTest[
	TypeTheoryType[TypeTheoryTerm["equalityReflexivity"["trueIntroduction"], prelude]],
	TypeTheoryTerm["trueIntroduction" == "trueIntroduction", prelude],
	TestID -> "An-implicit-type-argument-is-inferred"
]

VerificationTest[
	TypeTheoryType[TypeTheoryTerm["equalityReflexivity"[NonNegativeIntegers], prelude]],
	TypeTheoryTerm[NonNegativeIntegers == NonNegativeIntegers, prelude],
	TestID -> "A-universe-level-is-inferred"
]

VerificationTest[
	{TypeTheoryType[TypeTheoryTerm[Subscript["equalityReflexivity", 1][3], prelude]], First @ TypeTheoryType[TypeTheoryTerm[Subscript["equalityReflexivity", 0][3], prelude]]},
	{TypeTheoryTerm[3 == 3, prelude], "TypeMismatch"},
	TestID -> "Explicit-universe-levels-with-Subscript"
]

VerificationTest[
	TypeTheoryType[TypeTheoryTerm[Construct["equalityReflexivity", NonNegativeIntegers, 3], prelude]],
	TypeTheoryTerm[3 == 3, prelude],
	TestID -> "Construct-gives-every-argument-explicitly"
]

VerificationTest[
	TypeTheoryType[TypeTheoryTerm[Typed[Function[{x}, x + 1], NonNegativeIntegers -> NonNegativeIntegers], prelude]],
	TypeTheoryTerm[NonNegativeIntegers -> NonNegativeIntegers, prelude],
	TestID -> "A-binder-takes-its-type-from-the-expected-type"
]

VerificationTest[
	TypeTheoryType[TypeTheoryTerm[NonNegativeIntegers -> TypeUniverse[0], prelude]],
	TypeTheoryTerm[TypeUniverse[1], prelude],
	TestID -> "A-rule-is-a-function-type"
]

VerificationTest[
	TypeTheoryType[TypeTheoryTerm[1 + 2 + 3 + 4, prelude]],
	TypeTheoryTerm[NonNegativeIntegers, prelude],
	TestID -> "A-sum-of-several-terms-is-read-left-to-right"
]

VerificationTest[
	{
		TypeTheoryType[TypeTheoryTerm[Exists[{Typed[n, NonNegativeIntegers]}, n + n == 4], prelude]],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm["existsIntroduction"[2, "equalityReflexivity"[4]], prelude], TypeTheoryTerm[Exists[{Typed[n, NonNegativeIntegers]}, n + n == 4]]], _Success]
	},
	{TypeTheoryTerm[TypeUniverse[0], prelude], True},
	TestID -> "A-witness-proves-an-existential-statement"
]

VerificationTest[
	With[{booleans = TypeTheoryEnvironment[{TypeTheoryInductiveType["Bool", TypeUniverse[1], {"Bool.false" -> "Bool", "Bool.true" -> "Bool"}]}]},
		TypeTheoryType[TypeTheoryTerm[Function[{Typed["b", "Bool"]}, "b"], booleans]] === TypeTheoryTerm["Bool" -> "Bool", booleans]
	],
	True,
	TestID -> "Strings-name-constants-and-variables"
]

VerificationTest[
	First /@ {
		TypeTheoryType[TypeTheoryTerm[Unknown, prelude]],
		TypeTheoryType[TypeTheoryTerm[Function[{x}, x], prelude]],
		TypeTheoryType[TypeTheoryTerm[Function[{Typed[x, NonNegativeIntegers]}, "equalityReflexivity"], prelude]],
		TypeTheoryType[TypeTheoryTerm["zero"[1], prelude]]
	},
	{"ElaborationFailed", "ElaborationFailed", "UnsolvedImplicitArgument", "ElaborationFailed"},
	TestID -> "Elaboration-errors-are-Failures"
]

(* A proof where data belongs: the list's element type would be True, a proposition, not a type of TypeUniverse[u].
   The solution that fails is undone, so the expected type is the hole, and the two sorts are named, where the
   message used to read "TrueIntroduction has type True, but the expected type is True". Types of one sort keep the
   plain message. *)
VerificationTest[
	{
		Lookup[Last[TypeTheoryType[TypeTheoryTerm[Prepend["trueIntroduction"][{}], prelude]]], {"MessageTemplate", "MessageParameters"}] /. {template_String, parameters_List} :> {
			StringContainsQ[template, "whose sort is"],
			Length[parameters],
			ToString[parameters[[3]]] =!= "True"
		},
		Length[Last[TypeTheoryType[TypeTheoryTerm[Typed["trueIntroduction", False], prelude]]]["MessageParameters"]]
	},
	{{True, 5, True}, 3},
	TestID -> "A-proof-where-data-belongs-is-told-apart-by-its-sort"
]

VerificationTest[
	MatchQ[TypeTheoryCheck[
		TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]},
			InductiveRecursor[NonNegativeIntegers][
				Function[{Typed[k, NonNegativeIntegers]}, Or[True, k == k]],
				"orIntroductionLeft"["trueIntroduction"],
				Function[{Typed[k, NonNegativeIntegers], Typed[ih, Or[True, k == k]]}, "orIntroductionLeft"["trueIntroduction"]],
				n
			]
		], prelude],
		TypeTheoryTerm[ForAll[{Typed[n, NonNegativeIntegers]}, Or[True, n == n]]]
	], _Success],
	True,
	TestID -> "An-implicit-argument-solved-by-the-expected-type-stays-inside-its-binder"
]

VerificationTest[
	MatchQ[TypeTheoryCheck[
		TypeTheoryTerm[
			Function[
				{
					Typed[f, ForAll[{Typed[h, Exists[Function[{Typed[x, TypeUniverse[0]]}, x]]]}, NonNegativeIntegers]],
					Typed[e1, Exists[Function[{Typed[x, TypeUniverse[0]]}, x]]],
					Typed[e2, Exists[Function[{Typed[x, TypeUniverse[0]]}, x]]]
				},
				Typed["equalityReflexivity"[f[e1]], f[e1] == f[e2]]
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
	], _Success],
	True,
	TestID -> "A-binder-type-enters-the-context-with-the-implicit-arguments-solved-in-it"
]

VerificationTest[
	MatchQ[TypeTheoryCheck[
		TypeTheoryTerm[
			Function[{TypedImplicit[A, TypeUniverse[u]], Typed[P, TypeSpecifier[{A} -> TypeUniverse[0]]], Typed[h, Exists[P]]},
				InductiveRecursor[Exists][
					Function[{Typed[t, Exists[P]]}, And[True, Exists[P]]],
					Function[{Typed[w, A], Typed[k, P[w]]}, "andIntroduction"["trueIntroduction", "existsIntroduction"[w, k]]],
					h
				][[2]]
			],
			prelude
		],
		TypeTheoryTerm[ForAll[{TypedImplicit[A, TypeUniverse[u]], Typed[P, TypeSpecifier[{A} -> TypeUniverse[0]]], Typed[h, Exists[P]]}, Exists[P]]]
	], _Success],
	True,
	TestID -> "A-projection-from-a-term-with-solved-implicit-arguments"
]


(* === overloaded names === *)

VerificationTest[
	{
		TypeTheoryType[TypeTheoryTerm[Typed[True, Booleans]]],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm["trueIntroduction"], TypeTheoryTerm[True]], _Success],
		TypeTheoryType[TypeTheoryTerm[Function[{Typed[b, Booleans]}, b && True]]],
		TypeTheoryType[TypeTheoryTerm[Not[1 == 2]]]
	},
	{TypeTheoryTerm[Booleans, prelude], True, TypeTheoryTerm[Booleans -> Booleans, prelude], TypeTheoryTerm[TypeUniverse[0], prelude]},
	TestID -> "True-and-the-connectives-take-the-meaning-their-type-or-arguments-give"
]

VerificationTest[
	{
		TypeTheoryType[TypeTheoryTerm[Typed[True, Booleans] == False]],
		TypeTheoryType[TypeTheoryTerm[Typed[Identity[Not[False]], Booleans]]],
		TypeTheoryType[TypeTheoryTerm[With[{t = True}, Typed[t, Booleans]]]],
		MatchQ[TypeTheoryCheck[
			TypeTheoryTerm[Function[{Typed[x, TypeUniverse[0]]}, "equalityReflexivity"[True]]],
			TypeTheoryTerm[ForAll[{Typed[x, TypeUniverse[0]]}, Typed[True, TypeUniverse[0]] == True]]
		], _Success]
	},
	{TypeTheoryTerm[TypeUniverse[0], prelude], TypeTheoryTerm[Booleans, prelude], TypeTheoryTerm[Booleans, prelude], True},
	TestID -> "A-name-waits-until-a-later-type-decides-it"
]

VerificationTest[
	First /@ {TypeTheoryType[TypeTheoryTerm[True]], TypeTheoryType[TypeTheoryTerm[True == False]], TypeTheoryType[TypeTheoryTerm[Identity[Not[False]]]], TypeTheoryType[TypeTheoryTerm[And]]},
	{"Ambiguous", "Ambiguous", "Ambiguous", "Ambiguous"},
	TestID -> "A-name-both-meanings-fit-is-ambiguous"
]

VerificationTest[
	TypeTheoryType[TypeTheoryTerm[
		Function[{Typed[B, TypeUniverse[v + 1]]}, Wrapped[B]],
		TypeTheoryEnvironment[TypeTheoryEnvironment[], {
			TypeTheoryInductiveType[Wrapped, ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[x, A]}, TypeUniverse[u + 1]], {
				WrappedIntroduction -> ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[x, A]}, Wrapped[x]]
			}]
		}]
	]][[1]],
	TypeUniverse[v + 1] -> TypeUniverse[v + 2],
	TestID -> "A-universe-level-unifies-with-a-larger-successor"
]

VerificationTest[
	{
		Naturals,
		TypeTheoryType[TypeTheoryTerm[Function[{Typed[n, Naturals]}, n + 1]]] === TypeTheoryType[TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]}, n + 1]]],
		TypeTheoryType[TypeTheoryTerm[InductiveRecursor[Naturals]]] === TypeTheoryType[TypeTheoryTerm[InductiveRecursor[NonNegativeIntegers]]]
	},
	{NonNegativeIntegers, True, True},
	TestID -> "Naturals-stands-for-NonNegativeIntegers"
]

VerificationTest[
	{
		Block[{Counting = NonNegativeIntegers}, TypeTheoryType[TypeTheoryTerm[Function[{Typed[k, Counting]}, k]]]] === TypeTheoryType[TypeTheoryTerm[Function[{Typed[k, NonNegativeIntegers]}, k]]],
		Block[{x = 5}, First[TypeTheoryType[TypeTheoryTerm[x + 1]]]],
		DefinitionallyEqualQ[
			TypeTheoryType[TypeTheoryTerm[Function[{Typed[Naturals, TypeUniverse[1]], Typed[x, Naturals]}, x]]],
			TypeTheoryType[TypeTheoryTerm[Function[{Typed[A, TypeUniverse[1]], Typed[x, A]}, x]]]
		]
	},
	{True, "ElaborationFailed", True},
	TestID -> "A-symbol-whose-value-is-a-constant-stands-for-it-unless-bound"
]

VerificationTest[
	With[
		{
			environment = TypeTheoryEnvironment[TypeTheoryEnvironment[], {
				TypeTheoryAxiom[Symmetric, ForAll[{TypedImplicit[A, TypeUniverse[1]], TypedImplicit[r, TypeSpecifier[{A, A} -> TypeUniverse[0]]], Typed[h, ForAll[{Typed[a, A], Typed[b, A]}, Implies[r[a, b], r[b, a]]]]}, TypeUniverse[0]]],
				TypeTheoryDefinition[SymmetricOf, Function[{Typed[A, TypeUniverse[1]], Typed[r, TypeSpecifier[{A, A} -> TypeUniverse[0]]], Typed[h, ForAll[{Typed[a, A], Typed[b, A]}, Implies[r[a, b], r[b, a]]]]}, Symmetric[h]]]
			}]
		},
		FreeQ[Last[Normal[environment]], HoldPattern[Construct[Symmetric, A, r, h]]]
	],
	False,
	TestID -> "A-pattern-solution-is-eta-reduced"
]

VerificationTest[
	FreeQ[TypeTheoryType[TypeTheoryTerm["functionExtensionality"[Function[{Typed[b, Booleans]}, "equalityReflexivity"["not"[b]]]]]], Function],
	True,
	TestID -> "A-constant-applied-to-the-pattern-variables-solves-as-the-constant"
]

VerificationTest[
	{
		SubsetQ[Select[Keys[prelude], StringQ], {"{}", "and", "booleanEqualityDecidable", "equal", "equalFalse", "equalTrue", "false", "falseDecidable", "falseNotTrue", "lessEqual", "lessEqualFalse", "lessEqualTrue", "not", "or", "Prepend", "true", "trueDecidable", "trueNotFalse", "zero", "successor", "pair", "none", "some", "equalityReflexivity", "joinAssociativity"}],
		Join @@ (Names["WolframInstitute`TypeTheory`" <> #] & /@ {"Boolean*", "EqualityReflexivity", "Pair", "NaturalNumberZero", "JoinAssociativity", "OptionSome", "Lists", "ListPrepend"}),
		WeakHeadNormalForm[TypeTheoryTerm["not"["true"]]] === WeakHeadNormalForm[TypeTheoryTerm[Typed[False, Booleans]]],
		Last[TypeTheoryType[TypeTheoryTerm[True]]["MessageParameters"]],
		Last[TypeTheoryType[TypeTheoryTerm[Not]]["MessageParameters"]]
	},
	{
		True,
		{},
		True,
		"true",
		"not"
	},
	TestID -> "The-constructors-and-the-theorems-of-the-prelude-are-named-by-strings"
]

VerificationTest[
	TypeTheoryType[TypeTheoryTerm[
		Function[{Typed[x, NonNegativeIntegers]}, "none"] == Function[{Typed[y, NonNegativeIntegers]}, Typed["none", Option[Decidable[y == y]]]],
		prelude
	]],
	TypeTheoryTerm[TypeUniverse[0], prelude],
	TestID -> "A-metavariable-left-in-a-function-is-lifted-out-of-its-binders"
]

VerificationTest[
	{
		First @ TypeTheoryType[TypeTheoryTerm[Map[Function[{Typed[n, NonNegativeIntegers]}, "equalityReflexivity"[n]], {}], prelude]],
		TypeTheoryType[TypeTheoryTerm[Typed[Map[Function[{Typed[n, NonNegativeIntegers]}, "none"], {}], {Option[NonNegativeIntegers]}], prelude]]
	},
	{"TypeMismatch", TypeTheoryTerm[{Option[NonNegativeIntegers]}, prelude]},
	TestID -> "A-solution-names-only-variables-in-the-scope-of-its-metavariable"
]

VerificationTest[
	{
		TypeTheoryType[TypeTheoryTerm[Exists[{Typed[x, NonNegativeIntegers], Typed[y, NonNegativeIntegers]}, x + y == 5], prelude]],
		MatchQ[
			TypeTheoryCheck[
				TypeTheoryTerm["existsIntroduction"[2, "existsIntroduction"[3, "equalityReflexivity"[5]]], prelude],
				TypeTheoryTerm[Exists[{Typed[x, NonNegativeIntegers]}, Exists[{Typed[y, NonNegativeIntegers]}, x + y == 5]], prelude]
			],
			_Success
		]
	},
	{TypeTheoryTerm[TypeUniverse[0], prelude], True},
	TestID -> "Exists-with-several-binders-is-one-Exists-in-another"
]

(* a metavariable's solution that names a variable out of its scope only inside a redex is beta reduced: the codomain
   ((t) ↦ N)[o] of a function of o is N, so the function passes where A → ?b is expected, and a getter built with the
   recursor proves the injectivity of "some" *)
VerificationTest[
	{
		DefinitionallyEqualQ[TypeTheoryType[TypeTheoryTerm["equalityCongruence"[Function[{Typed[o, Option[NonNegativeIntegers]]}, Typed[0, Function[{Typed[t, Option[NonNegativeIntegers]]}, NonNegativeIntegers][o]]], "equalityReflexivity"["some"[3]]]]], TypeTheoryTerm[0 == 0]],
		TypeTheoryProof[ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, Implies["some"[m] == "some"[n], m == n]], {
			TypeTheoryTactic["Introduce", m, n, e],
			TypeTheoryTactic["Exact", "equalityCongruence"[Function[{Typed[o, Option[NonNegativeIntegers]]}, InductiveRecursor[Option][Function[{Typed[t, Option[NonNegativeIntegers]]}, NonNegativeIntegers], 0, Function[{Typed[k, NonNegativeIntegers]}, k], o]], e]]
		}]["Goals"]
	},
	{True, {}},
	TestID -> "A-solution-out-of-scope-only-inside-a-redex-is-beta-reduced"
]

(* a variable written without a type takes the type its body gives it, as Lean leaves a binder's type to unification *)
VerificationTest[
	{
		First[WeakHeadNormalForm[TypeTheoryTerm[ForAll[{n}, n + 0 == n]]]],
		First[WeakHeadNormalForm[TypeTheoryTerm[ForAll[n, n + 0 == n]]]],
		First[TypeTheoryType[TypeTheoryTerm[Function[{x}, x + 1]]]],
		MatchQ[TypeTheoryEnvironment[{TypeTheoryTheorem[AddZeroUntyped, ForAll[{n}, n + 0 == n], Function[{n}, "equalityReflexivity"[n]]]}], _TypeTheoryEnvironment],
		TypeTheoryType[TypeTheoryTerm[ForAll[{x}, x == x]]]["Tag"]
	},
	{
		ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n],
		ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n],
		NonNegativeIntegers -> NonNegativeIntegers,
		True,
		"ElaborationFailed"
	},
	TestID -> "A-binder-without-a-type-takes-the-type-its-body-gives-it"
]

(* ForAll[x, condition, body] and Exists[x, condition, body] read as in the Wolfram Language *)
VerificationTest[
	{
		First[WeakHeadNormalForm[TypeTheoryTerm[ForAll[{Typed[n, Naturals]}, 1 <= n, 0 < n]]]],
		First[WeakHeadNormalForm[TypeTheoryTerm[Exists[{Typed[n, Naturals]}, 1 <= n, n == 2]]]],
		First[WeakHeadNormalForm[TypeTheoryTerm[ForAll[n, 1 <= n, 0 < n]]]]
	},
	{
		ForAll[{Typed[n, NonNegativeIntegers]}, Implies[1 <= n, 0 < n]],
		Exists[{Typed[n, NonNegativeIntegers]}, 1 <= n && n == 2],
		ForAll[{Typed[n, NonNegativeIntegers]}, Implies[1 <= n, 0 < n]]
	},
	TestID -> "ForAll-and-Exists-with-a-condition-read-as-in-the-Wolfram-Language"
]

(* a list written as a term is the list of its elements, as a list ending in {} shows *)
VerificationTest[
	{
		First[TypeTheoryType[TypeTheoryTerm[{1, 2}]]],
		First[WeakHeadNormalForm[TypeTheoryTerm[Length[{1, 2, 3}]]]],
		DefinitionallyEqualQ[TypeTheoryTerm[Reverse[{1, 2}]], TypeTheoryTerm[{2, 1}]],
		DefinitionallyEqualQ[TypeTheoryTerm[{1, 2}], TypeTheoryTerm[Prepend[1][Prepend[2][{}]]]],
		First[TypeTheoryType[TypeTheoryTerm[Typed[{}, {Naturals}]]]],
		TypeTheoryType[TypeTheoryTerm[{1}, TypeTheoryEnvironment[]]]["Tag"]
	},
	{{NonNegativeIntegers}, 3, True, True, {NonNegativeIntegers}, "ElaborationFailed"},
	TestID -> "A-list-written-as-a-term-is-the-list-of-its-elements"
]

(* A variable written without a type whose sort nothing decides: a theorem's statement is a proposition where it can be,
   so p is a proposition; a level left over becomes a universe parameter u_1 of the declaration, as Lean binds one; a
   term on its own, which has no parameters, takes Type; a variable whose type nothing decides is still asked for. A
   declaration reads back without the option "UniverseParameters" where Automatic gives the same list. *)
VerificationTest[
	With[
		{
			environment = TypeTheoryEnvironment[prelude, {
				TypeTheoryTheorem[ClassicalSelfImplication, ForAll[{p}, Implies[p, p]], Function[{p, h}, h]],
				TypeTheoryAxiom[PolymorphicIdentity, ForAll[{a}, a -> a]],
				TypeTheoryTheorem[PolymorphicSelfEquality, ForAll[{A, Typed[x, A]}, x == x], Function[{A, Typed[x, A]}, "equalityReflexivity"[x]]]
			}]
		},
		{
			environment[ClassicalSelfImplication],
			environment[PolymorphicIdentity],
			Length[environment[PolymorphicSelfEquality]],
			TypeTheoryProof[ForAll[{p}, Implies[p, p]], prelude, {TypeTheoryTactic["Introduce"], TypeTheoryTactic["Introduce"], TypeTheoryTactic["Assumption"]}]["Goals"],
			First[TypeTheoryType[TypeTheoryTerm[Function[{a}, Function[Typed[x, a], x]], prelude]]],
			First[TypeTheoryType[TypeTheoryTerm[ForAll[{a}, a == a], prelude]]]
		}
	],
	{
		TypeTheoryTheorem[ClassicalSelfImplication, ForAll[{Typed[p, TypeUniverse[0]]}, Implies[p, p]], Function[{Typed[p, TypeUniverse[0]], Typed[h, p]}, h]],
		TypeTheoryAxiom[PolymorphicIdentity, ForAll[{Typed[a, TypeUniverse["u_1"]]}, a -> a]],
		3,
		{},
		ForAll[{Typed[a, TypeUniverse[1]]}, a -> a],
		"ElaborationFailed"
	},
	TestID -> "A-level-nothing-decides-is-Prop-a-universe-parameter-or-Type"
]

(* a binder of a type Sequence[...] takes the arguments that are left as one Sequence, as the Wolfram Language applies a
   function to its arguments, and its type gives how many; one argument that is a sequence already is the sequence
   itself, a Sequence among the elements is spliced, and a curried function takes one argument at a time. The type
   Sequence[A, B] is the family at the list of its types, Sequence[As], As a list of types, at As, and Sequence[{A}]
   the sequences of one list of A *)
VerificationTest[
	With[
		{
			pairs = TypeTheoryEnvironment[TypeTheoryEnvironment["WolframLanguage"], {
				TypeTheoryAxiom[sum, Sequence[NonNegativeIntegers, NonNegativeIntegers] -> NonNegativeIntegers],
				TypeTheoryAxiom[curried, Sequence[NonNegativeIntegers] -> Sequence[NonNegativeIntegers] -> NonNegativeIntegers]
			}]
		},
		{
			Replace[TypeTheoryType[TypeTheoryTerm[Sequence[1, Typed[2, Expressions]], pairs]], TypeTheoryTerm[type_, ___] :> HoldComplete[type]],
			DefinitionallyEqualQ[TypeTheoryTerm[sum[1, 2], pairs], TypeTheoryTerm[sum[Sequence[1, 2]], pairs]],
			DefinitionallyEqualQ[TypeTheoryTerm[Function[{Typed[s, Sequence[NonNegativeIntegers, NonNegativeIntegers]]}, sum[s]][Sequence[1, 2]], pairs], TypeTheoryTerm[sum[1, 2], pairs]],
			DefinitionallyEqualQ[TypeTheoryTerm[Sequence[1, Sequence[2, 3]], pairs], TypeTheoryTerm["sequencePrepend"[1, "sequencePrepend"[2, "sequencePrepend"[3, "emptySequence"]]], pairs]],
			First[TypeTheoryType[TypeTheoryTerm[sum[1], pairs]]],
			First[TypeTheoryType[TypeTheoryTerm[curried[1][2], pairs]]],
			First[TypeTheoryType[TypeTheoryTerm[curried[1, 2], pairs]]],
			DefinitionallyEqualQ[TypeTheoryTerm[Join[{1}, {2}], pairs], TypeTheoryTerm[{1, 2}, pairs]],
			DefinitionallyEqualQ[TypeTheoryTerm[Sequence[NonNegativeIntegers, Expressions], pairs], TypeTheoryTerm[Sequence[Prepend[NonNegativeIntegers][Prepend[Expressions][{}]]], pairs]],
			DefinitionallyEqualQ[TypeTheoryTerm[Sequence[NonNegativeIntegers], pairs], TypeTheoryTerm[Sequence[{NonNegativeIntegers}], pairs]],
			First[TypeTheoryType[TypeTheoryTerm[Function[{Typed[As, {TypeUniverse[1]}]}, Sequence[As]], pairs]]]
		}
	],
	{
		HoldComplete[Sequence[NonNegativeIntegers, Expressions]], True, True, True, "TypeMismatch", NonNegativeIntegers, "TypeMismatch", True, True, False,
		{TypeUniverse[1]} -> TypeUniverse[2]
	},
	TestID -> "A-Sequence-binder-takes-the-arguments-that-are-left-as-one-Sequence"
]

(* a term held in a symbol and read in another environment keeps the meaning of its own environment's constants: one the
   other environment does not declare is refused, as a string-named constant would otherwise be read as a string, and the
   term reads as itself in its own environment or one that extends it *)
VerificationTest[
	With[{cited = TypeTheoryEnvironment[{TypeTheoryAxiom["_example", 2 + 2 == 4], TypeTheoryAxiom[Foreign, NonNegativeIntegers]}]},
		Block[{proof = TypeTheoryTerm["_example", cited], number = TypeTheoryTerm[Foreign + 1, cited]},
			{
				First[TypeTheoryType[Typed[proof, 2 + 2 == 4]]],
				First[TypeTheoryType[number + 1]],
				First[TypeTheoryType[proof, TypeTheoryEnvironment["Prelude"]]],
				DefinitionallyEqualQ[TypeTheoryType[Typed[proof, 2 + 2 == 4], cited], TypeTheoryTerm[2 + 2 == 4, cited]],
				DefinitionallyEqualQ[TypeTheoryType[number + 1, TypeTheoryEnvironment[cited, {TypeTheoryAxiom[Other, NonNegativeIntegers]}]], TypeTheoryTerm[NonNegativeIntegers]]
			}
		]
	],
	{"ElaborationFailed", "ElaborationFailed", "ElaborationFailed", True, True},
	TestID -> "A-term-read-in-another-environment-keeps-its-constants"
]

(* body & is a pure function of its slots, with as many arguments as the type expected takes and at least as many as its
   highest slot; a binder whose type comes from the type expected has it with its redexes reduced, as a recursor's case
   of the motive applied *)
VerificationTest[
	With[
		{
			counted = TypeTheoryEnvironment[{
				TypeTheoryInductiveType[BinaryTree, TypeUniverse[1], {BinaryLeaf -> BinaryTree, BinaryNode -> ForAll[{Typed[left, BinaryTree], Typed[right, BinaryTree]}, BinaryTree]}],
				TypeTheoryDefinition[NodeCount, tree |-> InductiveRecursor[BinaryTree][Naturals &, 1, #3 + #4 + 1 &, tree]]
			}]
		},
		{
			DefinitionallyEqualQ[TypeTheoryTerm[NodeCount[BinaryNode[BinaryLeaf, BinaryNode[BinaryLeaf, BinaryLeaf]]], counted], TypeTheoryTerm[5, counted]],
			DefinitionallyEqualQ[TypeTheoryType[Typed[n, NonNegativeIntegers] |-> (# + n &)[1]], TypeTheoryTerm[NonNegativeIntegers -> NonNegativeIntegers]],
			DefinitionallyEqualQ[TypeTheoryType[Typed[#1 + (#1 &)[2] &, NonNegativeIntegers -> NonNegativeIntegers]], TypeTheoryTerm[NonNegativeIntegers -> NonNegativeIntegers]],
			FreeQ[counted[NodeCount], HoldPattern[Function[{_}, NonNegativeIntegers][_]]]
		}
	],
	{True, True, True, True},
	TestID -> "A-pure-function-of-slots-and-binder-types-without-redexes"
]
