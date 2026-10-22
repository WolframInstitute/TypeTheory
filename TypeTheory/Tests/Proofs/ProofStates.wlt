(* ::Package:: *)

(* Tests for Proofs/ProofStates.wl: proof states, the tactics, and the acceptance examples n + 0 == n by
   computation and 0 + n == n by induction. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

prelude = TypeTheoryEnvironment["Prelude"]

zeroLeft = TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, 0 + n == n], prelude, {
	TypeTheoryTactic["Introduce", n],
	TypeTheoryTactic["Induction", n],
	TypeTheoryTactic["Reflexivity"],
	TypeTheoryTactic["Introduce", k, ih],
	TypeTheoryTactic["Exact", EqualityCongruence[NaturalNumberSuccessor, ih]]
}]


VerificationTest[
	TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n], prelude]["Goals"],
	{TypeTheoryTerm[RightTee[{}, ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n]], prelude]},
	TestID -> "A-proof-starts-with-its-statement-as-the-goal"
]

VerificationTest[
	TypeTheoryProof[TypeTheoryTerm[ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n], prelude]]["Goals"],
	{TypeTheoryTerm[RightTee[{}, ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n]], prelude]},
	TestID -> "A-proof-of-a-TypeTheoryTerm-takes-its-environment"
]

VerificationTest[
	TypeTheoryTactic["Introduce", n][TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n], prelude]]["Goals"],
	{TypeTheoryTerm[RightTee[{Typed[n, NonNegativeIntegers]}, n + 0 == n], prelude]},
	TestID -> "Introduce-moves-a-variable-into-the-hypotheses"
]

VerificationTest[
	With[
		{
			proved = Append[prelude, TypeTheoryTheorem[
				ZeroRightIdentity,
				TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n], prelude, {TypeTheoryTactic["Introduce", n], TypeTheoryTactic["Reflexivity"]}]
			]]
		},
		TypeOf[TypeTheoryTerm[ZeroRightIdentity, proved]] === TypeTheoryTerm[ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n], proved]
	],
	True,
	TestID -> "n-plus-zero-is-n-by-computation"
]

VerificationTest[
	TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n], {TypeTheoryTactic["Introduce", n], TypeTheoryTactic["Reflexivity"]}]["Goals"],
	{},
	TestID -> "A-proof-without-an-environment-is-in-the-prelude"
]

VerificationTest[
	First @ TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, 0 + n == n], prelude, {TypeTheoryTactic["Introduce", n], TypeTheoryTactic["Reflexivity"]}],
	"NotReflexive",
	TestID -> "zero-plus-n-is-not-n-by-computation"
]

VerificationTest[
	With[
		{
			equations = TypeTheoryEnvironment[TypeTheoryEnvironment[], {
				TypeTheoryInductiveType["Unit", TypeUniverse[1], {"Unit.unit" -> "Unit"}],
				TypeTheoryInductiveType[
					"Eq",
					ForAll[{TypedImplicit[A, TypeUniverse[u]], Typed[x, A], Typed[y, A]}, TypeUniverse[0]],
					{"Eq.refl" -> ForAll[{TypedImplicit[A, TypeUniverse[u]], Typed[x, A]}, "Eq"[x, x]]}
				]
			}]
		},
		{
			TypeTheoryProof[TypeTheoryTerm["Eq"["Unit.unit", "Unit.unit"], equations], {TypeTheoryTactic["Reflexivity"]}]["Goals"],
			First @ TypeTheoryProof[TypeTheoryTerm["Unit", equations], {TypeTheoryTactic["Reflexivity"]}]
		}
	],
	{{}, "EquationExpected"},
	TestID -> "Reflexivity-solves-an-equation-of-another-type-of-equations"
]

VerificationTest[
	TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, 0 + n == n], prelude, {TypeTheoryTactic["Introduce", n], TypeTheoryTactic["Induction", n]}]["Goals"],
	With[{n = WolframInstitute`TypeTheory`Library`Prelude`Private`n},
		{
			TypeTheoryTerm[RightTee[{}, 0 + NaturalNumberZero == NaturalNumberZero], prelude],
			TypeTheoryTerm[RightTee[{}, ForAll[{Typed[n, NonNegativeIntegers]}, Implies[0 + n == n, 0 + NaturalNumberSuccessor[n] == NaturalNumberSuccessor[n]]]], prelude]
		}
	],
	TestID -> "Induction-gives-a-goal-per-constructor"
]

VerificationTest[
	zeroLeft["Goals"],
	{},
	TestID -> "zero-plus-n-is-n-by-induction"
]

VerificationTest[
	With[
		{
			proved = TypeTheoryEnvironment[prelude, {
				TypeTheoryTheorem[ZeroLeftIdentity, zeroLeft],
				TypeTheoryTheorem[ZeroLeftIdentityAgain, ForAll[{Typed[m, NonNegativeIntegers]}, 0 + m == m], zeroLeft]
			}]
		},
		{
			MatchQ[TypeTheoryCheck[TypeTheoryTerm[ZeroLeftIdentity[7], proved], TypeTheoryTerm[0 + 7 == 7]], _Success],
			TypeOf[TypeTheoryTerm[ZeroLeftIdentityAgain, proved]] === TypeTheoryTerm[ForAll[{Typed[m, NonNegativeIntegers]}, 0 + m == m], proved],
			MatchQ[TypeTheoryCheck[proved], _Success]
		}
	],
	{True, True, True},
	TestID -> "A-finished-proof-is-declared-and-used"
]

VerificationTest[
	TypeTheoryProof[ForAll[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]]}, Implies[a, Implies[b, And[a, b]]]], prelude, {
		TypeTheoryTactic["Introduce", a, b, ha, hb],
		TypeTheoryTactic["Apply", AndIntroduction],
		TypeTheoryTactic["Assumption"],
		TypeTheoryTactic["Exact", hb]
	}]["Term"],
	TypeTheoryTerm[Function[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]], Typed[ha, a], Typed[hb, b]}, AndIntroduction[ha, hb]], prelude],
	TestID -> "Apply-leaves-a-goal-per-argument"
]

VerificationTest[
	TypeTheoryProof[ForAll[{Typed[x, NonNegativeIntegers], Typed[y, NonNegativeIntegers], Typed[z, NonNegativeIntegers]}, Implies[x == y, Implies[y == z, x == z]]], prelude, {
		TypeTheoryTactic["Introduce", x, y, z, h1, h2],
		TypeTheoryTactic["Apply", EqualityTransitivity],
		TypeTheoryTactic["Exact", h1],
		TypeTheoryTactic["Exact", h2]
	}]["Goals"],
	{},
	TestID -> "Solving-a-goal-can-solve-another-goal-it-mentions"
]

VerificationTest[
	TypeTheoryProof[ForAll[{Typed[p, TypeUniverse[0]]}, Implies[p, Not[Not[p]]]], prelude, {
		TypeTheoryTactic["Introduce", p, hp, hnp],
		TypeTheoryTactic["Exact", hnp[hp]]
	}]["Goals"],
	{},
	TestID -> "Introduce-unfolds-Not"
]

VerificationTest[
	First /@ {
		TypeTheoryTactic["Introduce", x][TypeTheoryProof[2 + 2 == 4, prelude]],
		TypeTheoryTactic["Bogus"][TypeTheoryProof[2 + 2 == 4, prelude]],
		TypeTheoryTactic["Exact", EqualityReflexivity[5]][TypeTheoryProof[2 + 2 == 4, prelude]],
		TypeTheoryTactic["Reflexivity"][TypeTheoryProof[2 + 2 == 5, prelude]],
		TypeTheoryTactic["Reflexivity"][TypeTheoryTactic["Reflexivity"][TypeTheoryProof[2 + 2 == 4, prelude]]]
	},
	{"NothingToIntroduce", "UnknownTactic", "TypeMismatch", "NotReflexive", "NoGoals"},
	TestID -> "A-tactic-that-does-not-apply-gives-a-Failure"
]

VerificationTest[
	First @ Append[prelude, TypeTheoryTheorem[Absurd, TypeTheoryProof[False, prelude]]],
	"ProofIncomplete",
	TestID -> "An-unfinished-proof-cannot-be-declared"
]

VerificationTest[
	MatchQ[ToBoxes[zeroLeft], InterpretationBox[_FrameBox, _TypeTheoryProof]] && MatchQ[ToBoxes[TypeTheoryProof[2 + 2 == 4, prelude]], InterpretationBox[_FrameBox, _TypeTheoryProof]],
	True,
	TestID -> "A-proof-displays-its-goals"
]

VerificationTest[
	ToExpression[ToBoxes[zeroLeft]] === zeroLeft,
	True,
	TestID -> "A-proof-display-is-interpreted-as-the-proof"
]

VerificationTest[
	{
		TypeTheoryCheck[TypeTheoryTerm[EqualityReflexivity[4], prelude], TypeTheoryTerm[2 + 2 == 4]][[1]],
		TypeTheoryCheck[TypeTheoryEnvironment[{TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, EqualityReflexivity[4]]}]][[1]]
	},
	{"TypeChecked", "EnvironmentChecked"},
	TestID -> "A-check-that-passes-gives-a-Success"
]

(* Rewrite, Constructor, Cases, Generalize, and induction on families and with dependent hypotheses *)

rewritten = TypeTheoryProof[ForAll[{Typed[x, NonNegativeIntegers], Typed[y, NonNegativeIntegers]}, Implies[x == y, y + 1 == x + 1]], prelude, {
	TypeTheoryTactic["Introduce", x, y, h],
	TypeTheoryTactic["Rewrite", h, "RightToLeft"]
}]

VerificationTest[
	TypeTheoryProof[ForAll[{Typed[x, NonNegativeIntegers], Typed[y, NonNegativeIntegers]}, Implies[x == y, x + 0 == y]], prelude, {
		TypeTheoryTactic["Introduce", x, y, h],
		TypeTheoryTactic["Rewrite", h]
	}]["Goals"],
	{TypeTheoryTerm[RightTee[{Typed[x, NonNegativeIntegers], Typed[y, NonNegativeIntegers], Typed[h, x == y]}, y + 0 == y], prelude]},
	TestID -> "Rewrite-replaces-the-left-side-of-an-equation"
]

VerificationTest[
	{
		TypeTheoryProof[ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers]}, a + b + c == b + a + c], prelude, {
			TypeTheoryTactic["Introduce", a, b, c],
			TypeTheoryTactic["Rewrite", AdditionCommutativity]
		}]["Goals"],
		rewritten["Goals"]
	},
	{{}, {}},
	TestID -> "Rewrite-finds-an-instance-of-a-lemma-and-closes-a-goal-it-makes-reflexive"
]

VerificationTest[
	TypeTheoryProof[ForAll[{Typed[x, NonNegativeIntegers], Typed[y, NonNegativeIntegers]}, Implies[x == y, Exists[{Typed[k, NonNegativeIntegers]}, k + x == k + y]]], prelude, {
		TypeTheoryTactic["Introduce", x, y, h],
		TypeTheoryTactic["Rewrite", h]
	}]["Goals"],
	{TypeTheoryTerm[RightTee[{Typed[x, NonNegativeIntegers], Typed[y, NonNegativeIntegers], Typed[h, x == y]}, Exists[{Typed[k, NonNegativeIntegers]}, k + y == k + y]], prelude]},
	TestID -> "Rewrite-reaches-under-binders"
]

VerificationTest[
	{
		First @ TypeTheoryProof[ForAll[{Typed[x, NonNegativeIntegers], Typed[y, NonNegativeIntegers]}, Implies[x == y, 1 == 1 + 0]], prelude, {
			TypeTheoryTactic["Introduce", x, y, h],
			TypeTheoryTactic["Rewrite", h]
		}],
		First @ TypeTheoryProof[ForAll[{Typed[p, TypeUniverse[0]]}, Implies[p, p]], prelude, {
			TypeTheoryTactic["Introduce", p, hp],
			TypeTheoryTactic["Rewrite", hp]
		}]
	},
	{"NoInstance", "EquationExpected"},
	TestID -> "Rewrite-without-an-instance-or-an-equation-gives-a-Failure"
]

VerificationTest[
	MatchQ[TypeTheoryCheck[TypeTheoryEnvironment[prelude, {TypeTheoryTheorem[SuccessorRespectsEquality, rewritten]}]], _Success],
	True,
	TestID -> "A-proof-by-Rewrite-is-a-theorem"
]

VerificationTest[
	{
		TypeTheoryProof[And[True, True], prelude, {TypeTheoryTactic["Constructor"], TypeTheoryTactic["Constructor"], TypeTheoryTactic["Constructor"]}]["Goals"],
		TypeTheoryProof[Exists[{Typed[k, NonNegativeIntegers]}, k == 2], prelude, {TypeTheoryTactic["Constructor"], TypeTheoryTactic["Exact", EqualityReflexivity[2]]}]["Goals"],
		First @ TypeTheoryProof[False, prelude, {TypeTheoryTactic["Constructor"]}],
		First @ TypeTheoryProof[ForAll[{Typed[p, TypeUniverse[0]]}, Implies[p, p]], prelude, {TypeTheoryTactic["Constructor"]}]
	},
	{{}, {}, "NoConstructorApplies", "InductiveTypeExpected"},
	TestID -> "Constructor-applies-the-first-constructor-that-fits"
]

VerificationTest[
	{
		TypeTheoryProof[ForAll[{Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]]}, Implies[And[p, q], And[q, p]]], prelude, {
			TypeTheoryTactic["Introduce", p, q, h],
			TypeTheoryTactic["Cases", h],
			TypeTheoryTactic["Introduce", hp, hq],
			TypeTheoryTactic["Constructor"],
			TypeTheoryTactic["Exact", hq],
			TypeTheoryTactic["Exact", hp]
		}]["Goals"],
		TypeTheoryProof[ForAll[{Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]]}, Implies[Or[p, q], Or[q, p]]], prelude, {
			TypeTheoryTactic["Introduce", p, q, h],
			TypeTheoryTactic["Cases", h],
			TypeTheoryTactic["Introduce", hp],
			TypeTheoryTactic["Apply", OrIntroductionRight],
			TypeTheoryTactic["Exact", hp],
			TypeTheoryTactic["Introduce", hq],
			TypeTheoryTactic["Apply", OrIntroductionLeft],
			TypeTheoryTactic["Exact", hq]
		}]["Goals"],
		TypeTheoryProof[ForAll[{Typed[p, TypeUniverse[0]]}, Implies[False, p]], prelude, {TypeTheoryTactic["Introduce", p, h], TypeTheoryTactic["Cases", h]}]["Goals"]
	},
	{{}, {}, {}},
	TestID -> "Cases-splits-a-hypothesis-of-a-connective"
]

VerificationTest[
	TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, Or[n == 0, Exists[{Typed[k, NonNegativeIntegers]}, n == k + 1]]], prelude, {
		TypeTheoryTactic["Introduce", n],
		TypeTheoryTactic["Cases", n]
	}]["Goals"],
	With[{n = WolframInstitute`TypeTheory`Library`Prelude`Private`n},
		{
			TypeTheoryTerm[RightTee[{}, Or[NaturalNumberZero == 0, Exists[{Typed[k, NonNegativeIntegers]}, NaturalNumberZero == k + 1]]], prelude],
			TypeTheoryTerm[RightTee[{}, ForAll[{Typed[n, NonNegativeIntegers]}, Or[NaturalNumberSuccessor[n] == 0, Exists[{Typed[k, NonNegativeIntegers]}, NaturalNumberSuccessor[n] == k + 1]]]], prelude]
		}
	],
	TestID -> "Cases-gives-the-fields-without-induction-hypotheses"
]

VerificationTest[
	TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers], Typed[h, n + 0 == n]}, 0 + n == n], prelude, {
		TypeTheoryTactic["Introduce", n, h],
		TypeTheoryTactic["Induction", n]
	}]["Goals"],
	With[{n = WolframInstitute`TypeTheory`Library`Prelude`Private`n},
		{
			TypeTheoryTerm[RightTee[{}, Implies[NaturalNumberZero + 0 == NaturalNumberZero, 0 + NaturalNumberZero == NaturalNumberZero]], prelude],
			TypeTheoryTerm[RightTee[{}, ForAll[{Typed[n, NonNegativeIntegers]}, Implies[
				Implies[n + 0 == n, 0 + n == n],
				Implies[NaturalNumberSuccessor[n] + 0 == NaturalNumberSuccessor[n], 0 + NaturalNumberSuccessor[n] == NaturalNumberSuccessor[n]]
			]]], prelude]
		}
	],
	TestID -> "Induction-generalizes-the-hypotheses-that-depend-on-the-variable"
]

VerificationTest[
	With[
		{
			proof = TypeTheoryProof[ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, Implies[a <= b, a <= b + 1]], prelude, {
				TypeTheoryTactic["Introduce", a, b, h],
				TypeTheoryTactic["Induction", h],
				TypeTheoryTactic["Apply", LessEqualStep],
				TypeTheoryTactic["Apply", LessEqualReflexivity],
				TypeTheoryTactic["Introduce", m, hm, ih],
				TypeTheoryTactic["Apply", LessEqualStep],
				TypeTheoryTactic["Exact", ih]
			}]
		},
		{proof["Goals"], MatchQ[TypeTheoryCheck[TypeTheoryEnvironment[prelude, {TypeTheoryTheorem[LessEqualSuccessorRight, proof]}]], _Success]}
	],
	{{}, True},
	TestID -> "Induction-on-an-inductive-family-whose-index-is-a-variable"
]

VerificationTest[
	First @ TypeTheoryProof[ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, Implies[a <= b + 1, a <= b + 2]], prelude, {
		TypeTheoryTactic["Introduce", a, b, h],
		TypeTheoryTactic["Induction", h]
	}],
	"IndexNotVariable",
	TestID -> "Induction-on-a-family-whose-index-is-not-a-variable-gives-a-Failure"
]

VerificationTest[
	TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers], Typed[m, NonNegativeIntegers]}, Implies[n == m, m == n]], prelude, {
		TypeTheoryTactic["Introduce", n, m, h],
		TypeTheoryTactic["Generalize", m]
	}]["Goals"],
	{TypeTheoryTerm[RightTee[{Typed[n, NonNegativeIntegers]}, ForAll[{Typed[m, NonNegativeIntegers]}, Implies[n == m, m == n]]], prelude]},
	TestID -> "Generalize-moves-a-hypothesis-and-those-that-depend-on-it-back-into-the-goal"
]

(* Change, Simplify and Decide, and laws of lists proved with tactics alone *)

joinEmpty = TypeTheoryProof[ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[l, Lists[\[Alpha]]]}, Join[l, EmptyList] == l], prelude, {
	TypeTheoryTactic["Introduce", \[Alpha], l],
	TypeTheoryTactic["Induction", l],
	TypeTheoryTactic["Reflexivity"],
	TypeTheoryTactic["Introduce", x, rest, ih],
	TypeTheoryTactic["Change", ListPrepend[x, Join[rest, EmptyList]] == ListPrepend[x, rest]],
	TypeTheoryTactic["Rewrite", ih]
}]

reverseTwice = TypeTheoryProof[ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[l, Lists[\[Alpha]]]}, Reverse[Reverse[l]] == l], prelude, {
	TypeTheoryTactic["Introduce", \[Alpha], l],
	TypeTheoryTactic["Induction", l],
	TypeTheoryTactic["Reflexivity"],
	TypeTheoryTactic["Introduce", x, rest, ih],
	TypeTheoryTactic["Change", Reverse[Join[Reverse[rest], ListPrepend[x, EmptyList]]] == ListPrepend[x, rest]],
	TypeTheoryTactic["Rewrite", ReverseJoin],
	TypeTheoryTactic["Rewrite", ih],
	TypeTheoryTactic["Reflexivity"]
}]

VerificationTest[
	{
		joinEmpty["Goals"],
		reverseTwice["Goals"],
		MatchQ[TypeTheoryCheck[TypeTheoryEnvironment[prelude, {TypeTheoryTheorem[JoinEmptyAgain, joinEmpty], TypeTheoryTheorem[ReverseTwice, reverseTwice]}]], _Success]
	},
	{{}, {}, True},
	TestID -> "Laws-of-lists-are-proved-with-tactics"
]

VerificationTest[
	First @ TypeTheoryProof[2 + 2 == 4, prelude, {TypeTheoryTactic["Change", 2 + 2 == 5]}],
	"NotDefinitionallyEqual",
	TestID -> "Change-needs-a-statement-equal-by-computation"
]

VerificationTest[
	{
		TypeTheoryProof[ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[a, Lists[\[Alpha]]], Typed[b, Lists[\[Alpha]]]}, Length[Reverse[Join[a, b]]] == Length[a] + Length[b]], prelude, {
			TypeTheoryTactic["Introduce", \[Alpha], a, b],
			TypeTheoryTactic["Simplify", {LengthReverse, LengthJoin}]
		}]["Goals"],
		TypeTheoryProof[ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[a, Lists[\[Alpha]]], Typed[b, Lists[\[Alpha]]]}, Length[Reverse[Join[a, b]]] == Length[b] + Length[a]], prelude, {
			TypeTheoryTactic["Introduce", \[Alpha], a, b],
			TypeTheoryTactic["Simplify", {LengthReverse, LengthJoin}]
		}]["Goals"]
	},
	{
		{},
		{TypeTheoryTerm[RightTee[{Typed[\[Alpha], TypeUniverse[u + 1]], Typed[a, Lists[\[Alpha]]], Typed[b, Lists[\[Alpha]]]}, Length[a] + Length[b] == Length[b] + Length[a]], prelude]}
	},
	TestID -> "Simplify-rewrites-with-the-lemmas-and-closes-what-becomes-reflexive"
]

VerificationTest[
	First @ TypeTheoryProof[ForAll[{Typed[m, NonNegativeIntegers]}, m == m + 1], prelude, {
		TypeTheoryTactic["Introduce", m],
		TypeTheoryTactic["Simplify", {AdditionCommutativity}]
	}],
	"NoProgress",
	TestID -> "Simplify-that-leaves-the-goal-as-it-is-gives-a-Failure"
]

VerificationTest[
	{
		TypeTheoryProof[And[3 + 4 == 7, Or[5 <= 2, Not[2 == 3]]], prelude, {TypeTheoryTactic["Decide"]}]["Goals"],
		TypeTheoryProof[2 < 5, prelude, {TypeTheoryTactic["Decide"]}]["Goals"],
		TypeTheoryProof[2 != 3, prelude, {TypeTheoryTactic["Decide"]}]["Goals"],
		First @ TypeTheoryProof[2 + 2 == 5, prelude, {TypeTheoryTactic["Decide"]}],
		First @ TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, n <= n + 1], prelude, {TypeTheoryTactic["Introduce", n], TypeTheoryTactic["Decide"]}]
	},
	{{}, {}, {}, "DecidedFalse", "NotDecided"},
	TestID -> "Decide-proves-closed-statements-by-computing-their-decision"
]
