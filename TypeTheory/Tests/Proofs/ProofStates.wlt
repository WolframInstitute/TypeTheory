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
	TypeTheoryTactic["Exact", "equalityCongruence"["successor", ih]]
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

(* in a list of tactics written out, "name" and "name"[arguments] stand for TypeTheoryTactic["name", arguments], whose
   arguments stay held: n has a value here, which neither form evaluates *)
VerificationTest[
	Block[{n = 5, k = 6, ih = 7},
		{
			TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n], prelude, {"Introduce"[n], "Reflexivity"}]["Goals"],
			TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, 0 + n == n], prelude, {
				"Introduce"[n], "Induction"[n], "Reflexivity", "Introduce"[k, ih], "Exact"["equalityCongruence"["successor", ih]]
			}]["Term"] === zeroLeft["Term"],
			TypeTheoryTactic["Introduce"[n, k]],
			With[{steps = {"Introduce"[m], "Reflexivity"}}, TypeTheoryProof[ForAll[{Typed[m, NonNegativeIntegers]}, m + 0 == m], steps]["Goals"]],
			TypeTheoryProof[ForAll[{Typed[m, NonNegativeIntegers]}, m + 0 == m], {TypeTheoryTactic["Introduce"[m]], TypeTheoryTactic["Reflexivity"]}]["Goals"]
		}
	],
	{{}, True, HoldForm[TypeTheoryTactic["Introduce", n, k]], {}, {}},
	SameTest -> Function[{actual, expected}, MapAt[HoldForm, actual, 3] === expected],
	TestID -> "A-tactic-is-written-as-its-name-applied-to-its-arguments"
]

VerificationTest[
	{
		FailureQ[TypeTheoryProof[ForAll[{Typed[m, NonNegativeIntegers]}, m + 0 == m], prelude, {"Introduce"[m]}, 5]],
		MatchQ[TypeTheoryProof[_Association], _TypeTheoryProof]
	},
	{True, True},
	TestID -> "TypeTheoryProof-refuses-arguments-out-of-order-and-a-pattern-starts-no-proof"
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
		TypeTheoryType[TypeTheoryTerm[ZeroRightIdentity, proved]] === TypeTheoryTerm[ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n], proved]
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
			TypeTheoryTerm[RightTee[{}, 0 + "zero" == "zero"], prelude],
			TypeTheoryTerm[RightTee[{}, ForAll[{Typed[n, NonNegativeIntegers]}, Implies[0 + n == n, 0 + "successor"[n] == "successor"[n]]]], prelude]
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
			TypeTheoryType[TypeTheoryTerm[ZeroLeftIdentityAgain, proved]] === TypeTheoryTerm[ForAll[{Typed[m, NonNegativeIntegers]}, 0 + m == m], proved],
			MatchQ[TypeTheoryCheck[proved], _Success]
		}
	],
	{True, True, True},
	TestID -> "A-finished-proof-is-declared-and-used"
]

VerificationTest[
	TypeTheoryProof[ForAll[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]]}, Implies[a, Implies[b, And[a, b]]]], prelude, {
		TypeTheoryTactic["Introduce", a, b, ha, hb],
		TypeTheoryTactic["Apply", "andIntroduction"],
		TypeTheoryTactic["Assumption"],
		TypeTheoryTactic["Exact", hb]
	}]["Term"],
	TypeTheoryTerm[Function[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]], Typed[ha, a], Typed[hb, b]}, "andIntroduction"[ha, hb]], prelude],
	TestID -> "Apply-leaves-a-goal-per-argument"
]

VerificationTest[
	TypeTheoryProof[ForAll[{Typed[x, NonNegativeIntegers], Typed[y, NonNegativeIntegers], Typed[z, NonNegativeIntegers]}, Implies[x == y, Implies[y == z, x == z]]], prelude, {
		TypeTheoryTactic["Introduce", x, y, z, h1, h2],
		TypeTheoryTactic["Apply", "equalityTransitivity"],
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
		TypeTheoryTactic["Exact", "equalityReflexivity"[5]][TypeTheoryProof[2 + 2 == 4, prelude]],
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
	(* the display holds a handle to the proof, a symbol whose value it is, not the proof's term *)
	{
		MatchQ[ToBoxes[zeroLeft], InterpretationBox[_FrameBox, handle_Symbol /; handle === zeroLeft]],
		MatchQ[ToBoxes[TypeTheoryProof[2 + 2 == 4, prelude]], InterpretationBox[_FrameBox, _Symbol]],
		ToExpression[ToBoxes[zeroLeft], StandardForm] === zeroLeft
	},
	{True, True, True},
	TestID -> "A-proof-displays-its-goals"
]

VerificationTest[
	ToExpression[ToBoxes[zeroLeft]] === zeroLeft,
	True,
	TestID -> "A-proof-display-is-interpreted-as-the-proof"
]

VerificationTest[
	{
		TypeTheoryCheck[TypeTheoryTerm["equalityReflexivity"[4], prelude], TypeTheoryTerm[2 + 2 == 4]][[1]],
		TypeTheoryCheck[TypeTheoryEnvironment[{TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, "equalityReflexivity"[4]]}]][[1]]
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
			TypeTheoryTactic["Rewrite", "additionCommutativity"]
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
		TypeTheoryProof[Exists[{Typed[k, NonNegativeIntegers]}, k == 2], prelude, {TypeTheoryTactic["Constructor"], TypeTheoryTactic["Exact", "equalityReflexivity"[2]]}]["Goals"],
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
			TypeTheoryTactic["Apply", "orIntroductionRight"],
			TypeTheoryTactic["Exact", hp],
			TypeTheoryTactic["Introduce", hq],
			TypeTheoryTactic["Apply", "orIntroductionLeft"],
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
			TypeTheoryTerm[RightTee[{}, Or["zero" == 0, Exists[{Typed[k, NonNegativeIntegers]}, "zero" == k + 1]]], prelude],
			TypeTheoryTerm[RightTee[{}, ForAll[{Typed[n, NonNegativeIntegers]}, Or["successor"[n] == 0, Exists[{Typed[k, NonNegativeIntegers]}, "successor"[n] == k + 1]]]], prelude]
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
			TypeTheoryTerm[RightTee[{}, Implies["zero" + 0 == "zero", 0 + "zero" == "zero"]], prelude],
			TypeTheoryTerm[RightTee[{}, ForAll[{Typed[n, NonNegativeIntegers]}, Implies[
				Implies[n + 0 == n, 0 + n == n],
				Implies["successor"[n] + 0 == "successor"[n], 0 + "successor"[n] == "successor"[n]]
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
				TypeTheoryTactic["Apply", "lessEqualStep"],
				TypeTheoryTactic["Apply", "lessEqualReflexivity"],
				TypeTheoryTactic["Introduce", m, hm, ih],
				TypeTheoryTactic["Apply", "lessEqualStep"],
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

(* Change, RewriteRepeated and Decide, and laws of lists proved with tactics alone *)

joinEmpty = TypeTheoryProof[ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[l, {\[Alpha]}]}, Join[l, {}] == l], prelude, {
	TypeTheoryTactic["Introduce", \[Alpha], l],
	TypeTheoryTactic["Induction", l],
	TypeTheoryTactic["Reflexivity"],
	TypeTheoryTactic["Introduce", x, rest, ih],
	TypeTheoryTactic["Change", Prepend[x][Join[rest, {}]] == Prepend[x][rest]],
	TypeTheoryTactic["Rewrite", ih]
}]

reverseTwice = TypeTheoryProof[ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[l, {\[Alpha]}]}, Reverse[Reverse[l]] == l], prelude, {
	TypeTheoryTactic["Introduce", \[Alpha], l],
	TypeTheoryTactic["Induction", l],
	TypeTheoryTactic["Reflexivity"],
	TypeTheoryTactic["Introduce", x, rest, ih],
	TypeTheoryTactic["Change", Reverse[Join[Reverse[rest], Prepend[x][{}]]] == Prepend[x][rest]],
	TypeTheoryTactic["Rewrite", "reverseJoin"],
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
		TypeTheoryProof[ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[a, {\[Alpha]}], Typed[b, {\[Alpha]}]}, Length[Reverse[Join[a, b]]] == Length[a] + Length[b]], prelude, {
			TypeTheoryTactic["Introduce", \[Alpha], a, b],
			TypeTheoryTactic["RewriteRepeated", {"lengthReverse", "lengthJoin"}]
		}]["Goals"],
		TypeTheoryProof[ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[a, {\[Alpha]}], Typed[b, {\[Alpha]}]}, Length[Reverse[Join[a, b]]] == Length[b] + Length[a]], prelude, {
			TypeTheoryTactic["Introduce", \[Alpha], a, b],
			TypeTheoryTactic["RewriteRepeated", "lengthReverse", "lengthJoin"]
		}]["Goals"]
	},
	{
		{},
		{TypeTheoryTerm[RightTee[{Typed[\[Alpha], TypeUniverse[u + 1]], Typed[a, {\[Alpha]}], Typed[b, {\[Alpha]}]}, Length[a] + Length[b] == Length[b] + Length[a]], prelude]}
	},
	TestID -> "RewriteRepeated-rewrites-with-the-lemmas-and-closes-what-becomes-reflexive"
]

VerificationTest[
	First @ TypeTheoryProof[ForAll[{Typed[m, NonNegativeIntegers]}, m == m + 1], prelude, {
		TypeTheoryTactic["Introduce", m],
		TypeTheoryTactic["RewriteRepeated", "additionCommutativity"]
	}],
	"NoProgress",
	TestID -> "RewriteRepeated-that-leaves-the-goal-as-it-is-gives-a-Failure"
]

(* the tactic was named "Simplify", which is a function of the Wolfram Language that does something else: the old name
   is a Failure that names the new one *)
VerificationTest[
	With[{failure = TypeTheoryProof[ForAll[{Typed[m, NonNegativeIntegers]}, m + 0 == m], prelude, {TypeTheoryTactic["Introduce", m], TypeTheoryTactic["Simplify", {"additionZeroRight"}]}]},
		{First[failure], StringContainsQ[ToString[failure["Message"]], "RewriteRepeated"]}
	],
	{"UnknownTactic", True},
	TestID -> "The-tactic-Simplify-is-named-RewriteRepeated"
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

VerificationTest[
	First @ TypeTheoryProof[Exists[{Typed[x, NonNegativeIntegers]}, ForAll[{Typed[y, NonNegativeIntegers]}, y == x]], prelude, {
		TypeTheoryTactic["Constructor"],
		TypeTheoryTactic["Introduce", y],
		TypeTheoryTactic["Exact", "equalityReflexivity"[y]]
	}],
	"TypeMismatch",
	TestID -> "A-goal-is-not-solved-with-a-hypothesis-it-does-not-have"
]

(* RewriteRepeated unfolds a definition it is given where the definition computes, and Rewrite reaches into hypotheses *)

joinAssociativity = TypeTheoryProof[ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[a, {\[Alpha]}], Typed[b, {\[Alpha]}], Typed[c, {\[Alpha]}]}, Join[Join[a, b], c] == Join[a, Join[b, c]]], prelude, {
	TypeTheoryTactic["Introduce", \[Alpha], a, b, c],
	TypeTheoryTactic["Induction", a],
	TypeTheoryTactic["RewriteRepeated", Join],
	TypeTheoryTactic["Introduce", x, rest, ih],
	TypeTheoryTactic["RewriteRepeated", Join, ih]
}]

lengthJoin = TypeTheoryProof[ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[a, {\[Alpha]}], Typed[b, {\[Alpha]}]}, Length[Join[a, b]] == Length[a] + Length[b]], prelude, {
	TypeTheoryTactic["Introduce", \[Alpha], a, b],
	TypeTheoryTactic["Induction", a],
	TypeTheoryTactic["RewriteRepeated", Join, Length, "additionZeroLeft"],
	TypeTheoryTactic["Introduce", x, rest, ih],
	TypeTheoryTactic["RewriteRepeated", Join, Length, ih, "additionSuccessorLeft"]
}]

reverseJoin = TypeTheoryProof[ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[a, {\[Alpha]}], Typed[b, {\[Alpha]}]}, Reverse[Join[a, b]] == Join[Reverse[b], Reverse[a]]], prelude, {
	TypeTheoryTactic["Introduce", \[Alpha], a, b],
	TypeTheoryTactic["Induction", a],
	TypeTheoryTactic["RewriteRepeated", Join, Reverse, "joinEmptyRight"],
	TypeTheoryTactic["Introduce", x, rest, ih],
	TypeTheoryTactic["RewriteRepeated", Join, Reverse, ih, Append, "joinAssociativity"]
}]

VerificationTest[
	{
		joinAssociativity["Goals"],
		lengthJoin["Goals"],
		reverseJoin["Goals"],
		MatchQ[
			TypeTheoryCheck[TypeTheoryEnvironment[prelude, {
				TypeTheoryTheorem[JoinAssociativityAgain, joinAssociativity],
				TypeTheoryTheorem[LengthJoinAgain, lengthJoin],
				TypeTheoryTheorem[ReverseJoinAgain, reverseJoin]
			}]],
			_Success
		]
	},
	{{}, {}, {}, True},
	TestID -> "RewriteRepeated-unfolds-a-definition-by-recursion-where-it-computes"
]

VerificationTest[
	{
		TypeTheoryProof[ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[x, \[Alpha]], Typed[a, {\[Alpha]}]}, Reverse[Prepend[x][a]] == Append[Reverse[a], x]], prelude, {
			TypeTheoryTactic["Introduce", \[Alpha], x, a],
			TypeTheoryTactic["RewriteRepeated", Reverse]
		}]["Goals"],
		TypeTheoryProof[ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[x, \[Alpha]], Typed[a, {\[Alpha]}]}, Append[a, x] == Join[a, Prepend[x][{}]]], prelude, {
			TypeTheoryTactic["Introduce", \[Alpha], x, a],
			TypeTheoryTactic["RewriteRepeated", Append]
		}]["Goals"],
		First @ TypeTheoryProof[ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u + 1]], Typed[a, {\[Alpha]}]}, Join[a, {}] == a], prelude, {
			TypeTheoryTactic["Introduce", \[Alpha], a],
			TypeTheoryTactic["RewriteRepeated", Join]
		}]
	},
	{{}, {}, "NoProgress"},
	TestID -> "RewriteRepeated-folds-recursive-calls-back-and-leaves-a-definition-that-does-not-compute"
]

VerificationTest[
	With[
		{
			forward = TypeTheoryProof[ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, Implies[a == b, Implies[a + 1 == 3, b + 1 == 3]]], prelude, {
				TypeTheoryTactic["Introduce", a, b, h, k],
				TypeTheoryTactic["Rewrite", h, "At" -> k]
			}],
			backward = TypeTheoryProof[ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]}, Implies[a == b, Implies[b + 1 == 3, a + 1 == 3]]], prelude, {
				TypeTheoryTactic["Introduce", a, b, h, k],
				TypeTheoryTactic["Rewrite", h, "RightToLeft", "At" -> k],
				TypeTheoryTactic["Exact", k]
			}]
		},
		{
			forward["Goals"],
			MatchQ[
				TypeTheoryCheck[TypeTheoryEnvironment[prelude, {
					TypeTheoryTheorem[RewrittenHypothesis, TypeTheoryTactic["Exact", k][forward]],
					TypeTheoryTheorem[RewrittenHypothesisBack, backward]
				}]],
				_Success
			]
		}
	],
	{
		{TypeTheoryTerm[RightTee[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[h, a == b], Typed[k, b + 1 == 3]}, b + 1 == 3], prelude]},
		True
	},
	TestID -> "Rewrite-at-a-hypothesis-replaces-it-with-the-rewritten-one"
]

(* Wolfram finds, the kernel checks *)

VerificationTest[
	With[
		{
			pythagorean = TypeTheoryProof[Exists[{Typed[x, NonNegativeIntegers], Typed[y, NonNegativeIntegers]}, And[x^2 + y^2 == 25, x < y, 0 < x]], prelude, {TypeTheoryTactic["FindInstance"]}],
			taxicab = TypeTheoryProof[Exists[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers]}, And[a^3 + b^3 == c^3 + 1, 1 < a, a < b]], prelude, {
				TypeTheoryTactic["FindInstance"]
			}]
		},
		{
			pythagorean["Goals"],
			pythagorean["Term"],
			taxicab["Goals"],
			MatchQ[TypeTheoryCheck[TypeTheoryEnvironment[prelude, {TypeTheoryTheorem[PythagoreanPair, pythagorean], TypeTheoryTheorem[Taxicab, taxicab]}]], _Success]
		}
	],
	{
		{},
		TypeTheoryTerm[
			"existsIntroduction"[3, "existsIntroduction"[4, "decideSoundness"["equalityReflexivity"["true"]]]],
			prelude
		],
		{},
		True
	},
	TestID -> "FindInstance-finds-witnesses-that-the-kernel-checks-by-computing"
]

VerificationTest[
	First /@ {
		TypeTheoryProof[Exists[{Typed[n, NonNegativeIntegers]}, n * n == 143], prelude, {TypeTheoryTactic["FindInstance"]}],
		TypeTheoryProof[ForAll[{Typed[m, NonNegativeIntegers]}, Exists[{Typed[n, NonNegativeIntegers]}, n == m + 1]], prelude, {TypeTheoryTactic["Introduce", m], TypeTheoryTactic["FindInstance"]}],
		TypeTheoryProof[2 + 2 == 4, prelude, {TypeTheoryTactic["FindInstance"]}]
	},
	{"NoInstance", "NotTranslatable", "ExistentialExpected"},
	TestID -> "FindInstance-fails-without-an-instance-or-on-what-it-cannot-translate"
]

(* the side of an equation may meet its instance only by computation: m 2 is m (1 + 1), so the rewrite takes it,
   where it used to leave the goal unchanged without a word; a side with no instance at all still fails *)
VerificationTest[
	With[
		{
			rewritten = TypeTheoryProof[ForAll[{Typed[m, NonNegativeIntegers]}, m * 2 == m + m], {
				TypeTheoryTactic["Introduce", m],
				TypeTheoryTactic["Rewrite", "multiplicationSuccessorRight"[m, 1]]
			}]
		},
		{
			MatchQ[rewritten["Goals"], {TypeTheoryTerm[_ ⊢ m * 1 + m == m + m, _]}],
			TypeTheoryTactic["Rewrite", "multiplicationOneRight"[m]][rewritten]["Goals"],
			First @ TypeTheoryProof[ForAll[{Typed[m, NonNegativeIntegers]}, m * 2 == m + m], {TypeTheoryTactic["Introduce", m], TypeTheoryTactic["Rewrite", "additionCommutativity"[m, 5]]}]
		}
	],
	{True, {}, "NoInstance"},
	TestID -> "Rewrite-takes-an-instance-equal-to-the-side-by-computation"
]

(* Rewrite compares its candidates without unfolding a definition:
   (2 + 2) + 1 is an instance of 4 + 1 by arithmetic on literals, but Doubled[2] + 1 is none, equal to it only once
   Doubled unfolds *)
VerificationTest[
	With[{doubled = TypeTheoryEnvironment[{TypeTheoryDefinition[Doubled, Function[{Typed[n, NonNegativeIntegers]}, n + n]]}]},
		{
			MatchQ[TypeTheoryProof[(2 + 2) + 1 == 5, doubled, {TypeTheoryTactic["Rewrite", "additionCommutativity"[4, 1]]}]["Goals"], {TypeTheoryTerm[_ ⊢ 1 + 4 == 5, _]}],
			First @ TypeTheoryProof[Doubled[2] + 1 == 5, doubled, {TypeTheoryTactic["Rewrite", "additionCommutativity"[4, 1]]}]
		}
	],
	{True, "NoInstance"},
	TestID -> "Rewrite-takes-no-instance-that-needs-a-definition-unfolded"
]

(* a premise P[x] whose P the goal fixes as a function is beta reduced in the new goal, not left as a redex *)
VerificationTest[
	With[{applied = TypeTheoryProof[Exists[{Typed[x, NonNegativeIntegers]}, x + 1 == 3], {TypeTheoryTactic["Apply", "existsIntroduction"]}]},
		{FreeQ[applied["Goals"], Function], TypeTheoryTactic["Exact", "equalityReflexivity"[3]][applied]["Goals"]}
	],
	{True, {}},
	TestID -> "Apply-states-its-new-goals-beta-reduced"
]

(* classical propositional logic by a truth table: each atom split by "excludedMiddle", the hypotheses that are propositions
   used, and an atom any proposition no connective builds *)
VerificationTest[
	With[
		{
			peirce = TypeTheoryProof[ForAll[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]]}, Implies[Implies[Implies[a, b], a], a]], prelude,
				{TypeTheoryTactic["Introduce"], TypeTheoryTactic["Introduce"], TypeTheoryTactic["Classical"]}],
			doubleNegation = TypeTheoryProof[ForAll[{Typed[a, TypeUniverse[0]]}, Implies[Not[Not[a]], a]], prelude,
				{TypeTheoryTactic["Introduce"], TypeTheoryTactic["Introduce"], TypeTheoryTactic["Classical"]}],
			syllogism = TypeTheoryProof[ForAll[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]]}, Implies[Or[a, b], Implies[Not[a], b]]], prelude,
				{TypeTheoryTactic["Introduce"], TypeTheoryTactic["Introduce"], TypeTheoryTactic["Introduce"], TypeTheoryTactic["Introduce"], TypeTheoryTactic["Classical"]}]
		},
		{
			peirce["Goals"], Head[Append[prelude, TypeTheoryTheorem[ClassicalPeirce, peirce]]],
			doubleNegation["Goals"], Head[Append[prelude, TypeTheoryTheorem[ClassicalDoubleNegation, doubleNegation]]],
			syllogism["Goals"], Head[Append[prelude, TypeTheoryTheorem[ClassicalSyllogism, syllogism]]],
			TypeTheoryProof[Or[2 + 2 == 4, Not[2 + 2 == 4]], prelude, {TypeTheoryTactic["Classical"]}]["Goals"]
		}
	],
	{{}, TypeTheoryEnvironment, {}, TypeTheoryEnvironment, {}, TypeTheoryEnvironment, {}},
	TestID -> "Classical-proves-the-tautologies-of-classical-propositional-logic"
]

VerificationTest[
	First @ TypeTheoryProof[ForAll[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]]}, Implies[a, b]], prelude,
		{TypeTheoryTactic["Introduce"], TypeTheoryTactic["Introduce"], TypeTheoryTactic["Introduce"], TypeTheoryTactic["Classical"]}],
	"NotATautology",
	TestID -> "Classical-refuses-a-goal-its-hypotheses-do-not-imply"
]

(* "RewriteRepeated" unfolds a definition applied to another before the outer one, so the inner one's recursive call folds back
   too: total[Join[Prepend[x][l], m]] is x + total[Join[l, m]], where the induction hypothesis applies *)
VerificationTest[
	Module[{total, environment},
		environment = TypeTheoryEnvironment[{TypeTheoryDefinition[total, Function[{Typed[l, {NonNegativeIntegers}]},
			InductiveRecursor[List][Function[{Typed[t, {NonNegativeIntegers}]}, NonNegativeIntegers], 0, Function[{Typed[x, NonNegativeIntegers], Typed[rest, {NonNegativeIntegers}], Typed[r, NonNegativeIntegers]}, x + r], l]
		]]}];
		TypeTheoryProof[
			ForAll[{Typed[a, {NonNegativeIntegers}], Typed[b, {NonNegativeIntegers}]}, total[Join[a, b]] == total[a] + total[b]],
			environment,
			{"Introduce"[a, b], "Induction"[a], "RewriteRepeated"[total, Join], "Ring", "Introduce"[x, rest, ih], "RewriteRepeated"[total, Join, ih], "Ring"}
		]["Goals"]
	],
	{},
	TestID -> "RewriteRepeated-unfolds-an-inner-definition-first-so-its-recursive-call-folds-back"
]

(* a statement may hold the patterns of a rule, as a statement about rewriting does, and is no pattern itself; a proof
   with no environment that names what only the Wolfram Language environment declares is in it; a negative integer
   where an expression is expected is its atom *)
VerificationTest[
	{
		TypeTheoryProof[Replace[f[5], f[x_] :> x] == 5, {"Reflexivity"}]["Goals"],
		TypeTheoryProof[Head[f[x]] == f, {"Reflexivity"}]["Goals"],
		MatchQ[TypeTheoryProof[_Association], Verbatim[TypeTheoryProof][Verbatim[_Association]]],
		TypeTheoryProof[Construct[f, -2] == f[-2], {"Reflexivity"}]["Goals"]
	},
	{{}, {}, True, {}},
	TestID -> "A-statement-about-rules-proves-and-negative-integers-are-expressions"
]

(* "NonlinearArithmetic" multiplies each inequality among the hypotheses by each side of each, so a product of
   inequalities follows linearly, where "LinearArithmetic" finds no combination *)
VerificationTest[
	{
		TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers], Typed[m, NonNegativeIntegers]}, Implies[n <= m, n n <= m m]], {"Introduce"[n, m, h], "NonlinearArithmetic"}]["Goals"],
		TypeTheoryProof[
			ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[c, NonNegativeIntegers], Typed[d, NonNegativeIntegers]}, Implies[a <= b, Implies[c <= d, a c <= b d]]],
			{"Introduce"[a, b, c, d, h1, h2], "NonlinearArithmetic"}
		]["Goals"],
		First[TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers], Typed[m, NonNegativeIntegers]}, Implies[n <= m, n n <= m m]], {"Introduce"[n, m, h], "LinearArithmetic"}]]
	},
	{{}, {}, "NoLinearCombination"},
	TestID -> "NonlinearArithmetic-proves-products-of-inequalities"
]

(* "NonlinearArithmetic" with large literals: the products of the hypothesis are scaled by literals near the bound, and
   the kernel checks the proof without unfolding a product by a literal; the bound of a 64-bit multiplication,
   n (n + 1) <= 2^63 - 1 below 3037000499, in well under a second *)
VerificationTest[
	{
		TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, Implies[n <= 32, n n <= 1024]], {"Introduce"[n, h], "NonlinearArithmetic"}]["Goals"],
		TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, Implies[n <= 1000, n n <= 1000000]], {"Introduce"[n, h], "NonlinearArithmetic"}]["Goals"],
		With[{timed = AbsoluteTiming[TypeTheoryProof[
			ForAll[{Typed[n, NonNegativeIntegers]}, Implies[n <= 3037000499, n (n + 1) <= 9223372036854775807]],
			{"Introduce"[n, h], "NonlinearArithmetic"}
		]]},
			{Last[timed]["Goals"], First[timed] < 10}
		]
	},
	{{}, {}, {{}, True}},
	TestID -> "NonlinearArithmetic-proves-bounds-with-large-literals"
]


(* the term of an unfinished proof has a hole for each open goal, numbered as the goals are listed, whatever ids the
   proof keeps: ?1 and ?2 after the induction, and ?1, the step, once the base case is closed *)
VerificationTest[
	With[{proof = TypeTheoryProof[ForAll[{Typed[n, Naturals]}, 0 + n == n], {"Introduce"[n], "Induction"[n]}]},
		{
			Cases[proof["Term"], Placeholder[hole_String, ___] :> hole, {0, Infinity}, Heads -> True],
			Cases[TypeTheoryTactic["Reflexivity"][proof]["Term"], Placeholder[hole_String, ___] :> hole, {0, Infinity}, Heads -> True],
			(* each hole carries its goal, which it shows on mouseover: the base case, and the step under its hypothesis *)
			Cases[proof["Term"], Placeholder[_String, goal_] :> HoldComplete[goal], {0, Infinity}, Heads -> True] === Map[Function[goal, Replace[goal, TypeTheoryTerm[sequent_, ___] :> HoldComplete[sequent]]], proof["Goals"]],
			With[{boxes = Block[{WolframInstitute`TypeTheory`PackageScope`$displayTooltips = True}, ToBoxes[proof["Term"]]]},
				Map[
					Function[hole, Count[boxes, TooltipBox[box_ /; ! FreeQ[box, text_String /; StringContainsQ[text, hole]] && FreeQ[box, _TooltipBox], tip_ /; tip =!= "", ___], {0, Infinity}]],
					{"?1", "?2"}
				]
			]
		}
	],
	{{"?1", "?2"}, {"?1"}, True, {1, 1}},
	TestID -> "The-holes-of-an-unfinished-proof's-term-are-numbered-as-its-goals"
]

(* A definition by recursion unfolds at x + 1 as at successor[x], which shows alike, and recurses on x as it is written;
   at x + 2 it unfolds twice. A recursion that gives a function, the recursor applied further to the definition's last
   variables, unfolds too, its recursive call folded back into the definition. And a rewrite finds f[k + 1] where the
   goal has f[successor[k]]. Each goal is closed by the reflexivity that ends the rewrite. *)
VerificationTest[
	With[
		{
			unfolding = TypeTheoryEnvironment[{
				TypeTheoryDefinition[UnfoldingSum, n |-> InductiveRecursor[Naturals][Naturals &, 0, {k, r} |-> (k + 1) + r, n]],
				TypeTheoryDefinition[UnfoldingAdd, {n, m} |-> InductiveRecursor[Naturals][(Naturals -> Naturals) &, x |-> x, {k, r} |-> (x |-> r[x + 1]), n][m]]
			}]
		},
		{
			TypeTheoryProof[ForAll[{a}, UnfoldingSum[a + 1] == (a + 1) + UnfoldingSum[a]], unfolding, {"Introduce"[a], "RewriteRepeated"[UnfoldingSum]}]["Goals"],
			TypeTheoryProof[ForAll[{a}, UnfoldingSum[a + 2] == (a + 1 + 1) + ((a + 1) + UnfoldingSum[a])], unfolding, {"Introduce"[a], "RewriteRepeated"[UnfoldingSum]}]["Goals"],
			TypeTheoryProof[ForAll[{a, b}, UnfoldingAdd[a + 1, b] == UnfoldingAdd[a, b + 1]], unfolding, {"Introduce"[a, b], "RewriteRepeated"[UnfoldingAdd]}]["Goals"],
			NormalForm[TypeTheoryTerm[UnfoldingAdd[3, 4], unfolding]],
			TypeTheoryProof[ForAll[{Typed[f, Naturals -> Naturals], Typed[k, Naturals]}, Implies[f[k + 1] == 0, f["successor"[k]] == 0]], {"Introduce"[f, k, h], "Rewrite"[h]}]["Goals"],
			(* a variable for the argument: nothing unfolds, and the goal that no lemma changes is a failure *)
			Replace[TypeTheoryProof[ForAll[{a}, UnfoldingSum[a] == 0], unfolding, {"Introduce"[a], "RewriteRepeated"[UnfoldingSum]}], failure_Failure :> failure["Tag"]]
		}
	],
	{{}, {}, {}, TypeTheoryTerm[7, _], {}, "NoProgress"},
	SameTest -> MatchQ,
	TestID -> "A-recursion-unfolds-at-a-sum-with-a-literal-and-where-it-gives-a-function"
]

(* "Cases" and "Induction" split on a term that is no hypothesis: every copy of it in the goal becomes a variable, which
   is split, and each case is stated with the recursors that meet a constructor computed. The proof they give is checked
   by the kernel as any other. A term the goal does not have is refused, and a hypothesis is still split by its name. *)
VerificationTest[
	Module[{statement, split, finished, sum},
		split = TypeTheoryProof[
			ForAll[{Typed[n, NonNegativeIntegers], Typed[m, NonNegativeIntegers]},
				InductiveRecursor[Booleans][Function[{Typed[b, Booleans]}, NonNegativeIntegers], n, n + 1, Decide[m == 0]] <= n + 1
			],
			prelude,
			{"Introduce"[n, m], "Cases"[Decide[m == 0]]}
		];
		finished = TypeTheoryTactic["LinearArithmetic"][TypeTheoryTactic["LinearArithmetic"][split]];
		sum = TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers], Typed[m, NonNegativeIntegers]}, 0 + (n + m) == n + m], prelude,
			{"Introduce"[n, m], "Induction"[n + m], "Reflexivity", "Introduce"[k, ih], "Exact"["equalityCongruence"["successor", ih]]}
		];
		{
			split["Goals"],
			finished["Goals"],
			Head[TypeTheoryEnvironment[prelude, TypeTheoryTheorem["splitOnADecision", finished]]],
			sum["Goals"],
			Head[TypeTheoryEnvironment[prelude, TypeTheoryTheorem["inductionOnASum", sum]]],
			TypeTheoryTactic["Cases", Decide[m == 1]][
				TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers], Typed[m, NonNegativeIntegers]}, n + m == n + m], prelude, {"Introduce"[n, m]}]
			],
			Length[TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, n == n], prelude, {"Introduce"[n], "Cases"[n]}]["Goals"]]
		}
	],
	{
		{
			TypeTheoryTerm[RightTee[{Typed[n, NonNegativeIntegers], Typed[m, NonNegativeIntegers]}, n <= n + 1], _],
			TypeTheoryTerm[RightTee[{Typed[n, NonNegativeIntegers], Typed[m, NonNegativeIntegers]}, n + 1 <= n + 1], _]
		},
		{},
		TypeTheoryEnvironment,
		{},
		TypeTheoryEnvironment,
		Failure["NoInstance", _],
		2
	},
	SameTest -> MatchQ,
	TestID -> "Cases-and-Induction-split-on-a-term-of-the-goal"
]

(* A tactic's comparison remembers its steps, as a kernel check does. Quotient[k + 12, 12] and Quotient[k, 12] + 1 are
   not equal by computation, and saying so took three times as long for each unit of the divisor, half an hour at 12,
   while the comparison repeated its parts; "Change" and "Assumption" compare the same way. *)
VerificationTest[
	With[{integers = TypeTheoryEnvironment["Integers"]},
		TimeConstrained[
			{
				TypeTheoryProof[ForAll[{Typed[k, NonNegativeIntegers]}, Quotient[k + 12, 12] == Quotient[k, 12] + 1], integers, {"Introduce"[k], "Reflexivity"}],
				TypeTheoryProof[ForAll[{Typed[k, NonNegativeIntegers]}, Quotient[k + 12, 12] == Quotient[k, 12] + 1], integers,
					{"Introduce"[k], "Change"[Quotient[k, 12] + 1 == Quotient[k + 12, 12]]}],
				TypeTheoryProof[
					ForAll[{Typed[k, NonNegativeIntegers]}, Implies[Quotient[k, 12] + 1 == Quotient[k + 12, 12], Quotient[k + 12, 12] == Quotient[k, 12] + 1]],
					integers,
					{"Introduce"[k, h], "Assumption"}
				]
			},
			60,
			"TimedOut"
		]
	],
	{Failure["NotReflexive", _], Failure["NotDefinitionallyEqual", _], Failure["NoAssumption", _]},
	SameTest -> MatchQ,
	TestID -> "A-tactic-that-compares-two-terms-answers-in-time"
]

(* Outside the kernel's own files every comparison by definitionallyEqualQ runs with the kernel's caches: it is written
   inside withKernelCaches, or inside withCheckedTerms, which has them. The sources are read held, in a context of their
   own, and each call is looked for under one of the two; a caller that is under neither is listed, by its file. *)
VerificationTest[
	Module[{kernelFiles, files, named, uncachedCalls},
		kernelFiles = {
			"CoreTerms.wl", "TypeChecking.wl", "InductiveTypes.wl", "NaturalNumbers.wl", "Quotients.wl", "Quantities.wl", "Cubical.wl", "Environment.wl",
			"Declarations.wl", "CompiledKernel.wl"
		};
		files = Select[FileNames["*.wl", FileNameJoin[{Directory[], "TypeTheory", "Kernel"}], Infinity], Function[file, ! MemberQ[kernelFiles, FileNameTake[file]]]];
		named[held_, position_, names_] := Replace[
			Extract[held, Append[position, 0], HoldComplete],
			{HoldComplete[head_Symbol] :> MemberQ[names, SymbolName[Unevaluated[head]]], _ -> False}
		];
		uncachedCalls[file_] := Block[{$Context = "TypeTheoryCallerScan`", $ContextPath = {"System`"}},
			With[{held = ReadList[file, HoldComplete[Expression]]},
				Count[
					Position[held, call_ /; named[HoldComplete[call], {1}, {"definitionallyEqualQ"}], {2, Infinity}],
					position_ /; NoneTrue[Range[Length[position] - 1], Function[depth, named[held, Take[position, depth], {"withKernelCaches", "withCheckedTerms"}]]]
				]
			]
		];
		{
			Length[files] > 20,
			Select[Map[Function[file, {FileNameTake[file], uncachedCalls[file]}], files], Function[entry, Last[entry] > 0]]
		}
	],
	{True, {}},
	TestID -> "Every-comparison-outside-the-kernel-runs-with-the-kernels-caches"
]
