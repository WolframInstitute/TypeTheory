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
			TypeTheoryCheck[TypeTheoryTerm[ZeroLeftIdentity[7], proved], TypeTheoryTerm[0 + 7 == 7]],
			TypeOf[TypeTheoryTerm[ZeroLeftIdentityAgain, proved]] === TypeTheoryTerm[ForAll[{Typed[m, NonNegativeIntegers]}, 0 + m == m], proved],
			TypeTheoryCheck[proved]
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
	MatchQ[ToBoxes[zeroLeft], _FrameBox] && MatchQ[ToBoxes[TypeTheoryProof[2 + 2 == 4, prelude]], _FrameBox],
	True,
	TestID -> "A-proof-displays-its-goals"
]
