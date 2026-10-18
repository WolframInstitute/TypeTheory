(* ::Package:: *)

(* Tests for Proofs/ProofStates.wl: proof states, the tactics, and the acceptance examples n + 0 == n by
   computation and 0 + n == n by induction. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

SetAttributes[withPrelude, HoldAll]
withPrelude[body_] := Block[{$TypeTheoryEnvironment = $TypeTheoryEnvironment}, body]

zeroLeft = TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, 0 + n == n], {
	TypeTheoryTactic["Introduce", n],
	TypeTheoryTactic["Induction", n],
	TypeTheoryTactic["Reflexivity"],
	TypeTheoryTactic["Introduce", k, ih],
	TypeTheoryTactic["Exact", EqualityCongruence[NaturalNumberSuccessor, ih]]
}]


VerificationTest[
	TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n]]["Goals"],
	{TypeTheoryTerm[RightTee[{}, ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n]]]},
	TestID -> "A-proof-starts-with-its-statement-as-the-goal"
]

VerificationTest[
	TypeTheoryTactic["Introduce", n][TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n]]]["Goals"],
	{TypeTheoryTerm[RightTee[{Typed[n, NonNegativeIntegers]}, n + 0 == n]]},
	TestID -> "Introduce-moves-a-variable-into-the-hypotheses"
]

VerificationTest[
	withPrelude[
		DeclareTheorem[AdditionZeroRight, TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n], {TypeTheoryTactic["Introduce", n], TypeTheoryTactic["Reflexivity"]}]];
		TypeOf[TypeTheoryTerm[AdditionZeroRight]]
	],
	TypeTheoryTerm[ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n]],
	TestID -> "n-plus-zero-is-n-by-computation"
]

VerificationTest[
	TypeTheoryTactic["Introduce", n][TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, 0 + n == n]]] // TypeTheoryTactic["Reflexivity"] // First,
	"NotReflexive",
	TestID -> "zero-plus-n-is-not-n-by-computation"
]

VerificationTest[
	TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, 0 + n == n], {TypeTheoryTactic["Introduce", n], TypeTheoryTactic["Induction", n]}]["Goals"],
	{
		TypeTheoryTerm[RightTee[{}, 0 + NaturalNumberZero == NaturalNumberZero]],
		TypeTheoryTerm[RightTee[{}, ForAll[{Typed[\[FormalN], NonNegativeIntegers]}, Implies[0 + \[FormalN] == \[FormalN], 0 + NaturalNumberSuccessor[\[FormalN]] == NaturalNumberSuccessor[\[FormalN]]]]]]
	},
	TestID -> "Induction-gives-a-goal-per-constructor"
]

VerificationTest[
	zeroLeft["Goals"],
	{},
	TestID -> "zero-plus-n-is-n-by-induction"
]

VerificationTest[
	withPrelude[
		DeclareTheorem[AdditionZeroLeft, zeroLeft];
		{TypeOf[TypeTheoryTerm[AdditionZeroLeft]], TypeTheoryCheck[TypeTheoryTerm[AdditionZeroLeft[7]], TypeTheoryTerm[0 + 7 == 7]], TypeTheoryCheck[$TypeTheoryEnvironment]}
	],
	{TypeTheoryTerm[ForAll[{Typed[n, NonNegativeIntegers]}, 0 + n == n]], True, True},
	TestID -> "A-finished-proof-is-declared-and-used"
]

VerificationTest[
	withPrelude[
		DeclareTheorem[AdditionZeroLeftAgain, ForAll[{Typed[m, NonNegativeIntegers]}, 0 + m == m], zeroLeft];
		TypeOf[TypeTheoryTerm[AdditionZeroLeftAgain]]
	],
	TypeTheoryTerm[ForAll[{Typed[m, NonNegativeIntegers]}, 0 + m == m]],
	TestID -> "A-proof-stored-in-a-symbol-proves-a-stated-theorem"
]

VerificationTest[
	TypeTheoryProof[ForAll[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]]}, Implies[a, Implies[b, And[a, b]]]], {
		TypeTheoryTactic["Introduce", a, b, ha, hb],
		TypeTheoryTactic["Apply", AndIntroduction],
		TypeTheoryTactic["Assumption"],
		TypeTheoryTactic["Exact", hb]
	}]["Term"],
	TypeTheoryTerm[Function[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]], Typed[ha, a], Typed[hb, b]}, AndIntroduction[ha, hb]]],
	TestID -> "Apply-leaves-a-goal-per-argument"
]

VerificationTest[
	TypeTheoryProof[ForAll[{Typed[x, NonNegativeIntegers], Typed[y, NonNegativeIntegers], Typed[z, NonNegativeIntegers]}, Implies[x == y, Implies[y == z, x == z]]], {
		TypeTheoryTactic["Introduce", x, y, z, h1, h2],
		TypeTheoryTactic["Apply", EqualityTransitivity],
		TypeTheoryTactic["Exact", h1],
		TypeTheoryTactic["Exact", h2]
	}]["Goals"],
	{},
	TestID -> "Solving-a-goal-can-solve-another-goal-it-mentions"
]

VerificationTest[
	TypeTheoryProof[ForAll[{Typed[p, TypeUniverse[0]]}, Implies[p, Not[Not[p]]]], {
		TypeTheoryTactic["Introduce", p, hp, hnp],
		TypeTheoryTactic["Exact", hnp[hp]]
	}]["Goals"],
	{},
	TestID -> "Introduce-unfolds-Not"
]

VerificationTest[
	First /@ {
		TypeTheoryTactic["Introduce", x][TypeTheoryProof[2 + 2 == 4]],
		TypeTheoryTactic["Bogus"][TypeTheoryProof[2 + 2 == 4]],
		TypeTheoryTactic["Exact", EqualityReflexivity[5]][TypeTheoryProof[2 + 2 == 4]],
		TypeTheoryTactic["Reflexivity"][TypeTheoryProof[2 + 2 == 5]],
		TypeTheoryTactic["Reflexivity"][TypeTheoryTactic["Reflexivity"][TypeTheoryProof[2 + 2 == 4]]]
	},
	{"NothingToIntroduce", "UnknownTactic", "TypeMismatch", "NotReflexive", "NoGoals"},
	TestID -> "A-tactic-that-does-not-apply-gives-a-Failure"
]

VerificationTest[
	withPrelude[First @ DeclareTheorem[Absurd, TypeTheoryProof[False]]],
	"ProofIncomplete",
	TestID -> "An-unfinished-proof-cannot-be-declared"
]

VerificationTest[
	MatchQ[ToBoxes[zeroLeft], _FrameBox] && MatchQ[ToBoxes[TypeTheoryProof[2 + 2 == 4]], _FrameBox],
	True,
	TestID -> "A-proof-displays-its-goals"
]
