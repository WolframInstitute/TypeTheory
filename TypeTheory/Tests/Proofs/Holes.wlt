(* ::Package:: *)

(* Tests for holes: TypeTheoryHole and TypeTheoryTactic["Hole"] leave a proof to give, as Lean's sorry, and the theorem
   declares a constant of the kind "Hole" for each, which the queries report apart from the axioms.
   Run with: TestReport["TypeTheory/Tests/Proofs/Holes.wlt"] from the repository root. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

open = TypeTheoryEnvironment[{
	TypeTheoryTheorem[AllZero, ForAll[{Typed[n, Naturals]}, n == 0], Function[{Typed[n, Naturals]}, TypeTheoryHole[<|"Citation" -> "nowhere", "Evaluation" -> HoldForm[2 + 2]|>]]],
	TypeTheoryTheorem[ThreeIsZero, 3 == 0, AllZero[3]],
	TypeTheoryTheorem[Proved, 1 == 1, EqualityReflexivity[1]]
}]


VerificationTest[
	Take[Keys[open], -4],
	{TypeTheoryHole[AllZero, 1], AllZero, ThreeIsZero, Proved},
	TestID -> "A-theorem-with-a-hole-declares-the-hole-before-it"
]

VerificationTest[
	{
		Keys[Information[TypeTheoryTerm[ThreeIsZero, open], "Holes"]],
		Information[TypeTheoryTerm[ThreeIsZero, open], "Holes"][AllZero][[1, "Annotation"]],
		Information[TypeTheoryTerm[Proved, open], "Holes"],
		TypeTheoryAxiomClosure[TypeTheoryTerm[ThreeIsZero, open]]
	},
	{{AllZero}, <|"Citation" -> "nowhere", "Evaluation" -> HoldForm[2 + 2]|>, <||>, <||>},
	TestID -> "A-theorem-that-uses-one-with-a-hole-inherits-it-and-holes-are-no-axioms"
]

VerificationTest[
	{
		MatchQ[TypeTheoryCheck[open], _Success],
		Keys[TypeTheoryEnvironment[TypeTheoryEnvironment[], Normal[open]]] === Keys[open],
		Normal[TypeTheoryEnvironment[TypeTheoryEnvironment[], Normal[open]]] === Normal[open],
		FreeQ[Normal[open], TypeTheoryHole[_, _]]
	},
	{True, True, True, True},
	TestID -> "Holes-replay-and-read-back-as-the-TypeTheoryHole-they-were-written-as"
]

VerificationTest[
	With[{proved = TypeTheoryEnvironment[{TypeTheoryTheorem[Halfway, TypeTheoryProof[ForAll[{Typed[n, Naturals]}, n + 0 == n && 0 + n == n], {
			TypeTheoryTactic["Introduce", n], TypeTheoryTactic["Constructor"], TypeTheoryTactic["Reflexivity"], TypeTheoryTactic["Hole", "zero plus n"]
		}]]}]},
		{
			Information[TypeTheoryTerm[Halfway, proved], "Holes"][Halfway][[1, "Annotation"]],
			MatchQ[TypeTheoryCheck[proved], _Success]
		}
	],
	{<|"Citation" -> "zero plus n"|>, True},
	TestID -> "The-Hole-tactic-closes-a-goal-with-a-hole-over-its-hypotheses"
]

VerificationTest[
	{
		TypeTheoryCheck[TypeTheoryTerm[Typed[TypeTheoryHole[], 1 == 1]]]["Tag"],
		TypeTheoryEnvironment[{TypeTheoryTheorem[InStatement, TypeTheoryHole[], EqualityReflexivity[1]]}]["Tag"],
		TypeTheoryEnvironment[{TypeTheoryTheorem[Unfinished, TypeTheoryProof[1 == 1, {}]]}]["Tag"]
	},
	{"ElaborationFailed", "ElaborationFailed", "ProofIncomplete"},
	TestID -> "A-hole-stands-only-in-a-proof-and-an-open-goal-is-still-no-proof"
]

VerificationTest[
	Module[{file = FileNameJoin[{$TemporaryDirectory, "holes-test.wxf"}], loaded},
		Export[file, open];
		loaded = TypeTheoryEnvironment[File[file]];
		DeleteFile[file];
		{Normal[loaded] === Normal[open], Information[TypeTheoryTerm[TypeTheoryHole[AllZero, 1], loaded], "Annotation"]}
	],
	{True, <|"Citation" -> "nowhere", "Evaluation" -> HoldForm[2 + 2]|>},
	TestID -> "A-saved-environment-keeps-its-holes-and-their-annotations"
]
