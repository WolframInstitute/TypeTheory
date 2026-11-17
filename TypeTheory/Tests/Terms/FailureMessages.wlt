(* ::Package:: *)

(* Tests for the messages of TypeTheory's failures: a message is plain text wherever it is read, in a log, a test or an
   agent's string, its parameters the text of their boxes and never Wolfram's linear syntax for boxes, \!\(...\); the
   parameters stay the terms they are.
   Run with: TestReport["TypeTheory/Tests/Terms/FailureMessages.wlt"] from the repository root. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

prelude = TypeTheoryEnvironment["Prelude"]

mismatch = TypeTheoryEnvironment[prelude, {TypeTheoryTheorem["bad", 2 + 2 == 5, "equalityReflexivity"[4]]}]

(* a failure of every area: checking, elaboration, a tactic, an environment by name, a query, rules, a check's method,
   a definition read from the Wolfram Language *)
messages = {
	mismatch,
	TypeTheoryType[TypeTheoryTerm[Typed["trueIntroduction", False], prelude]],
	TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, n == n + 1], prelude, {"Introduce"[n], "Reflexivity"}],
	TypeTheoryEnvironment["NoSuchEnvironment"],
	Information[prelude, "NoSuchProperty"],
	TypeTheoryCheck[prelude, Method -> "NoSuchMethod"],
	TypeTheoryRules["NoSuchRules"],
	TypeTheoryFormalize[Typed[Plus, {"PackedArray"::["Integer64", 3]} -> "Integer64"], "Machine"]
}

VerificationTest[
	{
		Map[Head, messages],
		Select[messages, Function[result, ! StringQ[result["Message"]] || ! StringFreeQ[result["Message"], "\\!\\("]]],
		StringStartsQ[mismatch["Message"], "equalityReflexivity[4] has type 4"],
		StringFreeQ[mismatch["Message"], "store$"],
		MatchQ[mismatch["MessageParameters"], {_HoldForm, _TypeTheoryTerm, _TypeTheoryTerm}]
	},
	{
		ConstantArray[Failure, 8],
		{},
		True,
		True,
		True
	},
	TestID -> "A-failure-message-is-plain-text-in-every-area-and-its-parameters-stay-terms"
]

(* a message shows the same text whether boxes are drawn for a notebook or for a terminal *)
VerificationTest[
	Map[
		Function[setting, Internal`WithLocalSettings[
			SetEnvironment["TYPETHEORY_NOTEBOOK_BOXES" -> setting],
			mismatch["Message"],
			SetEnvironment["TYPETHEORY_NOTEBOOK_BOXES" -> "True"]
		]],
		{"True", None}
	] // Apply[SameQ],
	True,
	TestID -> "A-failure-message-is-the-same-text-for-a-notebook-and-a-terminal"
]
