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

(* an environment among a message's parameters is its head and an ellipsis, never its summary panel's boxes *)
VerificationTest[
	With[{text = TypeTheoryProof[ForAll[{Typed[a, TypeUniverse[0]]}, Implies[a, a]], Automatic, prelude]["Message"]},
		{StringQ[text], StringContainsQ[text, "TypeTheoryEnvironment[\[Ellipsis]]"], StringFreeQ[text, "Box" | "FontCapHeight" | "\n"]}
	],
	{True, True, True},
	TestID -> "An-environment-in-a-failure-message-is-its-head-and-an-ellipsis"
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

(* text for a terminal has no character of Unicode's private use area, which a terminal shows as nothing: ℕ, 𝔹 and ==
   are written as Unicode and ASCII *)
VerificationTest[
	With[
		{
			failure = TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers], Typed[b, Booleans]}, n == n + 1], {"Introduce"[n, b], "Reflexivity"}],
			text = ToString[TypeTheoryTerm[ForAll[{Typed[k, NonNegativeIntegers]}, k == k]]]
		},
		{
			Select[ToCharacterCode[failure["Message"] <> text], 57344 <= # <= 63743 &],
			StringContainsQ[failure["Message"], "\:2115"] && StringContainsQ[failure["Message"], "\|01d539"] && StringContainsQ[failure["Message"], "=="],
			StringContainsQ[text, "\:2115"] && StringContainsQ[text, "=="]
		}
	],
	{{}, True, True},
	TestID -> "Text-for-a-terminal-has-no-private-use-characters"
]
