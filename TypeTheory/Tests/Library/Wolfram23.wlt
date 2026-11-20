(* ::Package:: *)

(* Tests for Library/Wolfram23.wl: the systems of Smith's chain of emulations to Wolfram's (2,3) Turing machine, the
   framework of step functions and simulations, and the relabelings from System 3 to System 0, every theorem checked
   when the environment is built. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

wolfram23 = TypeTheoryEnvironment["Wolfram23"]

configuration[left_List, head_, right_List, state_] := "lookaheadConfiguration"[left, head, right, state]

VerificationTest[
	{
		Head[wolfram23],
		Length[Information[wolfram23, "Constants"]],
		Select[
			{"stepsAdd", "optionCases", "forwardSimulation", "forwardSimulationSteps", "forwardSimulationCompose", "relabelingSimulation", "phi3Step", "phi2Step",
				"system0FollowsSystem1", "system0StepsPositive", "system0Simulates1", "system0Simulates3", "turingMachineFollowsSystem0", "agreementSimulation",
				"wolfram23Simulates3", "cyclicTagStep", "selected", "cyclicTagBlock", "selectedOneHot", "encodeWordJoin", "cyclicTagBlockSteps", "cookStep"},
			! MemberQ[Keys[wolfram23], #] &
		]
	},
	{TypeTheoryEnvironment, 351, {}},
	TestID -> "The-Wolfram23-environment-has-the-framework-and-the-relabelings-from-System-3-to-System-0"
]

(* System 0 is Wolfram's (2,3) machine: A0 -> B1>, and a move off the left end is none *)
VerificationTest[
	{
		DefinitionallyEqualQ[
			TypeTheoryTerm["lookaheadStep"["system0", "lookaheadConfiguration"[{}, "color0", {"color0", "color0"}, "stateA"]], wolfram23],
			TypeTheoryTerm["some"["lookaheadConfiguration"[{"color1"}, "color0", {"color0"}, "stateB"]], wolfram23]
		],
		DefinitionallyEqualQ[
			TypeTheoryTerm["lookaheadStep"["system0", "lookaheadConfiguration"[{}, "color1", {"color0"}, "stateA"]], wolfram23],
			TypeTheoryTerm[Typed["none", Option["LookaheadConfiguration"]], wolfram23]
		]
	},
	{True, True},
	TestID -> "System-0-steps-as-Wolframs-2-3-machine-and-stops-at-the-left-end"
]

(* at the right end the lookahead machine stops, and the standard machine moves onto a new blank *)
VerificationTest[
	{
		DefinitionallyEqualQ[
			TypeTheoryTerm["lookaheadStep"["system0", "lookaheadConfiguration"[{"color2"}, "color0", {}, "stateA"]], wolfram23],
			TypeTheoryTerm[Typed["none", Option["LookaheadConfiguration"]], wolfram23]
		],
		DefinitionallyEqualQ[
			TypeTheoryTerm["turingMachineStep"["system0", "lookaheadConfiguration"[{"color2"}, "color0", {}, "stateA"]], wolfram23],
			TypeTheoryTerm["some"["lookaheadConfiguration"[{"color1", "color2"}, "color0", {}, "stateB"]], wolfram23]
		]
	},
	{True, True},
	TestID -> "The-standard-machine-extends-the-tape-where-the-lookahead-machine-stops"
]

(* System 1's B21 is three steps of System 0, B2 -> A0>, A1 -> A2<, A0 -> B1>, to where System 1's B12> goes *)
VerificationTest[
	{
		DefinitionallyEqualQ[
			TypeTheoryTerm["system0Steps"["lookaheadConfiguration"[{}, "color2", {"color1", "color0"}, "stateB"]], wolfram23],
			TypeTheoryTerm[3, wolfram23]
		],
		DefinitionallyEqualQ[
			TypeTheoryTerm["steps"["lookaheadStep"["system0"], 3, "lookaheadConfiguration"[{"color0"}, "color2", {"color1", "color0"}, "stateB"]], wolfram23],
			TypeTheoryTerm["lookaheadStep"["system1", "lookaheadConfiguration"[{"color0"}, "color2", {"color1", "color0"}, "stateB"]], wolfram23]
		]
	},
	{True, True},
	TestID -> "System-1s-B21-is-three-steps-of-System-0"
]

(* the case tree proves only what holds: phi3 does not turn a step of System 3 into one of System 1. In state C at the
   left end, System 3's C0 moves left off the tape, while System 1's C0 moves right *)
caseTree = With[
	{
		leftSplit = {"Cases"[left], "Reflexivity", "Introduce"[x, rest], "Reflexivity"},
		colorSplit = Function[{variable, branch}, Join[{"Cases"[variable]}, branch, branch, branch]]
	},
	With[{rightSplit = Join[{"Cases"[right]}, leftSplit, {"Introduce"[neighbour, beyond]}, colorSplit[neighbour, leftSplit]]},
		Join[{"Introduce"[c], "Cases"[c], "Introduce"[left, head, right, state], "Cases"[state]}, Flatten[ConstantArray[colorSplit[head, rightSplit], 3], 1]]
	]
]

VerificationTest[
	{
		DefinitionallyEqualQ[
			TypeTheoryTerm["lookaheadStep"["system1", "phi3"["lookaheadConfiguration"[{}, "color0", {"color0"}, "stateC"]]], wolfram23],
			TypeTheoryTerm["optionMap"["phi3", "lookaheadStep"["system3", "lookaheadConfiguration"[{}, "color0", {"color0"}, "stateC"]]], wolfram23]
		],
		With[{script = caseTree}, Head[TypeTheoryProof[
			ForAll[{Typed[c, "LookaheadConfiguration"]}, "lookaheadStep"["system1", "phi3"[c]] == "optionMap"["phi3", "lookaheadStep"["system3", c]]],
			wolfram23,
			script
		]]]
	},
	{False, Failure},
	TestID -> "A-relabeling-to-the-wrong-system-is-refused"
]

(* a cyclic tag system: data 1 0 with appendants 1 and 0 0; the 1 appends the first appendant, the 0 nothing, and the
   appendants come round again after two steps *)
VerificationTest[
	DefinitionallyEqualQ[
		TypeTheoryTerm["steps"["cyclicTagStep", 2, "cyclicTagConfiguration"[{"true", "false"}, {{"true"}, {"false", "false"}}]], wolfram23],
		TypeTheoryTerm["some"["cyclicTagConfiguration"[{"true"}, {{"true"}, {"false", "false"}}]], wolfram23]
	],
	True,
	TestID -> "A-cyclic-tag-system-appends-under-its-ones-and-rotates-its-appendants"
]

(* Cook's construction on a 2-tag system of two symbols, 0 -> 1 and 1 -> 0 0: the tag step from 0 1 1 to 1 1 is 2 + 2 steps
   of the cyclic tag system between the encoded words *)
productions = Function[{Typed[i, NonNegativeIntegers]},
	InductiveRecursor[NonNegativeIntegers][Function[{Typed[q, NonNegativeIntegers]}, {NonNegativeIntegers}], {1}, Function[{Typed[j, NonNegativeIntegers], Typed[r, {NonNegativeIntegers}]}, {0, 0}], i]]

VerificationTest[
	With[{productions = productions},
		{
			DefinitionallyEqualQ[TypeTheoryTerm["tagStep"[productions, {0, 1, 1}], wolfram23], TypeTheoryTerm["some"[{1, 1}], wolfram23]],
			DefinitionallyEqualQ[
				TypeTheoryTerm["steps"["cyclicTagStep", 4, "cookConfiguration"[2, productions, {0, 1, 1}]], wolfram23],
				TypeTheoryTerm["some"["cookConfiguration"[2, productions, {1, 1}]], wolfram23]
			]
		}
	],
	{True, True},
	TestID -> "A-tag-step-is-k-plus-k-steps-of-Cooks-cyclic-tag-system"
]
