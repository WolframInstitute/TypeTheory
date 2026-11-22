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
				"wolfram23Simulates3", "cyclicTagStep", "selected", "cyclicTagBlock", "selectedOneHot", "encodeWordJoin", "cyclicTagBlockSteps", "cookStep", "someInjective", "noneNotSome", "allBelowJoin", "cookSimulation", "passOutAlignedPairs", "passOutShiftedPairs", "tagRoundEven", "tagRoundOddBefore", "tagRoundOddFirst", "tagRoundEvenWhole",
				"minskyRound1", "minskyRound2", "minskyRound3Right", "minskyRound3Left", "minskyRound4", "minskyRound5", "minskyStep", "minskySimulation",
				"divideMultiple", "minskyDecodeEncode", "minskyNumbersSimulation", "divideSpecification", "minskyNumbersBelow", "machineToCyclicTag",
				"xorMergeAppendant", "bound5Step", "ctsToSystem5Represents", "ctsToSystem5BagStrictlyAbove", "ctsToSystem5RulesStrictlyAbove",
				"representsDecode", "representsRulesEmpty", "representsBagNonEmpty", "representsTerminal", "representsStepFalse", "representsStepTrue", "system5Simulation",
				"system4Step", "system4DStep", "system4PopPhase", "system5ToSystem4", "system5ToSystem4WellFormed", "system5ToSystem4Represents",
				"decodeS4", "repS4DStep", "repS4PStep", "repS4TurnStep", "repS4DecodeBand", "repS4Exit", "repS4Terminal", "system4Simulation",
				"stepRIteratePow2", "parAtRowBits", "sys3ScanBlock", "encSet", "initAC", "rep3Init", "system3Simulation", "system0SimulatesSystem4",
				"rep3Exit", "phiExit", "wolfram23ExitStep", "decodeBlocks", "decodeW23", "rep3Decode",
				"forwardSimulationSchedule", "configSize", "turingMachineConfinement", "conjecture0Finite",
				"undbl", "decodeOneHot", "decodeTagWord", "parseWord", "natToBits", "trimTrailingFalse", "canon", "decodeCTS", "decodeTM",
				"decodeCTSWord", "wolfram23Universal"},
			! MemberQ[Keys[wolfram23], #] &
		]
	},
	{TypeTheoryEnvironment, 1089, {}},
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

(* a round of the tag system 0 -> 1, 1 -> 0 0 over 0 1 1 1: two steps read 0 and 1, and append what the round reads *)
VerificationTest[
	With[{productions = productions},
		{
			DefinitionallyEqualQ[TypeTheoryTerm["steps"["tagStep"[productions], 2, {0, 1, 1, 1}], wolfram23], TypeTheoryTerm["some"[{1, 0, 0}], wolfram23]],
			DefinitionallyEqualQ[TypeTheoryTerm["passOutFrom"[productions, {0, 1, 1, 1}, "true"], wolfram23], TypeTheoryTerm[{1, 0, 0}, wolfram23]],
			DefinitionallyEqualQ[TypeTheoryTerm["passOutFrom"[productions, {0, 1, 1, 1}, "false"], wolfram23], TypeTheoryTerm[{0, 0, 0, 0}, wolfram23]]
		}
	],
	{True, True, True},
	TestID -> "A-round-of-a-tag-system-reads-the-first-symbol-of-each-pair"
]

(* rung 1: a binary machine's step is rounds of the tag system that follows it, from the word of the configuration to the
   word of the next. A move to the right from state 1 on a blank tape is three rounds, 2 + 2 + 2 steps; a move to the left
   with a 1 on the left is five, 3 + 3 + 3 + 2 + 2 *)
VerificationTest[
	{
		DefinitionallyEqualQ[
			TypeTheoryTerm["binaryStep"[Function[{Typed[q, NonNegativeIntegers], Typed[h, Booleans]}, "machineTransition"[0, "true", "moveRight"]], "binaryConfiguration"[1, Typed[{}, {Booleans}], "false", Typed[{}, {Booleans}]]], wolfram23],
			TypeTheoryTerm["some"["binaryConfiguration"[0, {"true"}, "false", Typed[{}, {Booleans}]]], wolfram23]
		],
		DefinitionallyEqualQ[
			TypeTheoryTerm["steps"["tagStep"["minskyProductions"[Function[{Typed[q, NonNegativeIntegers], Typed[h, Booleans]}, "machineTransition"[0, "true", "moveRight"]]]], 6,
				"binaryWord"["binaryConfiguration"[1, Typed[{}, {Booleans}], "false", Typed[{}, {Booleans}]]]], wolfram23],
			TypeTheoryTerm["some"["binaryWord"["binaryConfiguration"[0, {"true"}, "false", Typed[{}, {Booleans}]]]], wolfram23]
		],
		DefinitionallyEqualQ[
			TypeTheoryTerm["steps"["tagStep"["minskyProductions"[Function[{Typed[q, NonNegativeIntegers], Typed[h, Booleans]}, "machineTransition"[0, "true", "moveLeft"]]]], 13,
				"binaryWord"["binaryConfiguration"[1, {"true"}, "false", Typed[{}, {Booleans}]]]], wolfram23],
			TypeTheoryTerm["some"["binaryWord"["binaryConfiguration"[0, Typed[{}, {Booleans}], "true", {"true"}]]], wolfram23]
		]
	},
	{True, True, True},
	TestID -> "A-binary-machine-step-is-three-or-five-rounds-of-the-tag-system"
]

(* rungs 1 and 2 joined: a symbol is the number 84 q + 4 kind + 2 h + b + 1, which decodes back, and a step of the tag
   system on numbers is the step on symbols, encoded *)
VerificationTest[
	{
		DefinitionallyEqualQ[TypeTheoryTerm["minskyEncode"["symbolJ"[2, "true", "false"]], wolfram23], TypeTheoryTerm[84 * 2 + 76 + 2 + 1, wolfram23]],
		DefinitionallyEqualQ[TypeTheoryTerm["minskyDecode"[84 * 2 + 76 + 2 + 1], wolfram23], TypeTheoryTerm["symbolJ"[2, "true", "false"], wolfram23]],
		DefinitionallyEqualQ[TypeTheoryTerm["divideBy"[84, 200], wolfram23], TypeTheoryTerm["quotientRemainder"[2, 32], wolfram23]],
		DefinitionallyEqualQ[
			TypeTheoryTerm["tagStep"["minskyNumbers"[Function[{Typed[q, NonNegativeIntegers], Typed[h, Booleans]}, "machineTransition"[0, "true", "moveRight"]]],
				Map["minskyEncode", "binaryWord"["binaryConfiguration"[1, Typed[{}, {Booleans}], "false", Typed[{}, {Booleans}]]]]], wolfram23],
			TypeTheoryTerm["optionMap"[Function[{Typed[v, {"MinskySymbol"}]}, Map["minskyEncode", v]],
				"tagStep"["minskyProductions"[Function[{Typed[q, NonNegativeIntegers], Typed[h, Booleans]}, "machineTransition"[0, "true", "moveRight"]]],
					"binaryWord"["binaryConfiguration"[1, Typed[{}, {Booleans}], "false", Typed[{}, {Booleans}]]]]], wolfram23]
		]
	},
	{True, True, True, True},
	TestID -> "A-symbol-is-a-number-that-decodes-back-and-the-tag-system-on-numbers-follows"
]

(* rung 3: cyclic tag system to System 5 — Smith's p. 29 example (data 0 1, appendants 1 and 1 0, budget 2):
   t = 0 decodes to 0 0 1 1, t = 4 (after reading 0) to 1 1, t = 10 (after reading 1 and appending 1 0) to 1 1 0 0,
   and t = 11 halts with empty rules and a non-empty bag *)
smith29 = "ctsToSystem5"["cyclicTagConfiguration"[{"false", "true"}, {{"true"}, {"true", "false"}}], 2]

VerificationTest[
	With[{start = smith29},
		{
			DefinitionallyEqualQ[
				TypeTheoryTerm["optionBind"["steps"["system5Step", 0, start], Function[{Typed[s, "System5Configuration"]}, "decodeBag"[s[["bag"]]]]], wolfram23],
				TypeTheoryTerm["some"[{"false", "false", "true", "true"}], wolfram23]
			],
			DefinitionallyEqualQ[
				TypeTheoryTerm["optionBind"["steps"["system5Step", 4, start], Function[{Typed[s, "System5Configuration"]}, "decodeBag"[s[["bag"]]]]], wolfram23],
				TypeTheoryTerm["some"[{"true", "true"}], wolfram23]
			],
			DefinitionallyEqualQ[
				TypeTheoryTerm["optionBind"["steps"["system5Step", 10, start], Function[{Typed[s, "System5Configuration"]}, "decodeBag"[s[["bag"]]]]], wolfram23],
				TypeTheoryTerm["some"[{"true", "true", "false", "false"}], wolfram23]
			],
			DefinitionallyEqualQ[
				TypeTheoryTerm["steps"["system5Step", 11, start], wolfram23],
				TypeTheoryTerm[Typed["none", Option["System5Configuration"]], wolfram23]
			]
		}
	],
	{True, True, True, True},
	TestID -> "System-5-follows-Smiths-p-29-cyclic-tag-example-and-halts-at-budget-zero"
]

(* decodeBag checks strict increase above 0, even length, and gaps 1 or 2; invalid bags decode to none *)
VerificationTest[
	{
		DefinitionallyEqualQ[TypeTheoryTerm["decodeBag"[{0, 1}], wolfram23], TypeTheoryTerm[Typed["none", Option[{Booleans}]], wolfram23]],
		DefinitionallyEqualQ[TypeTheoryTerm["decodeBag"[{3, 4, 1, 2}], wolfram23], TypeTheoryTerm[Typed["none", Option[{Booleans}]], wolfram23]],
		DefinitionallyEqualQ[TypeTheoryTerm["decodeBag"[{1, 2, 5}], wolfram23], TypeTheoryTerm[Typed["none", Option[{Booleans}]], wolfram23]],
		DefinitionallyEqualQ[TypeTheoryTerm["decodeBag"[{1, 4}], wolfram23], TypeTheoryTerm[Typed["none", Option[{Booleans}]], wolfram23]],
		TypeTheoryAxiomClosure[TypeTheoryTerm["system5Simulation", wolfram23]],
		TypeTheoryAxiomClosure[TypeTheoryTerm["bound5Step", wolfram23]],
		TypeTheoryAxiomClosure[TypeTheoryTerm["representsDecode", wolfram23]],
		TypeTheoryAxiomClosure[TypeTheoryTerm["representsTerminal", wolfram23]]
	},
	{True, True, True, True, <||>, <||>, <||>, <||>},
	TestID -> "decodeBag-rejects-malformed-bags-and-rung-3-uses-no-axioms"
]

(* rung 4: System 5 to System 4 — Smith's five zipper transition rules, encoder + decoder round-trip, and odd-parity guard *)
smith34 = "system4Configuration"[{"star4", "set4"[Typed[{}, {NonNegativeIntegers}]], "set4"[{0, 6, 8}]}, {"set4"[{3, 4}], "star4", "set4"[{8}], "set4"[{11, 20}]}, "state4B"]
s4Encoded = "system5ToSystem4"["system5Configuration"[{1, 2}, {{0}}], 4]

VerificationTest[
	With[{trace = smith34, encoded = s4Encoded},
		{
			(* Smith p. 34: in state B on {3, 4} (no 0), decrement to {2, 3} and step right onto star4 *)
			DefinitionallyEqualQ[
				TypeTheoryTerm["system4Step"[trace], wolfram23],
				TypeTheoryTerm["some"["system4Configuration"[{"set4"[{2, 3}], "star4", "set4"[Typed[{}, {NonNegativeIntegers}]], "set4"[{0, 6, 8}]}, {"star4", "set4"[{8}], "set4"[{11, 20}]}, "state4B"]], wolfram23]
			],
			(* Next step: B on star4 drops star4, moves left to {2, 3}, and switches to A *)
			DefinitionallyEqualQ[
				TypeTheoryTerm["steps"["system4Step", 2, trace], wolfram23],
				TypeTheoryTerm["some"["system4Configuration"[{"star4", "set4"[Typed[{}, {NonNegativeIntegers}]], "set4"[{0, 6, 8}]}, {"set4"[{2, 3}], "set4"[{8}], "set4"[{11, 20}]}, "state4A"]], wolfram23]
			],
			(* C on star4 before {8}: steps right past star4, XOR-inserts 1 into {8} -> {1, 8}, stays in C *)
			DefinitionallyEqualQ[
				TypeTheoryTerm["system4Step"["system4Configuration"[{"set4"[{2, 3}]}, {"star4", "set4"[{8}]}, "state4C"]], wolfram23],
				TypeTheoryTerm["some"["system4Configuration"[{"star4", "set4"[{2, 3}]}, {"set4"[{1, 8}]}, "state4C"]], wolfram23]
			],
			(* Encoded System 5 bag {1, 2} decodes back before and after the 1-step turn into state4B *)
			DefinitionallyEqualQ[
				TypeTheoryTerm["decodeS4"[encoded, 6], wolfram23],
				TypeTheoryTerm["some"[{1, 2}], wolfram23]
			],
			DefinitionallyEqualQ[
				TypeTheoryTerm["optionBind"["system4Step"[encoded], Function[{Typed[c, "System4Configuration"]}, "decodeS4"[c, 6]]], wolfram23],
				TypeTheoryTerm["some"[{1, 2}], wolfram23]
			]
		}
	],
	{True, True, True, True, True},
	TestID -> "System-4-follows-Smiths-zipper-rules-and-decodes-encoded-System-5-bags"
]

(* decodeS4 rejects odd-parity elements with none, and all rung 4 theorems use no axioms *)
VerificationTest[
	{
		DefinitionallyEqualQ[
			TypeTheoryTerm["decodeS4"["system4Configuration"[Typed[{}, {"System4Element"}], {"set4"[{1}], "star4"}, "state4B"], 4], wolfram23],
			TypeTheoryTerm[Typed["none", Option[{NonNegativeIntegers}]], wolfram23]
		],
		DefinitionallyEqualQ[
			TypeTheoryTerm["decodeS4"["system4Configuration"[Typed[{}, {"System4Element"}], {"set4"[{0, 3}], "star4"}, "state4B"], 4], wolfram23],
			TypeTheoryTerm[Typed["none", Option[{NonNegativeIntegers}]], wolfram23]
		],
		TypeTheoryAxiomClosure[TypeTheoryTerm["system4Simulation", wolfram23]],
		TypeTheoryAxiomClosure[TypeTheoryTerm["system5ToSystem4Represents", wolfram23]],
		TypeTheoryAxiomClosure[TypeTheoryTerm["system5ToSystem4WellFormed", wolfram23]],
		TypeTheoryAxiomClosure[TypeTheoryTerm["repS4DecodeBand", wolfram23]],
		TypeTheoryAxiomClosure[TypeTheoryTerm["repS4TurnStep", wolfram23]],
		TypeTheoryAxiomClosure[TypeTheoryTerm["repS4Terminal", wolfram23]]
	},
	{True, True, <||>, <||>, <||>, <||>, <||>, <||>},
	TestID -> "decodeS4-rejects-odd-parity-elements-and-rung-4-uses-no-axioms"
]

(* rung 5: System 4 to System 3 — Rule-60 parity blocks, encSet + decodeW23 round-trip, and exit step *)
VerificationTest[
	{
		(* Rule-60 parity orthogonality at width 2^3 = 8 *)
		DefinitionallyEqualQ[TypeTheoryTerm["parAt"["rowBits"[8, 2], 2], wolfram23], TypeTheoryTerm["true", wolfram23]],
		DefinitionallyEqualQ[TypeTheoryTerm["parAt"["rowBits"[8, 2], 5], wolfram23], TypeTheoryTerm["false", wolfram23]],
		(* encSet always starts with true and decodes back to the System 5 bag {1, 2} *)
		DefinitionallyEqualQ[TypeTheoryTerm["headBool"["encSet"[8, {0, 2}]], wolfram23], TypeTheoryTerm["true", wolfram23]],
		DefinitionallyEqualQ[
			TypeTheoryTerm["decodeBlocks"[8, 6, "ofBits"["encSet"[8, {0, 2}]]], wolfram23],
			TypeTheoryTerm["some"[{1, 2}], wolfram23]
		],
		DefinitionallyEqualQ[
			TypeTheoryTerm["decodeW23"[8, 6, "lookaheadConfiguration"[Typed[{}, {"Color"}],
				"toCell"["headBool"["encSet"[8, {0, 2}]]],
				Join["tailList"["ofBits"["encSet"[8, {0, 2}]]], {"color0", "color2"}],
				"stateB"]], wolfram23],
			TypeTheoryTerm["some"[{"false"}], wolfram23]
		],
		(* Final exit step of Wolfram's (2,3) machine from state B on color2 at the right end of the tape *)
		DefinitionallyEqualQ[
			TypeTheoryTerm["turingMachineStep"["system0", "lookaheadConfiguration"[{"color1"}, "color2", Typed[{}, {"Color"}], "stateB"]], wolfram23],
			TypeTheoryTerm["some"["lookaheadConfiguration"[{"color0", "color1"}, "color0", Typed[{}, {"Color"}], "stateA"]], wolfram23]
		]
	},
	{True, True, True, True, True, True},
	TestID -> "System-3-Rule-60-parity-blocks-decodeW23-round-trip-and-exit-step"
]

(* decodeW23 and decodeBlocks reject head == color0, empty tapes, non-multiple widths, and odd parity; rung 5 uses no axioms *)
VerificationTest[
	{
		DefinitionallyEqualQ[
			TypeTheoryTerm["decodeW23"[4, 4, "lookaheadConfiguration"[Typed[{}, {"Color"}], "color0", {"color1", "color1", "color1", "color1"}, "stateB"]], wolfram23],
			TypeTheoryTerm[Typed["none", Option[{Booleans}]], wolfram23]
		],
		DefinitionallyEqualQ[
			TypeTheoryTerm["decodeBlocks"[4, 4, {"color1", "color2", "color1"}], wolfram23],
			TypeTheoryTerm[Typed["none", Option[{NonNegativeIntegers}]], wolfram23]
		],
		DefinitionallyEqualQ[
			TypeTheoryTerm["decodeBlocks"[4, 4, Typed[{}, {"Color"}]], wolfram23],
			TypeTheoryTerm[Typed["none", Option[{NonNegativeIntegers}]], wolfram23]
		],
		DefinitionallyEqualQ[
			TypeTheoryTerm["decodeBlocks"[8, 4, "ofBits"["rowBits"[8, 1]]], wolfram23],
			TypeTheoryTerm[Typed["none", Option[{NonNegativeIntegers}]], wolfram23]
		],
		TypeTheoryAxiomClosure[TypeTheoryTerm["parAtRowBits", wolfram23]],
		TypeTheoryAxiomClosure[TypeTheoryTerm["system3Simulation", wolfram23]],
		TypeTheoryAxiomClosure[TypeTheoryTerm["system0SimulatesSystem4", wolfram23]],
		TypeTheoryAxiomClosure[TypeTheoryTerm["rep3Init", wolfram23]],
		TypeTheoryAxiomClosure[TypeTheoryTerm["rep3Exit", wolfram23]],
		TypeTheoryAxiomClosure[TypeTheoryTerm["rep3Decode", wolfram23]],
		TypeTheoryAxiomClosure[TypeTheoryTerm["wolfram23ExitStep", wolfram23]]
	},
	{True, True, True, True, <||>, <||>, <||>, <||>, <||>, <||>, <||>},
	TestID -> "decodeW23-rejects-malformed-tapes-and-rung-5-uses-no-axioms"
]

(* rung 7: computable decoder stack (undbl, decodeOneHot, decodeTagWord, parseWord, natToBits, canon, decodeCTS) *)
VerificationTest[
	{
		DefinitionallyEqualQ[
			TypeTheoryTerm["undbl"["doubleWord"[{"true", "false", "true"}]], wolfram23],
			TypeTheoryTerm["some"[{"true", "false", "true"}], wolfram23]
		],
		DefinitionallyEqualQ[
			TypeTheoryTerm["decodeOneHot"["oneHot"[5, 3]], wolfram23],
			TypeTheoryTerm["some"[3], wolfram23]
		],
		DefinitionallyEqualQ[
			TypeTheoryTerm["decodeTagWord"[4, "encodeWord"[4, {2, 0, 3}]], wolfram23],
			TypeTheoryTerm["some"[{2, 0, 3}], wolfram23]
		],
		DefinitionallyEqualQ[
			TypeTheoryTerm["parseWord"["binaryWord"["binaryConfiguration"[1, {"true", "false"}, "true", {"false", "true", "false"}]]], wolfram23],
			TypeTheoryTerm["some"["minskyParsed"[1, 1, 5]], wolfram23]
		],
		DefinitionallyEqualQ[
			TypeTheoryTerm["canon"["binaryConfiguration"[1, {"true", "false", "false"}, "true", {"false", "true", "false"}]], wolfram23],
			TypeTheoryTerm["binaryConfiguration"[1, {"true"}, "true", {"false", "true"}], wolfram23]
		],
		DefinitionallyEqualQ[
			TypeTheoryTerm["cfgOfNums"[1, 1, 5], wolfram23],
			TypeTheoryTerm["binaryConfiguration"[1, {"true"}, "true", {"false", "true"}], wolfram23]
		],
		DefinitionallyEqualQ[
			TypeTheoryTerm["decodeCTS"[1, "encodeWord"[84 * 1 + 1, Map["minskyEncode", "binaryWord"["binaryConfiguration"[0, Typed[{}, {Booleans}], "false", Typed[{}, {Booleans}]]]]]], wolfram23],
			TypeTheoryTerm["some"["binaryConfiguration"[0, Typed[{}, {Booleans}], "false", Typed[{}, {Booleans}]]], wolfram23]
		]
	},
	{True, True, True, True, True, True, True},
	TestID -> "Rung-7-decoders-round-trip-doubling-one-hot-Minsky-words-and-binary-configurations"
]

(* rung 7 decoders reject malformed inputs with none, and Conjecture 0 + wolfram23Universal use zero axioms *)
VerificationTest[
	{
		DefinitionallyEqualQ[TypeTheoryTerm["undbl"[{"true"}], wolfram23], TypeTheoryTerm[Typed["none", Option[{Booleans}]], wolfram23]],
		DefinitionallyEqualQ[TypeTheoryTerm["undbl"[{"true", "false"}], wolfram23], TypeTheoryTerm[Typed["none", Option[{Booleans}]], wolfram23]],
		DefinitionallyEqualQ[TypeTheoryTerm["decodeOneHot"[{"false", "false", "false"}], wolfram23], TypeTheoryTerm[Typed["none", Option[NonNegativeIntegers]], wolfram23]],
		DefinitionallyEqualQ[TypeTheoryTerm["decodeOneHot"[{"true", "true", "false"}], wolfram23], TypeTheoryTerm[Typed["none", Option[NonNegativeIntegers]], wolfram23]],
		DefinitionallyEqualQ[TypeTheoryTerm["decodeTagWord"[3, {"true", "false"}], wolfram23], TypeTheoryTerm[Typed["none", Option[{NonNegativeIntegers}]], wolfram23]],
		DefinitionallyEqualQ[TypeTheoryTerm["decodeTagWord"[3, {"false", "false", "false"}], wolfram23], TypeTheoryTerm[Typed["none", Option[{NonNegativeIntegers}]], wolfram23]],
		DefinitionallyEqualQ[TypeTheoryTerm["parseWord"[{"symbolA"[1], "symbolB"[1]}], wolfram23], TypeTheoryTerm[Typed["none", Option["MinskyParsed"]], wolfram23]],
		DefinitionallyEqualQ[TypeTheoryTerm["parseWord"[{"symbolA"[1], "pad", "symbolB"[2], "pad"}], wolfram23], TypeTheoryTerm[Typed["none", Option["MinskyParsed"]], wolfram23]],
		DefinitionallyEqualQ[TypeTheoryTerm["parseWord"[{"symbolA"[1], "pad", "symbolB"[1], "pad", "pad"}], wolfram23], TypeTheoryTerm[Typed["none", Option["MinskyParsed"]], wolfram23]],
		TypeTheoryAxiomClosure[TypeTheoryTerm["forwardSimulationSchedule", wolfram23]],
		TypeTheoryAxiomClosure[TypeTheoryTerm["turingMachineConfinement", wolfram23]],
		TypeTheoryAxiomClosure[TypeTheoryTerm["conjecture0Finite", wolfram23]],
		TypeTheoryAxiomClosure[TypeTheoryTerm["decodeCTSWord", wolfram23]],
		TypeTheoryAxiomClosure[TypeTheoryTerm["wolfram23Universal", wolfram23]]
	},
	{True, True, True, True, True, True, True, True, True, <||>, <||>, <||>, <||>, <||>},
	TestID -> "Rung-7-decoders-reject-malformed-inputs-and-universality-uses-no-axioms"
]

(* the environment by its name, as every library environment is named: a term and a type in it, and the default *)
VerificationTest[
	{
		Head[TypeTheoryTerm["minskySimulation", "Wolfram23"]],
		TypeTheoryType["minskySimulation", "Wolfram23"] === TypeTheoryType[TypeTheoryTerm["minskySimulation", wolfram23]],
		Block[{$TypeTheoryEnvironment = "Wolfram23"}, Head[TypeTheoryType["cookSimulation"]]],
		Head[TypeTheoryProofTree[wolfram23["minskySimulation"]["Term"]]]
	},
	{TypeTheoryTerm, True, TypeTheoryTerm, TypeTheoryProofTree},
	TestID -> "A-term-and-a-type-in-the-Wolfram23-environment-by-its-name"
]
