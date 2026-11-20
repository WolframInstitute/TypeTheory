(* ::Package:: *)

(*
Wolfram's (2,3) Turing machine and Smith's chain of emulations: TypeTheoryEnvironment["Wolfram23"] is the prelude with
the systems of the chain, built and checked the first time it is asked for. The design is in
docs/notes/Wolfram23Universality.md; this file holds rungs 6, 2 and 1 so far.

	"steps"[step, n, s]                n steps of a step function step : S -> Option[S], the last step taken at the end
	"optionBind", "optionMap",         the option's monad, and the first of two options where it has a value
	"orElse"
	"forwardSimulation"[f, g, R]       g follows f along R: from R[s, t] a step of f is at least one step of g, keeping R
	"forwardSimulationSteps"           n steps of f are at least n steps of g, keeping R
	"Color", "LookaheadState",         the cells 0, 1, 2, the states A, B, C, the directions, and the rules of a
	"Direction", "LookaheadRule"       lookahead machine: a rule rewrites the head, or the head and its right neighbour
	"LookaheadConfiguration"           a zipper: the cells left of the head nearest first, the head, the cells right of
	                                   it, and the state
	"lookaheadStep"[m, c]              one step; none where the head would leave the tape
	"system0" ... "system3"            Smith's Systems 0 to 3 (p. 45); System 0 is Wolfram's (2,3) machine
	"phi3", "phi2"                     the relabelings from System 3 to System 2 and from System 2 to System 1
	"system0Steps"[c]                  the steps of System 0 that make one step of System 1: 3 on B21 and B22, else 1
	"CyclicTagConfiguration"           rung 2: a cyclic tag system's data and its appendants, rotated at each step
	"cookConfiguration"[k, p, w]       Cook's encoding of a 2-tag system's word, its symbols one-hot blocks of k bits
	"tagStep"[p, w]                    a step of a 2-tag system over any type of symbols
	"passOutFrom"[p, w, read]          what a round of it appends: the productions of every other symbol of w
	"BinaryConfiguration",             rung 1: a binary Turing machine, its configuration and step; state 0 halts
	"binaryStep"[tm, c]
	"MinskySymbol",                    Cocke and Minsky's symbols, their productions for a machine tm, and the word of a
	"minskyProductions"[tm],           configuration: the tag system follows the machine, a step being 3 or 5 rounds
	"binaryWord"[c]

The three theorems of the relabelings are proved by cases on the whole zipper (its state, its head, its right side and
the first cell there, its left side), each case computed by the kernel; the case trees are generated below. That System
0 reaches what System 1 reaches is stated as steps0 == orElse[step1, steps0], so that where System 1 is stuck the two
sides are one term, and every case closes by reflexivity.
*)


(* ::Section:: *)
(*PackageExported*)




(* ::Section:: *)
(*PackageScoped*)


PackageScoped[wolfram23Environment]
PackageScoped[$wolfram23Declarations]


(* ::Section:: *)
(*Usage Messages*)


wolfram23Environment::usage = "wolfram23Environment[] gives the prelude with the systems of Smith's chain of emulations to Wolfram's (2,3) Turing machine, built and checked the first time it is asked for."
$wolfram23Declarations::usage = "$wolfram23Declarations is the list of the declarations of the systems of Smith's chain, in order, each theorem proved by its tactics in the environment so far."


(* ::Section:: *)
(*Function Definitions*)


TypeTheoryEnvironment["Wolfram23"] := wolfram23Environment[]

wolfram23Environment[] := wolfram23Environment[] = withoutStoreTracking[
	libraryEnvironment["Wolfram23", preludeEnvironment[], withStoreCleanup[Fold[addMachineDeclaration, preludeEnvironment[], $wolfram23Declarations]]]
]

(* the rule tables of p. 45, a rule by the state and the head, or by the right neighbour as well *)
$stateNames = <|"A" -> "stateA", "B" -> "stateB", "C" -> "stateC"|>
$colorNames = <|0 -> "color0", 1 -> "color1", 2 -> "color2"|>
$directionNames = <|"L" -> "moveLeft", "R" -> "moveRight"|>
oneCellRule[state_, color_, direction_] := "oneCell"[$stateNames[state], $colorNames[color], $directionNames[direction]]
twoCellsRule[state_, color_, neighbour_, direction_] := "twoCells"[$stateNames[state], $colorNames[color], $colorNames[neighbour], $directionNames[direction]]
colorCases[x_, values_List, motive_] := InductiveRecursor["Color"] @@ Join[{Function[{Typed[t, "Color"]}, motive]}, values, {x}]
stateCases[x_, values_List, motive_] := InductiveRecursor["LookaheadState"] @@ Join[{Function[{Typed[t, "LookaheadState"]}, motive]}, values, {x}]
ruleTable[table_Association] := Function[{Typed[state, "LookaheadState"], Typed[head, "Color"], Typed[neighbour, "Color"]}, Evaluate[stateCases[
	state,
	Table[
		colorCases[head, Table[Replace[table[{name, color}], rules_List :> colorCases[neighbour, rules, "LookaheadRule"]], {color, 0, 2}], "LookaheadRule"],
		{name, {"A", "B", "C"}}
	],
	"LookaheadRule"
]]]
$system0Table = <|
	{"A", 0} -> oneCellRule["B", 1, "R"], {"A", 1} -> oneCellRule["A", 2, "L"], {"A", 2} -> oneCellRule["A", 1, "L"],
	{"B", 0} -> oneCellRule["A", 2, "L"], {"B", 1} -> oneCellRule["B", 2, "R"], {"B", 2} -> oneCellRule["A", 0, "R"],
	{"C", 0} -> oneCellRule["C", 0, "R"], {"C", 1} -> oneCellRule["C", 0, "R"], {"C", 2} -> oneCellRule["C", 0, "R"]
|>
$system1Table = Join[$system0Table, <|{"B", 2} -> {twoCellsRule["A", 0, 0, "R"], twoCellsRule["B", 1, 2, "R"], twoCellsRule["B", 1, 1, "R"]}|>]
$system2Table = Join[$system1Table, <|
	{"B", 2} -> {twoCellsRule["A", 0, 0, "R"], twoCellsRule["C", 1, 1, "R"], twoCellsRule["C", 1, 2, "R"]},
	{"C", 0} -> oneCellRule["A", 2, "L"],
	{"C", 1} -> {twoCellsRule["A", 0, 0, "R"], twoCellsRule["C", 1, 1, "R"], twoCellsRule["C", 1, 2, "R"]},
	{"C", 2} -> oneCellRule["B", 2, "R"]
|>]
$system3Table = <|
	{"A", 0} -> oneCellRule["B", 2, "R"], {"A", 1} -> oneCellRule["A", 1, "L"], {"A", 2} -> oneCellRule["A", 2, "L"],
	{"B", 0} -> oneCellRule["A", 2, "L"], {"B", 1} -> oneCellRule["B", 1, "R"],
	{"B", 2} -> {twoCellsRule["A", 0, 0, "R"], twoCellsRule["C", 2, 1, "R"], twoCellsRule["C", 2, 2, "R"]},
	{"C", 0} -> oneCellRule["A", 2, "L"],
	{"C", 1} -> {twoCellsRule["A", 0, 0, "R"], twoCellsRule["C", 2, 1, "R"], twoCellsRule["C", 2, 2, "R"]},
	{"C", 2} -> oneCellRule["B", 1, "R"]
|>

(* the case trees over a configuration: its fields, then the state, the head, the right side and its first cell, and the
   left side; System 1's B21 and B22 also split the cell after the neighbour, which the second of their three steps of
   System 0 reads *)
colorSplit[variable_, branch_List] := Join[{"Cases"[variable]}, branch, branch, branch]
$leftSplit = {"Cases"[left], "Reflexivity", "Introduce"[x, rest], "Reflexivity"}
$rightSplit = Join[{"Cases"[right]}, $leftSplit, {"Introduce"[neighbour, beyond]}, colorSplit[neighbour, $leftSplit]]
$beyondSplit = Join[{"Cases"[beyond]}, $leftSplit, {"Introduce"[next, further]}, $leftSplit]
$configurationScript = Join[
	{"Introduce"[c], "Cases"[c], "Introduce"[left, head, right, state], "Cases"[state]},
	Flatten[ConstantArray[colorSplit[head, $rightSplit], 3], 1]
]
$threeStepsScript = Join[
	{"Introduce"[c], "Cases"[c], "Introduce"[left, head, right, state], "Cases"[state]},
	colorSplit[head, $rightSplit],
	{"Cases"[head]}, $rightSplit, $rightSplit,
	{"Cases"[right]}, $leftSplit, {"Introduce"[neighbour, beyond], "Cases"[neighbour]}, $leftSplit, $beyondSplit, $beyondSplit,
	colorSplit[head, $rightSplit]
]

(* System 0's steps for a step of System 1 are 1 or 3, decided by computation in each case *)
$positiveScript = Join[
	{"Introduce"[c], "Cases"[c], "Introduce"[left, head, right, state], "Cases"[state], "Decide", "Cases"[head], "Decide", "Decide",
		"Cases"[right], "Decide", "Introduce"[neighbour, beyond], "Cases"[neighbour], "Decide", "Decide", "Decide", "Decide"}
]

(* rung 2: Cook's encoding of a 2-tag system, each symbol a one-hot block of k bits, and one tag step as k + k steps of
   the cyclic tag system *)
$cookDeclarations = With[{bits = {Booleans}, appendantList = {{Booleans}}}, {
	(* k bits, all false *)
	TypeTheoryDefinition["allFalse", Typed[
		Function[{Typed[k, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[q, NonNegativeIntegers]}, bits], Typed[{}, bits],
			Function[{Typed[j, NonNegativeIntegers], Typed[previous, bits]}, Prepend["false"][previous]], k]],
		NonNegativeIntegers -> bits
	]],
	(* the symbol i as k bits, true at position i alone *)
	TypeTheoryDefinition["oneHot", Typed[
		Function[{Typed[k, NonNegativeIntegers], Typed[i, NonNegativeIntegers]},
			InductiveRecursor[NonNegativeIntegers][Function[{Typed[q, NonNegativeIntegers]}, NonNegativeIntegers -> bits],
				Function[{Typed[x, NonNegativeIntegers]}, Typed[{}, bits]],
				Function[{Typed[j, NonNegativeIntegers], Typed[previous, NonNegativeIntegers -> bits]},
					Function[{Typed[x, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[q, NonNegativeIntegers]}, bits],
						Prepend["true"]["allFalse"[j]],
						Function[{Typed[y, NonNegativeIntegers], Typed[unused, bits]}, Prepend["false"][previous[y]]],
						x]]],
				k][i]],
		NonNegativeIntegers -> NonNegativeIntegers -> bits
	]],
	(* the appendants f[0], ..., f[k - 1] *)
	TypeTheoryDefinition["appendantsFrom", Typed[
		Function[{Typed[f, NonNegativeIntegers -> bits], Typed[k, NonNegativeIntegers]},
			InductiveRecursor[NonNegativeIntegers][Function[{Typed[q, NonNegativeIntegers]}, (NonNegativeIntegers -> bits) -> appendantList],
				Function[{Typed[g, NonNegativeIntegers -> bits]}, Typed[{}, appendantList]],
				Function[{Typed[j, NonNegativeIntegers], Typed[previous, (NonNegativeIntegers -> bits) -> appendantList]},
					Function[{Typed[g, NonNegativeIntegers -> bits]}, Prepend[g[0]][previous[Function[{Typed[x, NonNegativeIntegers]}, g[x + 1]]]]]],
				k][f]],
		(NonNegativeIntegers -> bits) -> NonNegativeIntegers -> appendantList
	]],
	machineTheorem["selectedAllFalse",
		ForAll[{Typed[k, NonNegativeIntegers], Typed[as, appendantList]}, "selected"["allFalse"[k], as] == Typed[{}, bits]],
		{
			"Introduce"[k], "Induction"[k],
			"Introduce"[as], "Reflexivity",
			"Introduce"[j, induction, as], "Cases"[as], "Reflexivity",
			"Introduce"[a, others],
			"Change"["selected"["allFalse"[j], others] == Typed[{}, bits]],
			induction[others]
		}
	],
	machineTheorem["selectedOneHot",
		ForAll[{Typed[k, NonNegativeIntegers], Typed[i, NonNegativeIntegers], Typed[f, NonNegativeIntegers -> bits]},
			Implies[i + 1 <= k, "selected"["oneHot"[k, i], "appendantsFrom"[f, k]] == f[i]]],
		{
			"Introduce"[k], "Induction"[k],
			"Introduce"[i, f, below], "Exact"["falseElimination"["successorNotZero"[i, "lessEqualAntisymmetry"[below, "lessEqualZero"[i + 1]]]]],
			"Introduce"[j, induction, i, f, below], "Cases"[i], "Introduce"[below],
			"Change"[Join[f[0], "selected"["allFalse"[j], "appendantsFrom"[Function[{Typed[x, NonNegativeIntegers]}, f[x + 1]], j]]] == f[0]],
			"Rewrite"["selectedAllFalse"[j, "appendantsFrom"[Function[{Typed[x, NonNegativeIntegers]}, f[x + 1]], j]]],
			"Rewrite"["joinEmptyRight"[f[0]]],
			"Introduce"[y, below],
			"Change"["selected"["oneHot"[j, y], "appendantsFrom"[Function[{Typed[x, NonNegativeIntegers]}, f[x + 1]], j]] == f[y + 1]],
			"Have"[yBelow, y + 1 <= j], "LinearArithmetic",
			induction[y, Function[{Typed[x, NonNegativeIntegers]}, f[x + 1]], yBelow]
		}
	],
	(* k empty appendants, which append nothing *)
	TypeTheoryDefinition["emptyAppendants", Typed[
		Function[{Typed[k, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][Function[{Typed[q, NonNegativeIntegers]}, appendantList], Typed[{}, appendantList],
			Function[{Typed[j, NonNegativeIntegers], Typed[previous, appendantList]}, Prepend[Typed[{}, bits]][previous]], k]],
		NonNegativeIntegers -> appendantList
	]],
	(* a word of the tag system, each symbol as its block *)
	TypeTheoryDefinition["encodeWord", Typed[
		Function[{Typed[k, NonNegativeIntegers], Typed[w, {NonNegativeIntegers}]}, InductiveRecursor[List][Function[{Typed[q, {NonNegativeIntegers}]}, bits], Typed[{}, bits],
			Function[{Typed[a, NonNegativeIntegers], Typed[rest, {NonNegativeIntegers}], Typed[previous, bits]}, Join["oneHot"[k, a], previous]], w]],
		NonNegativeIntegers -> {NonNegativeIntegers} -> bits
	]],
	(* a step of a 2-tag system: the first symbol's production appended, the first two symbols deleted *)
	TypeTheoryDefinition["tagStep", Typed[
		Function[{TypedImplicit[S, TypeUniverse[1]], Typed[productions, S -> {S}], Typed[w, {S}]},
			InductiveRecursor[List][Function[{Typed[q, {S}]}, Option[{S}]], Typed["none", Option[{S}]],
				Function[{Typed[a, S], Typed[rest, {S}], Typed[previous, Option[{S}]]},
					InductiveRecursor[List][Function[{Typed[q, {S}]}, Option[{S}]], Typed["none", Option[{S}]],
						Function[{Typed[b, S], Typed[rest2, {S}], Typed[previous2, Option[{S}]]}, "some"[Join[rest2, productions[a]]]],
						rest]],
				w]],
		ForAll[{TypedImplicit[S, TypeUniverse[1]]}, (S -> {S}) -> {S} -> Option[{S}]]
	]],
	(* Cook's cyclic tag system: the k symbols' productions encoded, then k empty appendants *)
	TypeTheoryDefinition["cookAppendants", Typed[
		Function[{Typed[k, NonNegativeIntegers], Typed[productions, NonNegativeIntegers -> {NonNegativeIntegers}]},
			Join["appendantsFrom"[Function[{Typed[i, NonNegativeIntegers]}, "encodeWord"[k, productions[i]]], k], "emptyAppendants"[k]]],
		NonNegativeIntegers -> (NonNegativeIntegers -> {NonNegativeIntegers}) -> appendantList
	]],
	TypeTheoryDefinition["cookConfiguration", Typed[
		Function[{Typed[k, NonNegativeIntegers], Typed[productions, NonNegativeIntegers -> {NonNegativeIntegers}], Typed[w, {NonNegativeIntegers}]},
			"cyclicTagConfiguration"["encodeWord"[k, w], "cookAppendants"[k, productions]]],
		NonNegativeIntegers -> (NonNegativeIntegers -> {NonNegativeIntegers}) -> {NonNegativeIntegers} -> "CyclicTagConfiguration"
	]],
	machineTheorem["lengthAllFalse", ForAll[{Typed[k, NonNegativeIntegers]}, Length["allFalse"[k]] == k],
		{"Introduce"[k], "Induction"[k], "Reflexivity", "Introduce"[j, induction], "Change"[Length["allFalse"[j]] + 1 == j + 1], "Rewrite"[induction]}
	],
	machineTheorem["lengthOneHot", ForAll[{Typed[k, NonNegativeIntegers], Typed[i, NonNegativeIntegers]}, Length["oneHot"[k, i]] == k],
		{
			"Introduce"[k], "Induction"[k], "Introduce"[i], "Reflexivity",
			"Introduce"[j, induction, i], "Cases"[i],
			"Change"[Length["allFalse"[j]] + 1 == j + 1], "Rewrite"["lengthAllFalse"[j]],
			"Introduce"[y], "Change"[Length["oneHot"[j, y]] + 1 == j + 1], "Rewrite"[induction[y]]
		}
	],
	machineTheorem["lengthAppendantsFrom", ForAll[{Typed[k, NonNegativeIntegers], Typed[f, NonNegativeIntegers -> bits]}, Length["appendantsFrom"[f, k]] == k],
		{
			"Introduce"[k], "Induction"[k], "Introduce"[f], "Reflexivity",
			"Introduce"[j, induction, f],
			"Change"[Length["appendantsFrom"[Function[{Typed[x, NonNegativeIntegers]}, f[x + 1]], j]] + 1 == j + 1],
			"Rewrite"[induction[Function[{Typed[x, NonNegativeIntegers]}, f[x + 1]]]]
		}
	],
	machineTheorem["lengthEmptyAppendants", ForAll[{Typed[k, NonNegativeIntegers]}, Length["emptyAppendants"[k]] == k],
		{"Introduce"[k], "Induction"[k], "Reflexivity", "Introduce"[j, induction], "Change"[Length["emptyAppendants"[j]] + 1 == j + 1], "Rewrite"[induction]}
	],
	machineTheorem["selectedEmptyAppendants", ForAll[{Typed[k, NonNegativeIntegers], Typed[blocks, bits]}, "selected"[blocks, "emptyAppendants"[k]] == Typed[{}, bits]],
		{
			"Introduce"[k], "Induction"[k],
			"Introduce"[blocks], "Cases"[blocks], "Reflexivity", "Introduce"[b, rest], "Reflexivity",
			"Introduce"[j, induction, blocks], "Cases"[blocks], "Reflexivity", "Introduce"[b, rest],
			"Change"[Join["appendantIf"[b, Typed[{}, bits]], "selected"[rest, "emptyAppendants"[j]]] == Typed[{}, bits]],
			"Rewrite"[induction[rest]],
			"Cases"[b], "Reflexivity", "Reflexivity"
		}
	],
	machineTheorem["encodeWordJoin",
		ForAll[{Typed[k, NonNegativeIntegers], Typed[u, {NonNegativeIntegers}], Typed[v, {NonNegativeIntegers}]},
			"encodeWord"[k, Join[u, v]] == Join["encodeWord"[k, u], "encodeWord"[k, v]]],
		{
			"Introduce"[k, u, v], "Induction"[u], "Reflexivity",
			"Introduce"[a, rest, induction],
			"Change"[Join["oneHot"[k, a], "encodeWord"[k, Join[rest, v]]] == Join[Join["oneHot"[k, a], "encodeWord"[k, rest]], "encodeWord"[k, v]]],
			"Rewrite"[induction],
			"Rewrite"["joinAssociativity"["oneHot"[k, a], "encodeWord"[k, rest], "encodeWord"[k, v]]]
		}
	],
	(* the block lemma with the count of steps named *)
	machineTheorem["cyclicTagBlockSteps",
		ForAll[{Typed[n, NonNegativeIntegers], Typed[blocks, bits], Typed[as, appendantList], Typed[r, bits], Typed[q, appendantList]},
			Implies[Length[blocks] == n, Implies[Length[as] == n,
				"steps"["cyclicTagStep", n, "cyclicTagConfiguration"[Join[blocks, r], Join[as, q]]] == "some"["cyclicTagConfiguration"[Join[r, "selected"[blocks, as]], Join[q, as]]]]]],
		{
			"Introduce"[n, blocks, as, r, q, blockLength, appendantsLength],
			"Rewrite"["equalitySymmetry"[blockLength]],
			"cyclicTagBlock"[blocks, as, r, q, "equalityTransitivity"[appendantsLength, "equalitySymmetry"[blockLength]]]
		}
	],
	(* rung 2: one step of a 2-tag system is k + k steps of Cook's cyclic tag system, where the first two symbols are below k *)
	With[
		{
			encoded = Function[{Typed[i, NonNegativeIntegers]}, "encodeWord"[k, productions[i]]]
		},
		machineTheorem["cookStep",
			ForAll[{Typed[k, NonNegativeIntegers], Typed[productions, NonNegativeIntegers -> {NonNegativeIntegers}], Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers],
				Typed[rest, {NonNegativeIntegers}]},
				Implies[a + 1 <= k, Implies[b + 1 <= k,
					"steps"["cyclicTagStep", k + k, "cookConfiguration"[k, productions, Prepend[a][Prepend[b][rest]]]] ==
						"some"["cookConfiguration"[k, productions, Join[rest, productions[a]]]]]]],
			{
				"Introduce"[k, productions, a, b, rest, aBelow, bBelow],
				"Change"["steps"["cyclicTagStep", k + k, "cyclicTagConfiguration"[Join["oneHot"[k, a], Join["oneHot"[k, b], "encodeWord"[k, rest]]],
					Join["appendantsFrom"[encoded, k], "emptyAppendants"[k]]]] ==
						"some"["cyclicTagConfiguration"["encodeWord"[k, Join[rest, productions[a]]], Join["appendantsFrom"[encoded, k], "emptyAppendants"[k]]]]],
				"Rewrite"["encodeWordJoin"[k, rest, productions[a]]],
				"Rewrite"["stepsAdd"["CyclicTagConfiguration", "cyclicTagStep", k, k, "cyclicTagConfiguration"[Join["oneHot"[k, a], Join["oneHot"[k, b], "encodeWord"[k, rest]]],
					Join["appendantsFrom"[encoded, k], "emptyAppendants"[k]]]]],
				"Rewrite"["cyclicTagBlockSteps"[k, "oneHot"[k, a], "appendantsFrom"[encoded, k], Join["oneHot"[k, b], "encodeWord"[k, rest]], "emptyAppendants"[k],
					"lengthOneHot"[k, a], "lengthAppendantsFrom"[k, encoded]]],
				"Rewrite"["selectedOneHot"[k, a, encoded, aBelow]],
				"Change"["steps"["cyclicTagStep", k, "cyclicTagConfiguration"[Join[Join["oneHot"[k, b], "encodeWord"[k, rest]], "encodeWord"[k, productions[a]]],
					Join["emptyAppendants"[k], "appendantsFrom"[encoded, k]]]] ==
						"some"["cyclicTagConfiguration"[Join["encodeWord"[k, rest], "encodeWord"[k, productions[a]]], Join["appendantsFrom"[encoded, k], "emptyAppendants"[k]]]]],
				"Rewrite"["joinAssociativity"["oneHot"[k, b], "encodeWord"[k, rest], "encodeWord"[k, productions[a]]]],
				"Rewrite"["cyclicTagBlockSteps"[k, "oneHot"[k, b], "emptyAppendants"[k], Join["encodeWord"[k, rest], "encodeWord"[k, productions[a]]], "appendantsFrom"[encoded, k],
					"lengthOneHot"[k, b], "lengthEmptyAppendants"[k]]],
				"Rewrite"["selectedEmptyAppendants"[k, "oneHot"[k, b]]],
				"Rewrite"["joinEmptyRight"[Join["encodeWord"[k, rest], "encodeWord"[k, productions[a]]]]]
			}
		]
	],
	machineTheorem["someInjective",
		ForAll[{Typed[S, TypeUniverse[1]], Typed[x, S], Typed[y, S]}, Implies["some"[x] == "some"[y], x == y]],
		{
			"Introduce"[S, x, y, same],
			"equalityCongruence"[Function[{Typed[o, Option[S]]}, InductiveRecursor[Option][Function[{Typed[q, Option[S]]}, S], x, Function[{Typed[z, S]}, z], o]], same]
		}
	],
	machineTheorem["noneNotSome",
		ForAll[{Typed[S, TypeUniverse[1]], Typed[x, S]}, Implies[Typed["none", Option[S]] == "some"[x], False]],
		{
			"Introduce"[S, x, same],
			Construct["equalitySubstitution", Option[S],
				Function[{Typed[o, Option[S]]}, InductiveRecursor[Option][Function[{Typed[q, Option[S]]}, TypeUniverse[0]], True, Function[{Typed[z, S]}, False], o]],
				Typed["none", Option[S]], "some"[x], same, "trueIntroduction"]
		}
	],
	(* every symbol of a word is below k *)
	TypeTheoryDefinition["allBelow", Typed[
		Function[{Typed[k, NonNegativeIntegers], Typed[w, {NonNegativeIntegers}]},
			InductiveRecursor[List][Function[{Typed[q, {NonNegativeIntegers}]}, TypeUniverse[0]], True,
				Function[{Typed[a, NonNegativeIntegers], Typed[rest, {NonNegativeIntegers}], Typed[previous, TypeUniverse[0]]}, And[a + 1 <= k, previous]], w]],
		NonNegativeIntegers -> {NonNegativeIntegers} -> TypeUniverse[0]
	]],
	machineTheorem["allBelowJoin",
		ForAll[{Typed[k, NonNegativeIntegers], Typed[u, {NonNegativeIntegers}], Typed[v, {NonNegativeIntegers}]},
			Implies["allBelow"[k, u], Implies["allBelow"[k, v], "allBelow"[k, Join[u, v]]]]],
		{
			"Introduce"[k, u, v], "Induction"[u],
			"Introduce"[uBelow, vBelow], vBelow,
			"Introduce"[a, rest, induction, uBelow, vBelow], "Cases"[uBelow], "Introduce"[aBelow, restBelow],
			"andIntroduction"[aBelow, induction[restBelow, vBelow]]
		}
	],
	(* rung 2: where every production keeps its symbols below k, Cook's cyclic tag system follows the tag system *)
	machineTheorem["cookSimulation",
		ForAll[{Typed[k, NonNegativeIntegers], Typed[productions, NonNegativeIntegers -> {NonNegativeIntegers}],
			Typed[good, ForAll[{Typed[i, NonNegativeIntegers]}, Implies[i + 1 <= k, "allBelow"[k, productions[i]]]]]},
			"forwardSimulation"["tagStep"[productions], "cyclicTagStep",
				Function[{Typed[w, {NonNegativeIntegers}], Typed[c, "CyclicTagConfiguration"]}, And[c == "cookConfiguration"[k, productions, w], "allBelow"[k, w]]]]],
		{
			"Introduce"[k, productions, good, s, t, s2, related, stepped],
			"Cases"[related], "Introduce"[encoded, below],
			"Cases"[s],
			(* the empty word and a word of one symbol make no step *)
			"Introduce"[stepped, encoded, below], "Exact"["falseElimination"["noneNotSome"[{NonNegativeIntegers}, s2, stepped]]],
			"Introduce"[a, rest, stepped, encoded, below], "Cases"[rest],
			"Introduce"[stepped, encoded, below], "Exact"["falseElimination"["noneNotSome"[{NonNegativeIntegers}, s2, stepped]]],
			"Introduce"[b, rest2, stepped, encoded, below],
			"Cases"[below], "Introduce"[aBelow, restBelow], "Cases"[restBelow], "Introduce"[bBelow, rest2Below],
			"Have"[next, Join[rest2, productions[a]] == s2], "someInjective"[{NonNegativeIntegers}, Join[rest2, productions[a]], s2, stepped],
			"Have"[positive, 1 <= k + k], "LinearArithmetic",
			"existsIntroduction"[k + k, "andIntroduction"[positive, "existsIntroduction"["cookConfiguration"[k, productions, s2], "andIntroduction"[
				"equalityTransitivity"["equalityTransitivity"[
					"equalityCongruence"[Function[{Typed[c, "CyclicTagConfiguration"]}, "steps"["cyclicTagStep", k + k, c]], encoded],
					"cookStep"[k, productions, a, b, rest2, aBelow, bBelow]],
					"equalityCongruence"[Function[{Typed[w, {NonNegativeIntegers}]}, "some"["cookConfiguration"[k, productions, w]]], next]],
				"andIntroduction"["equalityReflexivity"["cookConfiguration"[k, productions, s2]],
					Construct["equalitySubstitution", {NonNegativeIntegers}, Function[{Typed[w, {NonNegativeIntegers}]}, "allBelow"[k, w]], Join[rest2, productions[a]], s2, next,
						"allBelowJoin"[k, rest2, productions[a], rest2Below, good[a, aBelow]]]]]]]]
		}
	]
}]

(* rung 1: a round of a 2-tag system reads every other symbol of the word, from the first, and appends their productions.
   Words are over any type of symbols, so that Cocke and Minsky's symbols compute as they are written. *)
$roundDeclarations = {
	(* m copies of a word *)
	TypeTheoryDefinition["repeated", Typed[
		Function[{TypedImplicit[S, TypeUniverse[1]], Typed[w, {S}], Typed[m, NonNegativeIntegers]},
			InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, {S}], Typed[{}, {S}],
				Function[{Typed[k, NonNegativeIntegers], Typed[previous, {S}]}, Join[w, previous]], m]],
		ForAll[{TypedImplicit[S, TypeUniverse[1]]}, {S} -> NonNegativeIntegers -> {S}]
	]],
	(* m copies of the pair a b *)
	TypeTheoryDefinition["pairs", Typed[
		Function[{TypedImplicit[S, TypeUniverse[1]], Typed[a, S], Typed[b, S], Typed[m, NonNegativeIntegers]},
			InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, {S}], Typed[{}, {S}],
				Function[{Typed[k, NonNegativeIntegers], Typed[previous, {S}]}, Prepend[a][Prepend[b][previous]]], m]],
		ForAll[{TypedImplicit[S, TypeUniverse[1]]}, S -> S -> NonNegativeIntegers -> {S}]
	]],
	(* the productions of every other symbol of a word, from the first where read is true, from the second where false:
	   what a round appends *)
	TypeTheoryDefinition["passOutFrom", Typed[
		Function[{TypedImplicit[S, TypeUniverse[1]], Typed[productions, S -> {S}], Typed[w, {S}]},
			InductiveRecursor[List][Function[{Typed[q, {S}]}, Booleans -> {S}], Function[{Typed[read, Booleans]}, Typed[{}, {S}]],
				Function[{Typed[a, S], Typed[rest, {S}], Typed[previous, Booleans -> {S}]},
					Function[{Typed[read, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, {S}], previous["true"], Join[productions[a], previous["false"]], read]]],
				w]],
		ForAll[{TypedImplicit[S, TypeUniverse[1]]}, (S -> {S}) -> {S} -> Booleans -> {S}]
	]],
	(* pairs read from their first symbols, and from their second *)
	machineTheorem["passOutAlignedPairs",
		ForAll[{Typed[S, TypeUniverse[1]], Typed[productions, S -> {S}], Typed[a, S], Typed[b, S], Typed[m, NonNegativeIntegers], Typed[l, {S}]},
			"passOutFrom"[productions, Join["pairs"[a, b, m], l], "true"] == Join["repeated"[productions[a], m], "passOutFrom"[productions, l, "true"]]],
		{
			"Introduce"[S, productions, a, b, m, l], "Induction"[m],
			"Reflexivity",
			"Introduce"[k, induction],
			"Change"[Join[productions[a], "passOutFrom"[productions, Join["pairs"[a, b, k], l], "true"]] ==
				Join[Join[productions[a], "repeated"[productions[a], k]], "passOutFrom"[productions, l, "true"]]],
			"Rewrite"[induction],
			"Rewrite"["joinAssociativity"[productions[a], "repeated"[productions[a], k], "passOutFrom"[productions, l, "true"]]]
		}
	],
	machineTheorem["passOutShiftedPairs",
		ForAll[{Typed[S, TypeUniverse[1]], Typed[productions, S -> {S}], Typed[a, S], Typed[b, S], Typed[m, NonNegativeIntegers], Typed[l, {S}]},
			"passOutFrom"[productions, Join["pairs"[a, b, m], l], "false"] == Join["repeated"[productions[b], m], "passOutFrom"[productions, l, "false"]]],
		{
			"Introduce"[S, productions, a, b, m, l], "Induction"[m],
			"Reflexivity",
			"Introduce"[k, induction],
			"Change"[Join[productions[b], "passOutFrom"[productions, Join["pairs"[a, b, k], l], "false"]] ==
				Join[Join[productions[b], "repeated"[productions[b], k]], "passOutFrom"[productions, l, "false"]]],
			"Rewrite"[induction],
			"Rewrite"["joinAssociativity"[productions[b], "repeated"[productions[b], k], "passOutFrom"[productions, l, "false"]]]
		}
	],
	(* a round over a word of even length 2 n: n steps append what it reads, after whatever came after it *)
	machineTheorem["tagRoundEven",
		ForAll[{Typed[S, TypeUniverse[1]], Typed[productions, S -> {S}], Typed[n, NonNegativeIntegers]},
			ForAll[{Typed[u, {S}], Typed[t, {S}]}, Implies[Length[u] == 2 * n,
				"steps"["tagStep"[productions], n, Join[u, t]] == "some"[Join[t, "passOutFrom"[productions, u, "true"]]]]]],
		{
			"Introduce"[S, productions, n], "Induction"[n],
			"Introduce"[u, t, length], "Cases"[u],
			"Introduce"[length],
			"Change"["some"[t] == "some"[Join[t, Typed[{}, {S}]]]],
			"Rewrite"["joinEmptyRight"[t]],
			"Introduce"[a, rest, length], "Exact"["falseElimination"["successorNotZero"[Length[rest], length]]],
			"Introduce"[k, induction, u, t, length], "Cases"[u],
			"Introduce"[length],
			"Have"[zero, Length[Typed[{}, {S}]] == 0], "Reflexivity",
			"Have"[impossible, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"["falseElimination"[impossible]],
			"Introduce"[a, rest, length], "Cases"[rest],
			"Introduce"[length],
			"Have"[one, Length[{a}] == 1], "Reflexivity",
			"Have"[impossible, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"["falseElimination"[impossible]],
			"Introduce"[b, rest2, length],
			"Have"[expanded, Length[Prepend[a][Prepend[b][rest2]]] == Length[rest2] + 2], "Reflexivity",
			"Have"[restLength, Length[rest2] == 2 * k], "LinearArithmetic",
			"Change"["steps"["tagStep"[productions], k + 1, Prepend[a][Prepend[b][Join[rest2, t]]]] ==
				"some"[Join[t, Join[productions[a], "passOutFrom"[productions, rest2, "true"]]]]],
			"Rewrite"["additionCommutativity"[k, 1]],
			"Rewrite"["stepsAdd"[{S}, "tagStep"[productions], 1, k, Prepend[a][Prepend[b][Join[rest2, t]]]]],
			"Change"["steps"["tagStep"[productions], k, Join[Join[rest2, t], productions[a]]] ==
				"some"[Join[t, Join[productions[a], "passOutFrom"[productions, rest2, "true"]]]]],
			"Rewrite"["joinAssociativity"[rest2, t, productions[a]]],
			"Rewrite"[induction[rest2, Join[t, productions[a]], restLength]],
			"Rewrite"["joinAssociativity"[t, productions[a], "passOutFrom"[productions, rest2, "true"]]]
		}
	],
	(* an odd word followed by c :: d: its last symbol is read with c as its partner *)
	machineTheorem["tagRoundOddBefore",
		ForAll[{Typed[S, TypeUniverse[1]], Typed[productions, S -> {S}], Typed[c, S], Typed[m, NonNegativeIntegers]},
			ForAll[{Typed[v, {S}], Typed[d, {S}]}, Implies[Length[v] == 2 * m + 1,
				"steps"["tagStep"[productions], m + 1, Join[v, Prepend[c][d]]] == "some"[Join[d, "passOutFrom"[productions, v, "true"]]]]]],
		{
			"Introduce"[S, productions, c, m], "Induction"[m],
			(* one symbol: it is read with c as its partner *)
			"Introduce"[v, d, length], "Cases"[v],
			"Introduce"[length], "Exact"["falseElimination"["successorNotZero"[0, "equalitySymmetry"[length]]]],
			"Introduce"[z, rest, length], "Cases"[rest],
			"Introduce"[length],
			"Change"["some"[Join[d, productions[z]]] == "some"[Join[d, Join[productions[z], Typed[{}, {S}]]]]],
			"Rewrite"["joinEmptyRight"[productions[z]]],
			"Introduce"[y, rest2, length],
			"Have"[expanded, Length[Prepend[z][Prepend[y][rest2]]] == Length[rest2] + 2], "Reflexivity",
			"Have"[impossible, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"["falseElimination"[impossible]],
			(* two symbols more: one step, the rest by induction *)
			"Introduce"[k, induction, v, d, length], "Cases"[v],
			"Introduce"[length],
			"Have"[zero, Length[Typed[{}, {S}]] == 0], "Reflexivity",
			"Have"[impossible, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"["falseElimination"[impossible]],
			"Introduce"[x, rest, length], "Cases"[rest],
			"Introduce"[length],
			"Have"[one, Length[{x}] == 1], "Reflexivity",
			"Have"[impossible, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"["falseElimination"[impossible]],
			"Introduce"[y, rest2, length],
			"Have"[expanded, Length[Prepend[x][Prepend[y][rest2]]] == Length[rest2] + 2], "Reflexivity",
			"Have"[restLength, Length[rest2] == 2 * k + 1], "LinearArithmetic",
			"Change"["steps"["tagStep"[productions], k + 1 + 1, Prepend[x][Prepend[y][Join[rest2, Prepend[c][d]]]]] ==
				"some"[Join[d, Join[productions[x], "passOutFrom"[productions, rest2, "true"]]]]],
			"Rewrite"["additionCommutativity"[k + 1, 1]],
			"Rewrite"["stepsAdd"[{S}, "tagStep"[productions], 1, k + 1, Prepend[x][Prepend[y][Join[rest2, Prepend[c][d]]]]]],
			"Change"["steps"["tagStep"[productions], k + 1, Join[Join[rest2, Prepend[c][d]], productions[x]]] ==
				"some"[Join[d, Join[productions[x], "passOutFrom"[productions, rest2, "true"]]]]],
			"Rewrite"["joinAssociativity"[rest2, Prepend[c][d], productions[x]]],
			"Change"["steps"["tagStep"[productions], k + 1, Join[rest2, Prepend[c][Join[d, productions[x]]]]] ==
				"some"[Join[d, Join[productions[x], "passOutFrom"[productions, rest2, "true"]]]]],
			"Rewrite"[induction[rest2, Join[d, productions[x]], restLength]],
			"Rewrite"["joinAssociativity"[d, productions[x], "passOutFrom"[productions, rest2, "true"]]]
		}
	],
	(* a round over a word a :: b :: l of odd length whose first production is c :: d: its last symbol is read with c as
	   its partner, so the next round reads from the second symbol of what this one appends *)
	machineTheorem["tagRoundOddFirst",
		ForAll[{Typed[S, TypeUniverse[1]], Typed[productions, S -> {S}], Typed[n, NonNegativeIntegers], Typed[a, S], Typed[b, S], Typed[l, {S}], Typed[c, S], Typed[d, {S}]},
			Implies[Length[l] == 2 * n + 1, Implies[productions[a] == Prepend[c][d],
				"steps"["tagStep"[productions], n + 2, Prepend[a][Prepend[b][l]]] == "some"[Join[d, "passOutFrom"[productions, l, "true"]]]]]],
		{
			"Introduce"[S, productions, n, a, b, l, c, d, length, first],
			"Change"["steps"["tagStep"[productions], n + 1 + 1, Prepend[a][Prepend[b][l]]] == "some"[Join[d, "passOutFrom"[productions, l, "true"]]]],
			"Rewrite"["additionCommutativity"[n + 1, 1]],
			"Rewrite"["stepsAdd"[{S}, "tagStep"[productions], 1, n + 1, Prepend[a][Prepend[b][l]]]],
			"Change"["steps"["tagStep"[productions], n + 1, Join[l, productions[a]]] == "some"[Join[d, "passOutFrom"[productions, l, "true"]]]],
			"Rewrite"[first],
			"Exact"["tagRoundOddBefore"[S, productions, c, n, l, d, length]]
		}
	],
	(* a round over a whole word of even length *)
	machineTheorem["tagRoundEvenWhole",
		ForAll[{Typed[S, TypeUniverse[1]], Typed[productions, S -> {S}], Typed[n, NonNegativeIntegers], Typed[u, {S}]},
			Implies[Length[u] == 2 * n, "steps"["tagStep"[productions], n, u] == "some"["passOutFrom"[productions, u, "true"]]]],
		{
			"Introduce"[S, productions, n, u, length],
			"Exact"["equalityTransitivity"[
				"equalityCongruence"[Function[{Typed[x, {S}]}, "steps"["tagStep"[productions], n, x]], "equalitySymmetry"["joinEmptyRight"[u]]],
				"tagRoundEven"[S, productions, n, u, Typed[{}, {S}], length]]]
		}
	]
}

(* rung 1, after Cocke and Minsky: a binary Turing machine, the 2-tag system that follows it, its symbols and their
   productions, the words of the five rounds of a step, and the step as rounds of the tag system *)
$minskyDeclarations = {
	(* a binary machine: in state q reading h, it goes to a state, writes a bit and moves; state 0 halts *)
	TypeTheoryInductiveType["MachineTransition", TypeUniverse[1], {
		"machineTransition" -> ForAll[{Typed[next, NonNegativeIntegers], Typed[write, Booleans], Typed[direction, "Direction"]}, "MachineTransition"]
	}],
	TypeTheoryInductiveType["BinaryConfiguration", TypeUniverse[1], {
		"binaryConfiguration" -> ForAll[{Typed[state, NonNegativeIntegers], Typed[left, {Booleans}], Typed[head, Booleans], Typed[right, {Booleans}]}, "BinaryConfiguration"]
	}],
	(* a bit as a number *)
	TypeTheoryDefinition["bitValue", Typed[Function[{Typed[h, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, NonNegativeIntegers], 0, 1, h]], Booleans -> NonNegativeIntegers]],
	(* the symbols: the pad, and each kind with a state, and the scanned bit h and the parity b of the left number where
	   the kind carries them *)
	TypeTheoryInductiveType["MinskySymbol", TypeUniverse[1], {
		"pad" -> "MinskySymbol",
		"symbolA" -> ForAll[{Typed[q, NonNegativeIntegers]}, "MinskySymbol"],
		"symbolAlpha" -> ForAll[{Typed[q, NonNegativeIntegers]}, "MinskySymbol"],
		"symbolB" -> ForAll[{Typed[q, NonNegativeIntegers]}, "MinskySymbol"],
		"symbolBeta" -> ForAll[{Typed[q, NonNegativeIntegers]}, "MinskySymbol"],
		"symbolP1" -> ForAll[{Typed[q, NonNegativeIntegers]}, "MinskySymbol"],
		"symbolP0" -> ForAll[{Typed[q, NonNegativeIntegers]}, "MinskySymbol"],
		"symbolSmallP" -> ForAll[{Typed[q, NonNegativeIntegers]}, "MinskySymbol"],
		"symbolQ" -> ForAll[{Typed[q, NonNegativeIntegers]}, "MinskySymbol"],
		"symbolR" -> ForAll[{Typed[q, NonNegativeIntegers]}, "MinskySymbol"],
		"symbolE" -> ForAll[{Typed[q, NonNegativeIntegers], Typed[h, Booleans]}, "MinskySymbol"],
		"symbolSmallE" -> ForAll[{Typed[q, NonNegativeIntegers], Typed[h, Booleans]}, "MinskySymbol"],
		"symbolF" -> ForAll[{Typed[q, NonNegativeIntegers], Typed[h, Booleans]}, "MinskySymbol"],
		"symbolSmallF" -> ForAll[{Typed[q, NonNegativeIntegers], Typed[h, Booleans]}, "MinskySymbol"],
		"symbolG" -> ForAll[{Typed[q, NonNegativeIntegers], Typed[h, Booleans]}, "MinskySymbol"],
		"symbolSmallG" -> ForAll[{Typed[q, NonNegativeIntegers], Typed[h, Booleans]}, "MinskySymbol"],
		"symbolH" -> ForAll[{Typed[q, NonNegativeIntegers], Typed[h, Booleans]}, "MinskySymbol"],
		"symbolK" -> ForAll[{Typed[q, NonNegativeIntegers], Typed[h, Booleans]}, "MinskySymbol"],
		"symbolI" -> ForAll[{Typed[q, NonNegativeIntegers], Typed[h, Booleans], Typed[b, Booleans]}, "MinskySymbol"],
		"symbolSmallI" -> ForAll[{Typed[q, NonNegativeIntegers], Typed[h, Booleans], Typed[b, Booleans]}, "MinskySymbol"],
		"symbolJ" -> ForAll[{Typed[q, NonNegativeIntegers], Typed[h, Booleans], Typed[b, Booleans]}, "MinskySymbol"],
		"symbolSmallJ" -> ForAll[{Typed[q, NonNegativeIntegers], Typed[h, Booleans], Typed[b, Booleans]}, "MinskySymbol"]
	}],
	(* the pad where a bit is false: it restores the frame a round of odd length shifted *)
	TypeTheoryDefinition["padUnless", Typed[
		Function[{Typed[h, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, {"MinskySymbol"}], {"pad"}, Typed[{}, {"MinskySymbol"}], h]],
		Booleans -> {"MinskySymbol"}
	]],
	(* the case of a direction *)
	TypeTheoryDefinition["byDirection", Typed[
		Function[{TypedImplicit[S, TypeUniverse[1]], Typed[d, "Direction"], Typed[leftCase, S], Typed[rightCase, S]}, InductiveRecursor["Direction"][Function[{Typed[t, "Direction"]}, S], leftCase, rightCase, d]],
		ForAll[{TypedImplicit[S, TypeUniverse[1]]}, "Direction" -> S -> S -> S]
	]],
	(* the productions: rounds 1 and 2 copy the word and read the scanned bit, round 3 makes the transition, rounds 4 and 5
	   halve the left number for a move to the left *)
	TypeTheoryDefinition["minskyProductions", Typed[
		Function[{Typed[tm, NonNegativeIntegers -> Booleans -> "MachineTransition"], Typed[s, "MinskySymbol"]}, InductiveRecursor["MinskySymbol"][Function[{Typed[t, "MinskySymbol"]}, {"MinskySymbol"}],
				Typed[{}, {"MinskySymbol"}],
				Function[{Typed[q, NonNegativeIntegers]}, {"symbolP1"[q], "symbolP0"[q]}],
				Function[{Typed[q, NonNegativeIntegers]}, {"symbolSmallP"[q], "symbolSmallP"[q]}],
				Function[{Typed[q, NonNegativeIntegers]}, {"symbolQ"[q]}],
				Function[{Typed[q, NonNegativeIntegers]}, {"symbolR"[q]}],
				Function[{Typed[q, NonNegativeIntegers]}, {"symbolE"[q, "true"], "symbolE"[q, "false"]}],
				Function[{Typed[q, NonNegativeIntegers]}, Typed[{}, {"MinskySymbol"}]],
				Function[{Typed[q, NonNegativeIntegers]}, {"symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"]}],
				Function[{Typed[q, NonNegativeIntegers]}, {"symbolF"[q, "true"], "symbolF"[q, "false"]}],
				Function[{Typed[q, NonNegativeIntegers]}, {"symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"]}],
				Function[{Typed[q, NonNegativeIntegers], Typed[h, Booleans]}, "byDirection"[tm[q][h][["direction"]], Join["padUnless"[h], {"symbolG"[q, h]}], Join["padUnless"[h], Prepend["symbolA"[tm[q][h][["next"]]]][Prepend["pad"]["pairs"["symbolAlpha"[tm[q][h][["next"]]], "pad", "bitValue"[tm[q][h][["write"]]]]]]]]],
				Function[{Typed[q, NonNegativeIntegers], Typed[h, Booleans]}, "byDirection"[tm[q][h][["direction"]], {"symbolSmallG"[q, h]}, {"symbolAlpha"[tm[q][h][["next"]]], "pad", "symbolAlpha"[tm[q][h][["next"]]], "pad"}]],
				Function[{Typed[q, NonNegativeIntegers], Typed[h, Booleans]}, "byDirection"[tm[q][h][["direction"]], {"symbolH"[q, h], "symbolH"[q, h]}, {"symbolB"[tm[q][h][["next"]]], "pad"}]],
				Function[{Typed[q, NonNegativeIntegers], Typed[h, Booleans]}, "byDirection"[tm[q][h][["direction"]], {"symbolK"[q, h], "symbolK"[q, h], "symbolK"[q, h], "symbolK"[q, h]}, {"symbolBeta"[tm[q][h][["next"]]], "pad"}]],
				Function[{Typed[q, NonNegativeIntegers], Typed[h, Booleans]}, {"symbolI"[q, h, "true"], "symbolI"[q, h, "false"]}],
				Function[{Typed[q, NonNegativeIntegers], Typed[h, Booleans]}, {"symbolSmallI"[q, h, "true"], "symbolSmallI"[q, h, "false"]}],
				Function[{Typed[q, NonNegativeIntegers], Typed[h, Booleans]}, {"symbolJ"[q, h, "true"], "symbolJ"[q, h, "false"]}],
				Function[{Typed[q, NonNegativeIntegers], Typed[h, Booleans]}, {"symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"]}],
				Function[{Typed[q, NonNegativeIntegers], Typed[h, Booleans], Typed[b, Booleans]}, Join["padUnless"[b], {"symbolA"[tm[q][h][["next"]]], "pad"}]],
				Function[{Typed[q, NonNegativeIntegers], Typed[h, Booleans], Typed[b, Booleans]}, {"symbolAlpha"[tm[q][h][["next"]]], "pad"}],
				Function[{Typed[q, NonNegativeIntegers], Typed[h, Booleans], Typed[b, Booleans]}, Prepend["symbolB"[tm[q][h][["next"]]]][Prepend["pad"]["pairs"["symbolBeta"[tm[q][h][["next"]]], "pad", 2 * "bitValue"[tm[q][h][["write"]]] + "bitValue"[b]]]]],
				Function[{Typed[q, NonNegativeIntegers], Typed[h, Booleans], Typed[b, Booleans]}, {"symbolBeta"[tm[q][h][["next"]]], "pad", "symbolBeta"[tm[q][h][["next"]]], "pad"}],
				s]],
		(NonNegativeIntegers -> Booleans -> "MachineTransition") -> "MinskySymbol" -> {"MinskySymbol"}
	]],
	(* helper lemmas: lengths of pairs, m copies of a pair are pairs, 2 n copies of a symbol are n pairs, and a round over
	   pairs alone *)
	machineTheorem["lengthPairs",
		ForAll[{Typed[S, TypeUniverse[1]], Typed[a, S], Typed[b, S], Typed[m, NonNegativeIntegers]}, Length["pairs"[a, b, m]] == 2 * m],
		{
			"Introduce"[S, a, b, m], "Induction"[m], "Reflexivity",
			"Introduce"[k, induction],
			"Change"[Length["pairs"[a, b, k]] + 1 + 1 == 2 * k + 2],
			"Rewrite"[induction],
			"Reflexivity"
		}
	],
	machineTheorem["repeatedPair",
		ForAll[{Typed[S, TypeUniverse[1]], Typed[a, S], Typed[b, S], Typed[m, NonNegativeIntegers]}, "repeated"[{a, b}, m] == "pairs"[a, b, m]],
		{
			"Introduce"[S, a, b, m], "Induction"[m], "Reflexivity",
			"Introduce"[k, induction],
			"Change"[Prepend[a][Prepend[b]["repeated"[{a, b}, k]]] == Prepend[a][Prepend[b]["pairs"[a, b, k]]]],
			"Rewrite"[induction]
		}
	],
	machineTheorem["repeatedDouble",
		ForAll[{Typed[S, TypeUniverse[1]], Typed[a, S], Typed[n, NonNegativeIntegers]}, "repeated"[{a}, 2 * n] == "pairs"[a, a, n]],
		{
			"Introduce"[S, a, n], "Induction"[n], "Reflexivity",
			"Introduce"[k, induction],
			"Change"[Prepend[a][Prepend[a]["repeated"[{a}, 2 * k]]] == Prepend[a][Prepend[a]["pairs"[a, a, k]]]],
			"Rewrite"[induction]
		}
	],
	machineTheorem["passOutPairs",
		ForAll[{Typed[S, TypeUniverse[1]], Typed[productions, S -> {S}], Typed[a, S], Typed[b, S], Typed[m, NonNegativeIntegers]},
			And["passOutFrom"[productions, "pairs"[a, b, m], "true"] == "repeated"[productions[a], m], "passOutFrom"[productions, "pairs"[a, b, m], "false"] == "repeated"[productions[b], m]]],
		{
			"Introduce"[S, productions, a, b, m],
			"Exact"["andIntroduction"[
				"equalityTransitivity"["equalityCongruence"[Function[{Typed[x, {S}]}, "passOutFrom"[productions, x, "true"]], "equalitySymmetry"["joinEmptyRight"["pairs"[a, b, m]]]],
					"equalityTransitivity"["passOutAlignedPairs"[S, productions, a, b, m, Typed[{}, {S}]], "joinEmptyRight"["repeated"[productions[a], m]]]],
				"equalityTransitivity"["equalityCongruence"[Function[{Typed[x, {S}]}, "passOutFrom"[productions, x, "false"]], "equalitySymmetry"["joinEmptyRight"["pairs"[a, b, m]]]],
					"equalityTransitivity"["passOutShiftedPairs"[S, productions, a, b, m, Typed[{}, {S}]], "joinEmptyRight"["repeated"[productions[b], m]]]]
			]]
		}
	],
	(* the word of a configuration in state q with left number m and right number N, and the word after round 1 *)
	TypeTheoryDefinition["minskyWord", Typed[
		Function[{Typed[q, NonNegativeIntegers], Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]},
			Prepend["symbolA"[q]][Prepend["pad"][Join["pairs"["symbolAlpha"[q], "pad", m], Prepend["symbolB"[q]][Prepend["pad"]["pairs"["symbolBeta"[q], "pad", n]]]]]]],
		NonNegativeIntegers -> NonNegativeIntegers -> NonNegativeIntegers -> {"MinskySymbol"}
	]],
	TypeTheoryDefinition["afterRound1", Typed[
		Function[{Typed[q, NonNegativeIntegers], Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]},
			Prepend["symbolP1"[q]][Prepend["symbolP0"[q]][Join["pairs"["symbolSmallP"[q], "symbolSmallP"[q], m], Prepend["symbolQ"[q]]["repeated"[{"symbolR"[q]}, n]]]]]],
		NonNegativeIntegers -> NonNegativeIntegers -> NonNegativeIntegers -> {"MinskySymbol"}
	]],
	(* round 1 copies the word: A -> P1 P0, alpha -> p p, B -> Q, beta -> r *)
	machineTheorem["minskyRound1",
		ForAll[{Typed[tm, NonNegativeIntegers -> Booleans -> "MachineTransition"], Typed[q, NonNegativeIntegers], Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]},
			"steps"["tagStep"["minskyProductions"[tm]], m + n + 2, "minskyWord"[q, m, n]] == "some"["afterRound1"[q, m, n]]],
		{
			"Introduce"[tm, q, m, n],
			"Have"[left, Length["pairs"["symbolAlpha"[q], "pad", m]] == 2 * m], "Exact"["lengthPairs"["MinskySymbol", "symbolAlpha"[q], "pad", m]],
			"Have"[right, Length["pairs"["symbolBeta"[q], "pad", n]] == 2 * n], "Exact"["lengthPairs"["MinskySymbol", "symbolBeta"[q], "pad", n]],
			"Have"[joined, Length[Join["pairs"["symbolAlpha"[q], "pad", m], Prepend["symbolB"[q]][Prepend["pad"]["pairs"["symbolBeta"[q], "pad", n]]]]] ==
				Length["pairs"["symbolAlpha"[q], "pad", m]] + Length[Prepend["symbolB"[q]][Prepend["pad"]["pairs"["symbolBeta"[q], "pad", n]]]]],
			"Exact"["lengthJoin"["pairs"["symbolAlpha"[q], "pad", m], Prepend["symbolB"[q]][Prepend["pad"]["pairs"["symbolBeta"[q], "pad", n]]]]],
			"Have"[middle, Length[Prepend["symbolB"[q]][Prepend["pad"]["pairs"["symbolBeta"[q], "pad", n]]]] == Length["pairs"["symbolBeta"[q], "pad", n]] + 2], "Reflexivity",
			"Have"[whole, Length["minskyWord"[q, m, n]] == Length[Join["pairs"["symbolAlpha"[q], "pad", m], Prepend["symbolB"[q]][Prepend["pad"]["pairs"["symbolBeta"[q], "pad", n]]]]] + 2], "Reflexivity",
			"Have"[length, Length["minskyWord"[q, m, n]] == 2 * (m + n + 2)], "LinearArithmetic",
			"Rewrite"["tagRoundEvenWhole"["MinskySymbol", "minskyProductions"[tm], m + n + 2, "minskyWord"[q, m, n], length]],
			"Change"["some"[Join[{"symbolP1"[q], "symbolP0"[q]}, "passOutFrom"["minskyProductions"[tm],
				Join["pairs"["symbolAlpha"[q], "pad", m], Prepend["symbolB"[q]][Prepend["pad"]["pairs"["symbolBeta"[q], "pad", n]]]], "true"]]] == "some"["afterRound1"[q, m, n]]],
			"Rewrite"["passOutAlignedPairs"["MinskySymbol", "minskyProductions"[tm], "symbolAlpha"[q], "pad", m, Prepend["symbolB"[q]][Prepend["pad"]["pairs"["symbolBeta"[q], "pad", n]]]]],
			"Change"["some"[Join[{"symbolP1"[q], "symbolP0"[q]}, Join["repeated"[{"symbolSmallP"[q], "symbolSmallP"[q]}, m],
				Prepend["symbolQ"[q]]["passOutFrom"["minskyProductions"[tm], "pairs"["symbolBeta"[q], "pad", n], "true"]]]]] == "some"["afterRound1"[q, m, n]]],
			"Rewrite"["andEliminationLeft"["passOutPairs"["MinskySymbol", "minskyProductions"[tm], "symbolBeta"[q], "pad", n]]],
			"Rewrite"["repeatedPair"["MinskySymbol", "symbolSmallP"[q], "symbolSmallP"[q], m]],
			"Reflexivity"
		}
	],
	(* the word after round 2: the scanned bit h read off the right number, n the rest of it *)
	TypeTheoryDefinition["afterRound2", Typed[
		Function[{Typed[q, NonNegativeIntegers], Typed[h, Booleans], Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]},
			Join[InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, {"MinskySymbol"}], Typed[{}, {"MinskySymbol"}], {"symbolE"[q, "true"]}, h],
				Prepend["symbolE"[q, "false"]][Join["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]]]],
		NonNegativeIntegers -> Booleans -> NonNegativeIntegers -> NonNegativeIntegers -> {"MinskySymbol"}
	]],
	(* round 2 reads P1, the p of every pair, Q, and every other r: the right number 2 n + h loses its lowest bit h, which
	   decides whether the round has odd length and E1 its partner *)
	machineTheorem["minskyRound2",
		ForAll[{Typed[tm, NonNegativeIntegers -> Booleans -> "MachineTransition"], Typed[q, NonNegativeIntegers], Typed[m, NonNegativeIntegers], Typed[h, Booleans], Typed[n, NonNegativeIntegers]},
			"steps"["tagStep"["minskyProductions"[tm]], m + n + 2, "afterRound1"[q, m, 2 * n + "bitValue"[h]]] == "some"["afterRound2"[q, h, m, n]]],
		{
			"Introduce"[tm, q, m, h, n],
			"Have"[left, Length["pairs"["symbolSmallP"[q], "symbolSmallP"[q], m]] == 2 * m], "Exact"["lengthPairs"["MinskySymbol", "symbolSmallP"[q], "symbolSmallP"[q], m]],
			"Have"[right, Length["pairs"["symbolR"[q], "symbolR"[q], n]] == 2 * n], "Exact"["lengthPairs"["MinskySymbol", "symbolR"[q], "symbolR"[q], n]],
			"Cases"[h],
			(* h false: odd length, E1 is the partner of the last r *)
			"Change"["steps"["tagStep"["minskyProductions"[tm]], m + n + 2, Prepend["symbolP1"[q]][Prepend["symbolP0"[q]][Join["pairs"["symbolSmallP"[q], "symbolSmallP"[q], m], Prepend["symbolQ"[q]]["repeated"[{"symbolR"[q]}, 2 * n]]]]]] ==
				"some"[Prepend["symbolE"[q, "false"]][Join["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]]]],
			"Rewrite"["repeatedDouble"["MinskySymbol", "symbolR"[q], n]],
			"Have"[joined, Length[Join["pairs"["symbolSmallP"[q], "symbolSmallP"[q], m], Prepend["symbolQ"[q]]["pairs"["symbolR"[q], "symbolR"[q], n]]]] == Length["pairs"["symbolSmallP"[q], "symbolSmallP"[q], m]] + Length[Prepend["symbolQ"[q]]["pairs"["symbolR"[q], "symbolR"[q], n]]]],
			"Exact"["lengthJoin"["pairs"["symbolSmallP"[q], "symbolSmallP"[q], m], Prepend["symbolQ"[q]]["pairs"["symbolR"[q], "symbolR"[q], n]]]],
			"Have"[middle, Length[Prepend["symbolQ"[q]]["pairs"["symbolR"[q], "symbolR"[q], n]]] == Length["pairs"["symbolR"[q], "symbolR"[q], n]] + 1], "Reflexivity",
			"Have"[length, Length[Join["pairs"["symbolSmallP"[q], "symbolSmallP"[q], m], Prepend["symbolQ"[q]]["pairs"["symbolR"[q], "symbolR"[q], n]]]] == 2 * (m + n) + 1], "LinearArithmetic",
			"Rewrite"["tagRoundOddFirst"["MinskySymbol", "minskyProductions"[tm], m + n, "symbolP1"[q], "symbolP0"[q], Join["pairs"["symbolSmallP"[q], "symbolSmallP"[q], m], Prepend["symbolQ"[q]]["pairs"["symbolR"[q], "symbolR"[q], n]]], "symbolE"[q, "true"], {"symbolE"[q, "false"]}, length,
				"equalityReflexivity"[{"symbolE"[q, "true"], "symbolE"[q, "false"]}]]],
			"Rewrite"["passOutAlignedPairs"["MinskySymbol", "minskyProductions"[tm], "symbolSmallP"[q], "symbolSmallP"[q], m, Prepend["symbolQ"[q]]["pairs"["symbolR"[q], "symbolR"[q], n]]]],
			"Change"["some"[Join[{"symbolE"[q, "false"]}, Join["repeated"[{"symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"]}, m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["passOutFrom"["minskyProductions"[tm], "pairs"["symbolR"[q], "symbolR"[q], n], "false"]]]]]] ==
				"some"[Prepend["symbolE"[q, "false"]][Join["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]]]],
			"Rewrite"["andEliminationRight"["passOutPairs"["MinskySymbol", "minskyProductions"[tm], "symbolR"[q], "symbolR"[q], n]]],
			"Change"["some"[Join[{"symbolE"[q, "false"]}, Join["repeated"[{"symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"]}, m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["repeated"[{"symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"]}, n]]]]]] ==
				"some"[Prepend["symbolE"[q, "false"]][Join["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]]]],
			"Rewrite"["repeatedPair"["MinskySymbol", "symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m]],
			"Rewrite"["repeatedPair"["MinskySymbol", "symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]],
			"Reflexivity",
			(* h true: even length *)
			"Change"["steps"["tagStep"["minskyProductions"[tm]], m + n + 2, Prepend["symbolP1"[q]][Prepend["symbolP0"[q]][Join["pairs"["symbolSmallP"[q], "symbolSmallP"[q], m], Prepend["symbolQ"[q]][Prepend["symbolR"[q]]["repeated"[{"symbolR"[q]}, 2 * n]]]]]]] ==
				"some"[Prepend["symbolE"[q, "true"]][Prepend["symbolE"[q, "false"]][Join["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]]]]],
			"Rewrite"["repeatedDouble"["MinskySymbol", "symbolR"[q], n]],
			"Have"[joined, Length[Join["pairs"["symbolSmallP"[q], "symbolSmallP"[q], m], Prepend["symbolQ"[q]][Prepend["symbolR"[q]]["pairs"["symbolR"[q], "symbolR"[q], n]]]]] ==
				Length["pairs"["symbolSmallP"[q], "symbolSmallP"[q], m]] + Length[Prepend["symbolQ"[q]][Prepend["symbolR"[q]]["pairs"["symbolR"[q], "symbolR"[q], n]]]]],
			"Exact"["lengthJoin"["pairs"["symbolSmallP"[q], "symbolSmallP"[q], m], Prepend["symbolQ"[q]][Prepend["symbolR"[q]]["pairs"["symbolR"[q], "symbolR"[q], n]]]]],
			"Have"[middle, Length[Prepend["symbolQ"[q]][Prepend["symbolR"[q]]["pairs"["symbolR"[q], "symbolR"[q], n]]]] == Length["pairs"["symbolR"[q], "symbolR"[q], n]] + 2], "Reflexivity",
			"Have"[whole, Length[Prepend["symbolP1"[q]][Prepend["symbolP0"[q]][Join["pairs"["symbolSmallP"[q], "symbolSmallP"[q], m], Prepend["symbolQ"[q]][Prepend["symbolR"[q]]["pairs"["symbolR"[q], "symbolR"[q], n]]]]]]] ==
				Length[Join["pairs"["symbolSmallP"[q], "symbolSmallP"[q], m], Prepend["symbolQ"[q]][Prepend["symbolR"[q]]["pairs"["symbolR"[q], "symbolR"[q], n]]]]] + 2], "Reflexivity",
			"Have"[length, Length[Prepend["symbolP1"[q]][Prepend["symbolP0"[q]][Join["pairs"["symbolSmallP"[q], "symbolSmallP"[q], m], Prepend["symbolQ"[q]][Prepend["symbolR"[q]]["pairs"["symbolR"[q], "symbolR"[q], n]]]]]]] == 2 * (m + n + 2)], "LinearArithmetic",
			"Rewrite"["tagRoundEvenWhole"["MinskySymbol", "minskyProductions"[tm], m + n + 2, Prepend["symbolP1"[q]][Prepend["symbolP0"[q]][Join["pairs"["symbolSmallP"[q], "symbolSmallP"[q], m], Prepend["symbolQ"[q]][Prepend["symbolR"[q]]["pairs"["symbolR"[q], "symbolR"[q], n]]]]]], length]],
			"Change"["some"[Join[{"symbolE"[q, "true"], "symbolE"[q, "false"]}, "passOutFrom"["minskyProductions"[tm], Join["pairs"["symbolSmallP"[q], "symbolSmallP"[q], m], Prepend["symbolQ"[q]][Prepend["symbolR"[q]]["pairs"["symbolR"[q], "symbolR"[q], n]]]], "true"]]] ==
				"some"[Prepend["symbolE"[q, "true"]][Prepend["symbolE"[q, "false"]][Join["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]]]]],
			"Rewrite"["passOutAlignedPairs"["MinskySymbol", "minskyProductions"[tm], "symbolSmallP"[q], "symbolSmallP"[q], m, Prepend["symbolQ"[q]][Prepend["symbolR"[q]]["pairs"["symbolR"[q], "symbolR"[q], n]]]]],
			"Change"["some"[Join[{"symbolE"[q, "true"], "symbolE"[q, "false"]}, Join["repeated"[{"symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"]}, m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["passOutFrom"["minskyProductions"[tm], "pairs"["symbolR"[q], "symbolR"[q], n], "true"]]]]]] ==
				"some"[Prepend["symbolE"[q, "true"]][Prepend["symbolE"[q, "false"]][Join["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]]]]],
			"Rewrite"["andEliminationLeft"["passOutPairs"["MinskySymbol", "minskyProductions"[tm], "symbolR"[q], "symbolR"[q], n]]],
			"Change"["some"[Join[{"symbolE"[q, "true"], "symbolE"[q, "false"]}, Join["repeated"[{"symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"]}, m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["repeated"[{"symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"]}, n]]]]]] ==
				"some"[Prepend["symbolE"[q, "true"]][Prepend["symbolE"[q, "false"]][Join["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]]]]],
			"Rewrite"["repeatedPair"["MinskySymbol", "symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m]],
			"Rewrite"["repeatedPair"["MinskySymbol", "symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]],
			"Reflexivity"
		}
	],
	(* an odd round from its head, pairs of a sum, a pair of pairs repeated, and the productions of a move *)
	(* a round over a word a :: l of odd length whose first production is c :: d *)
	machineTheorem["tagRoundOddHead",
		ForAll[{Typed[S, TypeUniverse[1]], Typed[productions, S -> {S}], Typed[n, NonNegativeIntegers], Typed[a, S], Typed[l, {S}], Typed[c, S], Typed[d, {S}]},
			Implies[Length[l] == 2 * n + 2, Implies[productions[a] == Prepend[c][d],
				"steps"["tagStep"[productions], n + 2, Prepend[a][l]] == "some"[Join[d, "passOutFrom"[productions, l, "false"]]]]]],
		{
			"Introduce"[S, productions, n, a, l, c, d, length, first], "Cases"[l],
			"Introduce"[length], "Exact"["falseElimination"["successorNotZero"[2 * n + 1, "equalitySymmetry"[length]]]],
			"Introduce"[b, rest, length],
			"Have"[restLength, Length[rest] == 2 * n + 1],
			"Have"[expanded, Length[Prepend[b][rest]] == Length[rest] + 1], "Reflexivity",
			"LinearArithmetic",
			"Exact"["tagRoundOddFirst"[S, productions, n, a, b, rest, c, d, restLength, first]]
		}
	],
	machineTheorem["pairsAdd",
		ForAll[{Typed[S, TypeUniverse[1]], Typed[a, S], Typed[b, S], Typed[k, NonNegativeIntegers], Typed[j, NonNegativeIntegers]},
			"pairs"[a, b, k + j] == Join["pairs"[a, b, j], "pairs"[a, b, k]]],
		{
			"Introduce"[S, a, b, k, j], "Induction"[j], "Reflexivity",
			"Introduce"[i, induction],
			"Change"[Prepend[a][Prepend[b]["pairs"[a, b, k + i]]] == Prepend[a][Prepend[b][Join["pairs"[a, b, i], "pairs"[a, b, k]]]]],
			"Rewrite"[induction]
		}
	],
	machineTheorem["repeatedPairTwice",
		ForAll[{Typed[S, TypeUniverse[1]], Typed[a, S], Typed[b, S], Typed[m, NonNegativeIntegers]}, "repeated"[{a, b, a, b}, m] == "pairs"[a, b, 2 * m]],
		{
			"Introduce"[S, a, b, m], "Induction"[m], "Reflexivity",
			"Introduce"[k, induction],
			"Change"[Prepend[a][Prepend[b][Prepend[a][Prepend[b]["repeated"[{a, b, a, b}, k]]]]] == Prepend[a][Prepend[b][Prepend[a][Prepend[b]["pairs"[a, b, 2 * k]]]]]],
			"Rewrite"[induction]
		}
	],
	machineTheorem["productionERight",
		ForAll[{Typed[tm, NonNegativeIntegers -> Booleans -> "MachineTransition"], Typed[q, NonNegativeIntegers], Typed[h, Booleans]},
			Implies[tm[q][h][["direction"]] == "moveRight", "minskyProductions"[tm]["symbolE"[q, h]] == Join["padUnless"[h], Prepend["symbolA"[tm[q][h][["next"]]]][Prepend["pad"]["pairs"["symbolAlpha"[tm[q][h][["next"]]], "pad", "bitValue"[tm[q][h][["write"]]]]]]]]],
		{
			"Introduce"[tm, q, h, moved],
			"Change"["byDirection"[tm[q][h][["direction"]], Join["padUnless"[h], {"symbolG"[q, h]}], Join["padUnless"[h], Prepend["symbolA"[tm[q][h][["next"]]]][Prepend["pad"]["pairs"["symbolAlpha"[tm[q][h][["next"]]], "pad", "bitValue"[tm[q][h][["write"]]]]]]]] == Join["padUnless"[h], Prepend["symbolA"[tm[q][h][["next"]]]][Prepend["pad"]["pairs"["symbolAlpha"[tm[q][h][["next"]]], "pad", "bitValue"[tm[q][h][["write"]]]]]]]],
			"Rewrite"[moved],
			"Reflexivity"
		}
	],
	machineTheorem["productionELeft",
		ForAll[{Typed[tm, NonNegativeIntegers -> Booleans -> "MachineTransition"], Typed[q, NonNegativeIntegers], Typed[h, Booleans]},
			Implies[tm[q][h][["direction"]] == "moveLeft", "minskyProductions"[tm]["symbolE"[q, h]] == Join["padUnless"[h], {"symbolG"[q, h]}]]],
		{
			"Introduce"[tm, q, h, moved],
			"Change"["byDirection"[tm[q][h][["direction"]], Join["padUnless"[h], {"symbolG"[q, h]}], Join["padUnless"[h], Prepend["symbolA"[tm[q][h][["next"]]]][Prepend["pad"]["pairs"["symbolAlpha"[tm[q][h][["next"]]], "pad", "bitValue"[tm[q][h][["write"]]]]]]]] == Join["padUnless"[h], {"symbolG"[q, h]}]],
			"Rewrite"[moved],
			"Reflexivity"
		}
	],
	machineTheorem["productionSmallERight",
		ForAll[{Typed[tm, NonNegativeIntegers -> Booleans -> "MachineTransition"], Typed[q, NonNegativeIntegers], Typed[h, Booleans]},
			Implies[tm[q][h][["direction"]] == "moveRight", "minskyProductions"[tm]["symbolSmallE"[q, h]] == {"symbolAlpha"[tm[q][h][["next"]]], "pad", "symbolAlpha"[tm[q][h][["next"]]], "pad"}]],
		{
			"Introduce"[tm, q, h, moved],
			"Change"["byDirection"[tm[q][h][["direction"]], {"symbolSmallG"[q, h]}, {"symbolAlpha"[tm[q][h][["next"]]], "pad", "symbolAlpha"[tm[q][h][["next"]]], "pad"}] == {"symbolAlpha"[tm[q][h][["next"]]], "pad", "symbolAlpha"[tm[q][h][["next"]]], "pad"}],
			"Rewrite"[moved],
			"Reflexivity"
		}
	],
	machineTheorem["productionSmallELeft",
		ForAll[{Typed[tm, NonNegativeIntegers -> Booleans -> "MachineTransition"], Typed[q, NonNegativeIntegers], Typed[h, Booleans]},
			Implies[tm[q][h][["direction"]] == "moveLeft", "minskyProductions"[tm]["symbolSmallE"[q, h]] == {"symbolSmallG"[q, h]}]],
		{
			"Introduce"[tm, q, h, moved],
			"Change"["byDirection"[tm[q][h][["direction"]], {"symbolSmallG"[q, h]}, {"symbolAlpha"[tm[q][h][["next"]]], "pad", "symbolAlpha"[tm[q][h][["next"]]], "pad"}] == {"symbolSmallG"[q, h]}],
			"Rewrite"[moved],
			"Reflexivity"
		}
	],
	machineTheorem["productionFRight",
		ForAll[{Typed[tm, NonNegativeIntegers -> Booleans -> "MachineTransition"], Typed[q, NonNegativeIntegers], Typed[h, Booleans]},
			Implies[tm[q][h][["direction"]] == "moveRight", "minskyProductions"[tm]["symbolF"[q, h]] == {"symbolB"[tm[q][h][["next"]]], "pad"}]],
		{
			"Introduce"[tm, q, h, moved],
			"Change"["byDirection"[tm[q][h][["direction"]], {"symbolH"[q, h], "symbolH"[q, h]}, {"symbolB"[tm[q][h][["next"]]], "pad"}] == {"symbolB"[tm[q][h][["next"]]], "pad"}],
			"Rewrite"[moved],
			"Reflexivity"
		}
	],
	machineTheorem["productionFLeft",
		ForAll[{Typed[tm, NonNegativeIntegers -> Booleans -> "MachineTransition"], Typed[q, NonNegativeIntegers], Typed[h, Booleans]},
			Implies[tm[q][h][["direction"]] == "moveLeft", "minskyProductions"[tm]["symbolF"[q, h]] == {"symbolH"[q, h], "symbolH"[q, h]}]],
		{
			"Introduce"[tm, q, h, moved],
			"Change"["byDirection"[tm[q][h][["direction"]], {"symbolH"[q, h], "symbolH"[q, h]}, {"symbolB"[tm[q][h][["next"]]], "pad"}] == {"symbolH"[q, h], "symbolH"[q, h]}],
			"Rewrite"[moved],
			"Reflexivity"
		}
	],
	machineTheorem["productionSmallFRight",
		ForAll[{Typed[tm, NonNegativeIntegers -> Booleans -> "MachineTransition"], Typed[q, NonNegativeIntegers], Typed[h, Booleans]},
			Implies[tm[q][h][["direction"]] == "moveRight", "minskyProductions"[tm]["symbolSmallF"[q, h]] == {"symbolBeta"[tm[q][h][["next"]]], "pad"}]],
		{
			"Introduce"[tm, q, h, moved],
			"Change"["byDirection"[tm[q][h][["direction"]], {"symbolK"[q, h], "symbolK"[q, h], "symbolK"[q, h], "symbolK"[q, h]}, {"symbolBeta"[tm[q][h][["next"]]], "pad"}] == {"symbolBeta"[tm[q][h][["next"]]], "pad"}],
			"Rewrite"[moved],
			"Reflexivity"
		}
	],
	machineTheorem["productionSmallFLeft",
		ForAll[{Typed[tm, NonNegativeIntegers -> Booleans -> "MachineTransition"], Typed[q, NonNegativeIntegers], Typed[h, Booleans]},
			Implies[tm[q][h][["direction"]] == "moveLeft", "minskyProductions"[tm]["symbolSmallF"[q, h]] == {"symbolK"[q, h], "symbolK"[q, h], "symbolK"[q, h], "symbolK"[q, h]}]],
		{
			"Introduce"[tm, q, h, moved],
			"Change"["byDirection"[tm[q][h][["direction"]], {"symbolK"[q, h], "symbolK"[q, h], "symbolK"[q, h], "symbolK"[q, h]}, {"symbolBeta"[tm[q][h][["next"]]], "pad"}] == {"symbolK"[q, h], "symbolK"[q, h], "symbolK"[q, h], "symbolK"[q, h]}],
			"Rewrite"[moved],
			"Reflexivity"
		}
	],
	(* the word after round 3 of a move to the right is the next configuration's: the written bit joins the left number *)
	machineTheorem["minskyRound3Right",
		ForAll[{Typed[tm, NonNegativeIntegers -> Booleans -> "MachineTransition"], Typed[q, NonNegativeIntegers], Typed[h, Booleans], Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]},
			Implies[tm[q][h][["direction"]] == "moveRight",
				"steps"["tagStep"["minskyProductions"[tm]], m + n + 2, "afterRound2"[q, h, m, n]] == "some"["minskyWord"[tm[q][h][["next"]], 2 * m + "bitValue"[tm[q][h][["write"]]], n]]]],
		{
			"Introduce"[tm, q, h, m, n],
			"Have"[left, Length["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m]] == 2 * m], "Exact"["lengthPairs"["MinskySymbol", "symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m]],
			"Have"[right, Length["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]] == 2 * n], "Exact"["lengthPairs"["MinskySymbol", "symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]],
			"Cases"[h],
			(* h false: odd length, the pad that E0 writes first is the partner of the last f *)
			"Introduce"[moved],
			"Change"["steps"["tagStep"["minskyProductions"[tm]], m + n + 2, Prepend["symbolE"[q, "false"]][Join["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]]] == "some"[Prepend["symbolA"[tm[q]["false"][["next"]]]][Prepend["pad"][Join["pairs"["symbolAlpha"[tm[q]["false"][["next"]]], "pad", 2 * m + "bitValue"[tm[q]["false"][["write"]]]], Prepend["symbolB"[tm[q]["false"][["next"]]]][Prepend["pad"]["pairs"["symbolBeta"[tm[q]["false"][["next"]]], "pad", n]]]]]]]],
			"Have"[joined, Length[Join["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]] == Length["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m]] + Length[Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]], "Exact"["lengthJoin"["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]],
			"Have"[tail, Length[Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]] == Length["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]] + 2], "Reflexivity",
			"Have"[length, Length[Join["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]] == 2 * (m + n) + 2], "LinearArithmetic",
			"Rewrite"["tagRoundOddHead"["MinskySymbol", "minskyProductions"[tm], m + n, "symbolE"[q, "false"], Join["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]], "pad", Prepend["symbolA"[tm[q]["false"][["next"]]]][Prepend["pad"]["pairs"["symbolAlpha"[tm[q]["false"][["next"]]], "pad", "bitValue"[tm[q]["false"][["write"]]]]]], length,
				"productionERight"[tm, q, "false", moved]]],
			"Rewrite"["passOutShiftedPairs"["MinskySymbol", "minskyProductions"[tm], "symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m, Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]],
			"Change"["some"[Join[Prepend["symbolA"[tm[q]["false"][["next"]]]][Prepend["pad"]["pairs"["symbolAlpha"[tm[q]["false"][["next"]]], "pad", "bitValue"[tm[q]["false"][["write"]]]]]], Join["repeated"["minskyProductions"[tm]["symbolSmallE"[q, "false"]], m], Join["minskyProductions"[tm]["symbolF"[q, "false"]], "passOutFrom"["minskyProductions"[tm], "pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n], "false"]]]]] == "some"[Prepend["symbolA"[tm[q]["false"][["next"]]]][Prepend["pad"][Join["pairs"["symbolAlpha"[tm[q]["false"][["next"]]], "pad", 2 * m + "bitValue"[tm[q]["false"][["write"]]]], Prepend["symbolB"[tm[q]["false"][["next"]]]][Prepend["pad"]["pairs"["symbolBeta"[tm[q]["false"][["next"]]], "pad", n]]]]]]]],
			"Rewrite"["andEliminationRight"["passOutPairs"["MinskySymbol", "minskyProductions"[tm], "symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]],
			"Rewrite"["productionSmallERight"[tm, q, "false", moved]],
			"Rewrite"["productionFRight"[tm, q, "false", moved]],
			"Rewrite"["productionSmallFRight"[tm, q, "false", moved]],
			"Change"["some"[Join[Prepend["symbolA"[tm[q]["false"][["next"]]]][Prepend["pad"]["pairs"["symbolAlpha"[tm[q]["false"][["next"]]], "pad", "bitValue"[tm[q]["false"][["write"]]]]]], Join["repeated"[{"symbolAlpha"[tm[q]["false"][["next"]]], "pad", "symbolAlpha"[tm[q]["false"][["next"]]], "pad"}, m], Join[{"symbolB"[tm[q]["false"][["next"]]], "pad"}, "repeated"[{"symbolBeta"[tm[q]["false"][["next"]]], "pad"}, n]]]]] == "some"[Prepend["symbolA"[tm[q]["false"][["next"]]]][Prepend["pad"][Join["pairs"["symbolAlpha"[tm[q]["false"][["next"]]], "pad", 2 * m + "bitValue"[tm[q]["false"][["write"]]]], Prepend["symbolB"[tm[q]["false"][["next"]]]][Prepend["pad"]["pairs"["symbolBeta"[tm[q]["false"][["next"]]], "pad", n]]]]]]]],
			"Rewrite"["repeatedPairTwice"["MinskySymbol", "symbolAlpha"[tm[q]["false"][["next"]]], "pad", m]],
			"Rewrite"["repeatedPair"["MinskySymbol", "symbolBeta"[tm[q]["false"][["next"]]], "pad", n]],
			"Rewrite"["pairsAdd"["MinskySymbol", "symbolAlpha"[tm[q]["false"][["next"]]], "pad", 2 * m, "bitValue"[tm[q]["false"][["write"]]]]],
			"Rewrite"["joinAssociativity"["pairs"["symbolAlpha"[tm[q]["false"][["next"]]], "pad", "bitValue"[tm[q]["false"][["write"]]]], "pairs"["symbolAlpha"[tm[q]["false"][["next"]]], "pad", 2 * m], Prepend["symbolB"[tm[q]["false"][["next"]]]][Prepend["pad"]["pairs"["symbolBeta"[tm[q]["false"][["next"]]], "pad", n]]]]],
			"Reflexivity",
			(* h true: even length *)
			"Introduce"[moved],
			"Change"["steps"["tagStep"["minskyProductions"[tm]], m + n + 2, Prepend["symbolE"[q, "true"]][Prepend["symbolE"[q, "false"]][Join["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]]]] == "some"[Prepend["symbolA"[tm[q]["true"][["next"]]]][Prepend["pad"][Join["pairs"["symbolAlpha"[tm[q]["true"][["next"]]], "pad", 2 * m + "bitValue"[tm[q]["true"][["write"]]]], Prepend["symbolB"[tm[q]["true"][["next"]]]][Prepend["pad"]["pairs"["symbolBeta"[tm[q]["true"][["next"]]], "pad", n]]]]]]]],
			"Have"[joined, Length[Join["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]] == Length["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m]] + Length[Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]], "Exact"["lengthJoin"["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]],
			"Have"[tail, Length[Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]] == Length["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]] + 2], "Reflexivity",
			"Have"[whole, Length[Prepend["symbolE"[q, "true"]][Prepend["symbolE"[q, "false"]][Join["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]]]] == Length[Join["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]] + 2], "Reflexivity",
			"Have"[length, Length[Prepend["symbolE"[q, "true"]][Prepend["symbolE"[q, "false"]][Join["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]]]] == 2 * (m + n + 2)], "LinearArithmetic",
			"Rewrite"["tagRoundEvenWhole"["MinskySymbol", "minskyProductions"[tm], m + n + 2, Prepend["symbolE"[q, "true"]][Prepend["symbolE"[q, "false"]][Join["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]]], length]],
			"Change"["some"[Join["minskyProductions"[tm]["symbolE"[q, "true"]], "passOutFrom"["minskyProductions"[tm], Join["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]], "true"]]] == "some"[Prepend["symbolA"[tm[q]["true"][["next"]]]][Prepend["pad"][Join["pairs"["symbolAlpha"[tm[q]["true"][["next"]]], "pad", 2 * m + "bitValue"[tm[q]["true"][["write"]]]], Prepend["symbolB"[tm[q]["true"][["next"]]]][Prepend["pad"]["pairs"["symbolBeta"[tm[q]["true"][["next"]]], "pad", n]]]]]]]],
			"Rewrite"["passOutAlignedPairs"["MinskySymbol", "minskyProductions"[tm], "symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m, Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]],
			"Change"["some"[Join["minskyProductions"[tm]["symbolE"[q, "true"]], Join["repeated"["minskyProductions"[tm]["symbolSmallE"[q, "true"]], m], Join["minskyProductions"[tm]["symbolF"[q, "true"]], "passOutFrom"["minskyProductions"[tm], "pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n], "true"]]]]] == "some"[Prepend["symbolA"[tm[q]["true"][["next"]]]][Prepend["pad"][Join["pairs"["symbolAlpha"[tm[q]["true"][["next"]]], "pad", 2 * m + "bitValue"[tm[q]["true"][["write"]]]], Prepend["symbolB"[tm[q]["true"][["next"]]]][Prepend["pad"]["pairs"["symbolBeta"[tm[q]["true"][["next"]]], "pad", n]]]]]]]],
			"Rewrite"["andEliminationLeft"["passOutPairs"["MinskySymbol", "minskyProductions"[tm], "symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]],
			"Rewrite"["productionERight"[tm, q, "true", moved]],
			"Rewrite"["productionSmallERight"[tm, q, "true", moved]],
			"Rewrite"["productionFRight"[tm, q, "true", moved]],
			"Rewrite"["productionSmallFRight"[tm, q, "true", moved]],
			"Change"["some"[Join[Prepend["symbolA"[tm[q]["true"][["next"]]]][Prepend["pad"]["pairs"["symbolAlpha"[tm[q]["true"][["next"]]], "pad", "bitValue"[tm[q]["true"][["write"]]]]]], Join["repeated"[{"symbolAlpha"[tm[q]["true"][["next"]]], "pad", "symbolAlpha"[tm[q]["true"][["next"]]], "pad"}, m], Join[{"symbolB"[tm[q]["true"][["next"]]], "pad"}, "repeated"[{"symbolBeta"[tm[q]["true"][["next"]]], "pad"}, n]]]]] == "some"[Prepend["symbolA"[tm[q]["true"][["next"]]]][Prepend["pad"][Join["pairs"["symbolAlpha"[tm[q]["true"][["next"]]], "pad", 2 * m + "bitValue"[tm[q]["true"][["write"]]]], Prepend["symbolB"[tm[q]["true"][["next"]]]][Prepend["pad"]["pairs"["symbolBeta"[tm[q]["true"][["next"]]], "pad", n]]]]]]]],
			"Rewrite"["repeatedPairTwice"["MinskySymbol", "symbolAlpha"[tm[q]["true"][["next"]]], "pad", m]],
			"Rewrite"["repeatedPair"["MinskySymbol", "symbolBeta"[tm[q]["true"][["next"]]], "pad", n]],
			"Rewrite"["pairsAdd"["MinskySymbol", "symbolAlpha"[tm[q]["true"][["next"]]], "pad", 2 * m, "bitValue"[tm[q]["true"][["write"]]]]],
			"Rewrite"["joinAssociativity"["pairs"["symbolAlpha"[tm[q]["true"][["next"]]], "pad", "bitValue"[tm[q]["true"][["write"]]]], "pairs"["symbolAlpha"[tm[q]["true"][["next"]]], "pad", 2 * m], Prepend["symbolB"[tm[q]["true"][["next"]]]][Prepend["pad"]["pairs"["symbolBeta"[tm[q]["true"][["next"]]], "pad", n]]]]],
			"Reflexivity"
		}
	],
	(* the word after round 3 of a move to the left: G (g)^m H H (k k)^(2 n), from which rounds 4 and 5 halve the left number *)
	TypeTheoryDefinition["afterRound3", Typed[
		Function[{Typed[q, NonNegativeIntegers], Typed[h, Booleans], Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]},
			Prepend["symbolG"[q, h]][Join["repeated"[{"symbolSmallG"[q, h]}, m], Prepend["symbolH"[q, h]][Prepend["symbolH"[q, h]]["pairs"["symbolK"[q, h], "symbolK"[q, h], 2 * n]]]]]],
		NonNegativeIntegers -> Booleans -> NonNegativeIntegers -> NonNegativeIntegers -> {"MinskySymbol"}
	]],
	machineTheorem["minskyRound3Left",
		ForAll[{Typed[tm, NonNegativeIntegers -> Booleans -> "MachineTransition"], Typed[q, NonNegativeIntegers], Typed[h, Booleans], Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]},
			Implies[tm[q][h][["direction"]] == "moveLeft",
				"steps"["tagStep"["minskyProductions"[tm]], m + n + 2, "afterRound2"[q, h, m, n]] == "some"["afterRound3"[q, h, m, n]]]],
		{
			"Introduce"[tm, q, h, m, n],
			"Have"[left, Length["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m]] == 2 * m], "Exact"["lengthPairs"["MinskySymbol", "symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m]],
			"Have"[right, Length["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]] == 2 * n], "Exact"["lengthPairs"["MinskySymbol", "symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]],
			"Cases"[h],
			(* h false: odd length, the pad that E0 writes first is the partner of the last f *)
			"Introduce"[moved],
			"Change"["steps"["tagStep"["minskyProductions"[tm]], m + n + 2, Prepend["symbolE"[q, "false"]][Join["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]]] == "some"[Prepend["symbolG"[q, "false"]][Join["repeated"[{"symbolSmallG"[q, "false"]}, m], Prepend["symbolH"[q, "false"]][Prepend["symbolH"[q, "false"]]["pairs"["symbolK"[q, "false"], "symbolK"[q, "false"], 2 * n]]]]]]],
			"Have"[joined, Length[Join["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]] == Length["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m]] + Length[Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]], "Exact"["lengthJoin"["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]],
			"Have"[tail, Length[Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]] == Length["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]] + 2], "Reflexivity",
			"Have"[length, Length[Join["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]] == 2 * (m + n) + 2], "LinearArithmetic",
			"Rewrite"["tagRoundOddHead"["MinskySymbol", "minskyProductions"[tm], m + n, "symbolE"[q, "false"], Join["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]], "pad", {"symbolG"[q, "false"]}, length, "productionELeft"[tm, q, "false", moved]]],
			"Rewrite"["passOutShiftedPairs"["MinskySymbol", "minskyProductions"[tm], "symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m, Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]],
			"Change"["some"[Join[{"symbolG"[q, "false"]}, Join["repeated"["minskyProductions"[tm]["symbolSmallE"[q, "false"]], m], Join["minskyProductions"[tm]["symbolF"[q, "false"]], "passOutFrom"["minskyProductions"[tm], "pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n], "false"]]]]] == "some"[Prepend["symbolG"[q, "false"]][Join["repeated"[{"symbolSmallG"[q, "false"]}, m], Prepend["symbolH"[q, "false"]][Prepend["symbolH"[q, "false"]]["pairs"["symbolK"[q, "false"], "symbolK"[q, "false"], 2 * n]]]]]]],
			"Rewrite"["andEliminationRight"["passOutPairs"["MinskySymbol", "minskyProductions"[tm], "symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]],
			"Rewrite"["productionSmallELeft"[tm, q, "false", moved]],
			"Rewrite"["productionFLeft"[tm, q, "false", moved]],
			"Rewrite"["productionSmallFLeft"[tm, q, "false", moved]],
			"Change"["some"[Join[{"symbolG"[q, "false"]}, Join["repeated"[{"symbolSmallG"[q, "false"]}, m], Join[{"symbolH"[q, "false"], "symbolH"[q, "false"]}, "repeated"[{"symbolK"[q, "false"], "symbolK"[q, "false"], "symbolK"[q, "false"], "symbolK"[q, "false"]}, n]]]]] == "some"[Prepend["symbolG"[q, "false"]][Join["repeated"[{"symbolSmallG"[q, "false"]}, m], Prepend["symbolH"[q, "false"]][Prepend["symbolH"[q, "false"]]["pairs"["symbolK"[q, "false"], "symbolK"[q, "false"], 2 * n]]]]]]],
			"Rewrite"["repeatedPairTwice"["MinskySymbol", "symbolK"[q, "false"], "symbolK"[q, "false"], n]],
			"Reflexivity",
			(* h true: even length *)
			"Introduce"[moved],
			"Change"["steps"["tagStep"["minskyProductions"[tm]], m + n + 2, Prepend["symbolE"[q, "true"]][Prepend["symbolE"[q, "false"]][Join["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]]]] == "some"[Prepend["symbolG"[q, "true"]][Join["repeated"[{"symbolSmallG"[q, "true"]}, m], Prepend["symbolH"[q, "true"]][Prepend["symbolH"[q, "true"]]["pairs"["symbolK"[q, "true"], "symbolK"[q, "true"], 2 * n]]]]]]],
			"Have"[joined, Length[Join["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]] == Length["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m]] + Length[Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]], "Exact"["lengthJoin"["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]],
			"Have"[tail, Length[Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]] == Length["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]] + 2], "Reflexivity",
			"Have"[whole, Length[Prepend["symbolE"[q, "true"]][Prepend["symbolE"[q, "false"]][Join["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]]]] == Length[Join["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]] + 2], "Reflexivity",
			"Have"[length, Length[Prepend["symbolE"[q, "true"]][Prepend["symbolE"[q, "false"]][Join["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]]]] == 2 * (m + n + 2)], "LinearArithmetic",
			"Rewrite"["tagRoundEvenWhole"["MinskySymbol", "minskyProductions"[tm], m + n + 2, Prepend["symbolE"[q, "true"]][Prepend["symbolE"[q, "false"]][Join["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]]], length]],
			"Change"["some"[Join["minskyProductions"[tm]["symbolE"[q, "true"]], "passOutFrom"["minskyProductions"[tm], Join["pairs"["symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m], Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]], "true"]]] == "some"[Prepend["symbolG"[q, "true"]][Join["repeated"[{"symbolSmallG"[q, "true"]}, m], Prepend["symbolH"[q, "true"]][Prepend["symbolH"[q, "true"]]["pairs"["symbolK"[q, "true"], "symbolK"[q, "true"], 2 * n]]]]]]],
			"Rewrite"["passOutAlignedPairs"["MinskySymbol", "minskyProductions"[tm], "symbolSmallE"[q, "true"], "symbolSmallE"[q, "false"], m, Prepend["symbolF"[q, "true"]][Prepend["symbolF"[q, "false"]]["pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]]]],
			"Change"["some"[Join["minskyProductions"[tm]["symbolE"[q, "true"]], Join["repeated"["minskyProductions"[tm]["symbolSmallE"[q, "true"]], m], Join["minskyProductions"[tm]["symbolF"[q, "true"]], "passOutFrom"["minskyProductions"[tm], "pairs"["symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n], "true"]]]]] == "some"[Prepend["symbolG"[q, "true"]][Join["repeated"[{"symbolSmallG"[q, "true"]}, m], Prepend["symbolH"[q, "true"]][Prepend["symbolH"[q, "true"]]["pairs"["symbolK"[q, "true"], "symbolK"[q, "true"], 2 * n]]]]]]],
			"Rewrite"["andEliminationLeft"["passOutPairs"["MinskySymbol", "minskyProductions"[tm], "symbolSmallF"[q, "true"], "symbolSmallF"[q, "false"], n]]],
			"Rewrite"["productionELeft"[tm, q, "true", moved]],
			"Rewrite"["productionSmallELeft"[tm, q, "true", moved]],
			"Rewrite"["productionFLeft"[tm, q, "true", moved]],
			"Rewrite"["productionSmallFLeft"[tm, q, "true", moved]],
			"Change"["some"[Join[{"symbolG"[q, "true"]}, Join["repeated"[{"symbolSmallG"[q, "true"]}, m], Join[{"symbolH"[q, "true"], "symbolH"[q, "true"]}, "repeated"[{"symbolK"[q, "true"], "symbolK"[q, "true"], "symbolK"[q, "true"], "symbolK"[q, "true"]}, n]]]]] == "some"[Prepend["symbolG"[q, "true"]][Join["repeated"[{"symbolSmallG"[q, "true"]}, m], Prepend["symbolH"[q, "true"]][Prepend["symbolH"[q, "true"]]["pairs"["symbolK"[q, "true"], "symbolK"[q, "true"], 2 * n]]]]]]],
			"Rewrite"["repeatedPairTwice"["MinskySymbol", "symbolK"[q, "true"], "symbolK"[q, "true"], n]],
			"Reflexivity"
		}
	],
	(* the word after round 4, and rounds 4 and 5 of a move to the left *)
	TypeTheoryDefinition["afterRound4", Typed[
		Function[{Typed[q, NonNegativeIntegers], Typed[h, Booleans], Typed[b, Booleans], Typed[i, NonNegativeIntegers], Typed[n, NonNegativeIntegers]},
			Join[InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, {"MinskySymbol"}], Typed[{}, {"MinskySymbol"}], {"symbolI"[q, h, "true"]}, b], Prepend["symbolI"[q, h, "false"]][Join["pairs"["symbolSmallI"[q, h, "true"], "symbolSmallI"[q, h, "false"], i], Prepend["symbolJ"[q, h, "true"]][Prepend["symbolJ"[q, h, "false"]]["pairs"["symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n]]]]]]],
		NonNegativeIntegers -> Booleans -> Booleans -> NonNegativeIntegers -> NonNegativeIntegers -> {"MinskySymbol"}
	]],
	(* round 4 reads G, every other g and every other k: the left number 2 i + b loses its lowest bit b, which decides
	   whether the round has odd length and I1 its partner *)
	machineTheorem["minskyRound4",
		ForAll[{Typed[tm, NonNegativeIntegers -> Booleans -> "MachineTransition"], Typed[q, NonNegativeIntegers], Typed[h, Booleans], Typed[b, Booleans], Typed[i, NonNegativeIntegers], Typed[n, NonNegativeIntegers]},
			"steps"["tagStep"["minskyProductions"[tm]], i + 2 * n + 2, "afterRound3"[q, h, 2 * i + "bitValue"[b], n]] == "some"["afterRound4"[q, h, b, i, n]]],
		{
			"Introduce"[tm, q, h, b, i, n],
			"Have"[left, Length["pairs"["symbolSmallG"[q, h], "symbolSmallG"[q, h], i]] == 2 * i], "Exact"["lengthPairs"["MinskySymbol", "symbolSmallG"[q, h], "symbolSmallG"[q, h], i]],
			"Have"[right, Length["pairs"["symbolK"[q, h], "symbolK"[q, h], 2 * n]] == 2 * (2 * n)], "Exact"["lengthPairs"["MinskySymbol", "symbolK"[q, h], "symbolK"[q, h], 2 * n]],
			"Have"[joined, Length[Join["pairs"["symbolSmallG"[q, h], "symbolSmallG"[q, h], i], Prepend["symbolH"[q, h]][Prepend["symbolH"[q, h]]["pairs"["symbolK"[q, h], "symbolK"[q, h], 2 * n]]]]] == Length["pairs"["symbolSmallG"[q, h], "symbolSmallG"[q, h], i]] + Length[Prepend["symbolH"[q, h]][Prepend["symbolH"[q, h]]["pairs"["symbolK"[q, h], "symbolK"[q, h], 2 * n]]]]], "Exact"["lengthJoin"["pairs"["symbolSmallG"[q, h], "symbolSmallG"[q, h], i], Prepend["symbolH"[q, h]][Prepend["symbolH"[q, h]]["pairs"["symbolK"[q, h], "symbolK"[q, h], 2 * n]]]]],
			"Have"[tail, Length[Prepend["symbolH"[q, h]][Prepend["symbolH"[q, h]]["pairs"["symbolK"[q, h], "symbolK"[q, h], 2 * n]]]] == Length["pairs"["symbolK"[q, h], "symbolK"[q, h], 2 * n]] + 2], "Reflexivity",
			"Cases"[b],
			(* b false: odd length *)
			"Change"["steps"["tagStep"["minskyProductions"[tm]], i + 2 * n + 2, Prepend["symbolG"[q, h]][Join["repeated"[{"symbolSmallG"[q, h]}, 2 * i], Prepend["symbolH"[q, h]][Prepend["symbolH"[q, h]]["pairs"["symbolK"[q, h], "symbolK"[q, h], 2 * n]]]]]] == "some"[Prepend["symbolI"[q, h, "false"]][Join["pairs"["symbolSmallI"[q, h, "true"], "symbolSmallI"[q, h, "false"], i], Prepend["symbolJ"[q, h, "true"]][Prepend["symbolJ"[q, h, "false"]]["pairs"["symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n]]]]]]],
			"Rewrite"["repeatedDouble"["MinskySymbol", "symbolSmallG"[q, h], i]],
			"Have"[length, Length[Join["pairs"["symbolSmallG"[q, h], "symbolSmallG"[q, h], i], Prepend["symbolH"[q, h]][Prepend["symbolH"[q, h]]["pairs"["symbolK"[q, h], "symbolK"[q, h], 2 * n]]]]] == 2 * (i + 2 * n) + 2], "LinearArithmetic",
			"Rewrite"["tagRoundOddHead"["MinskySymbol", "minskyProductions"[tm], i + 2 * n, "symbolG"[q, h], Join["pairs"["symbolSmallG"[q, h], "symbolSmallG"[q, h], i], Prepend["symbolH"[q, h]][Prepend["symbolH"[q, h]]["pairs"["symbolK"[q, h], "symbolK"[q, h], 2 * n]]]], "symbolI"[q, h, "true"], {"symbolI"[q, h, "false"]}, length, "equalityReflexivity"[{"symbolI"[q, h, "true"], "symbolI"[q, h, "false"]}]]],
			"Rewrite"["passOutShiftedPairs"["MinskySymbol", "minskyProductions"[tm], "symbolSmallG"[q, h], "symbolSmallG"[q, h], i, Prepend["symbolH"[q, h]][Prepend["symbolH"[q, h]]["pairs"["symbolK"[q, h], "symbolK"[q, h], 2 * n]]]]],
			"Change"["some"[Join[{"symbolI"[q, h, "false"]}, Join["repeated"[{"symbolSmallI"[q, h, "true"], "symbolSmallI"[q, h, "false"]}, i], Prepend["symbolJ"[q, h, "true"]][Prepend["symbolJ"[q, h, "false"]]["passOutFrom"["minskyProductions"[tm], "pairs"["symbolK"[q, h], "symbolK"[q, h], 2 * n], "false"]]]]]] == "some"[Prepend["symbolI"[q, h, "false"]][Join["pairs"["symbolSmallI"[q, h, "true"], "symbolSmallI"[q, h, "false"], i], Prepend["symbolJ"[q, h, "true"]][Prepend["symbolJ"[q, h, "false"]]["pairs"["symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n]]]]]]],
			"Rewrite"["andEliminationRight"["passOutPairs"["MinskySymbol", "minskyProductions"[tm], "symbolK"[q, h], "symbolK"[q, h], 2 * n]]],
			"Change"["some"[Join[{"symbolI"[q, h, "false"]}, Join["repeated"[{"symbolSmallI"[q, h, "true"], "symbolSmallI"[q, h, "false"]}, i], Prepend["symbolJ"[q, h, "true"]][Prepend["symbolJ"[q, h, "false"]]["repeated"[{"symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"]}, 2 * n]]]]]] == "some"[Prepend["symbolI"[q, h, "false"]][Join["pairs"["symbolSmallI"[q, h, "true"], "symbolSmallI"[q, h, "false"], i], Prepend["symbolJ"[q, h, "true"]][Prepend["symbolJ"[q, h, "false"]]["pairs"["symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n]]]]]]],
			"Rewrite"["repeatedPair"["MinskySymbol", "symbolSmallI"[q, h, "true"], "symbolSmallI"[q, h, "false"], i]],
			"Rewrite"["repeatedPair"["MinskySymbol", "symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n]],
			"Reflexivity",
			(* b true: even length *)
			"Change"["steps"["tagStep"["minskyProductions"[tm]], i + 2 * n + 2, Prepend["symbolG"[q, h]][Prepend["symbolSmallG"[q, h]][Join["repeated"[{"symbolSmallG"[q, h]}, 2 * i], Prepend["symbolH"[q, h]][Prepend["symbolH"[q, h]]["pairs"["symbolK"[q, h], "symbolK"[q, h], 2 * n]]]]]]] == "some"[Prepend["symbolI"[q, h, "true"]][Prepend["symbolI"[q, h, "false"]][Join["pairs"["symbolSmallI"[q, h, "true"], "symbolSmallI"[q, h, "false"], i], Prepend["symbolJ"[q, h, "true"]][Prepend["symbolJ"[q, h, "false"]]["pairs"["symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n]]]]]]]],
			"Rewrite"["repeatedDouble"["MinskySymbol", "symbolSmallG"[q, h], i]],
			"Have"[whole, Length[Prepend["symbolG"[q, h]][Prepend["symbolSmallG"[q, h]][Join["pairs"["symbolSmallG"[q, h], "symbolSmallG"[q, h], i], Prepend["symbolH"[q, h]][Prepend["symbolH"[q, h]]["pairs"["symbolK"[q, h], "symbolK"[q, h], 2 * n]]]]]]] == Length[Join["pairs"["symbolSmallG"[q, h], "symbolSmallG"[q, h], i], Prepend["symbolH"[q, h]][Prepend["symbolH"[q, h]]["pairs"["symbolK"[q, h], "symbolK"[q, h], 2 * n]]]]] + 2], "Reflexivity",
			"Have"[length, Length[Prepend["symbolG"[q, h]][Prepend["symbolSmallG"[q, h]][Join["pairs"["symbolSmallG"[q, h], "symbolSmallG"[q, h], i], Prepend["symbolH"[q, h]][Prepend["symbolH"[q, h]]["pairs"["symbolK"[q, h], "symbolK"[q, h], 2 * n]]]]]]] == 2 * (i + 2 * n + 2)], "LinearArithmetic",
			"Rewrite"["tagRoundEvenWhole"["MinskySymbol", "minskyProductions"[tm], i + 2 * n + 2, Prepend["symbolG"[q, h]][Prepend["symbolSmallG"[q, h]][Join["pairs"["symbolSmallG"[q, h], "symbolSmallG"[q, h], i], Prepend["symbolH"[q, h]][Prepend["symbolH"[q, h]]["pairs"["symbolK"[q, h], "symbolK"[q, h], 2 * n]]]]]], length]],
			"Change"["some"[Join[{"symbolI"[q, h, "true"], "symbolI"[q, h, "false"]}, "passOutFrom"["minskyProductions"[tm], Join["pairs"["symbolSmallG"[q, h], "symbolSmallG"[q, h], i], Prepend["symbolH"[q, h]][Prepend["symbolH"[q, h]]["pairs"["symbolK"[q, h], "symbolK"[q, h], 2 * n]]]], "true"]]] == "some"[Prepend["symbolI"[q, h, "true"]][Prepend["symbolI"[q, h, "false"]][Join["pairs"["symbolSmallI"[q, h, "true"], "symbolSmallI"[q, h, "false"], i], Prepend["symbolJ"[q, h, "true"]][Prepend["symbolJ"[q, h, "false"]]["pairs"["symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n]]]]]]]],
			"Rewrite"["passOutAlignedPairs"["MinskySymbol", "minskyProductions"[tm], "symbolSmallG"[q, h], "symbolSmallG"[q, h], i, Prepend["symbolH"[q, h]][Prepend["symbolH"[q, h]]["pairs"["symbolK"[q, h], "symbolK"[q, h], 2 * n]]]]],
			"Change"["some"[Join[{"symbolI"[q, h, "true"], "symbolI"[q, h, "false"]}, Join["repeated"[{"symbolSmallI"[q, h, "true"], "symbolSmallI"[q, h, "false"]}, i], Prepend["symbolJ"[q, h, "true"]][Prepend["symbolJ"[q, h, "false"]]["passOutFrom"["minskyProductions"[tm], "pairs"["symbolK"[q, h], "symbolK"[q, h], 2 * n], "true"]]]]]] == "some"[Prepend["symbolI"[q, h, "true"]][Prepend["symbolI"[q, h, "false"]][Join["pairs"["symbolSmallI"[q, h, "true"], "symbolSmallI"[q, h, "false"], i], Prepend["symbolJ"[q, h, "true"]][Prepend["symbolJ"[q, h, "false"]]["pairs"["symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n]]]]]]]],
			"Rewrite"["andEliminationLeft"["passOutPairs"["MinskySymbol", "minskyProductions"[tm], "symbolK"[q, h], "symbolK"[q, h], 2 * n]]],
			"Change"["some"[Join[{"symbolI"[q, h, "true"], "symbolI"[q, h, "false"]}, Join["repeated"[{"symbolSmallI"[q, h, "true"], "symbolSmallI"[q, h, "false"]}, i], Prepend["symbolJ"[q, h, "true"]][Prepend["symbolJ"[q, h, "false"]]["repeated"[{"symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"]}, 2 * n]]]]]] == "some"[Prepend["symbolI"[q, h, "true"]][Prepend["symbolI"[q, h, "false"]][Join["pairs"["symbolSmallI"[q, h, "true"], "symbolSmallI"[q, h, "false"], i], Prepend["symbolJ"[q, h, "true"]][Prepend["symbolJ"[q, h, "false"]]["pairs"["symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n]]]]]]]],
			"Rewrite"["repeatedPair"["MinskySymbol", "symbolSmallI"[q, h, "true"], "symbolSmallI"[q, h, "false"], i]],
			"Rewrite"["repeatedPair"["MinskySymbol", "symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n]],
			"Reflexivity"
		}
	],

	(* round 5 reads I, every other i, J and every other j: the next configuration's word, the left number halved and the
	   written bit and the left number's lowest bit joining the right number *)
	machineTheorem["minskyRound5",
		ForAll[{Typed[tm, NonNegativeIntegers -> Booleans -> "MachineTransition"], Typed[q, NonNegativeIntegers], Typed[h, Booleans], Typed[b, Booleans], Typed[i, NonNegativeIntegers], Typed[n, NonNegativeIntegers]},
			"steps"["tagStep"["minskyProductions"[tm]], i + 2 * n + 2, "afterRound4"[q, h, b, i, n]] == "some"["minskyWord"[tm[q][h][["next"]], i, 2 * (2 * n + "bitValue"[tm[q][h][["write"]]]) + "bitValue"[b]]]],
		{
			"Introduce"[tm, q, h, b, i, n],
			"Have"[left, Length["pairs"["symbolSmallI"[q, h, "true"], "symbolSmallI"[q, h, "false"], i]] == 2 * i], "Exact"["lengthPairs"["MinskySymbol", "symbolSmallI"[q, h, "true"], "symbolSmallI"[q, h, "false"], i]],
			"Have"[right, Length["pairs"["symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n]] == 2 * (2 * n)], "Exact"["lengthPairs"["MinskySymbol", "symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n]],
			"Have"[joined, Length[Join["pairs"["symbolSmallI"[q, h, "true"], "symbolSmallI"[q, h, "false"], i], Prepend["symbolJ"[q, h, "true"]][Prepend["symbolJ"[q, h, "false"]]["pairs"["symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n]]]]] == Length["pairs"["symbolSmallI"[q, h, "true"], "symbolSmallI"[q, h, "false"], i]] + Length[Prepend["symbolJ"[q, h, "true"]][Prepend["symbolJ"[q, h, "false"]]["pairs"["symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n]]]]], "Exact"["lengthJoin"["pairs"["symbolSmallI"[q, h, "true"], "symbolSmallI"[q, h, "false"], i], Prepend["symbolJ"[q, h, "true"]][Prepend["symbolJ"[q, h, "false"]]["pairs"["symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n]]]]],
			"Have"[tail, Length[Prepend["symbolJ"[q, h, "true"]][Prepend["symbolJ"[q, h, "false"]]["pairs"["symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n]]]] == Length["pairs"["symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n]] + 2], "Reflexivity",
			"Cases"[b],
			(* b false: odd length, the pad that I0 writes first is the partner of the last j *)
			"Change"["steps"["tagStep"["minskyProductions"[tm]], i + 2 * n + 2, Prepend["symbolI"[q, h, "false"]][Join["pairs"["symbolSmallI"[q, h, "true"], "symbolSmallI"[q, h, "false"], i], Prepend["symbolJ"[q, h, "true"]][Prepend["symbolJ"[q, h, "false"]]["pairs"["symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n]]]]]] == "some"[Prepend["symbolA"[tm[q][h][["next"]]]][Prepend["pad"][Join["pairs"["symbolAlpha"[tm[q][h][["next"]]], "pad", i], Prepend["symbolB"[tm[q][h][["next"]]]][Prepend["pad"]["pairs"["symbolBeta"[tm[q][h][["next"]]], "pad", 2 * (2 * n + "bitValue"[tm[q][h][["write"]]]) + 0]]]]]]]],
			"Have"[length, Length[Join["pairs"["symbolSmallI"[q, h, "true"], "symbolSmallI"[q, h, "false"], i], Prepend["symbolJ"[q, h, "true"]][Prepend["symbolJ"[q, h, "false"]]["pairs"["symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n]]]]] == 2 * (i + 2 * n) + 2], "LinearArithmetic",
			"Rewrite"["tagRoundOddHead"["MinskySymbol", "minskyProductions"[tm], i + 2 * n, "symbolI"[q, h, "false"], Join["pairs"["symbolSmallI"[q, h, "true"], "symbolSmallI"[q, h, "false"], i], Prepend["symbolJ"[q, h, "true"]][Prepend["symbolJ"[q, h, "false"]]["pairs"["symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n]]]], "pad", {"symbolA"[tm[q][h][["next"]]], "pad"}, length, "equalityReflexivity"[{"pad", "symbolA"[tm[q][h][["next"]]], "pad"}]]],
			"Rewrite"["passOutShiftedPairs"["MinskySymbol", "minskyProductions"[tm], "symbolSmallI"[q, h, "true"], "symbolSmallI"[q, h, "false"], i, Prepend["symbolJ"[q, h, "true"]][Prepend["symbolJ"[q, h, "false"]]["pairs"["symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n]]]]],
			"Change"["some"[Join[{"symbolA"[tm[q][h][["next"]]], "pad"}, Join["repeated"[{"symbolAlpha"[tm[q][h][["next"]]], "pad"}, i], Join["minskyProductions"[tm]["symbolJ"[q, h, "false"]], "passOutFrom"["minskyProductions"[tm], "pairs"["symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n], "false"]]]]] == "some"[Prepend["symbolA"[tm[q][h][["next"]]]][Prepend["pad"][Join["pairs"["symbolAlpha"[tm[q][h][["next"]]], "pad", i], Prepend["symbolB"[tm[q][h][["next"]]]][Prepend["pad"]["pairs"["symbolBeta"[tm[q][h][["next"]]], "pad", 2 * (2 * n + "bitValue"[tm[q][h][["write"]]]) + 0]]]]]]]],
			"Rewrite"["andEliminationRight"["passOutPairs"["MinskySymbol", "minskyProductions"[tm], "symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n]]],
			"Change"["some"[Join[{"symbolA"[tm[q][h][["next"]]], "pad"}, Join["repeated"[{"symbolAlpha"[tm[q][h][["next"]]], "pad"}, i], Join[Prepend["symbolB"[tm[q][h][["next"]]]][Prepend["pad"]["pairs"["symbolBeta"[tm[q][h][["next"]]], "pad", 2 * "bitValue"[tm[q][h][["write"]]] + 0]]], "repeated"[{"symbolBeta"[tm[q][h][["next"]]], "pad", "symbolBeta"[tm[q][h][["next"]]], "pad"}, 2 * n]]]]] == "some"[Prepend["symbolA"[tm[q][h][["next"]]]][Prepend["pad"][Join["pairs"["symbolAlpha"[tm[q][h][["next"]]], "pad", i], Prepend["symbolB"[tm[q][h][["next"]]]][Prepend["pad"]["pairs"["symbolBeta"[tm[q][h][["next"]]], "pad", 2 * (2 * n + "bitValue"[tm[q][h][["write"]]]) + 0]]]]]]]],
			"Rewrite"["repeatedPair"["MinskySymbol", "symbolAlpha"[tm[q][h][["next"]]], "pad", i]],
			"Rewrite"["repeatedPairTwice"["MinskySymbol", "symbolBeta"[tm[q][h][["next"]]], "pad", 2 * n]],
			"Have"[count, 2 * (2 * n + "bitValue"[tm[q][h][["write"]]]) + 0 == 2 * (2 * n) + (2 * "bitValue"[tm[q][h][["write"]]] + 0)], "LinearArithmetic",
			"Rewrite"[count],
			"Rewrite"["pairsAdd"["MinskySymbol", "symbolBeta"[tm[q][h][["next"]]], "pad", 2 * (2 * n), 2 * "bitValue"[tm[q][h][["write"]]] + 0]],
			"Reflexivity",
			(* b true: even length *)
			"Change"["steps"["tagStep"["minskyProductions"[tm]], i + 2 * n + 2, Prepend["symbolI"[q, h, "true"]][Prepend["symbolI"[q, h, "false"]][Join["pairs"["symbolSmallI"[q, h, "true"], "symbolSmallI"[q, h, "false"], i], Prepend["symbolJ"[q, h, "true"]][Prepend["symbolJ"[q, h, "false"]]["pairs"["symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n]]]]]]] == "some"[Prepend["symbolA"[tm[q][h][["next"]]]][Prepend["pad"][Join["pairs"["symbolAlpha"[tm[q][h][["next"]]], "pad", i], Prepend["symbolB"[tm[q][h][["next"]]]][Prepend["pad"]["pairs"["symbolBeta"[tm[q][h][["next"]]], "pad", 2 * (2 * n + "bitValue"[tm[q][h][["write"]]]) + 1]]]]]]]],
			"Have"[whole, Length[Prepend["symbolI"[q, h, "true"]][Prepend["symbolI"[q, h, "false"]][Join["pairs"["symbolSmallI"[q, h, "true"], "symbolSmallI"[q, h, "false"], i], Prepend["symbolJ"[q, h, "true"]][Prepend["symbolJ"[q, h, "false"]]["pairs"["symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n]]]]]]] == Length[Join["pairs"["symbolSmallI"[q, h, "true"], "symbolSmallI"[q, h, "false"], i], Prepend["symbolJ"[q, h, "true"]][Prepend["symbolJ"[q, h, "false"]]["pairs"["symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n]]]]] + 2], "Reflexivity",
			"Have"[length, Length[Prepend["symbolI"[q, h, "true"]][Prepend["symbolI"[q, h, "false"]][Join["pairs"["symbolSmallI"[q, h, "true"], "symbolSmallI"[q, h, "false"], i], Prepend["symbolJ"[q, h, "true"]][Prepend["symbolJ"[q, h, "false"]]["pairs"["symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n]]]]]]] == 2 * (i + 2 * n + 2)], "LinearArithmetic",
			"Rewrite"["tagRoundEvenWhole"["MinskySymbol", "minskyProductions"[tm], i + 2 * n + 2, Prepend["symbolI"[q, h, "true"]][Prepend["symbolI"[q, h, "false"]][Join["pairs"["symbolSmallI"[q, h, "true"], "symbolSmallI"[q, h, "false"], i], Prepend["symbolJ"[q, h, "true"]][Prepend["symbolJ"[q, h, "false"]]["pairs"["symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n]]]]]], length]],
			"Change"["some"[Join[{"symbolA"[tm[q][h][["next"]]], "pad"}, "passOutFrom"["minskyProductions"[tm], Join["pairs"["symbolSmallI"[q, h, "true"], "symbolSmallI"[q, h, "false"], i], Prepend["symbolJ"[q, h, "true"]][Prepend["symbolJ"[q, h, "false"]]["pairs"["symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n]]]], "true"]]] == "some"[Prepend["symbolA"[tm[q][h][["next"]]]][Prepend["pad"][Join["pairs"["symbolAlpha"[tm[q][h][["next"]]], "pad", i], Prepend["symbolB"[tm[q][h][["next"]]]][Prepend["pad"]["pairs"["symbolBeta"[tm[q][h][["next"]]], "pad", 2 * (2 * n + "bitValue"[tm[q][h][["write"]]]) + 1]]]]]]]],
			"Rewrite"["passOutAlignedPairs"["MinskySymbol", "minskyProductions"[tm], "symbolSmallI"[q, h, "true"], "symbolSmallI"[q, h, "false"], i, Prepend["symbolJ"[q, h, "true"]][Prepend["symbolJ"[q, h, "false"]]["pairs"["symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n]]]]],
			"Change"["some"[Join[{"symbolA"[tm[q][h][["next"]]], "pad"}, Join["repeated"[{"symbolAlpha"[tm[q][h][["next"]]], "pad"}, i], Join["minskyProductions"[tm]["symbolJ"[q, h, "true"]], "passOutFrom"["minskyProductions"[tm], "pairs"["symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n], "true"]]]]] == "some"[Prepend["symbolA"[tm[q][h][["next"]]]][Prepend["pad"][Join["pairs"["symbolAlpha"[tm[q][h][["next"]]], "pad", i], Prepend["symbolB"[tm[q][h][["next"]]]][Prepend["pad"]["pairs"["symbolBeta"[tm[q][h][["next"]]], "pad", 2 * (2 * n + "bitValue"[tm[q][h][["write"]]]) + 1]]]]]]]],
			"Rewrite"["andEliminationLeft"["passOutPairs"["MinskySymbol", "minskyProductions"[tm], "symbolSmallJ"[q, h, "true"], "symbolSmallJ"[q, h, "false"], 2 * n]]],
			"Change"["some"[Join[{"symbolA"[tm[q][h][["next"]]], "pad"}, Join["repeated"[{"symbolAlpha"[tm[q][h][["next"]]], "pad"}, i], Join[Prepend["symbolB"[tm[q][h][["next"]]]][Prepend["pad"]["pairs"["symbolBeta"[tm[q][h][["next"]]], "pad", 2 * "bitValue"[tm[q][h][["write"]]] + 1]]], "repeated"[{"symbolBeta"[tm[q][h][["next"]]], "pad", "symbolBeta"[tm[q][h][["next"]]], "pad"}, 2 * n]]]]] == "some"[Prepend["symbolA"[tm[q][h][["next"]]]][Prepend["pad"][Join["pairs"["symbolAlpha"[tm[q][h][["next"]]], "pad", i], Prepend["symbolB"[tm[q][h][["next"]]]][Prepend["pad"]["pairs"["symbolBeta"[tm[q][h][["next"]]], "pad", 2 * (2 * n + "bitValue"[tm[q][h][["write"]]]) + 1]]]]]]]],
			"Rewrite"["repeatedPair"["MinskySymbol", "symbolAlpha"[tm[q][h][["next"]]], "pad", i]],
			"Rewrite"["repeatedPairTwice"["MinskySymbol", "symbolBeta"[tm[q][h][["next"]]], "pad", 2 * n]],
			"Have"[count, 2 * (2 * n + "bitValue"[tm[q][h][["write"]]]) + 1 == 2 * (2 * n) + (2 * "bitValue"[tm[q][h][["write"]]] + 1)], "LinearArithmetic",
			"Rewrite"[count],
			"Rewrite"["pairsAdd"["MinskySymbol", "symbolBeta"[tm[q][h][["next"]]], "pad", 2 * (2 * n), 2 * "bitValue"[tm[q][h][["write"]]] + 1]],
			"Reflexivity"
		}
	],
	(* the binary machine: its step, the tape halves as numbers, nearest cell least significant, and the word of a
	   configuration; then one step of the machine is three or five rounds of the tag system *)
	TypeTheoryDefinition["tapeFirst", Typed[
		Function[{Typed[l, {Booleans}]}, InductiveRecursor[List][Function[{Typed[t, {Booleans}]}, Booleans], "false", Function[{Typed[a, Booleans], Typed[rest, {Booleans}], Typed[previous, Booleans]}, a], l]],
		{Booleans} -> Booleans
	]],
	TypeTheoryDefinition["tapeRest", Typed[
		Function[{Typed[l, {Booleans}]}, InductiveRecursor[List][Function[{Typed[t, {Booleans}]}, {Booleans}], Typed[{}, {Booleans}], Function[{Typed[a, Booleans], Typed[rest, {Booleans}], Typed[previous, {Booleans}]}, rest], l]],
		{Booleans} -> {Booleans}
	]],
	TypeTheoryDefinition["tapeValue", Typed[
		Function[{Typed[l, {Booleans}]}, InductiveRecursor[List][Function[{Typed[t, {Booleans}]}, NonNegativeIntegers], 0,
			Function[{Typed[a, Booleans], Typed[rest, {Booleans}], Typed[previous, NonNegativeIntegers]}, 2 * previous + "bitValue"[a]], l]],
		{Booleans} -> NonNegativeIntegers
	]],
	(* in state q reading the head, the machine writes, moves and changes state; state 0 halts *)
	TypeTheoryDefinition["binaryStep", Typed[
		Function[{Typed[tm, (NonNegativeIntegers -> Booleans -> "MachineTransition")], Typed[c, "BinaryConfiguration"]}, InductiveRecursor["BinaryConfiguration"][Function[{Typed[x, "BinaryConfiguration"]}, Option["BinaryConfiguration"]],
			Function[{Typed[q, NonNegativeIntegers], Typed[left, {Booleans}], Typed[head, Booleans], Typed[right, {Booleans}]},
				InductiveRecursor[NonNegativeIntegers][Function[{Typed[x, NonNegativeIntegers]}, Option["BinaryConfiguration"]], Typed["none", Option["BinaryConfiguration"]],
					Function[{Typed[j, NonNegativeIntegers], Typed[previous, Option["BinaryConfiguration"]]},
						"some"[Function[{Typed[t, "MachineTransition"]}, "byDirection"[t[["direction"]], "binaryConfiguration"[t[["next"]], "tapeRest"[left], "tapeFirst"[left], Prepend[t[["write"]]][right]], "binaryConfiguration"[t[["next"]], Prepend[t[["write"]]][left], "tapeFirst"[right], "tapeRest"[right]]]][tm[q][head]]]],
					q]],
			c]],
		(NonNegativeIntegers -> Booleans -> "MachineTransition") -> "BinaryConfiguration" -> Option["BinaryConfiguration"]
	]],
	TypeTheoryDefinition["binaryWord", Typed[
		Function[{Typed[c, "BinaryConfiguration"]}, InductiveRecursor["BinaryConfiguration"][Function[{Typed[x, "BinaryConfiguration"]}, {"MinskySymbol"}],
			Function[{Typed[q, NonNegativeIntegers], Typed[left, {Booleans}], Typed[head, Booleans], Typed[right, {Booleans}]},
				"minskyWord"[q, "tapeValue"[left], 2 * "tapeValue"[right] + "bitValue"[head]]],
			c]],
		"BinaryConfiguration" -> {"MinskySymbol"}
	]],
	machineTheorem["tapeSplit",
		ForAll[{Typed[l, {Booleans}]}, "tapeValue"[l] == 2 * "tapeValue"["tapeRest"[l]] + "bitValue"["tapeFirst"[l]]],
		{"Introduce"[l], "Cases"[l], "Reflexivity", "Introduce"[a, rest], "Reflexivity"}
	],
	machineTheorem["directionCases",
		ForAll[{Typed[d, "Direction"]}, Or[d == "moveLeft", d == "moveRight"]],
		{
			"Introduce"[d], "Cases"[d],
			"Exact"["orIntroductionLeft"["equalityReflexivity"["moveLeft"]]],
			"Exact"["orIntroductionRight"["equalityReflexivity"["moveRight"]]]
		}
	],
	(* a run of a steps, then a run of b steps, is a run of a + b steps *)
	machineTheorem["stepsThen",
		ForAll[{Typed[S, TypeUniverse[1]], Typed[step, S -> Option[S]], Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[x, S], Typed[y, S], Typed[z, S]},
			Implies["steps"[step, a, x] == "some"[y], Implies["steps"[step, b, y] == "some"[z], "steps"[step, a + b, x] == "some"[z]]]],
		{
			"Introduce"[S, step, a, b, x, y, z, first, second],
			"Rewrite"["stepsAdd"[S, step, a, b, x]],
			"Rewrite"[first],
			"Exact"[second]
		}
	],
	(* one step of the machine is three rounds of the tag system for a move to the right, five for a move to the left *)
	machineTheorem["minskyStep",
		ForAll[{Typed[tm, (NonNegativeIntegers -> Booleans -> "MachineTransition")], Typed[c, "BinaryConfiguration"], Typed[c2, "BinaryConfiguration"]},
			Implies["binaryStep"[tm, c] == "some"[c2],
				Exists[{Typed[s, NonNegativeIntegers]}, And[1 <= s, "steps"["tagStep"["minskyProductions"[tm]], s, "binaryWord"[c]] == "some"["binaryWord"[c2]]]]]],
		{
			"Introduce"[tm, c], "Cases"[c], "Introduce"[q, left, head, right, c2, stepped], "Cases"[q],
			(* state 0 halts *)
			"Introduce"[stepped], "Exact"["falseElimination"["noneNotSome"["BinaryConfiguration", c2, stepped]]],
			"Introduce"[k, stepped],
			"Have"[directions, Or[tm[k + 1][head][["direction"]] == "moveLeft", tm[k + 1][head][["direction"]] == "moveRight"]], "Exact"["directionCases"[tm[k + 1][head][["direction"]]]],
			"Cases"[directions],
			(* a move to the left: five rounds *)
			"Introduce"[moved],
			"Have"[next, "binaryConfiguration"[tm[k + 1][head][["next"]], "tapeRest"[left], "tapeFirst"[left], Prepend[tm[k + 1][head][["write"]]][right]] == c2],
			"Exact"["someInjective"["BinaryConfiguration", "binaryConfiguration"[tm[k + 1][head][["next"]], "tapeRest"[left], "tapeFirst"[left], Prepend[tm[k + 1][head][["write"]]][right]], c2, "equalityTransitivity"[
				"equalityCongruence"[Function[{Typed[d, "Direction"]}, "some"["byDirection"[d, "binaryConfiguration"[tm[k + 1][head][["next"]], "tapeRest"[left], "tapeFirst"[left], Prepend[tm[k + 1][head][["write"]]][right]], "binaryConfiguration"[tm[k + 1][head][["next"]], Prepend[tm[k + 1][head][["write"]]][left], "tapeFirst"[right], "tapeRest"[right]]]]], "equalitySymmetry"[moved]], stepped]]],
			"Rewrite"["equalitySymmetry"[next]],
			"Have"[split, "tapeValue"[left] == 2 * "tapeValue"["tapeRest"[left]] + "bitValue"["tapeFirst"[left]]], "Exact"["tapeSplit"[left]],
			"Have"[round3, "steps"["tagStep"["minskyProductions"[tm]], "tapeValue"[left] + "tapeValue"[right] + 2, "afterRound2"[(k + 1), head, "tapeValue"[left], "tapeValue"[right]]] == "some"["afterRound3"[(k + 1), head, 2 * "tapeValue"["tapeRest"[left]] + "bitValue"["tapeFirst"[left]], "tapeValue"[right]]]],
			"Rewrite"["equalitySymmetry"[split]],
			"Exact"["minskyRound3Left"[tm, (k + 1), head, "tapeValue"[left], "tapeValue"[right], moved]],
			"Have"[positive, 1 <= ((("tapeValue"[left] + (2 * "tapeValue"[right] + "bitValue"[head]) + 2) + ("tapeValue"[left] + "tapeValue"[right] + 2)) + ("tapeValue"[left] + "tapeValue"[right] + 2) + ("tapeValue"["tapeRest"[left]] + 2 * "tapeValue"[right] + 2)) + ("tapeValue"["tapeRest"[left]] + 2 * "tapeValue"[right] + 2)], "LinearArithmetic",
			"Exact"["existsIntroduction"[((("tapeValue"[left] + (2 * "tapeValue"[right] + "bitValue"[head]) + 2) + ("tapeValue"[left] + "tapeValue"[right] + 2)) + ("tapeValue"[left] + "tapeValue"[right] + 2) + ("tapeValue"["tapeRest"[left]] + 2 * "tapeValue"[right] + 2)) + ("tapeValue"["tapeRest"[left]] + 2 * "tapeValue"[right] + 2), "andIntroduction"[positive,
				"stepsThen"[{"MinskySymbol"}, "tagStep"["minskyProductions"[tm]], (("tapeValue"[left] + (2 * "tapeValue"[right] + "bitValue"[head]) + 2) + ("tapeValue"[left] + "tapeValue"[right] + 2)) + ("tapeValue"[left] + "tapeValue"[right] + 2) + ("tapeValue"["tapeRest"[left]] + 2 * "tapeValue"[right] + 2), "tapeValue"["tapeRest"[left]] + 2 * "tapeValue"[right] + 2,
					"binaryWord"["binaryConfiguration"[(k + 1), left, head, right]], "afterRound4"[(k + 1), head, "tapeFirst"[left], "tapeValue"["tapeRest"[left]], "tapeValue"[right]], "binaryWord"["binaryConfiguration"[tm[k + 1][head][["next"]], "tapeRest"[left], "tapeFirst"[left], Prepend[tm[k + 1][head][["write"]]][right]]],
					"stepsThen"[{"MinskySymbol"}, "tagStep"["minskyProductions"[tm]], (("tapeValue"[left] + (2 * "tapeValue"[right] + "bitValue"[head]) + 2) + ("tapeValue"[left] + "tapeValue"[right] + 2)) + ("tapeValue"[left] + "tapeValue"[right] + 2), "tapeValue"["tapeRest"[left]] + 2 * "tapeValue"[right] + 2,
						"binaryWord"["binaryConfiguration"[(k + 1), left, head, right]], "afterRound3"[(k + 1), head, 2 * "tapeValue"["tapeRest"[left]] + "bitValue"["tapeFirst"[left]], "tapeValue"[right]], "afterRound4"[(k + 1), head, "tapeFirst"[left], "tapeValue"["tapeRest"[left]], "tapeValue"[right]],
						"stepsThen"[{"MinskySymbol"}, "tagStep"["minskyProductions"[tm]], ("tapeValue"[left] + (2 * "tapeValue"[right] + "bitValue"[head]) + 2) + ("tapeValue"[left] + "tapeValue"[right] + 2), "tapeValue"[left] + "tapeValue"[right] + 2,
							"binaryWord"["binaryConfiguration"[(k + 1), left, head, right]], "afterRound2"[(k + 1), head, "tapeValue"[left], "tapeValue"[right]], "afterRound3"[(k + 1), head, 2 * "tapeValue"["tapeRest"[left]] + "bitValue"["tapeFirst"[left]], "tapeValue"[right]],
							"stepsThen"[{"MinskySymbol"}, "tagStep"["minskyProductions"[tm]], "tapeValue"[left] + (2 * "tapeValue"[right] + "bitValue"[head]) + 2, "tapeValue"[left] + "tapeValue"[right] + 2,
								"binaryWord"["binaryConfiguration"[(k + 1), left, head, right]], "afterRound1"[(k + 1), "tapeValue"[left], 2 * "tapeValue"[right] + "bitValue"[head]], "afterRound2"[(k + 1), head, "tapeValue"[left], "tapeValue"[right]],
								"minskyRound1"[tm, (k + 1), "tapeValue"[left], 2 * "tapeValue"[right] + "bitValue"[head]],
								"minskyRound2"[tm, (k + 1), "tapeValue"[left], head, "tapeValue"[right]]],
							round3],
						"minskyRound4"[tm, (k + 1), head, "tapeFirst"[left], "tapeValue"["tapeRest"[left]], "tapeValue"[right]]],
					"minskyRound5"[tm, (k + 1), head, "tapeFirst"[left], "tapeValue"["tapeRest"[left]], "tapeValue"[right]]]]]],
			(* a move to the right: three rounds *)
			"Introduce"[moved],
			"Have"[next, "binaryConfiguration"[tm[k + 1][head][["next"]], Prepend[tm[k + 1][head][["write"]]][left], "tapeFirst"[right], "tapeRest"[right]] == c2],
			"Exact"["someInjective"["BinaryConfiguration", "binaryConfiguration"[tm[k + 1][head][["next"]], Prepend[tm[k + 1][head][["write"]]][left], "tapeFirst"[right], "tapeRest"[right]], c2, "equalityTransitivity"[
				"equalityCongruence"[Function[{Typed[d, "Direction"]}, "some"["byDirection"[d, "binaryConfiguration"[tm[k + 1][head][["next"]], "tapeRest"[left], "tapeFirst"[left], Prepend[tm[k + 1][head][["write"]]][right]], "binaryConfiguration"[tm[k + 1][head][["next"]], Prepend[tm[k + 1][head][["write"]]][left], "tapeFirst"[right], "tapeRest"[right]]]]], "equalitySymmetry"[moved]], stepped]]],
			"Rewrite"["equalitySymmetry"[next]],
			"Have"[split, "tapeValue"[right] == 2 * "tapeValue"["tapeRest"[right]] + "bitValue"["tapeFirst"[right]]], "Exact"["tapeSplit"[right]],
			"Have"[round3, "steps"["tagStep"["minskyProductions"[tm]], "tapeValue"[left] + "tapeValue"[right] + 2, "afterRound2"[(k + 1), head, "tapeValue"[left], "tapeValue"[right]]] ==
				"some"["minskyWord"[tm[k + 1][head][["next"]], 2 * "tapeValue"[left] + "bitValue"[tm[k + 1][head][["write"]]], 2 * "tapeValue"["tapeRest"[right]] + "bitValue"["tapeFirst"[right]]]]],
			"Rewrite"["equalitySymmetry"[split]],
			"Exact"["minskyRound3Right"[tm, (k + 1), head, "tapeValue"[left], "tapeValue"[right], moved]],
			"Have"[positive, 1 <= (("tapeValue"[left] + (2 * "tapeValue"[right] + "bitValue"[head]) + 2) + ("tapeValue"[left] + "tapeValue"[right] + 2)) + ("tapeValue"[left] + "tapeValue"[right] + 2)], "LinearArithmetic",
			"Exact"["existsIntroduction"[(("tapeValue"[left] + (2 * "tapeValue"[right] + "bitValue"[head]) + 2) + ("tapeValue"[left] + "tapeValue"[right] + 2)) + ("tapeValue"[left] + "tapeValue"[right] + 2), "andIntroduction"[positive,
				"stepsThen"[{"MinskySymbol"}, "tagStep"["minskyProductions"[tm]], ("tapeValue"[left] + (2 * "tapeValue"[right] + "bitValue"[head]) + 2) + ("tapeValue"[left] + "tapeValue"[right] + 2), "tapeValue"[left] + "tapeValue"[right] + 2,
					"binaryWord"["binaryConfiguration"[(k + 1), left, head, right]], "afterRound2"[(k + 1), head, "tapeValue"[left], "tapeValue"[right]], "binaryWord"["binaryConfiguration"[tm[k + 1][head][["next"]], Prepend[tm[k + 1][head][["write"]]][left], "tapeFirst"[right], "tapeRest"[right]]],
					"stepsThen"[{"MinskySymbol"}, "tagStep"["minskyProductions"[tm]], "tapeValue"[left] + (2 * "tapeValue"[right] + "bitValue"[head]) + 2, "tapeValue"[left] + "tapeValue"[right] + 2,
						"binaryWord"["binaryConfiguration"[(k + 1), left, head, right]], "afterRound1"[(k + 1), "tapeValue"[left], 2 * "tapeValue"[right] + "bitValue"[head]], "afterRound2"[(k + 1), head, "tapeValue"[left], "tapeValue"[right]],
						"minskyRound1"[tm, (k + 1), "tapeValue"[left], 2 * "tapeValue"[right] + "bitValue"[head]],
						"minskyRound2"[tm, (k + 1), "tapeValue"[left], head, "tapeValue"[right]]],
					round3]]]]
		}
	],
	(* rung 1 as a simulation: the tag system follows the machine, a configuration related to its word *)
	machineTheorem["minskySimulation",
		ForAll[{Typed[tm, (NonNegativeIntegers -> Booleans -> "MachineTransition")]},
			"forwardSimulation"["binaryStep"[tm], "tagStep"["minskyProductions"[tm]], Function[{Typed[c, "BinaryConfiguration"], Typed[w, {"MinskySymbol"}]}, w == "binaryWord"[c]]]],
		{
			"Introduce"[tm, s, t, s2, related, stepped],
			"Have"[run, Exists[{Typed[k, NonNegativeIntegers]}, And[1 <= k, "steps"["tagStep"["minskyProductions"[tm]], k, "binaryWord"[s]] == "some"["binaryWord"[s2]]]]],
			"Exact"["minskyStep"[tm, s, s2, stepped]],
			"Cases"[run], "Introduce"[k, both], "Cases"[both], "Introduce"[positive, reached],
			"Exact"["existsIntroduction"[k, "andIntroduction"[positive, "existsIntroduction"["binaryWord"[s2], "andIntroduction"[
				"equalityTransitivity"["equalityCongruence"[Function[{Typed[w, {"MinskySymbol"}]}, "steps"["tagStep"["minskyProductions"[tm]], k, w]], related], reached],
				"equalityReflexivity"["binaryWord"[s2]]]]]]]
		}
	]
}

$wolfram23Declarations = Join[With[
	{
		configuration = "LookaheadConfiguration", optional = Option["LookaheadConfiguration"], machine = "LookaheadState" -> "Color" -> "Color" -> "LookaheadRule",
		table0 = ruleTable[$system0Table], table1 = ruleTable[$system1Table], table2 = ruleTable[$system2Table], table3 = ruleTable[$system3Table],
		configurationScript = $configurationScript, threeStepsScript = $threeStepsScript, positiveScript = $positiveScript
	},
	{
		(* systems: a step function and its iteration *)
		TypeTheoryDefinition["optionBind", Typed[
			Function[{TypedImplicit[S, TypeUniverse[1]], TypedImplicit[T, TypeUniverse[1]], Typed[o, Option[S]], Typed[f, S -> Option[T]]},
				InductiveRecursor[Option][Function[{Typed[q, Option[S]]}, Option[T]], Typed["none", Option[T]], f, o]],
			ForAll[{TypedImplicit[S, TypeUniverse[1]], TypedImplicit[T, TypeUniverse[1]]}, Option[S] -> (S -> Option[T]) -> Option[T]]
		]],
		TypeTheoryDefinition["optionMap", Typed[
			Function[{TypedImplicit[S, TypeUniverse[1]], TypedImplicit[T, TypeUniverse[1]], Typed[f, S -> T], Typed[o, Option[S]]},
				InductiveRecursor[Option][Function[{Typed[q, Option[S]]}, Option[T]], Typed["none", Option[T]], Function[{Typed[y, S]}, "some"[f[y]]], o]],
			ForAll[{TypedImplicit[S, TypeUniverse[1]], TypedImplicit[T, TypeUniverse[1]]}, (S -> T) -> Option[S] -> Option[T]]
		]],
		TypeTheoryDefinition["orElse", Typed[
			Function[{TypedImplicit[S, TypeUniverse[1]], Typed[first, Option[S]], Typed[second, Option[S]]},
				InductiveRecursor[Option][Function[{Typed[q, Option[S]]}, Option[S]], second, Function[{Typed[y, S]}, "some"[y]], first]],
			ForAll[{TypedImplicit[S, TypeUniverse[1]]}, Option[S] -> Option[S] -> Option[S]]
		]],
		TypeTheoryDefinition["steps", Typed[
			Function[{TypedImplicit[S, TypeUniverse[1]], Typed[step, S -> Option[S]], Typed[n, NonNegativeIntegers], Typed[s, S]},
				InductiveRecursor[NonNegativeIntegers][Function[{Typed[k, NonNegativeIntegers]}, Option[S]], "some"[s],
					Function[{Typed[k, NonNegativeIntegers], Typed[previous, Option[S]]}, "optionBind"[previous, step]], n]],
			ForAll[{TypedImplicit[S, TypeUniverse[1]]}, (S -> Option[S]) -> NonNegativeIntegers -> S -> Option[S]]
		]],
		machineTheorem["stepsAdd",
			ForAll[{Typed[S, TypeUniverse[1]], Typed[step, S -> Option[S]], Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers], Typed[s, S]},
				"steps"[step, m + n, s] == "optionBind"["steps"[step, m, s], Function[{Typed[y, S]}, "steps"[step, n, y]]]],
			{
				"Introduce"[S, step, m, n, s],
				"Induction"[n],
				"Change"["steps"[step, m, s] == "optionBind"["steps"[step, m, s], Function[{Typed[y, S]}, "steps"[step, 0, y]]]],
				"Cases"["steps"[step, m, s]], "Reflexivity", "Introduce"[y], "Reflexivity",
				"Introduce"[k, induction],
				"Change"["optionBind"["steps"[step, m + k, s], step] == "optionBind"["steps"[step, m, s], Function[{Typed[y, S]}, "optionBind"["steps"[step, k, y], step]]]],
				"Rewrite"[induction],
				"Cases"["steps"[step, m, s]], "Reflexivity", "Introduce"[y], "Reflexivity"
			}
		],
		(* an option is none or some value, with its equation, which "Cases" on a term does not keep *)
		machineTheorem["optionCases",
			ForAll[{Typed[S, TypeUniverse[1]], Typed[o, Option[S]]}, Or[o == Typed["none", Option[S]], Exists[{Typed[y, S]}, o == "some"[y]]]],
			{
				"Introduce"[S, o], "Cases"[o],
				"Exact"["orIntroductionLeft"["equalityReflexivity"[Typed["none", Option[S]]]]],
				"Introduce"[y], "Exact"["orIntroductionRight"["existsIntroduction"[y, "equalityReflexivity"["some"[y]]]]]
			}
		],
		TypeTheoryDefinition["forwardSimulation", Typed[
			Function[{TypedImplicit[S, TypeUniverse[1]], TypedImplicit[T, TypeUniverse[1]], Typed[f, S -> Option[S]], Typed[g, T -> Option[T]], Typed[R, S -> T -> TypeUniverse[0]]},
				ForAll[{Typed[s, S], Typed[t, T], Typed[s2, S]}, Implies[R[s, t], Implies[f[s] == "some"[s2],
					Exists[{Typed[k, NonNegativeIntegers]}, And[1 <= k, Exists[{Typed[t2, T]}, And["steps"[g, k, t] == "some"[t2], R[s2, t2]]]]]]]]],
			ForAll[{TypedImplicit[S, TypeUniverse[1]], TypedImplicit[T, TypeUniverse[1]]}, (S -> Option[S]) -> (T -> Option[T]) -> (S -> T -> TypeUniverse[0]) -> TypeUniverse[0]]
		]],
		(* n steps of the source are j >= n steps of the target: the first n - 1 by induction, the last by the simulation *)
		With[
			{
				notSome = Function[{Typed[o, Option[S]]}, InductiveRecursor[Option][Function[{Typed[q, Option[S]]}, TypeUniverse[0]], True, Function[{Typed[x, S]}, False], o]],
				valueOr = Function[{Typed[o, Option[S]]}, InductiveRecursor[Option][Function[{Typed[q, Option[S]]}, S], s, Function[{Typed[x, S]}, x], o]],
				bindSource = Function[{Typed[o, Option[S]]}, "optionBind"[o, f]],
				bindTarget = Function[{Typed[o, Option[T]]}, "optionBind"[o, Function[{Typed[x, T]}, "steps"[g, k2, x]]]]
			},
			machineTheorem["forwardSimulationSteps",
				ForAll[{Typed[S, TypeUniverse[1]], Typed[T, TypeUniverse[1]], Typed[f, S -> Option[S]], Typed[g, T -> Option[T]], Typed[R, S -> T -> TypeUniverse[0]],
					Typed[simulation, "forwardSimulation"[f, g, R]], Typed[n, NonNegativeIntegers]},
					ForAll[{Typed[s, S], Typed[t, T], Typed[s2, S]}, Implies[R[s, t], Implies["steps"[f, n, s] == "some"[s2],
						Exists[{Typed[j, NonNegativeIntegers]}, And[n <= j, Exists[{Typed[t2, T]}, And["steps"[g, j, t] == "some"[t2], R[s2, t2]]]]]]]]],
				{
					"Introduce"[S, T, f, g, R, simulation, n],
					"Induction"[n],
					"Introduce"[s, t, s2, related, reached],
					"Exact"["existsIntroduction"[0, "andIntroduction"["lessEqualReflexivity", "existsIntroduction"[t, "andIntroduction"["equalityReflexivity"["some"[t]],
						Construct["equalitySubstitution", S, Function[{Typed[x, S]}, R[x, t]], s, s2, "equalityCongruence"[valueOr, reached], related]]]]]],
					"Introduce"[k, induction, s, t, s2, related, reached],
					"Have"[split, Or["steps"[f, k, s] == Typed["none", Option[S]], Exists[{Typed[y, S]}, "steps"[f, k, s] == "some"[y]]]],
					"Exact"["optionCases"[S, "steps"[f, k, s]]],
					"Cases"[split],
					"Introduce"[stuck],
					"Exact"["falseElimination"[Construct["equalitySubstitution", Option[S], notSome, Typed["none", Option[S]], "some"[s2],
						"equalityTransitivity"["equalitySymmetry"["equalityCongruence"[bindSource, stuck]], reached], "trueIntroduction"]]],
					"Introduce"[some], "Cases"[some], "Introduce"[y, before],
					"Have"[last, f[y] == "some"[s2]],
					"Exact"["equalityTransitivity"["equalitySymmetry"["equalityCongruence"[bindSource, before]], reached]],
					"Have"[first, Exists[{Typed[j, NonNegativeIntegers]}, And[k <= j, Exists[{Typed[t2, T]}, And["steps"[g, j, t] == "some"[t2], R[y, t2]]]]]],
					"Exact"[induction[s, t, y, related, before]],
					"Cases"[first], "Introduce"[j, firstSteps], "Cases"[firstSteps], "Introduce"[atLeast, firstTarget], "Cases"[firstTarget],
					"Introduce"[t1, firstReached], "Cases"[firstReached], "Introduce"[firstRun, firstRelated],
					"Have"[next, Exists[{Typed[k2, NonNegativeIntegers]}, And[1 <= k2, Exists[{Typed[t2, T]}, And["steps"[g, k2, t1] == "some"[t2], R[s2, t2]]]]]],
					"Exact"[simulation[y, t1, s2, firstRelated, last]],
					"Cases"[next], "Introduce"[k2, nextSteps], "Cases"[nextSteps], "Introduce"[positive, nextTarget], "Cases"[nextTarget],
					"Introduce"[t2, nextReached], "Cases"[nextReached], "Introduce"[nextRun, nextRelated],
					"Have"[bound, k + 1 <= j + k2], "LinearArithmetic",
					"Exact"["existsIntroduction"[j + k2, "andIntroduction"[bound, "existsIntroduction"[t2, "andIntroduction"[
						"equalityTransitivity"["equalityTransitivity"["stepsAdd"[T, g, j, k2, t], "equalityCongruence"[bindTarget, firstRun]], nextRun], nextRelated]]]]]
				}
			]
		],
		(* lookahead machines on one zipper tape *)
		TypeTheoryInductiveType["Color", TypeUniverse[1], {"color0" -> "Color", "color1" -> "Color", "color2" -> "Color"}],
		TypeTheoryInductiveType["LookaheadState", TypeUniverse[1], {"stateA" -> "LookaheadState", "stateB" -> "LookaheadState", "stateC" -> "LookaheadState"}],
		TypeTheoryInductiveType["Direction", TypeUniverse[1], {"moveLeft" -> "Direction", "moveRight" -> "Direction"}],
		TypeTheoryInductiveType["LookaheadRule", TypeUniverse[1], {
			"oneCell" -> ForAll[{Typed[state, "LookaheadState"], Typed[color, "Color"], Typed[direction, "Direction"]}, "LookaheadRule"],
			"twoCells" -> ForAll[{Typed[state, "LookaheadState"], Typed[color, "Color"], Typed[neighbour, "Color"], Typed[direction, "Direction"]}, "LookaheadRule"]
		}],
		TypeTheoryInductiveType[configuration, TypeUniverse[1], {
			"lookaheadConfiguration" -> ForAll[{Typed[left, {"Color"}], Typed[head, "Color"], Typed[right, {"Color"}], Typed[state, "LookaheadState"]}, configuration]
		}],
		(* the head moves left onto the nearest cell of the left side; none where that side is empty *)
		TypeTheoryDefinition["moveLeftOnto", Typed[
			Function[{Typed[left, {"Color"}], Typed[newRight, {"Color"}], Typed[state, "LookaheadState"]},
				InductiveRecursor[List][Function[{Typed[q, {"Color"}]}, optional], Typed["none", optional],
					Function[{Typed[x, "Color"], Typed[rest, {"Color"}], Typed[previous, optional]}, "some"["lookaheadConfiguration"[rest, x, newRight, state]]], left]],
			{"Color"} -> {"Color"} -> "LookaheadState" -> optional
		]],
		(* the rule for the state, the head and its right neighbour, color0 past the end: a one-cell rule rewrites the head,
		   a two-cell rule the head and its neighbour; moving off either end of the tape is none *)
		TypeTheoryDefinition["lookaheadStep", Typed[
			Function[{Typed[m, machine], Typed[c, configuration]}, InductiveRecursor[configuration][Function[{Typed[q, configuration]}, optional],
				Function[{Typed[left, {"Color"}], Typed[head, "Color"], Typed[right, {"Color"}], Typed[state, "LookaheadState"]},
					InductiveRecursor[List][Function[{Typed[q, {"Color"}]}, optional],
						InductiveRecursor["LookaheadRule"][Function[{Typed[q, "LookaheadRule"]}, optional],
							Function[{Typed[newState, "LookaheadState"], Typed[written, "Color"], Typed[d, "Direction"]},
								InductiveRecursor["Direction"][Function[{Typed[q, "Direction"]}, optional], "moveLeftOnto"[left, {written}, newState], Typed["none", optional], d]],
							Function[{Typed[newState, "LookaheadState"], Typed[written, "Color"], Typed[writtenNeighbour, "Color"], Typed[d, "Direction"]}, Typed["none", optional]],
							m[state, head, "color0"]],
						Function[{Typed[neighbour, "Color"], Typed[rest, {"Color"}], Typed[previous, optional]},
							InductiveRecursor["LookaheadRule"][Function[{Typed[q, "LookaheadRule"]}, optional],
								Function[{Typed[newState, "LookaheadState"], Typed[written, "Color"], Typed[d, "Direction"]},
									InductiveRecursor["Direction"][Function[{Typed[q, "Direction"]}, optional],
										"moveLeftOnto"[left, Prepend[written][Prepend[neighbour][rest]], newState],
										"some"["lookaheadConfiguration"[Prepend[written][left], neighbour, rest, newState]], d]],
								Function[{Typed[newState, "LookaheadState"], Typed[written, "Color"], Typed[writtenNeighbour, "Color"], Typed[d, "Direction"]},
									InductiveRecursor["Direction"][Function[{Typed[q, "Direction"]}, optional],
										"moveLeftOnto"[left, Prepend[written][Prepend[writtenNeighbour][rest]], newState],
										"some"["lookaheadConfiguration"[Prepend[written][left], writtenNeighbour, rest, newState]], d]],
								m[state, head, neighbour]]],
						right]],
				c]],
			machine -> configuration -> optional
		]],
		TypeTheoryDefinition["system0", Typed[table0, machine]],
		TypeTheoryDefinition["system1", Typed[table1, machine]],
		TypeTheoryDefinition["system2", Typed[table2, machine]],
		TypeTheoryDefinition["system3", Typed[table3, machine]],
		(* the relabelings of pp. 4-5 *)
		TypeTheoryDefinition["swapColor", Typed[
			Function[{Typed[a, "Color"]}, InductiveRecursor["Color"][Function[{Typed[q, "Color"]}, "Color"], "color0", "color2", "color1", a]],
			"Color" -> "Color"
		]],
		(* System 3 to System 2: every cell left of the head swapped, and the head itself in state A *)
		TypeTheoryDefinition["phi3", Typed[
			Function[{Typed[c, configuration]}, InductiveRecursor[configuration][Function[{Typed[q, configuration]}, configuration],
				Function[{Typed[left, {"Color"}], Typed[head, "Color"], Typed[right, {"Color"}], Typed[state, "LookaheadState"]},
					InductiveRecursor["LookaheadState"][Function[{Typed[q, "LookaheadState"]}, configuration],
						"lookaheadConfiguration"[Map["swapColor", left], "swapColor"[head], right, "stateA"],
						"lookaheadConfiguration"[Map["swapColor", left], head, right, "stateB"],
						"lookaheadConfiguration"[Map["swapColor", left], head, right, "stateC"], state]],
				c]],
			configuration -> configuration
		]],
		(* System 2 to System 1: state C is state B with the head swapped *)
		TypeTheoryDefinition["phi2", Typed[
			Function[{Typed[c, configuration]}, InductiveRecursor[configuration][Function[{Typed[q, configuration]}, configuration],
				Function[{Typed[left, {"Color"}], Typed[head, "Color"], Typed[right, {"Color"}], Typed[state, "LookaheadState"]},
					InductiveRecursor["LookaheadState"][Function[{Typed[q, "LookaheadState"]}, configuration],
						"lookaheadConfiguration"[left, head, right, "stateA"], "lookaheadConfiguration"[left, head, right, "stateB"],
						"lookaheadConfiguration"[left, "swapColor"[head], right, "stateB"], state]],
				c]],
			configuration -> configuration
		]],
		TypeTheoryDefinition["system0Steps", Typed[
			Function[{Typed[c, configuration]}, InductiveRecursor[configuration][Function[{Typed[q, configuration]}, NonNegativeIntegers],
				Function[{Typed[left, {"Color"}], Typed[head, "Color"], Typed[right, {"Color"}], Typed[state, "LookaheadState"]},
					InductiveRecursor["LookaheadState"][Function[{Typed[q, "LookaheadState"]}, NonNegativeIntegers], 1,
						InductiveRecursor["Color"][Function[{Typed[q, "Color"]}, NonNegativeIntegers], 1, 1,
							InductiveRecursor[List][Function[{Typed[q, {"Color"}]}, NonNegativeIntegers], 1,
								Function[{Typed[neighbour, "Color"], Typed[rest, {"Color"}], Typed[previous, NonNegativeIntegers]},
									InductiveRecursor["Color"][Function[{Typed[q, "Color"]}, NonNegativeIntegers], 1, 3, 3, neighbour]], right], head],
						1, state]],
				c]],
			configuration -> NonNegativeIntegers
		]],
		machineTheorem["phi3Step",
			ForAll[{Typed[c, "LookaheadConfiguration"]}, "lookaheadStep"["system2", "phi3"[c]] == "optionMap"["phi3", "lookaheadStep"["system3", c]]],
			configurationScript
		],
		machineTheorem["phi2Step",
			ForAll[{Typed[c, "LookaheadConfiguration"]}, "lookaheadStep"["system1", "phi2"[c]] == "optionMap"["phi2", "lookaheadStep"["system2", c]]],
			configurationScript
		],
		machineTheorem["system0FollowsSystem1",
			ForAll[{Typed[c, "LookaheadConfiguration"]},
				"steps"["lookaheadStep"["system0"], "system0Steps"[c], c] == "orElse"["lookaheadStep"["system1", c], "steps"["lookaheadStep"["system0"], "system0Steps"[c], c]]],
			threeStepsScript
		],
		machineTheorem["system0StepsPositive", ForAll[{Typed[c, "LookaheadConfiguration"]}, 1 <= "system0Steps"[c]], positiveScript],
		(* simulations compose: a step of f is k >= 1 steps of g, and those are j >= k steps of h *)
		machineTheorem["forwardSimulationCompose",
			ForAll[{Typed[S, TypeUniverse[1]], Typed[T, TypeUniverse[1]], Typed[U, TypeUniverse[1]], Typed[f, S -> Option[S]], Typed[g, T -> Option[T]], Typed[h, U -> Option[U]],
				Typed[R, S -> T -> TypeUniverse[0]], Typed[R2, T -> U -> TypeUniverse[0]], Typed[first, "forwardSimulation"[f, g, R]], Typed[second, "forwardSimulation"[g, h, R2]]},
				"forwardSimulation"[f, h, Function[{Typed[s, S], Typed[u, U]}, Exists[{Typed[t, T]}, And[R[s, t], R2[t, u]]]]]],
			{
				"Introduce"[S, T, U, f, g, h, R, R2, first, second, s, u, s2, related, stepped],
				"Cases"[related], "Introduce"[t, both], "Cases"[both], "Introduce"[relatedFirst, relatedSecond],
				"Have"[middle, Exists[{Typed[k, NonNegativeIntegers]}, And[1 <= k, Exists[{Typed[t2, T]}, And["steps"[g, k, t] == "some"[t2], R[s2, t2]]]]]],
				"Exact"[first[s, t, s2, relatedFirst, stepped]],
				"Cases"[middle], "Introduce"[k, middleSteps], "Cases"[middleSteps], "Introduce"[positive, middleTarget], "Cases"[middleTarget],
				"Introduce"[t2, middleReached], "Cases"[middleReached], "Introduce"[middleRun, middleRelated],
				"Have"[last, Exists[{Typed[j, NonNegativeIntegers]}, And[k <= j, Exists[{Typed[u2, U]}, And["steps"[h, j, u] == "some"[u2], R2[t2, u2]]]]]],
				"Exact"["forwardSimulationSteps"[T, U, g, h, R2, second, k, t, u, t2, relatedSecond, middleRun]],
				"Cases"[last], "Introduce"[j, lastSteps], "Cases"[lastSteps], "Introduce"[atLeast, lastTarget], "Cases"[lastTarget],
				"Introduce"[u2, lastReached], "Cases"[lastReached], "Introduce"[lastRun, lastRelated],
				"Have"[jPositive, 1 <= j], "LinearArithmetic",
				"Exact"["existsIntroduction"[j, "andIntroduction"[jPositive, "existsIntroduction"[u2, "andIntroduction"[lastRun,
					"existsIntroduction"[t2, "andIntroduction"[middleRelated, lastRelated]]]]]]]
			}
		],
		(* a map that turns each step of f into one step of g makes g follow f along it *)
		machineTheorem["relabelingSimulation",
			ForAll[{Typed[S, TypeUniverse[1]], Typed[T, TypeUniverse[1]], Typed[f, S -> Option[S]], Typed[g, T -> Option[T]], Typed[phi, S -> T],
				Typed[commutes, ForAll[{Typed[c, S]}, g[phi[c]] == "optionMap"[phi, f[c]]]]},
				"forwardSimulation"[f, g, Function[{Typed[c, S], Typed[d, T]}, d == phi[c]]]],
			{
				"Introduce"[S, T, f, g, phi, commutes, s, t, s2, related, stepped],
				"Exact"["existsIntroduction"[1, "andIntroduction"["lessEqualReflexivity", "existsIntroduction"[phi[s2], "andIntroduction"[
					"equalityTransitivity"["equalityTransitivity"["equalityCongruence"[g, related], commutes[s]],
						"equalityCongruence"[Function[{Typed[o, Option[S]]}, "optionMap"[phi, o]], stepped]],
					"equalityReflexivity"[phi[s2]]]]]]]
			}
		],
		machineTheorem["system0Simulates1",
			"forwardSimulation"["lookaheadStep"["system1"], "lookaheadStep"["system0"], Function[{Typed[c, configuration], Typed[d, configuration]}, d == c]],
			{
				"Introduce"[s, t, s2, related, stepped],
				"Exact"["existsIntroduction"["system0Steps"[s], "andIntroduction"["system0StepsPositive"[s], "existsIntroduction"[s2, "andIntroduction"[
					"equalityTransitivity"["equalityTransitivity"[
						"equalityCongruence"[Function[{Typed[x, configuration]}, "steps"["lookaheadStep"["system0"], "system0Steps"[s], x]], related],
						"system0FollowsSystem1"[s]],
						"equalityCongruence"[Function[{Typed[o, optional]}, "orElse"[o, "steps"["lookaheadStep"["system0"], "system0Steps"[s], s]]], stepped]],
					"equalityReflexivity"[s2]]]]]]
			}
		],
		(* the standard machine of one-cell rules, whose tape grows by a blank, color0, where the head passes its end *)
		TypeTheoryDefinition["turingMachineStep", Typed[
			Function[{Typed[m, machine], Typed[c, configuration]}, InductiveRecursor[configuration][Function[{Typed[q, configuration]}, optional],
				Function[{Typed[left, {"Color"}], Typed[head, "Color"], Typed[right, {"Color"}], Typed[state, "LookaheadState"]},
					InductiveRecursor["LookaheadRule"][Function[{Typed[q, "LookaheadRule"]}, optional],
						Function[{Typed[newState, "LookaheadState"], Typed[written, "Color"], Typed[d, "Direction"]},
							InductiveRecursor["Direction"][Function[{Typed[q, "Direction"]}, optional],
								InductiveRecursor[List][Function[{Typed[q, {"Color"}]}, optional],
									"some"["lookaheadConfiguration"[{}, "color0", Prepend[written][right], newState]],
									Function[{Typed[x, "Color"], Typed[rest, {"Color"}], Typed[previous, optional]}, "some"["lookaheadConfiguration"[rest, x, Prepend[written][right], newState]]],
									left],
								InductiveRecursor[List][Function[{Typed[q, {"Color"}]}, optional],
									"some"["lookaheadConfiguration"[Prepend[written][left], "color0", {}, newState]],
									Function[{Typed[x, "Color"], Typed[rest, {"Color"}], Typed[previous, optional]}, "some"["lookaheadConfiguration"[Prepend[written][left], x, rest, newState]]],
									right],
								d]],
						Function[{Typed[newState, "LookaheadState"], Typed[written, "Color"], Typed[writtenNeighbour, "Color"], Typed[d, "Direction"]}, Typed["none", optional]],
						m[state, head, "color0"]]],
				c]],
			machine -> configuration -> optional
		]],
		(* on the tape, System 0's lookahead step is the standard machine's step *)
		machineTheorem["turingMachineFollowsSystem0",
			ForAll[{Typed[c, "LookaheadConfiguration"]}, "turingMachineStep"["system0", c] == "orElse"["lookaheadStep"["system0", c], "turingMachineStep"["system0", c]]],
			configurationScript
		],
		(* a step function that agrees with f wherever f is defined follows f step for step *)
		machineTheorem["agreementSimulation",
			ForAll[{Typed[S, TypeUniverse[1]], Typed[f, S -> Option[S]], Typed[g, S -> Option[S]], Typed[agrees, ForAll[{Typed[c, S]}, g[c] == "orElse"[f[c], g[c]]]]},
				"forwardSimulation"[f, g, Function[{Typed[c, S], Typed[d, S]}, d == c]]],
			{
				"Introduce"[S, f, g, agrees, s, t, s2, related, stepped],
				"Exact"["existsIntroduction"[1, "andIntroduction"["lessEqualReflexivity", "existsIntroduction"[s2, "andIntroduction"[
					"equalityTransitivity"["equalityTransitivity"["equalityCongruence"[g, related], agrees[s]],
						"equalityCongruence"[Function[{Typed[o, Option[S]]}, "orElse"[o, g[s]]], stepped]],
					"equalityReflexivity"[s2]]]]]]
			}
		],
		(* rung 6: System 0, Wolfram's (2,3) machine, follows System 3 through phi3, then phi2, then 1 or 3 steps *)
		machineTheorem["system0Simulates3",
			"forwardSimulation"["lookaheadStep"["system3"], "lookaheadStep"["system0"], Function[{Typed[c, configuration], Typed[e, configuration]},
				Exists[{Typed[d1, configuration]}, And[
					Exists[{Typed[d2, configuration]}, And[d2 == "phi3"[c], d1 == "phi2"[d2]]],
					e == d1]]]],
			{
				"Exact"["forwardSimulationCompose"[configuration, configuration, configuration, "lookaheadStep"["system3"], "lookaheadStep"["system1"], "lookaheadStep"["system0"],
					Function[{Typed[c, configuration], Typed[d1, configuration]}, Exists[{Typed[d2, configuration]}, And[d2 == "phi3"[c], d1 == "phi2"[d2]]]],
					Function[{Typed[c, configuration], Typed[d, configuration]}, d == c],
					"forwardSimulationCompose"[configuration, configuration, configuration, "lookaheadStep"["system3"], "lookaheadStep"["system2"], "lookaheadStep"["system1"],
						Function[{Typed[c, configuration], Typed[d, configuration]}, d == "phi3"[c]], Function[{Typed[c, configuration], Typed[d, configuration]}, d == "phi2"[c]],
						"relabelingSimulation"[configuration, configuration, "lookaheadStep"["system3"], "lookaheadStep"["system2"], "phi3", "phi3Step"],
						"relabelingSimulation"[configuration, configuration, "lookaheadStep"["system2"], "lookaheadStep"["system1"], "phi2", "phi2Step"]],
					"system0Simulates1"]]
			}
		],
		(* the standard (2,3) machine, whose tape grows by blanks, follows System 3 *)
		machineTheorem["wolfram23Simulates3",
			"forwardSimulation"["lookaheadStep"["system3"], "turingMachineStep"["system0"], Function[{Typed[c, configuration], Typed[g, configuration]},
				Exists[{Typed[e, configuration]}, And[
					Exists[{Typed[d1, configuration]}, And[Exists[{Typed[d2, configuration]}, And[d2 == "phi3"[c], d1 == "phi2"[d2]]], e == d1]],
					g == e]]]],
			{
				"Exact"["forwardSimulationCompose"[configuration, configuration, configuration, "lookaheadStep"["system3"], "lookaheadStep"["system0"], "turingMachineStep"["system0"],
					Function[{Typed[c, configuration], Typed[e, configuration]},
						Exists[{Typed[d1, configuration]}, And[Exists[{Typed[d2, configuration]}, And[d2 == "phi3"[c], d1 == "phi2"[d2]]], e == d1]]],
					Function[{Typed[c, configuration], Typed[d, configuration]}, d == c],
					"system0Simulates3",
					"agreementSimulation"[configuration, "lookaheadStep"["system0"], "turingMachineStep"["system0"], "turingMachineFollowsSystem0"]]]
			}
		],
		(* rung 2: cyclic tag systems, the appendants carried in the configuration and rotated at each step *)
		TypeTheoryInductiveType["CyclicTagConfiguration", TypeUniverse[1], {
			"cyclicTagConfiguration" -> ForAll[{Typed[data, {Booleans}], Typed[appendants, {{Booleans}}]}, "CyclicTagConfiguration"]
		}],
		(* the appendant where the bit is true, nothing where it is false *)
		TypeTheoryDefinition["appendantIf", Typed[
			Function[{Typed[b, Booleans], Typed[a, {Booleans}]}, InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, {Booleans}], Typed[{}, {Booleans}], a, b]],
			Booleans -> {Booleans} -> {Booleans}
		]],
		(* one step: the first bit off the data, the first appendant appended where the bit is true, and the appendants rotated *)
		TypeTheoryDefinition["cyclicTagStep", Typed[
			Function[{Typed[c, "CyclicTagConfiguration"]}, InductiveRecursor["CyclicTagConfiguration"][Function[{Typed[q, "CyclicTagConfiguration"]}, Option["CyclicTagConfiguration"]],
				Function[{Typed[data, {Booleans}], Typed[appendants, {{Booleans}}]},
					InductiveRecursor[List][Function[{Typed[q, {Booleans}]}, Option["CyclicTagConfiguration"]], Typed["none", Option["CyclicTagConfiguration"]],
						Function[{Typed[b, Booleans], Typed[rest, {Booleans}], Typed[previous, Option["CyclicTagConfiguration"]]},
							InductiveRecursor[List][Function[{Typed[q, {{Booleans}}]}, Option["CyclicTagConfiguration"]], Typed["none", Option["CyclicTagConfiguration"]],
								Function[{Typed[a, {Booleans}], Typed[others, {{Booleans}}], Typed[previous2, Option["CyclicTagConfiguration"]]},
									"some"["cyclicTagConfiguration"[Join[rest, "appendantIf"[b, a]], Join[others, {a}]]]],
								appendants]],
						data]],
				c]],
			"CyclicTagConfiguration" -> Option["CyclicTagConfiguration"]
		]],
		(* the appendants a block of bits selects, in order *)
		TypeTheoryDefinition["selected", Typed[
			Function[{Typed[bits, {Booleans}], Typed[as, {{Booleans}}]},
				InductiveRecursor[List][Function[{Typed[q, {Booleans}]}, {{Booleans}} -> {Booleans}],
					Function[{Typed[x, {{Booleans}}]}, Typed[{}, {Booleans}]],
					Function[{Typed[b, Booleans], Typed[rest, {Booleans}], Typed[recurse, {{Booleans}} -> {Booleans}]},
						Function[{Typed[x, {{Booleans}}]}, InductiveRecursor[List][Function[{Typed[q, {{Booleans}}]}, {Booleans}], Typed[{}, {Booleans}],
							Function[{Typed[a, {Booleans}], Typed[others, {{Booleans}}], Typed[previous, {Booleans}]}, Join["appendantIf"[b, a], recurse[others]]], x]]],
					bits][as]],
			{Booleans} -> {{Booleans}} -> {Booleans}
		]],
		(* a block of bits as long as the next appendants appends the appendants under its 1s, in order, and rotates them *)
		With[{configuration = "cyclicTagConfiguration"}, machineTheorem["cyclicTagBlock",
			ForAll[{Typed[bits, {Booleans}], Typed[as, {{Booleans}}], Typed[r, {Booleans}], Typed[q, {{Booleans}}]},
				Implies[Length[as] == Length[bits],
					"steps"["cyclicTagStep", Length[bits], configuration[Join[bits, r], Join[as, q]]] == "some"[configuration[Join[r, "selected"[bits, as]], Join[q, as]]]]],
			{
				"Introduce"[bits], "Induction"[bits],
				(* no bits: no appendants, nothing appended *)
				"Introduce"[as, r, q, lengths], "Cases"[as], "Introduce"[lengths],
				"Change"["some"[configuration[r, q]] == "some"[configuration[Join[r, Typed[{}, {Booleans}]], Join[q, Typed[{}, {{Booleans}}]]]]],
				"Rewrite"["joinEmptyRight"[r]], "Rewrite"["joinEmptyRight"[q]],
				"Introduce"[a, others, lengths], "Exact"["falseElimination"["successorNotZero"[Length[others], lengths]]],
				(* a bit more: one step, the rest by induction *)
				"Introduce"[b, rest, induction, as, r, q, lengths], "Cases"[as], "Introduce"[lengths],
				"Exact"["falseElimination"["successorNotZero"[Length[rest], "equalitySymmetry"[lengths]]]],
				"Introduce"[a, others, lengths],
				"Have"[expanded, Length[others] + 1 == Length[rest] + 1], "Exact"[lengths],
				"Have"[restLengths, Length[others] == Length[rest]], "LinearArithmetic",
				"Change"["steps"["cyclicTagStep", Length[rest] + 1, configuration[Prepend[b][Join[rest, r]], Prepend[a][Join[others, q]]]] ==
					"some"[configuration[Join[r, Join["appendantIf"[b, a], "selected"[rest, others]]], Join[q, Prepend[a][others]]]]],
				"Rewrite"["additionCommutativity"[Length[rest], 1]],
				"Rewrite"["stepsAdd"["CyclicTagConfiguration", "cyclicTagStep", 1, Length[rest], configuration[Prepend[b][Join[rest, r]], Prepend[a][Join[others, q]]]]],
				"Change"["steps"["cyclicTagStep", Length[rest], configuration[Join[Join[rest, r], "appendantIf"[b, a]], Join[Join[others, q], {a}]]] ==
					"some"[configuration[Join[r, Join["appendantIf"[b, a], "selected"[rest, others]]], Join[q, Prepend[a][others]]]]],
				"Rewrite"["joinAssociativity"[rest, r, "appendantIf"[b, a]]],
				"Rewrite"["joinAssociativity"[others, q, {a}]],
				"Rewrite"[induction[others, Join[r, "appendantIf"[b, a]], Join[q, {a}], restLengths]],
				"Rewrite"["joinAssociativity"[r, "appendantIf"[b, a], "selected"[rest, others]]],
				"Rewrite"["joinAssociativity"[q, {a}, others]],
				"Reflexivity"
			}
		]]
	}
], $cookDeclarations, $roundDeclarations, $minskyDeclarations]
