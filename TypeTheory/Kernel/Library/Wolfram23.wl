(* ::Package:: *)

(*
Wolfram's (2,3) Turing machine and Smith's chain of emulations: TypeTheoryEnvironment["Wolfram23"] is the prelude with
the systems of the chain, built and checked the first time it is asked for. The design is in
docs/notes/Wolfram23Universality.md; this file holds its first milestone.

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

$wolfram23Declarations = With[
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
]
