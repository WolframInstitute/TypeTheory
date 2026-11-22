(* ::Package:: *)

(*
Rung 3 of Smith's chain of emulations to Wolfram's (2,3) Turing machine: a fueled cyclic tag system emulated by
Smith's System 5, built on the framework and cyclic tag definitions of Wolfram23.wl. The design is in
docs/notes/Wolfram23Universality.md.

	"strictlyAbove"[lo, xs]          xs is strictly increasing with every element above lo
	"allBelowEqual"[hi, xs]          every element of xs is at most hi
	"shiftUp", "shiftDown",          elementwise +d and -d on bags and rule lists
	"shiftUpRules"
	"xorMerge"[xs, ys]               symmetric difference of two strictly increasing lists of natural numbers
	"System5Configuration",          Smith's System 5: a strictly increasing bag of positive numbers and a queue of
	"system5Step"[c]                 rules; each step decrements the bag, drops 1 and XOR-merges the next rule, or
	                                 rotates nothing and increments all rules
	"bound5", "bound5Step"           the maximum element of a System 5 configuration grows by at most 1 per step
	"doubleWord"[w]                  each bit of a cyclic tag word doubled, with pairs encoded at gaps 1 (0) and 2 (1)
	"pairsOf", "pairsAsc"            the bag formed by ascending pairs at starts a for a word w
	"encodeAppendantSnd"[a, i]       second rule of an appendant block; its shift by 2 XOR-merges with it to give
	"xorMergeAppendant"              "pairsOf"["doubleWord"[a], "startsOf"[a, i]]
	"cycleAppendants", "ruleBlocks"  the rotating appendant schedule and its 4-rule blocks (r2+2, r2, {}, {})
	"decodeBag"[bag]                 reads a strictly increasing positive bag back to its doubled word, or none
	"FueledCyclicTag",               a cyclic tag configuration with a step budget, stepping while the budget is
	"fueledCyclicTagStep"            positive
	"system5Represents"[fc, s]       the simulation relation: s's bag encodes the doubled word and its rules are the
	                                 exact rule blocks for the remaining budget, shifted above the bag
	"ctsToSystem5"[cfg, budget]      the encoder, with "ctsToSystem5Represents", "ctsToSystem5BagStrictlyAbove" and
	                                 "ctsToSystem5RulesStrictlyAbove"
	"representsDecode",              decoding, empty rules at budget 0, non-empty bag on non-empty data, and halting
	"representsRulesEmpty",          at budget 0
	"representsBagNonEmpty",
	"representsTerminal"
	"representsStepFalse",           one cyclic tag step is x2 + 1 (on 0) or x2 + 2 (on 1) steps of System 5, four
	"representsStepTrue",            rule pops each, giving the forward simulation "system5Simulation"
	"system5Simulation"
*)


(* ::Section:: *)
(*PackageExported*)




(* ::Section:: *)
(*PackageScoped*)


PackageScoped[$system5Declarations]


(* ::Section:: *)
(*Usage Messages*)


$system5Declarations::usage = "$system5Declarations is the list of the declarations of rung 3 of Smith's chain (cyclic tag systems to System 5), in order, each theorem proved by its tactics in the environment so far."


(* ::Section:: *)
(*Function Definitions*)


$system5Declarations = {
	(* strictlyAbove[lo, xs]: xs is strictly increasing and every element is > lo *)
	TypeTheoryDefinition["strictlyAbove", Typed[
		Function[{Typed[lo, NonNegativeIntegers], Typed[xs, {NonNegativeIntegers}]},
			InductiveRecursor[List][Function[{Typed[q, {NonNegativeIntegers}]}, NonNegativeIntegers -> TypeUniverse[0]],
				Function[{Typed[bound, NonNegativeIntegers]}, True],
				Function[{Typed[x, NonNegativeIntegers], Typed[rest, {NonNegativeIntegers}], Typed[previous, NonNegativeIntegers -> TypeUniverse[0]]},
					Function[{Typed[bound, NonNegativeIntegers]}, And[bound + 1 <= x, previous[x]]]],
				xs][lo]],
		NonNegativeIntegers -> {NonNegativeIntegers} -> TypeUniverse[0]
	]],
	(* allBelowEqual[hi, xs]: every element of xs is <= hi *)
	TypeTheoryDefinition["allBelowEqual", Typed[
		Function[{Typed[hi, NonNegativeIntegers], Typed[xs, {NonNegativeIntegers}]},
			InductiveRecursor[List][Function[{Typed[q, {NonNegativeIntegers}]}, TypeUniverse[0]],
				True,
				Function[{Typed[x, NonNegativeIntegers], Typed[rest, {NonNegativeIntegers}], Typed[previous, TypeUniverse[0]]},
					And[x <= hi, previous]],
				xs]],
		NonNegativeIntegers -> {NonNegativeIntegers} -> TypeUniverse[0]
	]],
	TypeTheoryDefinition["shiftUp", Typed[
		Function[{Typed[d, NonNegativeIntegers], Typed[xs, {NonNegativeIntegers}]}, Map[Function[{Typed[x, NonNegativeIntegers]}, x + d], xs]],
		NonNegativeIntegers -> {NonNegativeIntegers} -> {NonNegativeIntegers}
	]],
	TypeTheoryDefinition["shiftDown", Typed[
		Function[{Typed[d, NonNegativeIntegers], Typed[xs, {NonNegativeIntegers}]}, Map[Function[{Typed[x, NonNegativeIntegers]}, Subtract[x, d]], xs]],
		NonNegativeIntegers -> {NonNegativeIntegers} -> {NonNegativeIntegers}
	]],
	TypeTheoryDefinition["shiftUpRules", Typed[
		Function[{Typed[d, NonNegativeIntegers], Typed[rs, {{NonNegativeIntegers}}]}, Map[Function[{Typed[r, {NonNegativeIntegers}]}, "shiftUp"[d, r]], rs]],
		NonNegativeIntegers -> {{NonNegativeIntegers}} -> {{NonNegativeIntegers}}
	]],
	TypeTheoryDefinition["xorMerge", Typed[
		Function[{Typed[xs, {NonNegativeIntegers}]},
			InductiveRecursor[List][Function[{Typed[q, {NonNegativeIntegers}]}, {NonNegativeIntegers} -> {NonNegativeIntegers}],
				Function[{Typed[ys, {NonNegativeIntegers}]}, ys],
				Function[{Typed[x, NonNegativeIntegers], Typed[xsRest, {NonNegativeIntegers}], Typed[mergeRest, {NonNegativeIntegers} -> {NonNegativeIntegers}]},
					Function[{Typed[ys, {NonNegativeIntegers}]},
						InductiveRecursor[List][Function[{Typed[q, {NonNegativeIntegers}]}, {NonNegativeIntegers}],
							Prepend[x][xsRest],
							Function[{Typed[y, NonNegativeIntegers], Typed[ysRest, {NonNegativeIntegers}], Typed[mergeYsRest, {NonNegativeIntegers}]},
								InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, {NonNegativeIntegers}],
									InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, {NonNegativeIntegers}],
										Prepend[y][mergeYsRest],
										Prepend[x][mergeRest[Prepend[y][ysRest]]],
										Decide[x + 1 <= y]],
									mergeRest[ysRest],
									Decide[x == y]]],
							ys]]],
				xs]],
		{NonNegativeIntegers} -> {NonNegativeIntegers} -> {NonNegativeIntegers}
	]],
	(* Helper lemmas on strictlyAbove and allBelowEqual *)
	machineTheorem["strictlyAboveWeaken",
		ForAll[{Typed[lo1, NonNegativeIntegers], Typed[lo2, NonNegativeIntegers], Typed[xs, {NonNegativeIntegers}]},
			Implies[lo2 <= lo1, Implies["strictlyAbove"[lo1, xs], "strictlyAbove"[lo2, xs]]]],
		{
			"Introduce"[lo1, lo2, xs], "Cases"[xs],
			"Introduce"[le, h], "Exact"["trueIntroduction"],
			"Introduce"[x, rest, le, h], "Cases"[h], "Introduce"[hx, hrest],
			"Have"[hx2, lo2 + 1 <= x], "LinearArithmetic",
			"Exact"["andIntroduction"[hx2, hrest]]
		}
	],
	machineTheorem["allBelowEqualWeaken",
		ForAll[{Typed[hi1, NonNegativeIntegers], Typed[hi2, NonNegativeIntegers], Typed[xs, {NonNegativeIntegers}]},
			Implies[hi1 <= hi2, Implies["allBelowEqual"[hi1, xs], "allBelowEqual"[hi2, xs]]]],
		{
			"Introduce"[hi1, hi2, xs], "Induction"[xs],
			"Introduce"[le, h], "Exact"["trueIntroduction"],
			"Introduce"[x, rest, ih, le, h], "Cases"[h], "Introduce"[hx, hrest],
			"Have"[hx2, x <= hi2], "LinearArithmetic",
			"Exact"["andIntroduction"[hx2, ih[le, hrest]]]
		}
	],
	machineTheorem["strictlyAboveJoin",
		ForAll[{Typed[xs, {NonNegativeIntegers}], Typed[ys, {NonNegativeIntegers}], Typed[lo, NonNegativeIntegers], Typed[mid, NonNegativeIntegers]},
			Implies[lo <= mid, Implies["strictlyAbove"[lo, xs], Implies["allBelowEqual"[mid, xs], Implies["strictlyAbove"[mid, ys], "strictlyAbove"[lo, Join[xs, ys]]]]]]],
		{
			"Introduce"[xs], "Induction"[xs],
			"Introduce"[ys, lo, mid, le, h1, h2, hy], "Exact"["strictlyAboveWeaken"[mid, lo, ys, le, hy]],
			"Introduce"[x, rest, ih, ys, lo, mid, le, h1, h2, hy],
			"Cases"[h1], "Introduce"[hx, hrest],
			"Cases"[h2], "Introduce"[xMid, restMid],
			"Exact"["andIntroduction"[hx, ih[ys, x, mid, xMid, hrest, restMid, hy]]]
		}
	],
	machineTheorem["allBelowEqualJoin",
		ForAll[{Typed[hi, NonNegativeIntegers], Typed[xs, {NonNegativeIntegers}], Typed[ys, {NonNegativeIntegers}]},
			Implies["allBelowEqual"[hi, xs], Implies["allBelowEqual"[hi, ys], "allBelowEqual"[hi, Join[xs, ys]]]]],
		{
			"Introduce"[hi, xs], "Induction"[xs],
			"Introduce"[ys, hx, hy], "Exact"[hy],
			"Introduce"[x, rest, ih, ys, hx, hy], "Cases"[hx], "Introduce"[xHi, restHi],
			"Exact"["andIntroduction"[xHi, ih[ys, restHi, hy]]]
		}
	],
	(* Shift lemmas *)
	machineTheorem["shiftUpZero",
		ForAll[{Typed[xs, {NonNegativeIntegers}]}, "shiftUp"[0, xs] == xs],
		{
			"Introduce"[xs], "Induction"[xs], "Reflexivity",
			"Introduce"[x, rest, ih], "Change"[Prepend[x + 0]["shiftUp"[0, rest]] == Prepend[x][rest]],
			"Rewrite"[ih], "Reflexivity"
		}
	],
	machineTheorem["shiftUpAdd",
		ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[xs, {NonNegativeIntegers}]},
			"shiftUp"[a, "shiftUp"[b, xs]] == "shiftUp"[b + a, xs]],
		{
			"Introduce"[a, b, xs], "Induction"[xs], "Reflexivity",
			"Introduce"[x, rest, ih], "Change"[Prepend[(x + b) + a]["shiftUp"[a, "shiftUp"[b, rest]]] == Prepend[x + (b + a)]["shiftUp"[b + a, rest]]],
			"Rewrite"["additionAssociativity"[x, b, a]], "Rewrite"[ih]
		}
	],
	machineTheorem["shiftUpRulesAdd",
		ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[rs, {{NonNegativeIntegers}}]},
			"shiftUpRules"[a, "shiftUpRules"[b, rs]] == "shiftUpRules"[b + a, rs]],
		{
			"Introduce"[a, b, rs], "Induction"[rs], "Reflexivity",
			"Introduce"[r, rest, ih],
			"Change"[Prepend["shiftUp"[a, "shiftUp"[b, r]]]["shiftUpRules"[a, "shiftUpRules"[b, rest]]] == Prepend["shiftUp"[b + a, r]]["shiftUpRules"[b + a, rest]]],
			"Rewrite"["shiftUpAdd"[a, b, r]], "Rewrite"[ih]
		}
	],
	machineTheorem["shiftDownZero",
		ForAll[{Typed[xs, {NonNegativeIntegers}]}, "shiftDown"[0, xs] == xs],
		{
			"Introduce"[xs], "Induction"[xs], "Reflexivity",
			"Introduce"[x, rest, ih], "Change"[Prepend[Subtract[x, 0]]["shiftDown"[0, rest]] == Prepend[x][rest]],
			"Rewrite"[ih], "Reflexivity"
		}
	],
	machineTheorem["subtractAdd",
		ForAll[{Typed[x, NonNegativeIntegers], Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]},
			Subtract[Subtract[x, a], b] == Subtract[x, a + b]],
		{
			"Introduce"[x, a, b], "Induction"[b],
			"Reflexivity",
			"Introduce"[k, ih],
			"Change"[NaturalNumberPredecessor[Subtract[Subtract[x, a], k]] == NaturalNumberPredecessor[Subtract[x, a + k]]],
			"Rewrite"[ih]
		}
	],
	machineTheorem["shiftDownAdd",
		ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[xs, {NonNegativeIntegers}]},
			"shiftDown"[b, "shiftDown"[a, xs]] == "shiftDown"[a + b, xs]],
		{
			"Introduce"[a, b, xs], "Induction"[xs], "Reflexivity",
			"Introduce"[x, rest, ih],
			"Change"[Prepend[Subtract[Subtract[x, a], b]]["shiftDown"[b, "shiftDown"[a, rest]]] == Prepend[Subtract[x, a + b]]["shiftDown"[a + b, rest]]],
			"Rewrite"["subtractAdd"[x, a, b]], "Rewrite"[ih]
		}
	],
	machineTheorem["shiftDownShiftUp",
		ForAll[{Typed[d, NonNegativeIntegers], Typed[xs, {NonNegativeIntegers}]},
			"shiftDown"[d, "shiftUp"[d, xs]] == xs],
		{
			"Introduce"[d, xs], "Induction"[xs], "Reflexivity",
			"Introduce"[x, rest, ih],
			"Change"[Prepend[Subtract[x + d, d]]["shiftDown"[d, "shiftUp"[d, rest]]] == Prepend[x][rest]],
			"Rewrite"["additionSubtractionCancellation"[x, d]], "Rewrite"[ih]
		}
	],
	(* xorMerge lemmas *)
	machineTheorem["xorMergeEmptyRight",
		ForAll[{Typed[xs, {NonNegativeIntegers}]}, "xorMerge"[xs, Typed[{}, {NonNegativeIntegers}]] == xs],
		{"Introduce"[xs], "Cases"[xs], "Reflexivity", "Introduce"[x, rest], "Reflexivity"}
	],
	machineTheorem["decideEqualTrue",
		ForAll[{Typed[x, NonNegativeIntegers], Typed[y, NonNegativeIntegers]}, Implies[x == y, Decide[x == y] == "true"]],
		{
			"Introduce"[x, y, eq],
			"Cases"["naturalNumberEqualityDecidable"[x, y]],
			"Introduce"[neq], "Exact"["falseElimination"[neq[eq]]],
			"Introduce"[same], "Reflexivity"
		}
	],
	machineTheorem["decideEqualFalse",
		ForAll[{Typed[x, NonNegativeIntegers], Typed[y, NonNegativeIntegers]}, Implies[Not[x == y], Decide[x == y] == "false"]],
		{
			"Introduce"[x, y, neq],
			"Cases"["naturalNumberEqualityDecidable"[x, y]],
			"Introduce"[d], "Reflexivity",
			"Introduce"[eq], "Exact"["falseElimination"[neq[eq]]]
		}
	],
	machineTheorem["decideLessEqualTrue",
		ForAll[{Typed[x, NonNegativeIntegers], Typed[y, NonNegativeIntegers]}, Implies[x <= y, Decide[x <= y] == "true"]],
		{
			"Introduce"[x, y, le],
			"Cases"["lessEqualDecidable"[x, y]],
			"Introduce"[nle], "Exact"["falseElimination"[nle[le]]],
			"Introduce"[same], "Reflexivity"
		}
	],
	machineTheorem["decideLessEqualFalse",
		ForAll[{Typed[x, NonNegativeIntegers], Typed[y, NonNegativeIntegers]}, Implies[Not[x <= y], Decide[x <= y] == "false"]],
		{
			"Introduce"[x, y, nle],
			"Cases"["lessEqualDecidable"[x, y]],
			"Introduce"[d], "Reflexivity",
			"Introduce"[le], "Exact"["falseElimination"[nle[le]]]
		}
	],
	machineTheorem["xorMergeSelf",
		ForAll[{Typed[xs, {NonNegativeIntegers}]}, "xorMerge"[xs, xs] == Typed[{}, {NonNegativeIntegers}]],
		{
			"Introduce"[xs], "Induction"[xs], "Reflexivity",
			"Introduce"[x, rest, ih],
			"Change"[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, {NonNegativeIntegers}],
				InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, {NonNegativeIntegers}],
					Prepend[x]["xorMerge"[Prepend[x][rest], rest]],
					Prepend[x]["xorMerge"[rest, Prepend[x][rest]]],
					Decide[x + 1 <= x]],
				"xorMerge"[rest, rest],
				Decide[x == x]] == Typed[{}, {NonNegativeIntegers}]],
			"Rewrite"["decideEqualTrue"[x, x, "equalityReflexivity"[x]]],
			"Exact"[ih]
		}
	],
	machineTheorem["xorMergePrefix",
		ForAll[{Typed[xs, {NonNegativeIntegers}], Typed[ys, {NonNegativeIntegers}], Typed[zs, {NonNegativeIntegers}], Typed[mid, NonNegativeIntegers]},
			Implies["allBelowEqual"[mid, xs], Implies["strictlyAbove"[mid, zs],
				"xorMerge"[Join[xs, ys], zs] == Join[xs, "xorMerge"[ys, zs]]]]],
		{
			"Introduce"[xs], "Induction"[xs],
			"Introduce"[ys, zs, mid, hx, hz], "Reflexivity",
			"Introduce"[x, rest, ih, ys, zs, mid, hx, hz],
			"Cases"[hx], "Introduce"[xMid, restMid],
			"Cases"[zs], "Introduce"[hz],
			"Rewrite"["xorMergeEmptyRight"[Join[Prepend[x][rest], ys]]],
			"Rewrite"["xorMergeEmptyRight"[ys]],
			"Introduce"[z, zRest, hz],
			"Cases"[hz], "Introduce"[midZ, zRestAbove],
			"Have"[neq, Not[x == z]], "Introduce"[eq], "Have"[bad, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"[bad],
			"Have"[lt, x + 1 <= z], "LinearArithmetic",
			"Change"[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, {NonNegativeIntegers}],
				InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, {NonNegativeIntegers}],
					Prepend[z]["xorMerge"[Prepend[x][Join[rest, ys]], zRest]],
					Prepend[x]["xorMerge"[Join[rest, ys], Prepend[z][zRest]]],
					Decide[x + 1 <= z]],
				"xorMerge"[Join[rest, ys], zRest],
				Decide[x == z]] == Prepend[x][Join[rest, "xorMerge"[ys, Prepend[z][zRest]]]]],
			"Rewrite"["decideEqualFalse"[x, z, neq]],
			"Rewrite"["decideLessEqualTrue"[x + 1, z, lt]],
			"Change"[Prepend[x]["xorMerge"[Join[rest, ys], Prepend[z][zRest]]] == Prepend[x][Join[rest, "xorMerge"[ys, Prepend[z][zRest]]]]],
			"Rewrite"[ih[ys, Prepend[z][zRest], mid, restMid, "andIntroduction"[midZ, zRestAbove]]]
		}
	],
	machineTheorem["xorMergeDisjoint",
		ForAll[{Typed[xs, {NonNegativeIntegers}], Typed[ys, {NonNegativeIntegers}], Typed[mid, NonNegativeIntegers]},
			Implies["allBelowEqual"[mid, xs], Implies["strictlyAbove"[mid, ys], "xorMerge"[xs, ys] == Join[xs, ys]]]],
		{
			"Introduce"[xs, ys, mid, hx, hy],
			"Exact"["equalityTransitivity"["equalityCongruence"[Function[{Typed[l, {NonNegativeIntegers}]}, "xorMerge"[l, ys]], "equalitySymmetry"["joinEmptyRight"[xs]]],
				"xorMergePrefix"[xs, Typed[{}, {NonNegativeIntegers}], ys, mid, hx, hy]]]
		}
	],
	machineTheorem["xorMergeCancelTail",
		ForAll[{Typed[xs, {NonNegativeIntegers}], Typed[ys, {NonNegativeIntegers}], Typed[mid, NonNegativeIntegers]},
			Implies["allBelowEqual"[mid, xs], Implies["strictlyAbove"[mid, ys], "xorMerge"[Join[xs, ys], ys] == xs]]],
		{
			"Introduce"[xs, ys, mid, hx, hy],
			"Rewrite"["xorMergePrefix"[xs, ys, ys, mid, hx, hy]],
			"Rewrite"["xorMergeSelf"[ys]],
			"Exact"["joinEmptyRight"[xs]]
		}
	],
	machineTheorem["xorMergeAllBelowEqual",
		ForAll[{Typed[hi, NonNegativeIntegers], Typed[xs, {NonNegativeIntegers}], Typed[ys, {NonNegativeIntegers}]},
			Implies["allBelowEqual"[hi, xs], Implies["allBelowEqual"[hi, ys], "allBelowEqual"[hi, "xorMerge"[xs, ys]]]]],
		{
			"Introduce"[hi, xs], "Induction"[xs],
			"Introduce"[ys, hx, hy], "Exact"[hy],
			"Introduce"[x, xsRest, ihX, ys, hx],
			"Cases"[hx], "Introduce"[xHi, xsRestHi],
			"Induction"[ys],
			"Introduce"[hy0], "Exact"["andIntroduction"[xHi, xsRestHi]],
			"Introduce"[y, ysRest, ihY, hy2],
			"Cases"[hy2], "Introduce"[yHi, ysRestHi],
			"Change"["allBelowEqual"[hi, InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, {NonNegativeIntegers}],
				InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, {NonNegativeIntegers}],
					Prepend[y]["xorMerge"[Prepend[x][xsRest], ysRest]],
					Prepend[x]["xorMerge"[xsRest, Prepend[y][ysRest]]],
					Decide[x + 1 <= y]],
				"xorMerge"[xsRest, ysRest],
				Decide[x == y]]]],
			"Cases"["naturalNumberEqualityDecidable"[x, y]],
			"Introduce"[neq],
			"Cases"["lessEqualDecidable"[x + 1, y]],
			"Introduce"[nlt],
			"Exact"["andIntroduction"[yHi, ihY[ysRestHi]]],
			"Introduce"[lt],
			"Exact"["andIntroduction"[xHi, ihX[Prepend[y][ysRest], xsRestHi, "andIntroduction"[yHi, ysRestHi]]]],
			"Introduce"[eq],
			"Exact"[ihX[ysRest, xsRestHi, ysRestHi]]
		}
	],
	machineTheorem["lessEqualExists",
		ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]},
			Implies[a <= b, Exists[{Typed[k, NonNegativeIntegers]}, b == k + a]]],
		{
			"Introduce"[a, b, h], "Induction"[h],
			"Exact"["existsIntroduction"[0, "equalitySymmetry"["additionZeroLeft"[a]]]],
			"Introduce"[j, hj, ih],
			"Cases"[ih], "Introduce"[k, eq],
			"Have"[eq2, j + 1 == (k + 1) + a], "LinearArithmetic",
			"Exact"["existsIntroduction"[k + 1, eq2]]
		}
	],
	machineTheorem["lessEqualExistsRight",
		ForAll[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers]},
			Implies[a <= b, Exists[{Typed[k, NonNegativeIntegers]}, b == a + k]]],
		{
			"Introduce"[a, b, h],
			"Cases"["lessEqualExists"[a, b, h]], "Introduce"[k, eq],
			"Have"[eq2, b == a + k], "LinearArithmetic",
			"Exact"["existsIntroduction"[k, eq2]]
		}
	],
	machineTheorem["shiftDownStrictlyAbove",
		ForAll[{Typed[xs, {NonNegativeIntegers}], Typed[d, NonNegativeIntegers], Typed[lo, NonNegativeIntegers]},
			Implies["strictlyAbove"[lo + d, xs], "strictlyAbove"[lo, "shiftDown"[d, xs]]]],
		{
			"Introduce"[xs], "Induction"[xs],
			"Introduce"[d, lo, h], "Exact"["trueIntroduction"],
			"Introduce"[x, rest, ih, d, lo, h],
			"Cases"[h], "Introduce"[hx, hrest],
			"Have"[le, d <= x], "LinearArithmetic",
			"Have"[xEq, Subtract[x, d] + d == x],
			"Cases"["lessEqualExists"[d, x, le]], "Introduce"[k, xk],
			"Rewrite"[xk], "Rewrite"["additionSubtractionCancellation"[k, d]],
			"Have"[h1, lo + 1 <= Subtract[x, d]], "LinearArithmetic",
			"Have"[hrest2, "strictlyAbove"[Subtract[x, d] + d, rest]],
			"Rewrite"[xEq], "Exact"[hrest],
			"Exact"["andIntroduction"[h1, ih[d, Subtract[x, d], hrest2]]]
		}
	],
	machineTheorem["shiftUpAllBelowEqual",
		ForAll[{Typed[xs, {NonNegativeIntegers}], Typed[d, NonNegativeIntegers], Typed[hi, NonNegativeIntegers]},
			Implies["allBelowEqual"[hi, xs], "allBelowEqual"[hi + d, "shiftUp"[d, xs]]]],
		{
			"Introduce"[xs], "Induction"[xs],
			"Introduce"[d, hi, h], "Exact"["trueIntroduction"],
			"Introduce"[x, rest, ih, d, hi, h], "Cases"[h], "Introduce"[hx, hrest],
			"Have"[hx2, x + d <= hi + d], "LinearArithmetic",
			"Exact"["andIntroduction"[hx2, ih[d, hi, hrest]]]
		}
	],
	machineTheorem["shiftDownAllBelowEqual",
		ForAll[{Typed[xs, {NonNegativeIntegers}], Typed[d, NonNegativeIntegers], Typed[hi, NonNegativeIntegers]},
			Implies["allBelowEqual"[hi + d, xs], "allBelowEqual"[hi, "shiftDown"[d, xs]]]],
		{
			"Introduce"[xs], "Induction"[xs],
			"Introduce"[d, hi, h], "Exact"["trueIntroduction"],
			"Introduce"[x, rest, ih, d, hi, h], "Cases"[h], "Introduce"[hx, hrest],
			"Have"[split, Or[d <= x, x < d]], "Exact"["lessEqualTotality"[d, x]],
			"Cases"[split],
			"Introduce"[ge],
			"Have"[subLe, Subtract[x, d] <= hi],
			"Cases"["lessEqualExists"[d, x, ge]], "Introduce"[k, xk], "Rewrite"[xk], "Rewrite"["additionSubtractionCancellation"[k, d]], "LinearArithmetic",
			"Exact"["andIntroduction"[subLe, ih[d, hi, hrest]]],
			"Introduce"[lt],
			"Have"[le, x <= d], "LinearArithmetic",
			"Have"[sub0, Subtract[x, d] == 0],
			"Cases"["lessEqualExistsRight"[x, d, le]], "Introduce"[k, dxk], "Rewrite"[dxk],
			"Rewrite"["equalitySymmetry"["subtractAdd"[x, x, k]]], "Rewrite"["subtractionSelf"[x]], "Exact"["subtractionZeroLeft"[k]],
			"Have"[subLe, Subtract[x, d] <= hi], "Rewrite"[sub0], "Exact"["lessEqualZero"[hi]],
			"Exact"["andIntroduction"[subLe, ih[d, hi, hrest]]]
		}
	],
	TypeTheoryInductiveType["System5Configuration", TypeUniverse[1], {
		"system5Configuration" -> ForAll[{Typed[bag, {NonNegativeIntegers}], Typed[rules, {{NonNegativeIntegers}}]}, "System5Configuration"]
	}],
	TypeTheoryDefinition["system5Step", Typed[
		Function[{Typed[c, "System5Configuration"]},
			InductiveRecursor["System5Configuration"][Function[{Typed[q, "System5Configuration"]}, Option["System5Configuration"]],
				Function[{Typed[bag, {NonNegativeIntegers}], Typed[rules, {{NonNegativeIntegers}}]},
					InductiveRecursor[List][Function[{Typed[q, {NonNegativeIntegers}]}, Option["System5Configuration"]],
						Typed["none", Option["System5Configuration"]],
						Function[{Typed[b, NonNegativeIntegers], Typed[restBag, {NonNegativeIntegers}], Typed[unused1, Option["System5Configuration"]]},
							InductiveRecursor[List][Function[{Typed[q, {{NonNegativeIntegers}}]}, Option["System5Configuration"]],
								Typed["none", Option["System5Configuration"]],
								Function[{Typed[nextRule, {NonNegativeIntegers}], Typed[restRules, {{NonNegativeIntegers}}], Typed[unused2, Option["System5Configuration"]]},
									InductiveRecursor[NonNegativeIntegers][Function[{Typed[q, NonNegativeIntegers]}, Option["System5Configuration"]],
										Typed["none", Option["System5Configuration"]],
										Function[{Typed[bPred, NonNegativeIntegers], Typed[unused3, Option["System5Configuration"]]},
											InductiveRecursor[NonNegativeIntegers][Function[{Typed[q, NonNegativeIntegers]}, Option["System5Configuration"]],
												"some"["system5Configuration"["xorMerge"["shiftDown"[1, restBag], "shiftUp"[1, nextRule]], "shiftUpRules"[1, restRules]]],
												Function[{Typed[k, NonNegativeIntegers], Typed[unused4, Option["System5Configuration"]]},
													"some"["system5Configuration"[Prepend[k + 1]["shiftDown"[1, restBag]], "shiftUpRules"[1, Prepend[nextRule][restRules]]]]],
												bPred]],
										b]],
								rules]],
						bag]],
				c]],
		"System5Configuration" -> Option["System5Configuration"]
	]],
	(* Pure decrements: j steps from (j + 1) :: rest, with nonempty rules *)
	machineTheorem["system5RunPureDecrement",
		ForAll[{Typed[j, NonNegativeIntegers], Typed[rest, {NonNegativeIntegers}], Typed[r, {NonNegativeIntegers}], Typed[rs, {{NonNegativeIntegers}}]},
			"steps"["system5Step", j, "system5Configuration"[Prepend[j + 1][rest], Prepend[r][rs]]] ==
				"some"["system5Configuration"[Prepend[1]["shiftDown"[j, rest]], "shiftUpRules"[j, Prepend[r][rs]]]]],
		{
			"Introduce"[j], "Induction"[j],
			"Introduce"[rest, r, rs],
			"Change"["some"["system5Configuration"[Prepend[1][rest], Prepend[r][rs]]] == "some"["system5Configuration"[Prepend[1]["shiftDown"[0, rest]], "shiftUpRules"[0, Prepend[r][rs]]]]],
			"Rewrite"["shiftDownZero"[rest]],
			"Change"["some"["system5Configuration"[Prepend[1][rest], Prepend[r][rs]]] == "some"["system5Configuration"[Prepend[1][rest], Prepend["shiftUp"[0, r]]["shiftUpRules"[0, rs]]]]],
			"Rewrite"["shiftUpZero"[r]],
			"Have"[rulesZero, ForAll[{Typed[l, {{NonNegativeIntegers}}]}, "shiftUpRules"[0, l] == l]],
			"Introduce"[l], "Induction"[l], "Reflexivity",
			"Introduce"[h, t, ihL], "Change"[Prepend["shiftUp"[0, h]]["shiftUpRules"[0, t]] == Prepend[h][t]],
			"Rewrite"["shiftUpZero"[h]], "Rewrite"[ihL],
			"Rewrite"[rulesZero[rs]],
			"Introduce"[k, ih, rest, r, rs],
			"Change"["steps"["system5Step", k + 1, "system5Configuration"[Prepend["successor"["successor"[k]]][rest], Prepend[r][rs]]] ==
				"some"["system5Configuration"[Prepend[1]["shiftDown"[k + 1, rest]], "shiftUpRules"[k + 1, Prepend[r][rs]]]]],
			"Rewrite"["additionCommutativity"[k, 1]],
			"Rewrite"["stepsAdd"["System5Configuration", "system5Step", 1, k, "system5Configuration"[Prepend["successor"["successor"[k]]][rest], Prepend[r][rs]]]],
			"Change"["steps"["system5Step", k, "system5Configuration"[Prepend[k + 1]["shiftDown"[1, rest]], Prepend["shiftUp"[1, r]]["shiftUpRules"[1, rs]]]] ==
				"some"["system5Configuration"[Prepend[1]["shiftDown"[1 + k, rest]], "shiftUpRules"[1 + k, Prepend[r][rs]]]]],
			"Rewrite"[ih["shiftDown"[1, rest], "shiftUp"[1, r], "shiftUpRules"[1, rs]]],
			"Rewrite"["shiftDownAdd"[1, k, rest]],
			"Change"["some"["system5Configuration"[Prepend[1]["shiftDown"[1 + k, rest]], "shiftUpRules"[k, "shiftUpRules"[1, Prepend[r][rs]]]]] ==
				"some"["system5Configuration"[Prepend[1]["shiftDown"[1 + k, rest]], "shiftUpRules"[1 + k, Prepend[r][rs]]]]],
			"Rewrite"["shiftUpRulesAdd"[k, 1, Prepend[r][rs]]]
		}
	],
	(* Run j pure decrements then pop rule r in j + 1 steps *)
	machineTheorem["system5RunThenPop",
		ForAll[{Typed[j, NonNegativeIntegers], Typed[rest, {NonNegativeIntegers}], Typed[r, {NonNegativeIntegers}], Typed[rs, {{NonNegativeIntegers}}]},
			"steps"["system5Step", j + 1, "system5Configuration"[Prepend[j + 1][rest], Prepend[r][rs]]] ==
				"some"["system5Configuration"["xorMerge"["shiftDown"[j + 1, rest], "shiftUp"[j + 1, r]], "shiftUpRules"[j + 1, rs]]]],
		{
			"Introduce"[j, rest, r, rs],
			"Rewrite"["stepsAdd"["System5Configuration", "system5Step", j, 1, "system5Configuration"[Prepend[j + 1][rest], Prepend[r][rs]]]],
			"Rewrite"["system5RunPureDecrement"[j, rest, r, rs]],
			"Change"["some"["system5Configuration"["xorMerge"["shiftDown"[1, "shiftDown"[j, rest]], "shiftUp"[1, "shiftUp"[j, r]]], "shiftUpRules"[1, "shiftUpRules"[j, rs]]]] ==
				"some"["system5Configuration"["xorMerge"["shiftDown"[j + 1, rest], "shiftUp"[j + 1, r]], "shiftUpRules"[j + 1, rs]]]],
			"Rewrite"["shiftDownAdd"[j, 1, rest]],
			"Rewrite"["shiftUpAdd"[1, j, r]],
			"Rewrite"["shiftUpRulesAdd"[1, j, rs]]
		}
	],
	(* Bound5 for Rung 4 *)
	TypeTheoryDefinition["allRulesBelowEqual", Typed[
		Function[{Typed[hi, NonNegativeIntegers], Typed[rs, {{NonNegativeIntegers}}]},
			InductiveRecursor[List][Function[{Typed[q, {{NonNegativeIntegers}}]}, TypeUniverse[0]],
				True,
				Function[{Typed[r, {NonNegativeIntegers}], Typed[rest, {{NonNegativeIntegers}}], Typed[previous, TypeUniverse[0]]},
					And["allBelowEqual"[hi, r], previous]],
				rs]],
		NonNegativeIntegers -> {{NonNegativeIntegers}} -> TypeUniverse[0]
	]],
	TypeTheoryDefinition["bound5", Typed[
		Function[{Typed[s, "System5Configuration"], Typed[B, NonNegativeIntegers]},
			And["allBelowEqual"[B, s[["bag"]]], "allRulesBelowEqual"[B, s[["rules"]]]]],
		"System5Configuration" -> NonNegativeIntegers -> TypeUniverse[0]
	]],
	machineTheorem["shiftUpRulesAllBelowEqual",
		ForAll[{Typed[rs, {{NonNegativeIntegers}}], Typed[d, NonNegativeIntegers], Typed[hi, NonNegativeIntegers]},
			Implies["allRulesBelowEqual"[hi, rs], "allRulesBelowEqual"[hi + d, "shiftUpRules"[d, rs]]]],
		{
			"Introduce"[rs], "Induction"[rs],
			"Introduce"[d, hi, h], "Exact"["trueIntroduction"],
			"Introduce"[r, rest, ih, d, hi, h], "Cases"[h], "Introduce"[hr, hrest],
			"Exact"["andIntroduction"["shiftUpAllBelowEqual"[r, d, hi, hr], ih[d, hi, hrest]]]
		}
	],
	machineTheorem["bound5Step",
		ForAll[{Typed[s, "System5Configuration"], Typed[s2, "System5Configuration"], Typed[B, NonNegativeIntegers]},
			Implies["bound5"[s, B], Implies["system5Step"[s] == "some"[s2], "bound5"[s2, B + 1]]]],
		{
			"Introduce"[s, s2, B, hb, hs],
			"Cases"[s], "Introduce"[bag, rules, hb, hs],
			"Cases"[bag], "Introduce"[hb, hs],
			"Exact"["falseElimination"["noneNotSome"["System5Configuration", s2, hs]]],
			"Introduce"[b, restBag, hb, hs],
			"Cases"[rules], "Introduce"[hb, hs],
			"Exact"["falseElimination"["noneNotSome"["System5Configuration", s2, hs]]],
			"Introduce"[nextRule, restRules, hb, hs],
			"Cases"[hb], "Introduce"[hBag, hRules],
			"Cases"[hBag], "Introduce"[hbLe, hRestBag],
			"Cases"[hRules], "Introduce"[hNextRule, hRestRules],
			"Have"[hRestBag2, "allBelowEqual"[B + 1, "shiftDown"[1, restBag]]],
			"Have"[hRestBagUp, "allBelowEqual"[(B + 1) + 1, restBag]],
			"Have"[le2, B <= (B + 1) + 1], "LinearArithmetic",
			"Exact"["allBelowEqualWeaken"[B, (B + 1) + 1, restBag, le2, hRestBag]],
			"Exact"["shiftDownAllBelowEqual"[restBag, 1, B + 1, hRestBagUp]],
			"Cases"[b], "Introduce"[hs, hbLe],
			"Exact"["falseElimination"["noneNotSome"["System5Configuration", s2, hs]]],
			"Introduce"[bPred, hs, hbLe],
			"Cases"[bPred], "Introduce"[hs, hbLe],
			"Have"[eqS2, "system5Configuration"["xorMerge"["shiftDown"[1, restBag], "shiftUp"[1, nextRule]], "shiftUpRules"[1, restRules]] == s2],
			"Exact"["someInjective"["System5Configuration", "system5Configuration"["xorMerge"["shiftDown"[1, restBag], "shiftUp"[1, nextRule]], "shiftUpRules"[1, restRules]], s2, hs]],
			"Rewrite"["equalitySymmetry"[eqS2]],
			"Exact"["andIntroduction"[
				"xorMergeAllBelowEqual"[B + 1, "shiftDown"[1, restBag], "shiftUp"[1, nextRule], hRestBag2, "shiftUpAllBelowEqual"[nextRule, 1, B, hNextRule]],
				"shiftUpRulesAllBelowEqual"[restRules, 1, B, hRestRules]]],
			"Introduce"[k, hs, hbLe],
			"Have"[eqS2, "system5Configuration"[Prepend[k + 1]["shiftDown"[1, restBag]], "shiftUpRules"[1, Prepend[nextRule][restRules]]] == s2],
			"Exact"["someInjective"["System5Configuration", "system5Configuration"[Prepend[k + 1]["shiftDown"[1, restBag]], "shiftUpRules"[1, Prepend[nextRule][restRules]]], s2, hs]],
			"Rewrite"["equalitySymmetry"[eqS2]],
			"Have"[kLe, k + 1 <= B + 1], "LinearArithmetic",
			"Exact"["andIntroduction"[
				"andIntroduction"[kLe, hRestBag2],
				"shiftUpRulesAllBelowEqual"[Prepend[nextRule][restRules], 1, B, "andIntroduction"[hNextRule, hRestRules]]]]
		}
	],
	TypeTheoryDefinition["doubleWord", Typed[
		Function[{Typed[w, {Booleans}]},
			InductiveRecursor[List][Function[{Typed[q, {Booleans}]}, {Booleans}], Typed[{}, {Booleans}],
				Function[{Typed[b, Booleans], Typed[rest, {Booleans}], Typed[previous, {Booleans}]}, Prepend[b][Prepend[b][previous]]], w]],
		{Booleans} -> {Booleans}
	]],
	machineTheorem["doubleWordJoin",
		ForAll[{Typed[u, {Booleans}], Typed[v, {Booleans}]}, "doubleWord"[Join[u, v]] == Join["doubleWord"[u], "doubleWord"[v]]],
		{
			"Introduce"[u], "Induction"[u], "Introduce"[v], "Reflexivity",
			"Introduce"[b, rest, ih, v],
			"Change"[Prepend[b][Prepend[b]["doubleWord"[Join[rest, v]]]] == Prepend[b][Prepend[b][Join["doubleWord"[rest], "doubleWord"[v]]]]],
			"Rewrite"[ih[v]]
		}
	],
	TypeTheoryDefinition["bitGap", Typed[
		Function[{Typed[b, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, NonNegativeIntegers], 1, 2, b]],
		Booleans -> NonNegativeIntegers
	]],
	machineTheorem["bitGapPos",
		ForAll[{Typed[b, Booleans]}, 1 <= "bitGap"[b]],
		{"Introduce"[b], "Cases"[b], "Decide", "Decide"}
	],
	TypeTheoryDefinition["pairsOf", Typed[
		Function[{Typed[w, {Booleans}]},
			InductiveRecursor[List][Function[{Typed[q, {Booleans}]}, {NonNegativeIntegers} -> {NonNegativeIntegers}],
				Function[{Typed[a, {NonNegativeIntegers}]}, Typed[{}, {NonNegativeIntegers}]],
				Function[{Typed[b, Booleans], Typed[rest, {Booleans}], Typed[previous, {NonNegativeIntegers} -> {NonNegativeIntegers}]},
					Function[{Typed[a, {NonNegativeIntegers}]},
						InductiveRecursor[List][Function[{Typed[q, {NonNegativeIntegers}]}, {NonNegativeIntegers}], Typed[{}, {NonNegativeIntegers}],
							Function[{Typed[x, NonNegativeIntegers], Typed[aRest, {NonNegativeIntegers}], Typed[unused, {NonNegativeIntegers}]},
								Prepend[x][Prepend[x + "bitGap"[b]][previous[aRest]]]], a]]], w]],
		{Booleans} -> {NonNegativeIntegers} -> {NonNegativeIntegers}
	]],
	TypeTheoryDefinition["pairsAsc", Typed[
		Function[{Typed[lo, NonNegativeIntegers], Typed[w, {Booleans}], Typed[a, {NonNegativeIntegers}]},
			InductiveRecursor[List][Function[{Typed[q, {Booleans}]}, NonNegativeIntegers -> {NonNegativeIntegers} -> TypeUniverse[0]],
				Function[{Typed[bound, NonNegativeIntegers], Typed[starts, {NonNegativeIntegers}]},
					InductiveRecursor[List][Function[{Typed[q, {NonNegativeIntegers}]}, TypeUniverse[0]], True,
						Function[{Typed[x, NonNegativeIntegers], Typed[rest, {NonNegativeIntegers}], Typed[u, TypeUniverse[0]]}, False], starts]],
				Function[{Typed[b, Booleans], Typed[wRest, {Booleans}], Typed[previous, NonNegativeIntegers -> {NonNegativeIntegers} -> TypeUniverse[0]]},
					Function[{Typed[bound, NonNegativeIntegers], Typed[starts, {NonNegativeIntegers}]},
						InductiveRecursor[List][Function[{Typed[q, {NonNegativeIntegers}]}, TypeUniverse[0]], False,
							Function[{Typed[x, NonNegativeIntegers], Typed[aRest, {NonNegativeIntegers}], Typed[u, TypeUniverse[0]]},
								And[bound + 1 <= x, previous[x + "bitGap"[b], aRest]]], starts]]],
				w][lo, a]],
		NonNegativeIntegers -> {Booleans} -> {NonNegativeIntegers} -> TypeUniverse[0]
	]],
	machineTheorem["pairsAscWeaken",
		ForAll[{Typed[lo1, NonNegativeIntegers], Typed[lo2, NonNegativeIntegers], Typed[w, {Booleans}], Typed[a, {NonNegativeIntegers}]},
			Implies[lo2 <= lo1, Implies["pairsAsc"[lo1, w, a], "pairsAsc"[lo2, w, a]]]],
		{
			"Introduce"[lo1, lo2, w], "Cases"[w],
			"Introduce"[a, le, h], "Exact"[h],
			"Introduce"[b, wRest, a, le, h], "Cases"[a], "Introduce"[h], "Exact"[h],
			"Introduce"[x, aRest, h], "Cases"[h], "Introduce"[hx, hrest],
			"Have"[hx2, lo2 + 1 <= x], "LinearArithmetic",
			"Exact"["andIntroduction"[hx2, hrest]]
		}
	],
	machineTheorem["pairsOfStrictlyAbove",
		ForAll[{Typed[w, {Booleans}], Typed[lo, NonNegativeIntegers], Typed[a, {NonNegativeIntegers}]},
			Implies["pairsAsc"[lo, w, a], "strictlyAbove"[lo, "pairsOf"[w, a]]]],
		{
			"Introduce"[w], "Induction"[w],
			"Introduce"[lo, a, h], "Exact"["trueIntroduction"],
			"Introduce"[b, wRest, ih, lo, a, h], "Cases"[a],
			"Introduce"[h], "Exact"["falseElimination"[h]],
			"Introduce"[x, aRest, h], "Cases"[h], "Introduce"[hx, hrest],
			"Have"[gPos, 1 <= "bitGap"[b]], "Exact"["bitGapPos"[b]],
			"Have"[gapPos, x + 1 <= x + "bitGap"[b]], "LinearArithmetic",
			"Exact"["andIntroduction"[hx, "andIntroduction"[gapPos, ih[x + "bitGap"[b], aRest, hrest]]]]
		}
	],
	machineTheorem["pairsOfShiftDown",
		ForAll[{Typed[w, {Booleans}], Typed[d, NonNegativeIntegers], Typed[a, {NonNegativeIntegers}]},
			Implies["pairsAsc"[d, w, a], "shiftDown"[d, "pairsOf"[w, a]] == "pairsOf"[w, "shiftDown"[d, a]]]],
		{
			"Introduce"[w], "Induction"[w],
			"Introduce"[d, a, h], "Reflexivity",
			"Introduce"[b, wRest, ih, d, a, h], "Cases"[a],
			"Introduce"[h], "Exact"["falseElimination"[h]],
			"Introduce"[x, aRest, h], "Cases"[h], "Introduce"[hx, hrest],
			"Have"[le, d <= x], "LinearArithmetic",
			"Have"[subAdd, Subtract[x + "bitGap"[b], d] == Subtract[x, d] + "bitGap"[b]],
			"Cases"["lessEqualExists"[d, x, le]], "Introduce"[k, xk],
			"Rewrite"[xk],
			"Have"[reassoc, (k + d) + "bitGap"[b] == (k + "bitGap"[b]) + d], "LinearArithmetic",
			"Rewrite"[reassoc],
			"Rewrite"["additionSubtractionCancellation"[k + "bitGap"[b], d]],
			"Rewrite"["additionSubtractionCancellation"[k, d]],
			"Have"[gPos, 1 <= "bitGap"[b]], "Exact"["bitGapPos"[b]],
			"Have"[dBelow, d <= x + "bitGap"[b]], "LinearArithmetic",
			"Have"[hrestD, "pairsAsc"[d, wRest, aRest]], "Exact"["pairsAscWeaken"[x + "bitGap"[b], d, wRest, aRest, dBelow, hrest]],
			"Change"[Prepend[Subtract[x, d]][Prepend[Subtract[x + "bitGap"[b], d]]["shiftDown"[d, "pairsOf"[wRest, aRest]]]] ==
				Prepend[Subtract[x, d]][Prepend[Subtract[x, d] + "bitGap"[b]]["pairsOf"[wRest, "shiftDown"[d, aRest]]]]],
			"Rewrite"[subAdd],
			"Rewrite"[ih[d, aRest, hrestD]]
		}
	],
	machineTheorem["pairsAscShiftDown",
		ForAll[{Typed[w, {Booleans}], Typed[d, NonNegativeIntegers], Typed[lo, NonNegativeIntegers], Typed[a, {NonNegativeIntegers}]},
			Implies["pairsAsc"[lo + d, w, a], "pairsAsc"[lo, w, "shiftDown"[d, a]]]],
		{
			"Introduce"[w], "Induction"[w],
			"Introduce"[d, lo, a, h], "Cases"[a], "Introduce"[h], "Exact"["trueIntroduction"],
			"Introduce"[x, aRest, h], "Exact"["falseElimination"[h]],
			"Introduce"[b, wRest, ih, d, lo, a, h], "Cases"[a],
			"Introduce"[h], "Exact"["falseElimination"[h]],
			"Introduce"[x, aRest, h], "Cases"[h], "Introduce"[hx, hrest],
			"Have"[le, d <= x], "LinearArithmetic",
			"Have"[xEq, Subtract[x, d] + d == x],
			"Cases"["lessEqualExists"[d, x, le]], "Introduce"[k, xk], "Rewrite"[xk], "Rewrite"["additionSubtractionCancellation"[k, d]],
			"Have"[hx2, lo + 1 <= Subtract[x, d]], "LinearArithmetic",
			"Have"[loEq, (Subtract[x, d] + "bitGap"[b]) + d == x + "bitGap"[b]], "LinearArithmetic",
			"Have"[hrest2, "pairsAsc"[(Subtract[x, d] + "bitGap"[b]) + d, wRest, aRest]], "Rewrite"[loEq], "Exact"[hrest],
			"Exact"["andIntroduction"[hx2, ih[d, Subtract[x, d] + "bitGap"[b], aRest, hrest2]]]
		}
	],
	machineTheorem["pairsOfJoin",
		ForAll[{Typed[w1, {Booleans}], Typed[w2, {Booleans}], Typed[a1, {NonNegativeIntegers}], Typed[a2, {NonNegativeIntegers}], Typed[lo, NonNegativeIntegers]},
			Implies["pairsAsc"[lo, w1, a1], "pairsOf"[Join[w1, w2], Join[a1, a2]] == Join["pairsOf"[w1, a1], "pairsOf"[w2, a2]]]],
		{
			"Introduce"[w1], "Induction"[w1],
			"Introduce"[w2, a1, a2, lo, h], "Cases"[a1], "Introduce"[h], "Reflexivity",
			"Introduce"[x, rest, h], "Exact"["falseElimination"[h]],
			"Introduce"[b, wRest, ih, w2, a1, a2, lo, h], "Cases"[a1],
			"Introduce"[h], "Exact"["falseElimination"[h]],
			"Introduce"[x, aRest, h], "Cases"[h], "Introduce"[hx, hrest],
			"Change"[Prepend[x][Prepend[x + "bitGap"[b]]["pairsOf"[Join[wRest, w2], Join[aRest, a2]]]] ==
				Prepend[x][Prepend[x + "bitGap"[b]][Join["pairsOf"[wRest, aRest], "pairsOf"[w2, a2]]]]],
			"Rewrite"[ih[w2, aRest, a2, x + "bitGap"[b], hrest]]
		}
	],
	machineTheorem["pairsAscJoin",
		ForAll[{Typed[w1, {Booleans}], Typed[w2, {Booleans}], Typed[a1, {NonNegativeIntegers}], Typed[a2, {NonNegativeIntegers}], Typed[lo, NonNegativeIntegers], Typed[mid, NonNegativeIntegers]},
			Implies[lo <= mid, Implies["pairsAsc"[lo, w1, a1], Implies["allBelowEqual"[mid, "pairsOf"[w1, a1]], Implies["pairsAsc"[mid, w2, a2],
				"pairsAsc"[lo, Join[w1, w2], Join[a1, a2]]]]]]],
		{
			"Introduce"[w1], "Induction"[w1],
			"Introduce"[w2, a1, a2, lo, mid, le, h1, h2, h3], "Cases"[a1],
			"Introduce"[h1, h2], "Exact"["pairsAscWeaken"[mid, lo, w2, a2, le, h3]],
			"Introduce"[x, rest, h1, h2], "Exact"["falseElimination"[h1]],
			"Introduce"[b, wRest, ih, w2, a1, a2, lo, mid, le, h1, h2, h3], "Cases"[a1],
			"Introduce"[h1, h2], "Exact"["falseElimination"[h1]],
			"Introduce"[x, aRest, h1, h2],
			"Cases"[h1], "Introduce"[hx, hrest],
			"Cases"[h2], "Introduce"[xMid, h2Rest],
			"Cases"[h2Rest], "Introduce"[xgMid, restMid],
			"Exact"["andIntroduction"[hx, ih[w2, aRest, a2, x + "bitGap"[b], mid, xgMid, hrest, restMid, h3]]]
		}
	],
	(* startsOf, appendantCounter, encodeAppendantSnd *)
	TypeTheoryDefinition["startsOf", Typed[
		Function[{Typed[a, {Booleans}]},
			InductiveRecursor[List][Function[{Typed[q, {Booleans}]}, NonNegativeIntegers -> {NonNegativeIntegers}],
				Function[{Typed[i, NonNegativeIntegers]}, Typed[{}, {NonNegativeIntegers}]],
				Function[{Typed[b, Booleans], Typed[rest, {Booleans}], Typed[previous, NonNegativeIntegers -> {NonNegativeIntegers}]},
					Function[{Typed[i, NonNegativeIntegers]},
						InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, {NonNegativeIntegers}],
							Prepend[i][Prepend[i + 2][previous[i + 4]]],
							Prepend[i][Prepend[i + 3][previous[i + 6]]],
							b]]], a]],
		{Booleans} -> NonNegativeIntegers -> {NonNegativeIntegers}
	]],
	TypeTheoryDefinition["appendantCounter", Typed[
		Function[{Typed[a, {Booleans}]},
			InductiveRecursor[List][Function[{Typed[q, {Booleans}]}, NonNegativeIntegers -> NonNegativeIntegers],
				Function[{Typed[i, NonNegativeIntegers]}, i],
				Function[{Typed[b, Booleans], Typed[rest, {Booleans}], Typed[previous, NonNegativeIntegers -> NonNegativeIntegers]},
					Function[{Typed[i, NonNegativeIntegers]},
						InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, NonNegativeIntegers], previous[i + 4], previous[i + 6], b]]], a]],
		{Booleans} -> NonNegativeIntegers -> NonNegativeIntegers
	]],
	TypeTheoryDefinition["encodeAppendantSnd", Typed[
		Function[{Typed[a, {Booleans}]},
			InductiveRecursor[List][Function[{Typed[q, {Booleans}]}, NonNegativeIntegers -> {NonNegativeIntegers}],
				Function[{Typed[i, NonNegativeIntegers]}, Typed[{}, {NonNegativeIntegers}]],
				Function[{Typed[b, Booleans], Typed[rest, {Booleans}], Typed[previous, NonNegativeIntegers -> {NonNegativeIntegers}]},
					Function[{Typed[i, NonNegativeIntegers]},
						InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, {NonNegativeIntegers}],
							Prepend[i][Prepend[i + 1][previous[i + 4]]],
							Prepend[i][Prepend[i + 3][previous[i + 6]]],
							b]]], a]],
		{Booleans} -> NonNegativeIntegers -> {NonNegativeIntegers}
	]],
	machineTheorem["appendantCounterShift",
		ForAll[{Typed[a, {Booleans}], Typed[i, NonNegativeIntegers], Typed[d, NonNegativeIntegers]},
			"appendantCounter"[a, i + d] == "appendantCounter"[a, i] + d],
		{
			"Introduce"[a], "Induction"[a], "Introduce"[i, d], "Reflexivity",
			"Introduce"[b, rest, ih, i, d], "Cases"[b],
			"Have"[eq4, (i + d) + 4 == (i + 4) + d], "LinearArithmetic",
			"Change"["appendantCounter"[rest, (i + d) + 4] == "appendantCounter"[rest, i + 4] + d],
			"Rewrite"[eq4], "Exact"[ih[i + 4, d]],
			"Have"[eq6, (i + d) + 6 == (i + 6) + d], "LinearArithmetic",
			"Change"["appendantCounter"[rest, (i + d) + 6] == "appendantCounter"[rest, i + 6] + d],
			"Rewrite"[eq6], "Exact"[ih[i + 6, d]]
		}
	],
	machineTheorem["appendantCounterGe",
		ForAll[{Typed[a, {Booleans}], Typed[i, NonNegativeIntegers]}, i <= "appendantCounter"[a, i]],
		{
			"Introduce"[a], "Induction"[a], "Introduce"[i], "Exact"["lessEqualReflexivity"],
			"Introduce"[b, rest, ih, i], "Cases"[b],
			"Change"[i <= "appendantCounter"[rest, i + 4]],
			"Have"[h4, i + 4 <= "appendantCounter"[rest, i + 4]], "Exact"[ih[i + 4]], "LinearArithmetic",
			"Change"[i <= "appendantCounter"[rest, i + 6]],
			"Have"[h6, i + 6 <= "appendantCounter"[rest, i + 6]], "Exact"[ih[i + 6]], "LinearArithmetic"
		}
	],
	machineTheorem["encodeAppendantSndShift",
		ForAll[{Typed[a, {Booleans}], Typed[i, NonNegativeIntegers], Typed[d, NonNegativeIntegers]},
			"shiftUp"[d, "encodeAppendantSnd"[a, i]] == "encodeAppendantSnd"[a, i + d]],
		{
			"Introduce"[a], "Induction"[a], "Introduce"[i, d], "Reflexivity",
			"Introduce"[b, rest, ih, i, d], "Cases"[b],
			"Change"[Prepend[i + d][Prepend[(i + 1) + d]["shiftUp"[d, "encodeAppendantSnd"[rest, i + 4]]]] ==
				Prepend[i + d][Prepend[(i + d) + 1]["encodeAppendantSnd"[rest, (i + d) + 4]]]],
			"Have"[e1, (i + 1) + d == (i + d) + 1], "LinearArithmetic",
			"Have"[e4, (i + 4) + d == (i + d) + 4], "LinearArithmetic",
			"Rewrite"[e1], "Rewrite"[ih[i + 4, d]], "Rewrite"[e4],
			"Change"[Prepend[i + d][Prepend[(i + 3) + d]["shiftUp"[d, "encodeAppendantSnd"[rest, i + 6]]]] ==
				Prepend[i + d][Prepend[(i + d) + 3]["encodeAppendantSnd"[rest, (i + d) + 6]]]],
			"Have"[e3, (i + 3) + d == (i + d) + 3], "LinearArithmetic",
			"Have"[e6, (i + 6) + d == (i + d) + 6], "LinearArithmetic",
			"Rewrite"[e3], "Rewrite"[ih[i + 6, d]], "Rewrite"[e6]
		}
	],
	machineTheorem["encodeAppendantSndStrictlyAbove",
		ForAll[{Typed[a, {Booleans}], Typed[lo, NonNegativeIntegers], Typed[i, NonNegativeIntegers]},
			Implies[lo + 1 <= i, "strictlyAbove"[lo, "encodeAppendantSnd"[a, i]]]],
		{
			"Introduce"[a], "Induction"[a], "Introduce"[lo, i, h], "Exact"["trueIntroduction"],
			"Introduce"[b, rest, ih, lo, i, h], "Cases"[b],
			"Have"[h1, i + 1 <= i + 1], "LinearArithmetic",
			"Have"[h4, (i + 1) + 1 <= i + 4], "LinearArithmetic",
			"Exact"["andIntroduction"[h, "andIntroduction"[h1, ih[i + 1, i + 4, h4]]]],
			"Have"[h3, i + 1 <= i + 3], "LinearArithmetic",
			"Have"[h6, (i + 3) + 1 <= i + 6], "LinearArithmetic",
			"Exact"["andIntroduction"[h, "andIntroduction"[h3, ih[i + 3, i + 6, h6]]]]
		}
	],
	machineTheorem["pairsAscStartsOf",
		ForAll[{Typed[a, {Booleans}], Typed[lo, NonNegativeIntegers], Typed[i, NonNegativeIntegers]},
			Implies[lo + 1 <= i, "pairsAsc"[lo, "doubleWord"[a], "startsOf"[a, i]]]],
		{
			"Introduce"[a], "Induction"[a], "Introduce"[lo, i, h], "Exact"["trueIntroduction"],
			"Introduce"[b, rest, ih, lo, i, h], "Cases"[b],
			"Have"[h2, (i + 1) + 1 <= i + 2], "LinearArithmetic",
			"Have"[h4, ((i + 2) + 1) + 1 <= i + 4], "LinearArithmetic",
			"Exact"["andIntroduction"[h, "andIntroduction"[h2, ih[(i + 2) + 1, i + 4, h4]]]],
			"Have"[h3, (i + 2) + 1 <= i + 3], "LinearArithmetic",
			"Have"[h6, ((i + 3) + 2) + 1 <= i + 6], "LinearArithmetic",
			"Exact"["andIntroduction"[h, "andIntroduction"[h3, ih[(i + 3) + 2, i + 6, h6]]]]
		}
	],
	machineTheorem["pairsOfStartsOfAllBelowEqual",
		ForAll[{Typed[a, {Booleans}], Typed[i, NonNegativeIntegers]},
			"allBelowEqual"["appendantCounter"[a, i], "pairsOf"["doubleWord"[a], "startsOf"[a, i + 1]]]],
		{
			"Introduce"[a], "Induction"[a], "Introduce"[i], "Exact"["trueIntroduction"],
			"Introduce"[b, rest, ih, i], "Cases"[b],
			"Have"[cGe, i + 4 <= "appendantCounter"[rest, i + 4]], "Exact"["appendantCounterGe"[rest, i + 4]],
			"Have"[h1, i + 1 <= "appendantCounter"[rest, i + 4]], "LinearArithmetic",
			"Have"[h2, (i + 1) + 1 <= "appendantCounter"[rest, i + 4]], "LinearArithmetic",
			"Have"[h3, (i + 1) + 2 <= "appendantCounter"[rest, i + 4]], "LinearArithmetic",
			"Have"[h4, ((i + 1) + 2) + 1 <= "appendantCounter"[rest, i + 4]], "LinearArithmetic",
			"Have"[eq4, (i + 1) + 4 == (i + 4) + 1], "LinearArithmetic",
			"Change"[And[i + 1 <= "appendantCounter"[rest, i + 4], And[(i + 1) + 1 <= "appendantCounter"[rest, i + 4],
				And[(i + 1) + 2 <= "appendantCounter"[rest, i + 4], And[((i + 1) + 2) + 1 <= "appendantCounter"[rest, i + 4],
					"allBelowEqual"["appendantCounter"[rest, i + 4], "pairsOf"["doubleWord"[rest], "startsOf"[rest, (i + 1) + 4]]]]]]]],
			"Rewrite"[eq4],
			"Exact"["andIntroduction"[h1, "andIntroduction"[h2, "andIntroduction"[h3, "andIntroduction"[h4, ih[i + 4]]]]]],
			"Have"[cGe, i + 6 <= "appendantCounter"[rest, i + 6]], "Exact"["appendantCounterGe"[rest, i + 6]],
			"Have"[h1, i + 1 <= "appendantCounter"[rest, i + 6]], "LinearArithmetic",
			"Have"[h2, (i + 1) + 2 <= "appendantCounter"[rest, i + 6]], "LinearArithmetic",
			"Have"[h3, (i + 1) + 3 <= "appendantCounter"[rest, i + 6]], "LinearArithmetic",
			"Have"[h4, ((i + 1) + 3) + 2 <= "appendantCounter"[rest, i + 6]], "LinearArithmetic",
			"Have"[eq6, (i + 1) + 6 == (i + 6) + 1], "LinearArithmetic",
			"Change"[And[i + 1 <= "appendantCounter"[rest, i + 6], And[(i + 1) + 2 <= "appendantCounter"[rest, i + 6],
				And[(i + 1) + 3 <= "appendantCounter"[rest, i + 6], And[((i + 1) + 3) + 2 <= "appendantCounter"[rest, i + 6],
					"allBelowEqual"["appendantCounter"[rest, i + 6], "pairsOf"["doubleWord"[rest], "startsOf"[rest, (i + 1) + 6]]]]]]]],
			"Rewrite"[eq6],
			"Exact"["andIntroduction"[h1, "andIntroduction"[h2, "andIntroduction"[h3, "andIntroduction"[h4, ih[i + 6]]]]]]
		}
	],
	machineTheorem["xorMergePrependLeft",
		ForAll[{Typed[x, NonNegativeIntegers], Typed[y, NonNegativeIntegers], Typed[xs, {NonNegativeIntegers}], Typed[ys, {NonNegativeIntegers}]},
			Implies[x + 1 <= y, "xorMerge"[Prepend[x][xs], Prepend[y][ys]] == Prepend[x]["xorMerge"[xs, Prepend[y][ys]]]]],
		{
			"Introduce"[x, y, xs, ys, lt],
			"Have"[neq, Not[x == y]], "Introduce"[e], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"[f],
			"Change"[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, {NonNegativeIntegers}],
				InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, {NonNegativeIntegers}],
					Prepend[y]["xorMerge"[Prepend[x][xs], ys]],
					Prepend[x]["xorMerge"[xs, Prepend[y][ys]]],
					Decide[x + 1 <= y]],
				"xorMerge"[xs, ys],
				Decide[x == y]] == Prepend[x]["xorMerge"[xs, Prepend[y][ys]]]],
			"Rewrite"["decideEqualFalse"[x, y, neq]],
			"Rewrite"["decideLessEqualTrue"[x + 1, y, lt]],
			"Reflexivity"
		}
	],
	machineTheorem["xorMergePrependRight",
		ForAll[{Typed[y, NonNegativeIntegers], Typed[xs, {NonNegativeIntegers}], Typed[ys, {NonNegativeIntegers}]},
			Implies["strictlyAbove"[y, xs], "xorMerge"[xs, Prepend[y][ys]] == Prepend[y]["xorMerge"[xs, ys]]]],
		{
			"Introduce"[y, xs, ys], "Cases"[xs],
			"Introduce"[h], "Reflexivity",
			"Introduce"[x, xRest, h], "Cases"[h], "Introduce"[yx, xRestAbove],
			"Have"[neq, Not[x == y]], "Introduce"[e], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"[f],
			"Have"[nlt, Not[x + 1 <= y]], "Introduce"[e], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"[f],
			"Change"[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, {NonNegativeIntegers}],
				InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, {NonNegativeIntegers}],
					Prepend[y]["xorMerge"[Prepend[x][xRest], ys]],
					Prepend[x]["xorMerge"[xRest, Prepend[y][ys]]],
					Decide[x + 1 <= y]],
				"xorMerge"[xRest, ys],
				Decide[x == y]] == Prepend[y]["xorMerge"[Prepend[x][xRest], ys]]],
			"Rewrite"["decideEqualFalse"[x, y, neq]],
			"Rewrite"["decideLessEqualFalse"[x + 1, y, nlt]],
			"Reflexivity"
		}
	],
	(* The centerpiece XOR merge lemma: merging r2 and r1 (= r2 + 2) produces pairsOf[doubleWord[a], startsOf[a, i]]! *)
	machineTheorem["xorMergeAppendant",
		ForAll[{Typed[a, {Booleans}], Typed[i, NonNegativeIntegers]},
			"xorMerge"["encodeAppendantSnd"[a, i], "shiftUp"[2, "encodeAppendantSnd"[a, i]]] ==
				"pairsOf"["doubleWord"[a], "startsOf"[a, i]]],
		{
			"Introduce"[a], "Induction"[a], "Introduce"[i], "Reflexivity",
			"Introduce"[b, rest, ih, i], "Cases"[b],
			(* b = false: r2 = i :: (i+1) :: r2', r1 = (i+2) :: (i+3) :: r1' *)
			"Change"["xorMerge"[Prepend[i][Prepend[i + 1]["encodeAppendantSnd"[rest, i + 4]]],
				Prepend[i + 2][Prepend[(i + 1) + 2]["shiftUp"[2, "encodeAppendantSnd"[rest, i + 4]]]]] ==
				Prepend[i][Prepend[i + 1][Prepend[i + 2][Prepend[(i + 2) + 1]["pairsOf"["doubleWord"[rest], "startsOf"[rest, i + 4]]]]]]],
			"Have"[lt02, i + 1 <= i + 2], "LinearArithmetic",
			"Have"[lt12, (i + 1) + 1 <= i + 2], "LinearArithmetic",
			"Have"[h24, (i + 2) + 1 <= i + 4], "LinearArithmetic",
			"Have"[h34, ((i + 1) + 2) + 1 <= i + 4], "LinearArithmetic",
			"Have"[eq3, (i + 1) + 2 == (i + 2) + 1], "LinearArithmetic",
			"Rewrite"["xorMergePrependLeft"[i, i + 2, Prepend[i + 1]["encodeAppendantSnd"[rest, i + 4]], Prepend[(i + 1) + 2]["shiftUp"[2, "encodeAppendantSnd"[rest, i + 4]]], lt02]],
			"Rewrite"["xorMergePrependLeft"[i + 1, i + 2, "encodeAppendantSnd"[rest, i + 4], Prepend[(i + 1) + 2]["shiftUp"[2, "encodeAppendantSnd"[rest, i + 4]]], lt12]],
			"Rewrite"["xorMergePrependRight"[i + 2, "encodeAppendantSnd"[rest, i + 4], Prepend[(i + 1) + 2]["shiftUp"[2, "encodeAppendantSnd"[rest, i + 4]]], "encodeAppendantSndStrictlyAbove"[rest, i + 2, i + 4, h24]]],
			"Rewrite"["xorMergePrependRight"[(i + 1) + 2, "encodeAppendantSnd"[rest, i + 4], "shiftUp"[2, "encodeAppendantSnd"[rest, i + 4]], "encodeAppendantSndStrictlyAbove"[rest, (i + 1) + 2, i + 4, h34]]],
			"Rewrite"[ih[i + 4]],
			"Rewrite"[eq3],
			(* b = true: r2 = i :: (i+3) :: r2', r1 = (i+2) :: (i+5) :: r1' *)
			"Change"["xorMerge"[Prepend[i][Prepend[i + 3]["encodeAppendantSnd"[rest, i + 6]]],
				Prepend[i + 2][Prepend[(i + 3) + 2]["shiftUp"[2, "encodeAppendantSnd"[rest, i + 6]]]]] ==
				Prepend[i][Prepend[i + 2][Prepend[i + 3][Prepend[(i + 3) + 2]["pairsOf"["doubleWord"[rest], "startsOf"[rest, i + 6]]]]]]],
			"Have"[lt02, i + 1 <= i + 2], "LinearArithmetic",
			"Have"[h23, (i + 2) + 1 <= i + 3], "LinearArithmetic",
			"Have"[h36, (i + 3) + 1 <= i + 6], "LinearArithmetic",
			"Have"[lt35, (i + 3) + 1 <= (i + 3) + 2], "LinearArithmetic",
			"Have"[h56, ((i + 3) + 2) + 1 <= i + 6], "LinearArithmetic",
			"Rewrite"["xorMergePrependLeft"[i, i + 2, Prepend[i + 3]["encodeAppendantSnd"[rest, i + 6]], Prepend[(i + 3) + 2]["shiftUp"[2, "encodeAppendantSnd"[rest, i + 6]]], lt02]],
			"Rewrite"["xorMergePrependRight"[i + 2, Prepend[i + 3]["encodeAppendantSnd"[rest, i + 6]], Prepend[(i + 3) + 2]["shiftUp"[2, "encodeAppendantSnd"[rest, i + 6]]],
				"andIntroduction"[h23, "encodeAppendantSndStrictlyAbove"[rest, i + 3, i + 6, h36]]]],
			"Rewrite"["xorMergePrependLeft"[i + 3, (i + 3) + 2, "encodeAppendantSnd"[rest, i + 6], "shiftUp"[2, "encodeAppendantSnd"[rest, i + 6]], lt35]],
			"Rewrite"["xorMergePrependRight"[(i + 3) + 2, "encodeAppendantSnd"[rest, i + 6], "shiftUp"[2, "encodeAppendantSnd"[rest, i + 6]], "encodeAppendantSndStrictlyAbove"[rest, (i + 3) + 2, i + 6, h56]]],
			"Rewrite"[ih[i + 6]]
		}
	],
	machineTheorem["shiftDownJoin",
		ForAll[{Typed[d, NonNegativeIntegers], Typed[xs, {NonNegativeIntegers}], Typed[ys, {NonNegativeIntegers}]},
			"shiftDown"[d, Join[xs, ys]] == Join["shiftDown"[d, xs], "shiftDown"[d, ys]]],
		{"Introduce"[d, xs, ys], "Exact"["mapJoin"[Function[{Typed[x, NonNegativeIntegers]}, Subtract[x, d]], xs, ys]]}
	],
	machineTheorem["shiftDownShiftUpGe",
		ForAll[{Typed[d1, NonNegativeIntegers], Typed[d2, NonNegativeIntegers], Typed[xs, {NonNegativeIntegers}]},
			Implies[d2 <= d1, "shiftDown"[d2, "shiftUp"[d1, xs]] == "shiftUp"[Subtract[d1, d2], xs]]],
		{
			"Introduce"[d1, d2, xs, le],
			"Cases"["lessEqualExists"[d2, d1, le]], "Introduce"[k, eq],
			"Rewrite"[eq],
			"Rewrite"["additionSubtractionCancellation"[k, d2]],
			"Rewrite"["equalitySymmetry"["shiftUpAdd"[d2, k, xs]]],
			"Exact"["shiftDownShiftUp"[d2, "shiftUp"[k, xs]]]
		}
	],
	machineTheorem["startsOfShiftDown",
		ForAll[{Typed[a, {Booleans}], Typed[i, NonNegativeIntegers], Typed[d, NonNegativeIntegers]},
			Implies[d <= i, "shiftDown"[d, "startsOf"[a, i]] == "startsOf"[a, Subtract[i, d]]]],
		{
			"Introduce"[a], "Induction"[a], "Introduce"[i, d, le], "Reflexivity",
			"Introduce"[b, rest, ih, i, d, le],
			"Cases"["lessEqualExists"[d, i, le]], "Introduce"[k, eq],
			"Rewrite"[eq], "Rewrite"["additionSubtractionCancellation"[k, d]],
			"Cases"[b],
			"Change"[Prepend[Subtract[k + d, d]][Prepend[Subtract[(k + d) + 2, d]]["shiftDown"[d, "startsOf"[rest, (k + d) + 4]]]] ==
				Prepend[k][Prepend[k + 2]["startsOf"[rest, k + 4]]]],
			"Have"[e2, (k + d) + 2 == (k + 2) + d], "LinearArithmetic",
			"Have"[e4, (k + d) + 4 == (k + 4) + d], "LinearArithmetic",
			"Have"[le4, d <= (k + 4) + d], "LinearArithmetic",
			"Rewrite"["additionSubtractionCancellation"[k, d]],
			"Rewrite"[e2], "Rewrite"["additionSubtractionCancellation"[k + 2, d]],
			"Rewrite"[e4], "Rewrite"[ih[(k + 4) + d, d, le4]], "Rewrite"["additionSubtractionCancellation"[k + 4, d]],
			"Change"[Prepend[Subtract[k + d, d]][Prepend[Subtract[(k + d) + 3, d]]["shiftDown"[d, "startsOf"[rest, (k + d) + 6]]]] ==
				Prepend[k][Prepend[k + 3]["startsOf"[rest, k + 6]]]],
			"Have"[e3, (k + d) + 3 == (k + 3) + d], "LinearArithmetic",
			"Have"[e6, (k + d) + 6 == (k + 6) + d], "LinearArithmetic",
			"Have"[le6, d <= (k + 6) + d], "LinearArithmetic",
			"Rewrite"["additionSubtractionCancellation"[k, d]],
			"Rewrite"[e3], "Rewrite"["additionSubtractionCancellation"[k + 3, d]],
			"Rewrite"[e6], "Rewrite"[ih[(k + 6) + d, d, le6]], "Rewrite"["additionSubtractionCancellation"[k + 6, d]]
		}
	],
	(* cycleAppendants & ruleBlocks *)
	TypeTheoryDefinition["cycleAppendants", Typed[
		Function[{Typed[as, {{Booleans}}], Typed[m, NonNegativeIntegers]},
			InductiveRecursor[NonNegativeIntegers][Function[{Typed[q, NonNegativeIntegers]}, {{Booleans}} -> {{Booleans}}],
				Function[{Typed[x, {{Booleans}}]}, Typed[{}, {{Booleans}}]],
				Function[{Typed[k, NonNegativeIntegers], Typed[previous, {{Booleans}} -> {{Booleans}}]},
					Function[{Typed[x, {{Booleans}}]},
						InductiveRecursor[List][Function[{Typed[q, {{Booleans}}]}, {{Booleans}}], Typed[{}, {{Booleans}}],
							Function[{Typed[a, {Booleans}], Typed[rest, {{Booleans}}], Typed[u, {{Booleans}}]},
								Prepend[a][previous[Join[rest, {a}]]]], x]]], m][as]],
		{{Booleans}} -> NonNegativeIntegers -> {{Booleans}}
	]],
	TypeTheoryDefinition["ruleBlocks", Typed[
		Function[{Typed[ws, {{Booleans}}]},
			InductiveRecursor[List][Function[{Typed[q, {{Booleans}}]}, NonNegativeIntegers -> {{NonNegativeIntegers}}],
				Function[{Typed[i, NonNegativeIntegers]}, Typed[{}, {{NonNegativeIntegers}}]],
				Function[{Typed[a, {Booleans}], Typed[rest, {{Booleans}}], Typed[previous, NonNegativeIntegers -> {{NonNegativeIntegers}}]},
					Function[{Typed[i, NonNegativeIntegers]},
						Prepend["shiftUp"[2, "encodeAppendantSnd"[a, i]]][
							Prepend["encodeAppendantSnd"[a, i]][
								Prepend[Typed[{}, {NonNegativeIntegers}]][
									Prepend[Typed[{}, {NonNegativeIntegers}]][
										previous["appendantCounter"[a, i]]]]]]]], ws]],
		{{Booleans}} -> NonNegativeIntegers -> {{NonNegativeIntegers}}
	]],
	machineTheorem["ruleBlocksShift",
		ForAll[{Typed[ws, {{Booleans}}], Typed[i, NonNegativeIntegers], Typed[d, NonNegativeIntegers]},
			"shiftUpRules"[d, "ruleBlocks"[ws, i]] == "ruleBlocks"[ws, i + d]],
		{
			"Introduce"[ws], "Induction"[ws], "Introduce"[i, d], "Reflexivity",
			"Introduce"[a, rest, ih, i, d],
			"Change"[Prepend["shiftUp"[d, "shiftUp"[2, "encodeAppendantSnd"[a, i]]]][
				Prepend["shiftUp"[d, "encodeAppendantSnd"[a, i]]][
					Prepend[Typed[{}, {NonNegativeIntegers}]][
						Prepend[Typed[{}, {NonNegativeIntegers}]][
							"shiftUpRules"[d, "ruleBlocks"[rest, "appendantCounter"[a, i]]]]]]] ==
				Prepend["shiftUp"[2, "encodeAppendantSnd"[a, i + d]]][
					Prepend["encodeAppendantSnd"[a, i + d]][
						Prepend[Typed[{}, {NonNegativeIntegers}]][
							Prepend[Typed[{}, {NonNegativeIntegers}]][
								"ruleBlocks"[rest, "appendantCounter"[a, i + d]]]]]]],
			"Rewrite"["shiftUpAdd"[d, 2, "encodeAppendantSnd"[a, i]]],
			"Have"[comm2, 2 + d == d + 2], "LinearArithmetic",
			"Rewrite"[comm2],
			"Rewrite"["equalitySymmetry"["shiftUpAdd"[2, d, "encodeAppendantSnd"[a, i]]]],
			"Rewrite"["encodeAppendantSndShift"[a, i, d]],
			"Rewrite"[ih["appendantCounter"[a, i], d]],
			"Rewrite"["appendantCounterShift"[a, i, d]]
		}
	],
	TypeTheoryDefinition["allRulesStrictlyAbove", Typed[
		Function[{Typed[lo, NonNegativeIntegers], Typed[rs, {{NonNegativeIntegers}}]},
			InductiveRecursor[List][Function[{Typed[q, {{NonNegativeIntegers}}]}, TypeUniverse[0]], True,
				Function[{Typed[r, {NonNegativeIntegers}], Typed[rest, {{NonNegativeIntegers}}], Typed[previous, TypeUniverse[0]]},
					And["strictlyAbove"[lo, r], previous]], rs]],
		NonNegativeIntegers -> {{NonNegativeIntegers}} -> TypeUniverse[0]
	]],
	machineTheorem["ruleBlocksStrictlyAbove",
		ForAll[{Typed[ws, {{Booleans}}], Typed[lo, NonNegativeIntegers], Typed[i, NonNegativeIntegers]},
			Implies[lo + 1 <= i, "allRulesStrictlyAbove"[lo, "ruleBlocks"[ws, i]]]],
		{
			"Introduce"[ws], "Induction"[ws], "Introduce"[lo, i, h], "Exact"["trueIntroduction"],
			"Introduce"[a, rest, ih, lo, i, h],
			"Have"[h2, lo + 1 <= i + 2], "LinearArithmetic",
			"Have"[r1Eq, "shiftUp"[2, "encodeAppendantSnd"[a, i]] == "encodeAppendantSnd"[a, i + 2]],
			"Exact"["encodeAppendantSndShift"[a, i, 2]],
			"Have"[hR1, "strictlyAbove"[lo, "shiftUp"[2, "encodeAppendantSnd"[a, i]]]],
			"Rewrite"[r1Eq], "Exact"["encodeAppendantSndStrictlyAbove"[a, lo, i + 2, h2]],
			"Have"[cGe, i <= "appendantCounter"[a, i]], "Exact"["appendantCounterGe"[a, i]],
			"Have"[hNext, lo + 1 <= "appendantCounter"[a, i]], "LinearArithmetic",
			"Exact"["andIntroduction"[hR1, "andIntroduction"["encodeAppendantSndStrictlyAbove"[a, lo, i, h],
				"andIntroduction"["trueIntroduction", "andIntroduction"["trueIntroduction", ih[lo, "appendantCounter"[a, i], hNext]]]]]]
		}
	],
	(* decodeBag with strict-increase-above-0 vacuity guard (Turing's review) *)
	TypeTheoryDefinition["decodeBagFrom", Typed[
		Function[{Typed[bag, {NonNegativeIntegers}]},
			InductiveRecursor[List][Function[{Typed[q, {NonNegativeIntegers}]}, NonNegativeIntegers -> Option[NonNegativeIntegers] -> Option[{Booleans}]],
				Function[{Typed[lo, NonNegativeIntegers], Typed[pending, Option[NonNegativeIntegers]]},
					InductiveRecursor[Option][Function[{Typed[q, Option[NonNegativeIntegers]]}, Option[{Booleans}]],
						"some"[Typed[{}, {Booleans}]],
						Function[{Typed[x, NonNegativeIntegers]}, Typed["none", Option[{Booleans}]]],
						pending]],
				Function[{Typed[y, NonNegativeIntegers], Typed[rest, {NonNegativeIntegers}], Typed[previous, NonNegativeIntegers -> Option[NonNegativeIntegers] -> Option[{Booleans}]]},
					Function[{Typed[lo, NonNegativeIntegers], Typed[pending, Option[NonNegativeIntegers]]},
						InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Option[{Booleans}]],
							Typed["none", Option[{Booleans}]],
							InductiveRecursor[Option][Function[{Typed[q, Option[NonNegativeIntegers]]}, Option[{Booleans}]],
								previous[y, "some"[y]],
								Function[{Typed[x, NonNegativeIntegers]},
									InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Option[{Booleans}]],
										InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Option[{Booleans}]],
											Typed["none", Option[{Booleans}]],
											InductiveRecursor[Option][Function[{Typed[q, Option[{Booleans}]]}, Option[{Booleans}]],
												Typed["none", Option[{Booleans}]],
												Function[{Typed[bits, {Booleans}]}, "some"[Prepend["true"][bits]]],
												previous[y, Typed["none", Option[NonNegativeIntegers]]]],
											Decide[y == x + 2]],
										InductiveRecursor[Option][Function[{Typed[q, Option[{Booleans}]]}, Option[{Booleans}]],
											Typed["none", Option[{Booleans}]],
											Function[{Typed[bits, {Booleans}]}, "some"[Prepend["false"][bits]]],
											previous[y, Typed["none", Option[NonNegativeIntegers]]]],
										Decide[y == x + 1]]],
								pending],
							Decide[lo + 1 <= y]]]],
				bag]],
		{NonNegativeIntegers} -> NonNegativeIntegers -> Option[NonNegativeIntegers] -> Option[{Booleans}]
	]],
	TypeTheoryDefinition["decodeBag", Typed[
		Function[{Typed[bag, {NonNegativeIntegers}]}, "decodeBagFrom"[bag, 0, Typed["none", Option[NonNegativeIntegers]]]],
		{NonNegativeIntegers} -> Option[{Booleans}]
	]],
	machineTheorem["decodeBagPairsOf",
		ForAll[{Typed[w, {Booleans}], Typed[lo, NonNegativeIntegers], Typed[a, {NonNegativeIntegers}]},
			Implies["pairsAsc"[lo, w, a], "decodeBagFrom"["pairsOf"[w, a], lo, Typed["none", Option[NonNegativeIntegers]]] == "some"[w]]],
		{
			"Introduce"[w], "Induction"[w],
			"Introduce"[lo, a, h], "Reflexivity",
			"Introduce"[b, wRest, ih, lo, a, h], "Cases"[a],
			"Introduce"[h], "Exact"["falseElimination"[h]],
			"Introduce"[x, aRest, h], "Cases"[h], "Introduce"[hx, hrest],
			"Cases"[b],
			"Introduce"[hrest],
			"Have"[h1, x + 1 <= x + 1], "LinearArithmetic",
			"Change"[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Option[{Booleans}]],
				Typed["none", Option[{Booleans}]],
				InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Option[{Booleans}]],
					Typed["none", Option[{Booleans}]],
					InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Option[{Booleans}]],
						InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Option[{Booleans}]],
							Typed["none", Option[{Booleans}]],
							InductiveRecursor[Option][Function[{Typed[q, Option[{Booleans}]]}, Option[{Booleans}]],
								Typed["none", Option[{Booleans}]],
								Function[{Typed[bits, {Booleans}]}, "some"[Prepend["true"][bits]]],
								"decodeBagFrom"["pairsOf"[wRest, aRest], x + 1, Typed["none", Option[NonNegativeIntegers]]]],
							Decide[x + 1 == x + 2]],
						InductiveRecursor[Option][Function[{Typed[q, Option[{Booleans}]]}, Option[{Booleans}]],
							Typed["none", Option[{Booleans}]],
							Function[{Typed[bits, {Booleans}]}, "some"[Prepend["false"][bits]]],
							"decodeBagFrom"["pairsOf"[wRest, aRest], x + 1, Typed["none", Option[NonNegativeIntegers]]]],
						Decide[x + 1 == x + 1]],
					Decide[x + 1 <= x + 1]],
				Decide[lo + 1 <= x]] == "some"[Prepend["false"][wRest]]],
			"Rewrite"["decideLessEqualTrue"[lo + 1, x, hx]],
			"Rewrite"["decideLessEqualTrue"[x + 1, x + 1, h1]],
			"Rewrite"["decideEqualTrue"[x + 1, x + 1, "equalityReflexivity"[x + 1]]],
			"Change"[InductiveRecursor[Option][Function[{Typed[q, Option[{Booleans}]]}, Option[{Booleans}]],
				Typed["none", Option[{Booleans}]],
				Function[{Typed[bits, {Booleans}]}, "some"[Prepend["false"][bits]]],
				"decodeBagFrom"["pairsOf"[wRest, aRest], x + 1, Typed["none", Option[NonNegativeIntegers]]]] == "some"[Prepend["false"][wRest]]],
			"Rewrite"[ih[x + 1, aRest, hrest]], "Reflexivity",
			"Introduce"[hrest],
			"Have"[h2, x + 1 <= x + 2], "LinearArithmetic",
			"Have"[neq21, Not[x + 2 == x + 1]], "Introduce"[e], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"[f],
			"Change"[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Option[{Booleans}]],
				Typed["none", Option[{Booleans}]],
				InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Option[{Booleans}]],
					Typed["none", Option[{Booleans}]],
					InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Option[{Booleans}]],
						InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Option[{Booleans}]],
							Typed["none", Option[{Booleans}]],
							InductiveRecursor[Option][Function[{Typed[q, Option[{Booleans}]]}, Option[{Booleans}]],
								Typed["none", Option[{Booleans}]],
								Function[{Typed[bits, {Booleans}]}, "some"[Prepend["true"][bits]]],
								"decodeBagFrom"["pairsOf"[wRest, aRest], x + 2, Typed["none", Option[NonNegativeIntegers]]]],
							Decide[x + 2 == x + 2]],
						InductiveRecursor[Option][Function[{Typed[q, Option[{Booleans}]]}, Option[{Booleans}]],
							Typed["none", Option[{Booleans}]],
							Function[{Typed[bits, {Booleans}]}, "some"[Prepend["false"][bits]]],
							"decodeBagFrom"["pairsOf"[wRest, aRest], x + 2, Typed["none", Option[NonNegativeIntegers]]]],
						Decide[x + 2 == x + 1]],
					Decide[x + 1 <= x + 2]],
				Decide[lo + 1 <= x]] == "some"[Prepend["true"][wRest]]],
			"Rewrite"["decideLessEqualTrue"[lo + 1, x, hx]],
			"Rewrite"["decideLessEqualTrue"[x + 1, x + 2, h2]],
			"Rewrite"["decideEqualFalse"[x + 2, x + 1, neq21]],
			"Rewrite"["decideEqualTrue"[x + 2, x + 2, "equalityReflexivity"[x + 2]]],
			"Change"[InductiveRecursor[Option][Function[{Typed[q, Option[{Booleans}]]}, Option[{Booleans}]],
				Typed["none", Option[{Booleans}]],
				Function[{Typed[bits, {Booleans}]}, "some"[Prepend["true"][bits]]],
				"decodeBagFrom"["pairsOf"[wRest, aRest], x + 2, Typed["none", Option[NonNegativeIntegers]]]] == "some"[Prepend["true"][wRest]]],
			"Rewrite"[ih[x + 2, aRest, hrest]], "Reflexivity"
		}
	],
	(* Fueled cyclic tag configuration, representation relation, and encoder *)
	TypeTheoryInductiveType["FueledCyclicTag", TypeUniverse[1], {
		"fueledCyclicTag" -> ForAll[{Typed[config, "CyclicTagConfiguration"], Typed[budget, NonNegativeIntegers]}, "FueledCyclicTag"]
	}],
	TypeTheoryDefinition["fueledCyclicTagStep", Typed[
		Function[{Typed[fc, "FueledCyclicTag"]},
			InductiveRecursor["FueledCyclicTag"][Function[{Typed[q, "FueledCyclicTag"]}, Option["FueledCyclicTag"]],
				Function[{Typed[cfg, "CyclicTagConfiguration"], Typed[budget, NonNegativeIntegers]},
					InductiveRecursor[NonNegativeIntegers][Function[{Typed[q, NonNegativeIntegers]}, Option["FueledCyclicTag"]],
						Typed["none", Option["FueledCyclicTag"]],
						Function[{Typed[n, NonNegativeIntegers], Typed[unused, Option["FueledCyclicTag"]]},
							"optionMap"[Function[{Typed[c2, "CyclicTagConfiguration"]}, "fueledCyclicTag"[c2, n]], "cyclicTagStep"[cfg]]],
						budget]],
				fc]],
		"FueledCyclicTag" -> Option["FueledCyclicTag"]
	]],
	TypeTheoryDefinition["system5Represents", Typed[
		Function[{Typed[fc, "FueledCyclicTag"], Typed[s, "System5Configuration"]},
			And[
				Exists[{Typed[starts, {NonNegativeIntegers}]},
					And["pairsAsc"[0, "doubleWord"[fc[["config"]][["data"]]], starts],
						s[["bag"]] == "pairsOf"["doubleWord"[fc[["config"]][["data"]]], starts]]],
				Exists[{Typed[k, NonNegativeIntegers]},
					And["allBelowEqual"[k, s[["bag"]]],
						s[["rules"]] == "ruleBlocks"["cycleAppendants"[fc[["config"]][["appendants"]], fc[["budget"]]], k + 3]]]
			]],
		"FueledCyclicTag" -> "System5Configuration" -> TypeUniverse[0]
	]],
	TypeTheoryDefinition["ctsToSystem5", Typed[
		Function[{Typed[cfg, "CyclicTagConfiguration"], Typed[budget, NonNegativeIntegers]},
			"system5Configuration"[
				"pairsOf"["doubleWord"[cfg[["data"]]], "startsOf"[cfg[["data"]], 1]],
				"ruleBlocks"["cycleAppendants"[cfg[["appendants"]], budget], "appendantCounter"[cfg[["data"]], 0] + 3]
			]],
		"CyclicTagConfiguration" -> NonNegativeIntegers -> "System5Configuration"
	]],
	(* Direct properties: encoder represents, decode, terminal, rules empty, bag non-empty, encoder invariants *)
	machineTheorem["ctsToSystem5Represents",
		ForAll[{Typed[cfg, "CyclicTagConfiguration"], Typed[budget, NonNegativeIntegers]},
			"system5Represents"["fueledCyclicTag"[cfg, budget], "ctsToSystem5"[cfg, budget]]],
		{
			"Introduce"[cfg, budget],
			"Have"[h01, 0 + 1 <= 1], "LinearArithmetic",
			"Exact"["andIntroduction"[
				"existsIntroduction"["startsOf"[cfg[["data"]], 1],
					"andIntroduction"["pairsAscStartsOf"[cfg[["data"]], 0, 1, h01],
						"equalityReflexivity"["pairsOf"["doubleWord"[cfg[["data"]]], "startsOf"[cfg[["data"]], 1]]]]],
				"existsIntroduction"["appendantCounter"[cfg[["data"]], 0],
					"andIntroduction"["pairsOfStartsOfAllBelowEqual"[cfg[["data"]], 0],
						"equalityReflexivity"["ruleBlocks"["cycleAppendants"[cfg[["appendants"]], budget], "appendantCounter"[cfg[["data"]], 0] + 3]]]]]]
		}
	],
	machineTheorem["ctsToSystem5BagStrictlyAbove",
		ForAll[{Typed[cfg, "CyclicTagConfiguration"], Typed[budget, NonNegativeIntegers]},
			"strictlyAbove"[0, "ctsToSystem5"[cfg, budget][["bag"]]]],
		{
			"Introduce"[cfg, budget],
			"Have"[h01, 0 + 1 <= 1], "LinearArithmetic",
			"Exact"["pairsOfStrictlyAbove"["doubleWord"[cfg[["data"]]], 0, "startsOf"[cfg[["data"]], 1], "pairsAscStartsOf"[cfg[["data"]], 0, 1, h01]]]
		}
	],
	machineTheorem["ctsToSystem5RulesStrictlyAbove",
		ForAll[{Typed[cfg, "CyclicTagConfiguration"], Typed[budget, NonNegativeIntegers]},
			"allRulesStrictlyAbove"[0, "ctsToSystem5"[cfg, budget][["rules"]]]],
		{
			"Introduce"[cfg, budget],
			"Have"[h03, 0 + 1 <= "appendantCounter"[cfg[["data"]], 0] + 3], "LinearArithmetic",
			"Exact"["ruleBlocksStrictlyAbove"["cycleAppendants"[cfg[["appendants"]], budget], 0, "appendantCounter"[cfg[["data"]], 0] + 3, h03]]
		}
	],
	machineTheorem["representsDecode",
		ForAll[{Typed[fc, "FueledCyclicTag"], Typed[s, "System5Configuration"]},
			Implies["system5Represents"[fc, s], "decodeBag"[s[["bag"]]] == "some"["doubleWord"[fc[["config"]][["data"]]]]]],
		{
			"Introduce"[fc, s, rep], "Cases"[rep], "Introduce"[bagPart, rulesPart],
			"Cases"[bagPart], "Introduce"[starts, both], "Cases"[both], "Introduce"[asc, eqBag],
			"Rewrite"[eqBag],
			"Exact"["decodeBagPairsOf"["doubleWord"[fc[["config"]][["data"]]], 0, starts, asc]]
		}
	],
	machineTheorem["representsRulesEmpty",
		ForAll[{Typed[cfg, "CyclicTagConfiguration"], Typed[s, "System5Configuration"]},
			Implies["system5Represents"["fueledCyclicTag"[cfg, 0], s], s[["rules"]] == Typed[{}, {{NonNegativeIntegers}}]]],
		{
			"Introduce"[cfg, s, rep], "Cases"[rep], "Introduce"[bagPart, rulesPart],
			"Cases"[rulesPart], "Introduce"[k, both], "Cases"[both], "Introduce"[bound, eqRules],
			"Exact"[eqRules]
		}
	],
	machineTheorem["representsBagNonEmpty",
		ForAll[{Typed[fc, "FueledCyclicTag"], Typed[s, "System5Configuration"]},
			Implies["system5Represents"[fc, s], Implies[Not[fc[["config"]][["data"]] == Typed[{}, {Booleans}]], Not[s[["bag"]] == Typed[{}, {NonNegativeIntegers}]]]]],
		{
			"Introduce"[fc, s], "Cases"[fc], "Introduce"[cfg, budget], "Cases"[cfg], "Introduce"[data, as],
			"Cases"[data],
			"Introduce"[rep, nonEmptyData, emptyBag], "Exact"[nonEmptyData["equalityReflexivity"[Typed[{}, {Booleans}]]]],
			"Introduce"[b, wRest, rep, nonEmptyData, emptyBag],
			"Cases"[rep], "Introduce"[bagPart, rulesPart],
			"Cases"[bagPart], "Introduce"[starts, both], "Cases"[both], "Introduce"[asc, eqBag],
			"Cases"[starts], "Introduce"[asc, eqBag], "Exact"[asc],
			"Introduce"[x, sRest, asc, eqBag],
			"Have"[bad, Prepend[x][Prepend[x + "bitGap"[b]]["pairsOf"[Prepend[b]["doubleWord"[wRest]], sRest]]] == Typed[{}, {NonNegativeIntegers}]],
			"Exact"["equalityTransitivity"["equalitySymmetry"[eqBag], emptyBag]],
			"Exact"[Construct["equalitySubstitution", {NonNegativeIntegers},
				Function[{Typed[l, {NonNegativeIntegers}]}, InductiveRecursor[List][Function[{Typed[q, {NonNegativeIntegers}]}, TypeUniverse[0]], False, Function[{Typed[h, NonNegativeIntegers], Typed[t, {NonNegativeIntegers}], Typed[u, TypeUniverse[0]]}, True], l]],
				Prepend[x][Prepend[x + "bitGap"[b]]["pairsOf"[Prepend[b]["doubleWord"[wRest]], sRest]]],
				Typed[{}, {NonNegativeIntegers}], bad, "trueIntroduction"]]
		}
	],
	machineTheorem["representsTerminal",
		ForAll[{Typed[cfg, "CyclicTagConfiguration"], Typed[s, "System5Configuration"]},
			Implies["system5Represents"["fueledCyclicTag"[cfg, 0], s], "system5Step"[s] == Typed["none", Option["System5Configuration"]]]],
		{
			"Introduce"[cfg, s], "Cases"[s], "Introduce"[bag, rules, rep],
			"Have"[emptyRules, rules == Typed[{}, {{NonNegativeIntegers}}]],
			"Exact"["representsRulesEmpty"[cfg, "system5Configuration"[bag, rules], rep]],
			"Rewrite"[emptyRules],
			"Cases"[bag], "Introduce"[rep1], "Reflexivity", "Introduce"[b, rest, rep2], "Reflexivity"
		}
	],
	machineTheorem["system5RunThenPopEmpty",
		ForAll[{Typed[j, NonNegativeIntegers], Typed[rest, {NonNegativeIntegers}], Typed[rs, {{NonNegativeIntegers}}]},
			"steps"["system5Step", j + 1, "system5Configuration"[Prepend[j + 1][rest], Prepend[Typed[{}, {NonNegativeIntegers}]][rs]]] ==
				"some"["system5Configuration"["shiftDown"[j + 1, rest], "shiftUpRules"[j + 1, rs]]]],
		{
			"Introduce"[j, rest, rs],
			"Rewrite"["system5RunThenPop"[j, rest, Typed[{}, {NonNegativeIntegers}], rs]],
			"Change"["some"["system5Configuration"["xorMerge"["shiftDown"[j + 1, rest], Typed[{}, {NonNegativeIntegers}]], "shiftUpRules"[j + 1, rs]]] ==
				"some"["system5Configuration"["shiftDown"[j + 1, rest], "shiftUpRules"[j + 1, rs]]]],
			"Rewrite"["xorMergeEmptyRight"["shiftDown"[j + 1, rest]]]
		}
	],
	machineTheorem["appendantCounterMonotonic",
		ForAll[{Typed[a, {Booleans}], Typed[i1, NonNegativeIntegers], Typed[i2, NonNegativeIntegers]},
			Implies[i1 <= i2, "appendantCounter"[a, i1] <= "appendantCounter"[a, i2]]],
		{
			"Introduce"[a, i1, i2, le],
			"Cases"["lessEqualExistsRight"[i1, i2, le]], "Introduce"[d, eq],
			"Rewrite"[eq],
			"Rewrite"["appendantCounterShift"[a, i1, d]],
			"LinearArithmetic"
		}
	],
	(* One CTS step with head bit false: x2 + 1 System 5 steps (4 rule pops), cancelling rule 1 with rule 2 *)
	machineTheorem["representsStepFalse",
		ForAll[
			{
				Typed[w, {Booleans}], Typed[a, {Booleans}], Typed[tailWs, {{Booleans}}],
				Typed[x1, NonNegativeIntegers], Typed[x2, NonNegativeIntegers], Typed[restStarts, {NonNegativeIntegers}],
				Typed[k, NonNegativeIntegers]
			},
			Implies[1 <= x1, Implies[x1 + 2 <= x2, Implies["pairsAsc"[x2 + 1, "doubleWord"[w], restStarts],
				Implies["allBelowEqual"[k, Prepend[x1][Prepend[x1 + 1][Prepend[x2][Prepend[x2 + 1]["pairsOf"["doubleWord"[w], restStarts]]]]]],
					And[
						"steps"["system5Step", x2 + 1, "system5Configuration"[
							Prepend[x1][Prepend[x1 + 1][Prepend[x2][Prepend[x2 + 1]["pairsOf"["doubleWord"[w], restStarts]]]]],
							"ruleBlocks"[Prepend[a][tailWs], k + 3]]] ==
							"some"["system5Configuration"[
								"pairsOf"["doubleWord"[w], "shiftDown"[x2 + 1, restStarts]],
								"ruleBlocks"[tailWs, ("appendantCounter"[a, k] + (x2 + 1)) + 3]]],
						And[
							"pairsAsc"[0, "doubleWord"[w], "shiftDown"[x2 + 1, restStarts]],
							"allBelowEqual"["appendantCounter"[a, k] + (x2 + 1), "pairsOf"["doubleWord"[w], "shiftDown"[x2 + 1, restStarts]]]
						]
					]]]]]
		],
		{
			"Introduce"[w, a, tailWs, x1, x2, restStarts, k, hx1, hx12, hAsc, hBound],
			"Cases"[hBound], "Introduce"[x1Le, hB1], "Cases"[hB1], "Introduce"[x1pLe, hB2],
			"Cases"[hB2], "Introduce"[x2Le, hB3], "Cases"[hB3], "Introduce"[x2pLe, hRestBound],
			"Cases"["lessEqualExists"[1, x1, hx1]], "Introduce"[d1, eqX1],
			"Cases"["lessEqualExists"[x1 + 2, x2, hx12]], "Introduce"[d3, eqX2],
			(* Pop 1: d1 + 1 (= x1) steps *)
			"Have"[pop1, "steps"["system5Step", d1 + 1, "system5Configuration"[
				Prepend[d1 + 1][Prepend[x1 + 1][Prepend[x2][Prepend[x2 + 1]["pairsOf"["doubleWord"[w], restStarts]]]]],
				"ruleBlocks"[Prepend[a][tailWs], k + 3]]] ==
				"some"["system5Configuration"[
					Join[Prepend[1][Prepend[d3 + 2][Prepend[d3 + 3]["shiftDown"[d1 + 1, "pairsOf"["doubleWord"[w], restStarts]]]]],
						"shiftUp"[(d1 + 1) + 2, "encodeAppendantSnd"[a, k + 3]]],
					Prepend["shiftUp"[d1 + 1, "encodeAppendantSnd"[a, k + 3]]][
						Prepend[Typed[{}, {NonNegativeIntegers}]][
							Prepend[Typed[{}, {NonNegativeIntegers}]][
								"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + (d1 + 1)]]]]]]],
			"Change"["steps"["system5Step", d1 + 1, "system5Configuration"[
				Prepend[d1 + 1][Prepend[x1 + 1][Prepend[x2][Prepend[x2 + 1]["pairsOf"["doubleWord"[w], restStarts]]]]],
				Prepend["shiftUp"[2, "encodeAppendantSnd"[a, k + 3]]][
					Prepend["encodeAppendantSnd"[a, k + 3]][
						Prepend[Typed[{}, {NonNegativeIntegers}]][
							Prepend[Typed[{}, {NonNegativeIntegers}]][
								"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3]]]]]]]] ==
				"some"["system5Configuration"[
					Join[Prepend[1][Prepend[d3 + 2][Prepend[d3 + 3]["shiftDown"[d1 + 1, "pairsOf"["doubleWord"[w], restStarts]]]]],
						"shiftUp"[(d1 + 1) + 2, "encodeAppendantSnd"[a, k + 3]]],
					Prepend["shiftUp"[d1 + 1, "encodeAppendantSnd"[a, k + 3]]][
						Prepend[Typed[{}, {NonNegativeIntegers}]][
							Prepend[Typed[{}, {NonNegativeIntegers}]][
								"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + (d1 + 1)]]]]]]],
			"Rewrite"["system5RunThenPop"[d1,
				Prepend[x1 + 1][Prepend[x2][Prepend[x2 + 1]["pairsOf"["doubleWord"[w], restStarts]]]],
				"shiftUp"[2, "encodeAppendantSnd"[a, k + 3]],
				Prepend["encodeAppendantSnd"[a, k + 3]][Prepend[Typed[{}, {NonNegativeIntegers}]][Prepend[Typed[{}, {NonNegativeIntegers}]]["ruleBlocks"[tailWs, "appendantCounter"[a, k + 3]]]]]]],
			"Have"[s1, Subtract[x1 + 1, d1 + 1] == 1],
			"Rewrite"[eqX1], "Have"[t1, (d1 + 1) + 1 == 1 + (d1 + 1)], "LinearArithmetic", "Rewrite"[t1], "Exact"["additionSubtractionCancellation"[1, d1 + 1]],
			"Have"[s2, Subtract[x2, d1 + 1] == d3 + 2],
			"Rewrite"[eqX2], "Rewrite"[eqX1], "Have"[t2, d3 + ((d1 + 1) + 2) == (d3 + 2) + (d1 + 1)], "LinearArithmetic", "Rewrite"[t2], "Exact"["additionSubtractionCancellation"[d3 + 2, d1 + 1]],
			"Have"[s3, Subtract[x2 + 1, d1 + 1] == d3 + 3],
			"Rewrite"[eqX2], "Rewrite"[eqX1], "Have"[t3, (d3 + ((d1 + 1) + 2)) + 1 == (d3 + 3) + (d1 + 1)], "LinearArithmetic", "Rewrite"[t3], "Exact"["additionSubtractionCancellation"[d3 + 3, d1 + 1]],
			"Have"[allLow1, "allBelowEqual"[k, Prepend[1][Prepend[d3 + 2][Prepend[d3 + 3]["shiftDown"[d1 + 1, "pairsOf"["doubleWord"[w], restStarts]]]]]]],
			"Have"[le1k, 1 <= k], "LinearArithmetic",
			"Have"[le2k, d3 + 2 <= k], "LinearArithmetic",
			"Have"[le3k, d3 + 3 <= k], "LinearArithmetic",
			"Have"[leRestK, "allBelowEqual"[k + (d1 + 1), "pairsOf"["doubleWord"[w], restStarts]]],
			"Have"[kk, k <= k + (d1 + 1)], "LinearArithmetic", "Exact"["allBelowEqualWeaken"[k, k + (d1 + 1), "pairsOf"["doubleWord"[w], restStarts], kk, hRestBound]],
			"Exact"["andIntroduction"[le1k, "andIntroduction"[le2k, "andIntroduction"[le3k, "shiftDownAllBelowEqual"["pairsOf"["doubleWord"[w], restStarts], d1 + 1, k, leRestK]]]]],
			"Have"[r1High, "strictlyAbove"[k, "shiftUp"[(d1 + 1) + 2, "encodeAppendantSnd"[a, k + 3]]]],
			"Rewrite"["encodeAppendantSndShift"[a, k + 3, (d1 + 1) + 2]],
			"Have"[hk1, k + 1 <= (k + 3) + ((d1 + 1) + 2)], "LinearArithmetic",
			"Exact"["encodeAppendantSndStrictlyAbove"[a, k, (k + 3) + ((d1 + 1) + 2), hk1]],
			"Change"["some"["system5Configuration"[
				"xorMerge"[Prepend[Subtract[x1 + 1, d1 + 1]][Prepend[Subtract[x2, d1 + 1]][Prepend[Subtract[x2 + 1, d1 + 1]]["shiftDown"[d1 + 1, "pairsOf"["doubleWord"[w], restStarts]]]]],
					"shiftUp"[d1 + 1, "shiftUp"[2, "encodeAppendantSnd"[a, k + 3]]]],
				Prepend["shiftUp"[d1 + 1, "encodeAppendantSnd"[a, k + 3]]][
					Prepend[Typed[{}, {NonNegativeIntegers}]][
						Prepend[Typed[{}, {NonNegativeIntegers}]][
							"shiftUpRules"[d1 + 1, "ruleBlocks"[tailWs, "appendantCounter"[a, k + 3]]]]]]]] ==
				"some"["system5Configuration"[
					Join[Prepend[1][Prepend[d3 + 2][Prepend[d3 + 3]["shiftDown"[d1 + 1, "pairsOf"["doubleWord"[w], restStarts]]]]],
						"shiftUp"[(d1 + 1) + 2, "encodeAppendantSnd"[a, k + 3]]],
					Prepend["shiftUp"[d1 + 1, "encodeAppendantSnd"[a, k + 3]]][
						Prepend[Typed[{}, {NonNegativeIntegers}]][
							Prepend[Typed[{}, {NonNegativeIntegers}]][
								"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + (d1 + 1)]]]]]]],
			"Rewrite"[s1], "Rewrite"[s2], "Rewrite"[s3],
			"Rewrite"["shiftUpAdd"[d1 + 1, 2, "encodeAppendantSnd"[a, k + 3]]],
			"Have"[comm2, 2 + (d1 + 1) == (d1 + 1) + 2], "LinearArithmetic", "Rewrite"[comm2],
			"Rewrite"["xorMergeDisjoint"[Prepend[1][Prepend[d3 + 2][Prepend[d3 + 3]["shiftDown"[d1 + 1, "pairsOf"["doubleWord"[w], restStarts]]]]],
				"shiftUp"[(d1 + 1) + 2, "encodeAppendantSnd"[a, k + 3]], k, allLow1, r1High]],
			"Rewrite"["ruleBlocksShift"[tailWs, "appendantCounter"[a, k + 3], d1 + 1]],
			(* Pop 2: 1 step, cancels tail! *)
			"Have"[pop2, "steps"["system5Step", 1, "system5Configuration"[
				Join[Prepend[1][Prepend[d3 + 2][Prepend[d3 + 3]["shiftDown"[d1 + 1, "pairsOf"["doubleWord"[w], restStarts]]]]],
					"shiftUp"[(d1 + 1) + 2, "encodeAppendantSnd"[a, k + 3]]],
				Prepend["shiftUp"[d1 + 1, "encodeAppendantSnd"[a, k + 3]]][
					Prepend[Typed[{}, {NonNegativeIntegers}]][
						Prepend[Typed[{}, {NonNegativeIntegers}]][
							"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + (d1 + 1)]]]]]] ==
				"some"["system5Configuration"[
					Prepend[d3 + 1][Prepend[d3 + 2]["shiftDown"[(d1 + 1) + 1, "pairsOf"["doubleWord"[w], restStarts]]]],
					Prepend[Typed[{}, {NonNegativeIntegers}]][
						Prepend[Typed[{}, {NonNegativeIntegers}]][
							"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + ((d1 + 1) + 1)]]]]]],
			"Change"["steps"["system5Step", 0 + 1, "system5Configuration"[
				Prepend[0 + 1][Join[Prepend[d3 + 2][Prepend[d3 + 3]["shiftDown"[d1 + 1, "pairsOf"["doubleWord"[w], restStarts]]]],
					"shiftUp"[(d1 + 1) + 2, "encodeAppendantSnd"[a, k + 3]]]],
				Prepend["shiftUp"[d1 + 1, "encodeAppendantSnd"[a, k + 3]]][
					Prepend[Typed[{}, {NonNegativeIntegers}]][
						Prepend[Typed[{}, {NonNegativeIntegers}]][
							"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + (d1 + 1)]]]]]] ==
				"some"["system5Configuration"[
					Prepend[d3 + 1][Prepend[d3 + 2]["shiftDown"[(d1 + 1) + 1, "pairsOf"["doubleWord"[w], restStarts]]]],
					Prepend[Typed[{}, {NonNegativeIntegers}]][
						Prepend[Typed[{}, {NonNegativeIntegers}]][
							"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + ((d1 + 1) + 1)]]]]]],
			"Rewrite"["system5RunThenPop"[0,
				Join[Prepend[d3 + 2][Prepend[d3 + 3]["shiftDown"[d1 + 1, "pairsOf"["doubleWord"[w], restStarts]]]],
					"shiftUp"[(d1 + 1) + 2, "encodeAppendantSnd"[a, k + 3]]],
				"shiftUp"[d1 + 1, "encodeAppendantSnd"[a, k + 3]],
				Prepend[Typed[{}, {NonNegativeIntegers}]][Prepend[Typed[{}, {NonNegativeIntegers}]]["ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + (d1 + 1)]]]]],
			"Rewrite"["shiftDownJoin"[1, Prepend[d3 + 2][Prepend[d3 + 3]["shiftDown"[d1 + 1, "pairsOf"["doubleWord"[w], restStarts]]]],
				"shiftUp"[(d1 + 1) + 2, "encodeAppendantSnd"[a, k + 3]]]],
			"Have"[le12, 1 <= (d1 + 1) + 2], "LinearArithmetic",
			"Rewrite"["shiftDownShiftUpGe"[(d1 + 1) + 2, 1, "encodeAppendantSnd"[a, k + 3], le12]],
			"Rewrite"["shiftUpAdd"[1, d1 + 1, "encodeAppendantSnd"[a, k + 3]]],
			"Have"[subEq, Subtract[(d1 + 1) + 2, 1] == (d1 + 1) + 1],
			"Have"[e12, (d1 + 1) + 2 == ((d1 + 1) + 1) + 1], "LinearArithmetic", "Rewrite"[e12], "Exact"["additionSubtractionCancellation"[(d1 + 1) + 1, 1]],
			"Rewrite"[subEq],
			"Have"[allLow2, "allBelowEqual"[k, Prepend[d3 + 1][Prepend[d3 + 2]["shiftDown"[(d1 + 1) + 1, "pairsOf"["doubleWord"[w], restStarts]]]]]],
			"Have"[le1k2, d3 + 1 <= k], "LinearArithmetic",
			"Have"[le2k2, d3 + 2 <= k], "LinearArithmetic",
			"Have"[leRestK2, "allBelowEqual"[k + ((d1 + 1) + 1), "pairsOf"["doubleWord"[w], restStarts]]],
			"Have"[kk2, k <= k + ((d1 + 1) + 1)], "LinearArithmetic", "Exact"["allBelowEqualWeaken"[k, k + ((d1 + 1) + 1), "pairsOf"["doubleWord"[w], restStarts], kk2, hRestBound]],
			"Exact"["andIntroduction"[le1k2, "andIntroduction"[le2k2, "shiftDownAllBelowEqual"["pairsOf"["doubleWord"[w], restStarts], (d1 + 1) + 1, k, leRestK2]]]],
			"Have"[r2High, "strictlyAbove"[k, "shiftUp"[(d1 + 1) + 1, "encodeAppendantSnd"[a, k + 3]]]],
			"Rewrite"["encodeAppendantSndShift"[a, k + 3, (d1 + 1) + 1]],
			"Have"[hk2, k + 1 <= (k + 3) + ((d1 + 1) + 1)], "LinearArithmetic",
			"Exact"["encodeAppendantSndStrictlyAbove"[a, k, (k + 3) + ((d1 + 1) + 1), hk2]],
			"Change"["some"["system5Configuration"[
				"xorMerge"[Join[Prepend[d3 + 1][Prepend[d3 + 2]["shiftDown"[1, "shiftDown"[d1 + 1, "pairsOf"["doubleWord"[w], restStarts]]]]],
					"shiftUp"[(d1 + 1) + 1, "encodeAppendantSnd"[a, k + 3]]],
					"shiftUp"[(d1 + 1) + 1, "encodeAppendantSnd"[a, k + 3]]],
				Prepend[Typed[{}, {NonNegativeIntegers}]][
					Prepend[Typed[{}, {NonNegativeIntegers}]][
						"shiftUpRules"[1, "ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + (d1 + 1)]]]]]] ==
				"some"["system5Configuration"[
					Prepend[d3 + 1][Prepend[d3 + 2]["shiftDown"[(d1 + 1) + 1, "pairsOf"["doubleWord"[w], restStarts]]]],
					Prepend[Typed[{}, {NonNegativeIntegers}]][
						Prepend[Typed[{}, {NonNegativeIntegers}]][
							"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + ((d1 + 1) + 1)]]]]]],
			"Rewrite"["shiftDownAdd"[d1 + 1, 1, "pairsOf"["doubleWord"[w], restStarts]]],
			"Rewrite"["xorMergeCancelTail"[Prepend[d3 + 1][Prepend[d3 + 2]["shiftDown"[(d1 + 1) + 1, "pairsOf"["doubleWord"[w], restStarts]]]],
				"shiftUp"[(d1 + 1) + 1, "encodeAppendantSnd"[a, k + 3]], k, allLow2, r2High]],
			"Rewrite"["ruleBlocksShift"[tailWs, "appendantCounter"[a, k + 3] + (d1 + 1), 1]],
			"Have"[assoc1, ("appendantCounter"[a, k + 3] + (d1 + 1)) + 1 == "appendantCounter"[a, k + 3] + ((d1 + 1) + 1)], "LinearArithmetic",
			"Rewrite"[assoc1],
			(* Pop 3: d3 + 1 steps, pops empty rule *)
			"Have"[pop3, "steps"["system5Step", d3 + 1, "system5Configuration"[
				Prepend[d3 + 1][Prepend[d3 + 2]["shiftDown"[(d1 + 1) + 1, "pairsOf"["doubleWord"[w], restStarts]]]],
				Prepend[Typed[{}, {NonNegativeIntegers}]][
					Prepend[Typed[{}, {NonNegativeIntegers}]][
						"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + ((d1 + 1) + 1)]]]]] ==
				"some"["system5Configuration"[
					Prepend[1]["shiftDown"[x2, "pairsOf"["doubleWord"[w], restStarts]]],
					Prepend[Typed[{}, {NonNegativeIntegers}]][
						"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + x2]]]]],
			"Rewrite"["system5RunThenPopEmpty"[d3,
				Prepend[d3 + 2]["shiftDown"[(d1 + 1) + 1, "pairsOf"["doubleWord"[w], restStarts]]],
				Prepend[Typed[{}, {NonNegativeIntegers}]]["ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + ((d1 + 1) + 1)]]]],
			"Have"[sub3, Subtract[d3 + 2, d3 + 1] == 1],
			"Have"[e3, d3 + 2 == 1 + (d3 + 1)], "LinearArithmetic", "Rewrite"[e3], "Exact"["additionSubtractionCancellation"[1, d3 + 1]],
			"Have"[sum3, ((d1 + 1) + 1) + (d3 + 1) == x2], "LinearArithmetic",
			"Change"["some"["system5Configuration"[
				Prepend[Subtract[d3 + 2, d3 + 1]]["shiftDown"[d3 + 1, "shiftDown"[(d1 + 1) + 1, "pairsOf"["doubleWord"[w], restStarts]]]],
				Prepend[Typed[{}, {NonNegativeIntegers}]][
					"shiftUpRules"[d3 + 1, "ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + ((d1 + 1) + 1)]]]]] ==
				"some"["system5Configuration"[
					Prepend[1]["shiftDown"[x2, "pairsOf"["doubleWord"[w], restStarts]]],
					Prepend[Typed[{}, {NonNegativeIntegers}]][
						"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + x2]]]]],
			"Rewrite"[sub3],
			"Rewrite"["shiftDownAdd"[(d1 + 1) + 1, d3 + 1, "pairsOf"["doubleWord"[w], restStarts]]],
			"Rewrite"[sum3],
			"Rewrite"["ruleBlocksShift"[tailWs, "appendantCounter"[a, k + 3] + ((d1 + 1) + 1), d3 + 1]],
			"Have"[assoc3, ("appendantCounter"[a, k + 3] + ((d1 + 1) + 1)) + (d3 + 1) == "appendantCounter"[a, k + 3] + x2], "LinearArithmetic",
			"Rewrite"[assoc3],
			(* Pop 4: 1 step, pops empty rule *)
			"Have"[pop4, "steps"["system5Step", 1, "system5Configuration"[
				Prepend[1]["shiftDown"[x2, "pairsOf"["doubleWord"[w], restStarts]]],
				Prepend[Typed[{}, {NonNegativeIntegers}]][
					"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + x2]]]] ==
				"some"["system5Configuration"[
					"shiftDown"[x2 + 1, "pairsOf"["doubleWord"[w], restStarts]],
					"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + (x2 + 1)]]]],
			"Change"["steps"["system5Step", 0 + 1, "system5Configuration"[
				Prepend[0 + 1]["shiftDown"[x2, "pairsOf"["doubleWord"[w], restStarts]]],
				Prepend[Typed[{}, {NonNegativeIntegers}]][
					"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + x2]]]] ==
				"some"["system5Configuration"[
					"shiftDown"[x2 + 1, "pairsOf"["doubleWord"[w], restStarts]],
					"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + (x2 + 1)]]]],
			"Rewrite"["system5RunThenPopEmpty"[0,
				"shiftDown"[x2, "pairsOf"["doubleWord"[w], restStarts]],
				"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + x2]]],
			"Rewrite"["shiftDownAdd"[x2, 1, "pairsOf"["doubleWord"[w], restStarts]]],
			"Rewrite"["ruleBlocksShift"[tailWs, "appendantCounter"[a, k + 3] + x2, 1]],
			"Have"[assoc4, ("appendantCounter"[a, k + 3] + x2) + 1 == "appendantCounter"[a, k + 3] + (x2 + 1)], "LinearArithmetic",
			"Rewrite"[assoc4],
			(* Compose all 4 runs! *)
			"Have"[runEq, "steps"["system5Step", x2 + 1, "system5Configuration"[
				Prepend[x1][Prepend[x1 + 1][Prepend[x2][Prepend[x2 + 1]["pairsOf"["doubleWord"[w], restStarts]]]]],
				"ruleBlocks"[Prepend[a][tailWs], k + 3]]] ==
				"some"["system5Configuration"[
					"pairsOf"["doubleWord"[w], "shiftDown"[x2 + 1, restStarts]],
					"ruleBlocks"[tailWs, ("appendantCounter"[a, k] + (x2 + 1)) + 3]]]],
			"Have"[totalSteps, x2 + 1 == (((d1 + 1) + 1) + (d3 + 1)) + 1], "LinearArithmetic",
			"Have"[eqSteps, "steps"["system5Step", x2 + 1, "system5Configuration"[
				Prepend[x1][Prepend[x1 + 1][Prepend[x2][Prepend[x2 + 1]["pairsOf"["doubleWord"[w], restStarts]]]]],
				"ruleBlocks"[Prepend[a][tailWs], k + 3]]] ==
				"steps"["system5Step", (((d1 + 1) + 1) + (d3 + 1)) + 1, "system5Configuration"[
					Prepend[x1][Prepend[x1 + 1][Prepend[x2][Prepend[x2 + 1]["pairsOf"["doubleWord"[w], restStarts]]]]],
					"ruleBlocks"[Prepend[a][tailWs], k + 3]]]],
			"Exact"["equalityCongruence"[
				Function[{Typed[n, NonNegativeIntegers]}, "steps"["system5Step", n, "system5Configuration"[
					Prepend[x1][Prepend[x1 + 1][Prepend[x2][Prepend[x2 + 1]["pairsOf"["doubleWord"[w], restStarts]]]]],
					"ruleBlocks"[Prepend[a][tailWs], k + 3]]]],
				totalSteps]],
			"Rewrite"[eqSteps],
			"Rewrite"["stepsAdd"["System5Configuration", "system5Step", ((d1 + 1) + 1) + (d3 + 1), 1,
				"system5Configuration"[Prepend[x1][Prepend[x1 + 1][Prepend[x2][Prepend[x2 + 1]["pairsOf"["doubleWord"[w], restStarts]]]]], "ruleBlocks"[Prepend[a][tailWs], k + 3]]]],
			"Rewrite"["stepsAdd"["System5Configuration", "system5Step", (d1 + 1) + 1, d3 + 1,
				"system5Configuration"[Prepend[x1][Prepend[x1 + 1][Prepend[x2][Prepend[x2 + 1]["pairsOf"["doubleWord"[w], restStarts]]]]], "ruleBlocks"[Prepend[a][tailWs], k + 3]]]],
			"Rewrite"["stepsAdd"["System5Configuration", "system5Step", d1 + 1, 1,
				"system5Configuration"[Prepend[x1][Prepend[x1 + 1][Prepend[x2][Prepend[x2 + 1]["pairsOf"["doubleWord"[w], restStarts]]]]], "ruleBlocks"[Prepend[a][tailWs], k + 3]]]],
			"Have"[eqHead, "steps"["system5Step", d1 + 1, "system5Configuration"[
				Prepend[x1][Prepend[x1 + 1][Prepend[x2][Prepend[x2 + 1]["pairsOf"["doubleWord"[w], restStarts]]]]],
				"ruleBlocks"[Prepend[a][tailWs], k + 3]]] ==
				"steps"["system5Step", d1 + 1, "system5Configuration"[
					Prepend[d1 + 1][Prepend[x1 + 1][Prepend[x2][Prepend[x2 + 1]["pairsOf"["doubleWord"[w], restStarts]]]]],
					"ruleBlocks"[Prepend[a][tailWs], k + 3]]]],
			"Exact"["equalityCongruence"[
				Function[{Typed[h, NonNegativeIntegers]}, "steps"["system5Step", d1 + 1, "system5Configuration"[
					Prepend[h][Prepend[x1 + 1][Prepend[x2][Prepend[x2 + 1]["pairsOf"["doubleWord"[w], restStarts]]]]],
					"ruleBlocks"[Prepend[a][tailWs], k + 3]]]],
				eqX1]],
			"Rewrite"[eqHead],
			"Rewrite"[pop1],
			"Change"["optionBind"["optionBind"["steps"["system5Step", 1, "system5Configuration"[
				Join[Prepend[1][Prepend[d3 + 2][Prepend[d3 + 3]["shiftDown"[d1 + 1, "pairsOf"["doubleWord"[w], restStarts]]]]],
					"shiftUp"[(d1 + 1) + 2, "encodeAppendantSnd"[a, k + 3]]],
				Prepend["shiftUp"[d1 + 1, "encodeAppendantSnd"[a, k + 3]]][
					Prepend[Typed[{}, {NonNegativeIntegers}]][
						Prepend[Typed[{}, {NonNegativeIntegers}]][
							"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + (d1 + 1)]]]]]],
				Function[{Typed[y, "System5Configuration"]}, "steps"["system5Step", d3 + 1, y]]],
				Function[{Typed[y, "System5Configuration"]}, "steps"["system5Step", 1, y]]] ==
				"some"["system5Configuration"[
					"pairsOf"["doubleWord"[w], "shiftDown"[x2 + 1, restStarts]],
					"ruleBlocks"[tailWs, ("appendantCounter"[a, k] + (x2 + 1)) + 3]]]],
			"Rewrite"[pop2],
			"Change"["optionBind"["steps"["system5Step", d3 + 1, "system5Configuration"[
				Prepend[d3 + 1][Prepend[d3 + 2]["shiftDown"[(d1 + 1) + 1, "pairsOf"["doubleWord"[w], restStarts]]]],
				Prepend[Typed[{}, {NonNegativeIntegers}]][
					Prepend[Typed[{}, {NonNegativeIntegers}]][
						"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + ((d1 + 1) + 1)]]]]],
				Function[{Typed[y, "System5Configuration"]}, "steps"["system5Step", 1, y]]] ==
				"some"["system5Configuration"[
					"pairsOf"["doubleWord"[w], "shiftDown"[x2 + 1, restStarts]],
					"ruleBlocks"[tailWs, ("appendantCounter"[a, k] + (x2 + 1)) + 3]]]],
			"Rewrite"[pop3],
			"Change"["steps"["system5Step", 1, "system5Configuration"[
				Prepend[1]["shiftDown"[x2, "pairsOf"["doubleWord"[w], restStarts]]],
				Prepend[Typed[{}, {NonNegativeIntegers}]][
					"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + x2]]]] ==
				"some"["system5Configuration"[
					"pairsOf"["doubleWord"[w], "shiftDown"[x2 + 1, restStarts]],
					"ruleBlocks"[tailWs, ("appendantCounter"[a, k] + (x2 + 1)) + 3]]]],
			"Rewrite"[pop4],
			"Rewrite"["pairsOfShiftDown"["doubleWord"[w], x2 + 1, restStarts, hAsc]],
			"Rewrite"["appendantCounterShift"[a, k, 3]],
			"Have"[cEq, ("appendantCounter"[a, k] + 3) + (x2 + 1) == ("appendantCounter"[a, k] + (x2 + 1)) + 3], "LinearArithmetic",
			"Rewrite"[cEq],
			(* Asc and Bound for the new bag *)
			"Have"[hAsc0, "pairsAsc"[0 + (x2 + 1), "doubleWord"[w], restStarts]],
			"Rewrite"["additionZeroLeft"[x2 + 1]], "Exact"[hAsc],
			"Have"[newAsc, "pairsAsc"[0, "doubleWord"[w], "shiftDown"[x2 + 1, restStarts]]],
			"Exact"["pairsAscShiftDown"["doubleWord"[w], x2 + 1, 0, restStarts, hAsc0]],
			"Have"[newBound, "allBelowEqual"["appendantCounter"[a, k] + (x2 + 1), "pairsOf"["doubleWord"[w], "shiftDown"[x2 + 1, restStarts]]]],
			"Rewrite"["equalitySymmetry"["pairsOfShiftDown"["doubleWord"[w], x2 + 1, restStarts, hAsc]]],
			"Have"[cGe, k <= "appendantCounter"[a, k]], "Exact"["appendantCounterGe"[a, k]],
			"Have"[leBig, k <= ("appendantCounter"[a, k] + (x2 + 1)) + (x2 + 1)], "LinearArithmetic",
			"Exact"["shiftDownAllBelowEqual"["pairsOf"["doubleWord"[w], restStarts], x2 + 1, "appendantCounter"[a, k] + (x2 + 1),
				"allBelowEqualWeaken"[k, ("appendantCounter"[a, k] + (x2 + 1)) + (x2 + 1), "pairsOf"["doubleWord"[w], restStarts], leBig, hRestBound]]],
			"Exact"["andIntroduction"[runEq, "andIntroduction"[newAsc, newBound]]]
		}
	],
	(* One CTS step with head bit true: x2 + 2 System 5 steps (4 rule pops), XOR-merging r2 and r1 into pairsOf[doubleWord[a], ...] *)
	machineTheorem["representsStepTrue",
		ForAll[
			{
				Typed[w, {Booleans}], Typed[a, {Booleans}], Typed[tailWs, {{Booleans}}],
				Typed[x1, NonNegativeIntegers], Typed[x2, NonNegativeIntegers], Typed[restStarts, {NonNegativeIntegers}],
				Typed[k, NonNegativeIntegers]
			},
			Implies[1 <= x1, Implies[x1 + 3 <= x2, Implies["pairsAsc"[x2 + 2, "doubleWord"[w], restStarts],
				Implies["allBelowEqual"[k, Prepend[x1][Prepend[x1 + 2][Prepend[x2][Prepend[x2 + 2]["pairsOf"["doubleWord"[w], restStarts]]]]]],
					Exists[{Typed[newStarts, {NonNegativeIntegers}]},
						And[
							"steps"["system5Step", x2 + 2, "system5Configuration"[
								Prepend[x1][Prepend[x1 + 2][Prepend[x2][Prepend[x2 + 2]["pairsOf"["doubleWord"[w], restStarts]]]]],
								"ruleBlocks"[Prepend[a][tailWs], k + 3]]] ==
								"some"["system5Configuration"[
									"pairsOf"["doubleWord"[Join[w, a]], newStarts],
									"ruleBlocks"[tailWs, ("appendantCounter"[a, k] + (x2 + 2)) + 3]]],
							And[
								"pairsAsc"[0, "doubleWord"[Join[w, a]], newStarts],
								"allBelowEqual"["appendantCounter"[a, k] + (x2 + 2), "pairsOf"["doubleWord"[Join[w, a]], newStarts]]
							]
						]]]]]]
		],
		{
			"Introduce"[w, a, tailWs, x1, x2, restStarts, k, hx1, hx12, hAsc, hBound],
			"Cases"[hBound], "Introduce"[x1Le, hB1], "Cases"[hB1], "Introduce"[x1pLe, hB2],
			"Cases"[hB2], "Introduce"[x2Le, hB3], "Cases"[hB3], "Introduce"[x2pLe, hRestBound],
			"Cases"["lessEqualExists"[1, x1, hx1]], "Introduce"[d1, eqX1],
			"Cases"["lessEqualExists"[x1 + 3, x2, hx12]], "Introduce"[d3, eqX2],
			"Cases"["lessEqualExists"[x2 + 2, k, x2pLe]], "Introduce"[dk, eqK],
			(* Pop 1: d1 + 1 (= x1) steps *)
			"Have"[pop1, "steps"["system5Step", d1 + 1, "system5Configuration"[
				Prepend[d1 + 1][Prepend[x1 + 2][Prepend[x2][Prepend[x2 + 2]["pairsOf"["doubleWord"[w], restStarts]]]]],
				"ruleBlocks"[Prepend[a][tailWs], k + 3]]] ==
				"some"["system5Configuration"[
					Join[Prepend[2][Prepend[d3 + 3][Prepend[d3 + 5]["shiftDown"[d1 + 1, "pairsOf"["doubleWord"[w], restStarts]]]]],
						"shiftUp"[(d1 + 1) + 2, "encodeAppendantSnd"[a, k + 3]]],
					Prepend["shiftUp"[d1 + 1, "encodeAppendantSnd"[a, k + 3]]][
						Prepend[Typed[{}, {NonNegativeIntegers}]][
							Prepend[Typed[{}, {NonNegativeIntegers}]][
								"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + (d1 + 1)]]]]]]],
			"Change"["steps"["system5Step", d1 + 1, "system5Configuration"[
				Prepend[d1 + 1][Prepend[x1 + 2][Prepend[x2][Prepend[x2 + 2]["pairsOf"["doubleWord"[w], restStarts]]]]],
				Prepend["shiftUp"[2, "encodeAppendantSnd"[a, k + 3]]][
					Prepend["encodeAppendantSnd"[a, k + 3]][
						Prepend[Typed[{}, {NonNegativeIntegers}]][
							Prepend[Typed[{}, {NonNegativeIntegers}]][
								"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3]]]]]]]] ==
				"some"["system5Configuration"[
					Join[Prepend[2][Prepend[d3 + 3][Prepend[d3 + 5]["shiftDown"[d1 + 1, "pairsOf"["doubleWord"[w], restStarts]]]]],
						"shiftUp"[(d1 + 1) + 2, "encodeAppendantSnd"[a, k + 3]]],
					Prepend["shiftUp"[d1 + 1, "encodeAppendantSnd"[a, k + 3]]][
						Prepend[Typed[{}, {NonNegativeIntegers}]][
							Prepend[Typed[{}, {NonNegativeIntegers}]][
								"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + (d1 + 1)]]]]]]],
			"Rewrite"["system5RunThenPop"[d1,
				Prepend[x1 + 2][Prepend[x2][Prepend[x2 + 2]["pairsOf"["doubleWord"[w], restStarts]]]],
				"shiftUp"[2, "encodeAppendantSnd"[a, k + 3]],
				Prepend["encodeAppendantSnd"[a, k + 3]][Prepend[Typed[{}, {NonNegativeIntegers}]][Prepend[Typed[{}, {NonNegativeIntegers}]]["ruleBlocks"[tailWs, "appendantCounter"[a, k + 3]]]]]]],
			"Have"[s1, Subtract[x1 + 2, d1 + 1] == 2],
			"Rewrite"[eqX1], "Have"[t1, (d1 + 1) + 2 == 2 + (d1 + 1)], "LinearArithmetic", "Rewrite"[t1], "Exact"["additionSubtractionCancellation"[2, d1 + 1]],
			"Have"[s2, Subtract[x2, d1 + 1] == d3 + 3],
			"Rewrite"[eqX2], "Rewrite"[eqX1], "Have"[t2, d3 + ((d1 + 1) + 3) == (d3 + 3) + (d1 + 1)], "LinearArithmetic", "Rewrite"[t2], "Exact"["additionSubtractionCancellation"[d3 + 3, d1 + 1]],
			"Have"[s3, Subtract[x2 + 2, d1 + 1] == d3 + 5],
			"Rewrite"[eqX2], "Rewrite"[eqX1], "Have"[t3, (d3 + ((d1 + 1) + 3)) + 2 == (d3 + 5) + (d1 + 1)], "LinearArithmetic", "Rewrite"[t3], "Exact"["additionSubtractionCancellation"[d3 + 5, d1 + 1]],
			"Have"[allLow1, "allBelowEqual"[k, Prepend[2][Prepend[d3 + 3][Prepend[d3 + 5]["shiftDown"[d1 + 1, "pairsOf"["doubleWord"[w], restStarts]]]]]]],
			"Have"[le1k, 2 <= k], "LinearArithmetic",
			"Have"[le2k, d3 + 3 <= k], "LinearArithmetic",
			"Have"[le3k, d3 + 5 <= k], "LinearArithmetic",
			"Have"[leRestK, "allBelowEqual"[k + (d1 + 1), "pairsOf"["doubleWord"[w], restStarts]]],
			"Have"[kk, k <= k + (d1 + 1)], "LinearArithmetic", "Exact"["allBelowEqualWeaken"[k, k + (d1 + 1), "pairsOf"["doubleWord"[w], restStarts], kk, hRestBound]],
			"Exact"["andIntroduction"[le1k, "andIntroduction"[le2k, "andIntroduction"[le3k, "shiftDownAllBelowEqual"["pairsOf"["doubleWord"[w], restStarts], d1 + 1, k, leRestK]]]]],
			"Have"[r1High, "strictlyAbove"[k, "shiftUp"[(d1 + 1) + 2, "encodeAppendantSnd"[a, k + 3]]]],
			"Rewrite"["encodeAppendantSndShift"[a, k + 3, (d1 + 1) + 2]],
			"Have"[hk1, k + 1 <= (k + 3) + ((d1 + 1) + 2)], "LinearArithmetic",
			"Exact"["encodeAppendantSndStrictlyAbove"[a, k, (k + 3) + ((d1 + 1) + 2), hk1]],
			"Change"["some"["system5Configuration"[
				"xorMerge"[Prepend[Subtract[x1 + 2, d1 + 1]][Prepend[Subtract[x2, d1 + 1]][Prepend[Subtract[x2 + 2, d1 + 1]]["shiftDown"[d1 + 1, "pairsOf"["doubleWord"[w], restStarts]]]]],
					"shiftUp"[d1 + 1, "shiftUp"[2, "encodeAppendantSnd"[a, k + 3]]]],
				Prepend["shiftUp"[d1 + 1, "encodeAppendantSnd"[a, k + 3]]][
					Prepend[Typed[{}, {NonNegativeIntegers}]][
						Prepend[Typed[{}, {NonNegativeIntegers}]][
							"shiftUpRules"[d1 + 1, "ruleBlocks"[tailWs, "appendantCounter"[a, k + 3]]]]]]]] ==
				"some"["system5Configuration"[
					Join[Prepend[2][Prepend[d3 + 3][Prepend[d3 + 5]["shiftDown"[d1 + 1, "pairsOf"["doubleWord"[w], restStarts]]]]],
						"shiftUp"[(d1 + 1) + 2, "encodeAppendantSnd"[a, k + 3]]],
					Prepend["shiftUp"[d1 + 1, "encodeAppendantSnd"[a, k + 3]]][
						Prepend[Typed[{}, {NonNegativeIntegers}]][
							Prepend[Typed[{}, {NonNegativeIntegers}]][
								"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + (d1 + 1)]]]]]]],
			"Rewrite"[s1], "Rewrite"[s2], "Rewrite"[s3],
			"Rewrite"["shiftUpAdd"[d1 + 1, 2, "encodeAppendantSnd"[a, k + 3]]],
			"Have"[comm2, 2 + (d1 + 1) == (d1 + 1) + 2], "LinearArithmetic", "Rewrite"[comm2],
			"Rewrite"["xorMergeDisjoint"[Prepend[2][Prepend[d3 + 3][Prepend[d3 + 5]["shiftDown"[d1 + 1, "pairsOf"["doubleWord"[w], restStarts]]]]],
				"shiftUp"[(d1 + 1) + 2, "encodeAppendantSnd"[a, k + 3]], k, allLow1, r1High]],
			"Rewrite"["ruleBlocksShift"[tailWs, "appendantCounter"[a, k + 3], d1 + 1]],
			(* Pop 2: 2 steps, XOR-merges r2 and r1 into pairsOf[doubleWord[a], startsOf[a, (k + 3) + (d1 + 1)]]! *)
			"Have"[pop2, "steps"["system5Step", 2, "system5Configuration"[
				Join[Prepend[2][Prepend[d3 + 3][Prepend[d3 + 5]["shiftDown"[d1 + 1, "pairsOf"["doubleWord"[w], restStarts]]]]],
					"shiftUp"[(d1 + 1) + 2, "encodeAppendantSnd"[a, k + 3]]],
				Prepend["shiftUp"[d1 + 1, "encodeAppendantSnd"[a, k + 3]]][
					Prepend[Typed[{}, {NonNegativeIntegers}]][
						Prepend[Typed[{}, {NonNegativeIntegers}]][
							"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + (d1 + 1)]]]]]] ==
				"some"["system5Configuration"[
					Join[Prepend[d3 + 1][Prepend[d3 + 3]["shiftDown"[(d1 + 1) + 2, "pairsOf"["doubleWord"[w], restStarts]]]],
						"pairsOf"["doubleWord"[a], "startsOf"[a, (k + 3) + (d1 + 1)]]],
					Prepend[Typed[{}, {NonNegativeIntegers}]][
						Prepend[Typed[{}, {NonNegativeIntegers}]][
							"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + ((d1 + 1) + 2)]]]]]],
			"Change"["steps"["system5Step", 1 + 1, "system5Configuration"[
				Prepend[1 + 1][Join[Prepend[d3 + 3][Prepend[d3 + 5]["shiftDown"[d1 + 1, "pairsOf"["doubleWord"[w], restStarts]]]],
					"shiftUp"[(d1 + 1) + 2, "encodeAppendantSnd"[a, k + 3]]]],
				Prepend["shiftUp"[d1 + 1, "encodeAppendantSnd"[a, k + 3]]][
					Prepend[Typed[{}, {NonNegativeIntegers}]][
						Prepend[Typed[{}, {NonNegativeIntegers}]][
							"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + (d1 + 1)]]]]]] ==
				"some"["system5Configuration"[
					Join[Prepend[d3 + 1][Prepend[d3 + 3]["shiftDown"[(d1 + 1) + 2, "pairsOf"["doubleWord"[w], restStarts]]]],
						"pairsOf"["doubleWord"[a], "startsOf"[a, (k + 3) + (d1 + 1)]]],
					Prepend[Typed[{}, {NonNegativeIntegers}]][
						Prepend[Typed[{}, {NonNegativeIntegers}]][
							"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + ((d1 + 1) + 2)]]]]]],
			"Rewrite"["system5RunThenPop"[1,
				Join[Prepend[d3 + 3][Prepend[d3 + 5]["shiftDown"[d1 + 1, "pairsOf"["doubleWord"[w], restStarts]]]],
					"shiftUp"[(d1 + 1) + 2, "encodeAppendantSnd"[a, k + 3]]],
				"shiftUp"[d1 + 1, "encodeAppendantSnd"[a, k + 3]],
				Prepend[Typed[{}, {NonNegativeIntegers}]][Prepend[Typed[{}, {NonNegativeIntegers}]]["ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + (d1 + 1)]]]]],
			"Rewrite"["shiftDownJoin"[2, Prepend[d3 + 3][Prepend[d3 + 5]["shiftDown"[d1 + 1, "pairsOf"["doubleWord"[w], restStarts]]]],
				"shiftUp"[(d1 + 1) + 2, "encodeAppendantSnd"[a, k + 3]]]],
			"Have"[le22, 2 <= (d1 + 1) + 2], "LinearArithmetic",
			"Rewrite"["shiftDownShiftUpGe"[(d1 + 1) + 2, 2, "encodeAppendantSnd"[a, k + 3], le22]],
			"Rewrite"["additionSubtractionCancellation"[d1 + 1, 2]],
			"Rewrite"["shiftUpAdd"[2, d1 + 1, "encodeAppendantSnd"[a, k + 3]]],
			"Have"[allLow2, "allBelowEqual"[k, Prepend[d3 + 1][Prepend[d3 + 3]["shiftDown"[(d1 + 1) + 2, "pairsOf"["doubleWord"[w], restStarts]]]]]],
			"Have"[le1k2, d3 + 1 <= k], "LinearArithmetic",
			"Have"[le2k2, d3 + 3 <= k], "LinearArithmetic",
			"Have"[leRestK2, "allBelowEqual"[k + ((d1 + 1) + 2), "pairsOf"["doubleWord"[w], restStarts]]],
			"Have"[kk2, k <= k + ((d1 + 1) + 2)], "LinearArithmetic", "Exact"["allBelowEqualWeaken"[k, k + ((d1 + 1) + 2), "pairsOf"["doubleWord"[w], restStarts], kk2, hRestBound]],
			"Exact"["andIntroduction"[le1k2, "andIntroduction"[le2k2, "shiftDownAllBelowEqual"["pairsOf"["doubleWord"[w], restStarts], (d1 + 1) + 2, k, leRestK2]]]],
			"Have"[r2pHigh, "strictlyAbove"[k, "shiftUp"[(d1 + 1) + 2, "encodeAppendantSnd"[a, k + 3]]]],
			"Rewrite"["encodeAppendantSndShift"[a, k + 3, (d1 + 1) + 2]],
			"Have"[hk2, k + 1 <= (k + 3) + ((d1 + 1) + 2)], "LinearArithmetic",
			"Exact"["encodeAppendantSndStrictlyAbove"[a, k, (k + 3) + ((d1 + 1) + 2), hk2]],
			"Change"["some"["system5Configuration"[
				"xorMerge"[Join[Prepend[d3 + 1][Prepend[d3 + 3]["shiftDown"[2, "shiftDown"[d1 + 1, "pairsOf"["doubleWord"[w], restStarts]]]]],
					"shiftUp"[d1 + 1, "encodeAppendantSnd"[a, k + 3]]],
					"shiftUp"[(d1 + 1) + 2, "encodeAppendantSnd"[a, k + 3]]],
				Prepend[Typed[{}, {NonNegativeIntegers}]][
					Prepend[Typed[{}, {NonNegativeIntegers}]][
						"shiftUpRules"[2, "ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + (d1 + 1)]]]]]] ==
				"some"["system5Configuration"[
					Join[Prepend[d3 + 1][Prepend[d3 + 3]["shiftDown"[(d1 + 1) + 2, "pairsOf"["doubleWord"[w], restStarts]]]],
						"pairsOf"["doubleWord"[a], "startsOf"[a, (k + 3) + (d1 + 1)]]],
					Prepend[Typed[{}, {NonNegativeIntegers}]][
						Prepend[Typed[{}, {NonNegativeIntegers}]][
							"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + ((d1 + 1) + 2)]]]]]],
			"Rewrite"["shiftDownAdd"[d1 + 1, 2, "pairsOf"["doubleWord"[w], restStarts]]],
			"Rewrite"["xorMergePrefix"[Prepend[d3 + 1][Prepend[d3 + 3]["shiftDown"[(d1 + 1) + 2, "pairsOf"["doubleWord"[w], restStarts]]]],
				"shiftUp"[d1 + 1, "encodeAppendantSnd"[a, k + 3]],
				"shiftUp"[(d1 + 1) + 2, "encodeAppendantSnd"[a, k + 3]], k, allLow2, r2pHigh]],
			"Rewrite"["equalitySymmetry"["shiftUpAdd"[2, d1 + 1, "encodeAppendantSnd"[a, k + 3]]]],
			"Rewrite"["encodeAppendantSndShift"[a, k + 3, d1 + 1]],
			"Rewrite"["xorMergeAppendant"[a, (k + 3) + (d1 + 1)]],
			"Rewrite"["ruleBlocksShift"[tailWs, "appendantCounter"[a, k + 3] + (d1 + 1), 2]],
			"Have"[assoc2, ("appendantCounter"[a, k + 3] + (d1 + 1)) + 2 == "appendantCounter"[a, k + 3] + ((d1 + 1) + 2)], "LinearArithmetic",
			"Rewrite"[assoc2],
			(* Pop 3: d3 + 1 steps, pops empty rule *)
			"Have"[pop3, "steps"["system5Step", d3 + 1, "system5Configuration"[
				Join[Prepend[d3 + 1][Prepend[d3 + 3]["shiftDown"[(d1 + 1) + 2, "pairsOf"["doubleWord"[w], restStarts]]]],
					"pairsOf"["doubleWord"[a], "startsOf"[a, (k + 3) + (d1 + 1)]]],
				Prepend[Typed[{}, {NonNegativeIntegers}]][
					Prepend[Typed[{}, {NonNegativeIntegers}]][
						"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + ((d1 + 1) + 2)]]]]] ==
				"some"["system5Configuration"[
					Prepend[2][Join["shiftDown"[x2, "pairsOf"["doubleWord"[w], restStarts]],
						"shiftDown"[d3 + 1, "pairsOf"["doubleWord"[a], "startsOf"[a, (k + 3) + (d1 + 1)]]]]],
					Prepend[Typed[{}, {NonNegativeIntegers}]][
						"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + x2]]]]],
			"Change"["steps"["system5Step", d3 + 1, "system5Configuration"[
				Prepend[d3 + 1][Prepend[d3 + 3][Join["shiftDown"[(d1 + 1) + 2, "pairsOf"["doubleWord"[w], restStarts]],
					"pairsOf"["doubleWord"[a], "startsOf"[a, (k + 3) + (d1 + 1)]]]]],
				Prepend[Typed[{}, {NonNegativeIntegers}]][
					Prepend[Typed[{}, {NonNegativeIntegers}]][
						"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + ((d1 + 1) + 2)]]]]] ==
				"some"["system5Configuration"[
					Prepend[2][Join["shiftDown"[x2, "pairsOf"["doubleWord"[w], restStarts]],
						"shiftDown"[d3 + 1, "pairsOf"["doubleWord"[a], "startsOf"[a, (k + 3) + (d1 + 1)]]]]],
					Prepend[Typed[{}, {NonNegativeIntegers}]][
						"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + x2]]]]],
			"Rewrite"["system5RunThenPopEmpty"[d3,
				Prepend[d3 + 3][Join["shiftDown"[(d1 + 1) + 2, "pairsOf"["doubleWord"[w], restStarts]],
					"pairsOf"["doubleWord"[a], "startsOf"[a, (k + 3) + (d1 + 1)]]]],
				Prepend[Typed[{}, {NonNegativeIntegers}]]["ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + ((d1 + 1) + 2)]]]],
			"Have"[sub3, Subtract[d3 + 3, d3 + 1] == 2],
			"Have"[e3, d3 + 3 == 2 + (d3 + 1)], "LinearArithmetic", "Rewrite"[e3], "Exact"["additionSubtractionCancellation"[2, d3 + 1]],
			"Have"[sum3, ((d1 + 1) + 2) + (d3 + 1) == x2], "LinearArithmetic",
			"Change"["some"["system5Configuration"[
				Prepend[Subtract[d3 + 3, d3 + 1]]["shiftDown"[d3 + 1, Join["shiftDown"[(d1 + 1) + 2, "pairsOf"["doubleWord"[w], restStarts]],
					"pairsOf"["doubleWord"[a], "startsOf"[a, (k + 3) + (d1 + 1)]]]]],
				Prepend[Typed[{}, {NonNegativeIntegers}]][
					"shiftUpRules"[d3 + 1, "ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + ((d1 + 1) + 2)]]]]] ==
				"some"["system5Configuration"[
					Prepend[2][Join["shiftDown"[x2, "pairsOf"["doubleWord"[w], restStarts]],
						"shiftDown"[d3 + 1, "pairsOf"["doubleWord"[a], "startsOf"[a, (k + 3) + (d1 + 1)]]]]],
					Prepend[Typed[{}, {NonNegativeIntegers}]][
						"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + x2]]]]],
			"Rewrite"[sub3],
			"Rewrite"["shiftDownJoin"[d3 + 1, "shiftDown"[(d1 + 1) + 2, "pairsOf"["doubleWord"[w], restStarts]],
				"pairsOf"["doubleWord"[a], "startsOf"[a, (k + 3) + (d1 + 1)]]]],
			"Rewrite"["shiftDownAdd"[(d1 + 1) + 2, d3 + 1, "pairsOf"["doubleWord"[w], restStarts]]],
			"Rewrite"[sum3],
			"Rewrite"["ruleBlocksShift"[tailWs, "appendantCounter"[a, k + 3] + ((d1 + 1) + 2), d3 + 1]],
			"Have"[assoc3, ("appendantCounter"[a, k + 3] + ((d1 + 1) + 2)) + (d3 + 1) == "appendantCounter"[a, k + 3] + x2], "LinearArithmetic",
			"Rewrite"[assoc3],
			(* Pop 4: 2 steps, pops empty rule *)
			"Have"[pop4, "steps"["system5Step", 2, "system5Configuration"[
				Prepend[2][Join["shiftDown"[x2, "pairsOf"["doubleWord"[w], restStarts]],
					"shiftDown"[d3 + 1, "pairsOf"["doubleWord"[a], "startsOf"[a, (k + 3) + (d1 + 1)]]]]],
				Prepend[Typed[{}, {NonNegativeIntegers}]][
					"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + x2]]]] ==
				"some"["system5Configuration"[
					Join["shiftDown"[x2 + 2, "pairsOf"["doubleWord"[w], restStarts]],
						"shiftDown"[d3 + 3, "pairsOf"["doubleWord"[a], "startsOf"[a, (k + 3) + (d1 + 1)]]]],
					"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + (x2 + 2)]]]],
			"Change"["steps"["system5Step", 1 + 1, "system5Configuration"[
				Prepend[1 + 1][Join["shiftDown"[x2, "pairsOf"["doubleWord"[w], restStarts]],
					"shiftDown"[d3 + 1, "pairsOf"["doubleWord"[a], "startsOf"[a, (k + 3) + (d1 + 1)]]]]],
				Prepend[Typed[{}, {NonNegativeIntegers}]][
					"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + x2]]]] ==
				"some"["system5Configuration"[
					Join["shiftDown"[x2 + 2, "pairsOf"["doubleWord"[w], restStarts]],
						"shiftDown"[d3 + 3, "pairsOf"["doubleWord"[a], "startsOf"[a, (k + 3) + (d1 + 1)]]]],
					"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + (x2 + 2)]]]],
			"Rewrite"["system5RunThenPopEmpty"[1,
				Join["shiftDown"[x2, "pairsOf"["doubleWord"[w], restStarts]],
					"shiftDown"[d3 + 1, "pairsOf"["doubleWord"[a], "startsOf"[a, (k + 3) + (d1 + 1)]]]],
				"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + x2]]],
			"Rewrite"["shiftDownJoin"[2, "shiftDown"[x2, "pairsOf"["doubleWord"[w], restStarts]],
				"shiftDown"[d3 + 1, "pairsOf"["doubleWord"[a], "startsOf"[a, (k + 3) + (d1 + 1)]]]]],
			"Rewrite"["shiftDownAdd"[x2, 2, "pairsOf"["doubleWord"[w], restStarts]]],
			"Rewrite"["shiftDownAdd"[d3 + 1, 2, "pairsOf"["doubleWord"[a], "startsOf"[a, (k + 3) + (d1 + 1)]]]],
			"Have"[e33, (d3 + 1) + 2 == d3 + 3], "LinearArithmetic", "Rewrite"[e33],
			"Rewrite"["ruleBlocksShift"[tailWs, "appendantCounter"[a, k + 3] + x2, 2]],
			"Have"[assoc4, ("appendantCounter"[a, k + 3] + x2) + 2 == "appendantCounter"[a, k + 3] + (x2 + 2)], "LinearArithmetic",
			"Rewrite"[assoc4],
			(* Simplify the appended shifted pairsOf into pairsOf[doubleWord[a], startsOf[a, base]] where base = dk + x1 + x1 + 5 *)
			"Have"[baseEq, (k + 3) + (d1 + 1) == (dk + x1 + x1 + 5) + (d3 + 3)], "LinearArithmetic",
			"Have"[subBase, Subtract[(k + 3) + (d1 + 1), d3 + 3] == dk + x1 + x1 + 5],
			"Rewrite"[baseEq], "Exact"["additionSubtractionCancellation"[dk + x1 + x1 + 5, d3 + 3]],
			"Have"[d3Le, d3 + 3 <= (k + 3) + (d1 + 1)], "LinearArithmetic",
			"Have"[d3Lt, (d3 + 3) + 1 <= (k + 3) + (d1 + 1)], "LinearArithmetic",
			"Have"[appShift, "shiftDown"[d3 + 3, "pairsOf"["doubleWord"[a], "startsOf"[a, (k + 3) + (d1 + 1)]]] ==
				"pairsOf"["doubleWord"[a], "startsOf"[a, dk + x1 + x1 + 5]]],
			"Rewrite"["pairsOfShiftDown"["doubleWord"[a], d3 + 3, "startsOf"[a, (k + 3) + (d1 + 1)], "pairsAscStartsOf"[a, d3 + 3, (k + 3) + (d1 + 1), d3Lt]]],
			"Rewrite"["startsOfShiftDown"[a, (k + 3) + (d1 + 1), d3 + 3, d3Le]],
			"Rewrite"[subBase],
			(* Build newStarts = Join[shiftDown[x2 + 2, restStarts], startsOf[a, dk + x1 + x1 + 5]] *)
			"Have"[hAsc0, "pairsAsc"[0 + (x2 + 2), "doubleWord"[w], restStarts]],
			"Rewrite"["additionZeroLeft"[x2 + 2]], "Exact"[hAsc],
			"Have"[restNewAsc, "pairsAsc"[0, "doubleWord"[w], "shiftDown"[x2 + 2, restStarts]]],
			"Exact"["pairsAscShiftDown"["doubleWord"[w], x2 + 2, 0, restStarts, hAsc0]],
			"Have"[restBoundDk, "allBelowEqual"[dk, "pairsOf"["doubleWord"[w], "shiftDown"[x2 + 2, restStarts]]]],
			"Rewrite"["equalitySymmetry"["pairsOfShiftDown"["doubleWord"[w], x2 + 2, restStarts, hAsc]]],
			"Have"[kEq2, k == dk + (x2 + 2)], "LinearArithmetic",
			"Have"[hRestDk, "allBelowEqual"[dk + (x2 + 2), "pairsOf"["doubleWord"[w], restStarts]]],
			"Rewrite"["equalitySymmetry"[kEq2]], "Exact"[hRestBound],
			"Exact"["shiftDownAllBelowEqual"["pairsOf"["doubleWord"[w], restStarts], x2 + 2, dk, hRestDk]],
			"Have"[dkLtBase, dk + 1 <= dk + x1 + x1 + 5], "LinearArithmetic",
			"Have"[appNewAsc, "pairsAsc"[dk, "doubleWord"[a], "startsOf"[a, dk + x1 + x1 + 5]]],
			"Exact"["pairsAscStartsOf"[a, dk, dk + x1 + x1 + 5, dkLtBase]],
			"Have"[newAsc, "pairsAsc"[0, "doubleWord"[Join[w, a]], Join["shiftDown"[x2 + 2, restStarts], "startsOf"[a, dk + x1 + x1 + 5]]]],
			"Rewrite"["doubleWordJoin"[w, a]],
			"Exact"["pairsAscJoin"["doubleWord"[w], "doubleWord"[a], "shiftDown"[x2 + 2, restStarts], "startsOf"[a, dk + x1 + x1 + 5],
				0, dk, "lessEqualZero"[dk], restNewAsc, restBoundDk, appNewAsc]],
			"Have"[bagJoinEq, "pairsOf"["doubleWord"[Join[w, a]], Join["shiftDown"[x2 + 2, restStarts], "startsOf"[a, dk + x1 + x1 + 5]]] ==
				Join["pairsOf"["doubleWord"[w], "shiftDown"[x2 + 2, restStarts]], "pairsOf"["doubleWord"[a], "startsOf"[a, dk + x1 + x1 + 5]]]],
			"Rewrite"["doubleWordJoin"[w, a]],
			"Exact"["pairsOfJoin"["doubleWord"[w], "doubleWord"[a], "shiftDown"[x2 + 2, restStarts], "startsOf"[a, dk + x1 + x1 + 5], 0, restNewAsc]],
			(* Bound on the new bag *)
			"Have"[cGe, k <= "appendantCounter"[a, k]], "Exact"["appendantCounterGe"[a, k]],
			"Have"[dkLeNew, dk <= "appendantCounter"[a, k] + (x2 + 2)], "LinearArithmetic",
			"Have"[baseLeNew, dk + x1 + x1 + 4 <= k + (x2 + 2)], "LinearArithmetic",
			"Have"[appBound1, "allBelowEqual"["appendantCounter"[a, dk + x1 + x1 + 4], "pairsOf"["doubleWord"[a], "startsOf"[a, (dk + x1 + x1 + 4) + 1]]]],
			"Exact"["pairsOfStartsOfAllBelowEqual"[a, dk + x1 + x1 + 4]],
			"Have"[appBound2, "allBelowEqual"["appendantCounter"[a, k] + (x2 + 2), "pairsOf"["doubleWord"[a], "startsOf"[a, dk + x1 + x1 + 5]]]],
			"Have"[b5Eq, (dk + x1 + x1 + 4) + 1 == dk + x1 + x1 + 5], "LinearArithmetic",
			"Have"[cntLe, "appendantCounter"[a, dk + x1 + x1 + 4] <= "appendantCounter"[a, k] + (x2 + 2)],
			"Rewrite"["equalitySymmetry"["appendantCounterShift"[a, k, x2 + 2]]],
			"Exact"["appendantCounterMonotonic"[a, dk + x1 + x1 + 4, k + (x2 + 2), baseLeNew]],
			"Rewrite"["equalitySymmetry"[b5Eq]],
			"Exact"["allBelowEqualWeaken"["appendantCounter"[a, dk + x1 + x1 + 4], "appendantCounter"[a, k] + (x2 + 2),
				"pairsOf"["doubleWord"[a], "startsOf"[a, (dk + x1 + x1 + 4) + 1]], cntLe, appBound1]],
			"Have"[newBound, "allBelowEqual"["appendantCounter"[a, k] + (x2 + 2), "pairsOf"["doubleWord"[Join[w, a]], Join["shiftDown"[x2 + 2, restStarts], "startsOf"[a, dk + x1 + x1 + 5]]]]],
			"Rewrite"[bagJoinEq],
			"Exact"["allBelowEqualJoin"["appendantCounter"[a, k] + (x2 + 2),
				"pairsOf"["doubleWord"[w], "shiftDown"[x2 + 2, restStarts]],
				"pairsOf"["doubleWord"[a], "startsOf"[a, dk + x1 + x1 + 5]],
				"allBelowEqualWeaken"[dk, "appendantCounter"[a, k] + (x2 + 2), "pairsOf"["doubleWord"[w], "shiftDown"[x2 + 2, restStarts]], dkLeNew, restBoundDk],
				appBound2]],
			(* Compose all 4 runs! *)
			"Have"[runEq, "steps"["system5Step", x2 + 2, "system5Configuration"[
				Prepend[x1][Prepend[x1 + 2][Prepend[x2][Prepend[x2 + 2]["pairsOf"["doubleWord"[w], restStarts]]]]],
				"ruleBlocks"[Prepend[a][tailWs], k + 3]]] ==
				"some"["system5Configuration"[
					"pairsOf"["doubleWord"[Join[w, a]], Join["shiftDown"[x2 + 2, restStarts], "startsOf"[a, dk + x1 + x1 + 5]]],
					"ruleBlocks"[tailWs, ("appendantCounter"[a, k] + (x2 + 2)) + 3]]]],
			"Have"[totalSteps, x2 + 2 == (((d1 + 1) + 2) + (d3 + 1)) + 2], "LinearArithmetic",
			"Have"[eqSteps, "steps"["system5Step", x2 + 2, "system5Configuration"[
				Prepend[x1][Prepend[x1 + 2][Prepend[x2][Prepend[x2 + 2]["pairsOf"["doubleWord"[w], restStarts]]]]],
				"ruleBlocks"[Prepend[a][tailWs], k + 3]]] ==
				"steps"["system5Step", (((d1 + 1) + 2) + (d3 + 1)) + 2, "system5Configuration"[
					Prepend[x1][Prepend[x1 + 2][Prepend[x2][Prepend[x2 + 2]["pairsOf"["doubleWord"[w], restStarts]]]]],
					"ruleBlocks"[Prepend[a][tailWs], k + 3]]]],
			"Exact"["equalityCongruence"[
				Function[{Typed[n, NonNegativeIntegers]}, "steps"["system5Step", n, "system5Configuration"[
					Prepend[x1][Prepend[x1 + 2][Prepend[x2][Prepend[x2 + 2]["pairsOf"["doubleWord"[w], restStarts]]]]],
					"ruleBlocks"[Prepend[a][tailWs], k + 3]]]],
				totalSteps]],
			"Rewrite"[eqSteps],
			"Rewrite"["stepsAdd"["System5Configuration", "system5Step", ((d1 + 1) + 2) + (d3 + 1), 2,
				"system5Configuration"[Prepend[x1][Prepend[x1 + 2][Prepend[x2][Prepend[x2 + 2]["pairsOf"["doubleWord"[w], restStarts]]]]], "ruleBlocks"[Prepend[a][tailWs], k + 3]]]],
			"Rewrite"["stepsAdd"["System5Configuration", "system5Step", (d1 + 1) + 2, d3 + 1,
				"system5Configuration"[Prepend[x1][Prepend[x1 + 2][Prepend[x2][Prepend[x2 + 2]["pairsOf"["doubleWord"[w], restStarts]]]]], "ruleBlocks"[Prepend[a][tailWs], k + 3]]]],
			"Rewrite"["stepsAdd"["System5Configuration", "system5Step", d1 + 1, 2,
				"system5Configuration"[Prepend[x1][Prepend[x1 + 2][Prepend[x2][Prepend[x2 + 2]["pairsOf"["doubleWord"[w], restStarts]]]]], "ruleBlocks"[Prepend[a][tailWs], k + 3]]]],
			"Have"[eqHead, "steps"["system5Step", d1 + 1, "system5Configuration"[
				Prepend[x1][Prepend[x1 + 2][Prepend[x2][Prepend[x2 + 2]["pairsOf"["doubleWord"[w], restStarts]]]]],
				"ruleBlocks"[Prepend[a][tailWs], k + 3]]] ==
				"steps"["system5Step", d1 + 1, "system5Configuration"[
					Prepend[d1 + 1][Prepend[x1 + 2][Prepend[x2][Prepend[x2 + 2]["pairsOf"["doubleWord"[w], restStarts]]]]],
					"ruleBlocks"[Prepend[a][tailWs], k + 3]]]],
			"Exact"["equalityCongruence"[
				Function[{Typed[h, NonNegativeIntegers]}, "steps"["system5Step", d1 + 1, "system5Configuration"[
					Prepend[h][Prepend[x1 + 2][Prepend[x2][Prepend[x2 + 2]["pairsOf"["doubleWord"[w], restStarts]]]]],
					"ruleBlocks"[Prepend[a][tailWs], k + 3]]]],
				eqX1]],
			"Rewrite"[eqHead],
			"Rewrite"[pop1],
			"Change"["optionBind"["optionBind"["steps"["system5Step", 2, "system5Configuration"[
				Join[Prepend[2][Prepend[d3 + 3][Prepend[d3 + 5]["shiftDown"[d1 + 1, "pairsOf"["doubleWord"[w], restStarts]]]]],
					"shiftUp"[(d1 + 1) + 2, "encodeAppendantSnd"[a, k + 3]]],
				Prepend["shiftUp"[d1 + 1, "encodeAppendantSnd"[a, k + 3]]][
					Prepend[Typed[{}, {NonNegativeIntegers}]][
						Prepend[Typed[{}, {NonNegativeIntegers}]][
							"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + (d1 + 1)]]]]]],
				Function[{Typed[y, "System5Configuration"]}, "steps"["system5Step", d3 + 1, y]]],
				Function[{Typed[y, "System5Configuration"]}, "steps"["system5Step", 2, y]]] ==
				"some"["system5Configuration"[
					"pairsOf"["doubleWord"[Join[w, a]], Join["shiftDown"[x2 + 2, restStarts], "startsOf"[a, dk + x1 + x1 + 5]]],
					"ruleBlocks"[tailWs, ("appendantCounter"[a, k] + (x2 + 2)) + 3]]]],
			"Rewrite"[pop2],
			"Change"["optionBind"["steps"["system5Step", d3 + 1, "system5Configuration"[
				Join[Prepend[d3 + 1][Prepend[d3 + 3]["shiftDown"[(d1 + 1) + 2, "pairsOf"["doubleWord"[w], restStarts]]]],
					"pairsOf"["doubleWord"[a], "startsOf"[a, (k + 3) + (d1 + 1)]]],
				Prepend[Typed[{}, {NonNegativeIntegers}]][
					Prepend[Typed[{}, {NonNegativeIntegers}]][
						"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + ((d1 + 1) + 2)]]]]],
				Function[{Typed[y, "System5Configuration"]}, "steps"["system5Step", 2, y]]] ==
				"some"["system5Configuration"[
					"pairsOf"["doubleWord"[Join[w, a]], Join["shiftDown"[x2 + 2, restStarts], "startsOf"[a, dk + x1 + x1 + 5]]],
					"ruleBlocks"[tailWs, ("appendantCounter"[a, k] + (x2 + 2)) + 3]]]],
			"Rewrite"[pop3],
			"Change"["steps"["system5Step", 2, "system5Configuration"[
				Prepend[2][Join["shiftDown"[x2, "pairsOf"["doubleWord"[w], restStarts]],
					"shiftDown"[d3 + 1, "pairsOf"["doubleWord"[a], "startsOf"[a, (k + 3) + (d1 + 1)]]]]],
				Prepend[Typed[{}, {NonNegativeIntegers}]][
					"ruleBlocks"[tailWs, "appendantCounter"[a, k + 3] + x2]]]] ==
				"some"["system5Configuration"[
					"pairsOf"["doubleWord"[Join[w, a]], Join["shiftDown"[x2 + 2, restStarts], "startsOf"[a, dk + x1 + x1 + 5]]],
					"ruleBlocks"[tailWs, ("appendantCounter"[a, k] + (x2 + 2)) + 3]]]],
			"Rewrite"[pop4],
			"Rewrite"["pairsOfShiftDown"["doubleWord"[w], x2 + 2, restStarts, hAsc]],
			"Rewrite"[appShift],
			"Rewrite"[bagJoinEq],
			"Rewrite"["appendantCounterShift"[a, k, 3]],
			"Have"[cEq, ("appendantCounter"[a, k] + 3) + (x2 + 2) == ("appendantCounter"[a, k] + (x2 + 2)) + 3], "LinearArithmetic",
			"Rewrite"[cEq],
			"Exact"["existsIntroduction"[Join["shiftDown"[x2 + 2, restStarts], "startsOf"[a, dk + x1 + x1 + 5]],
				"andIntroduction"[runEq, "andIntroduction"[newAsc, newBound]]]]
		}
	],
	(* Rung 3 main theorem: System 5 simulates any fueled cyclic tag system *)
	machineTheorem["system5Simulation",
		"forwardSimulation"["fueledCyclicTagStep", "system5Step", "system5Represents"],
		{
			"Introduce"[fc, s, fc2],
			"Cases"[fc], "Introduce"[cfg, budget],
			"Cases"[cfg], "Introduce"[data, as],
			"Cases"[budget],
			"Introduce"[rep, stepped], "Exact"["falseElimination"["noneNotSome"["FueledCyclicTag", fc2, stepped]]],
			"Introduce"[n, rep, stepped],
			"Cases"[data],
			"Introduce"[rep, stepped], "Exact"["falseElimination"["noneNotSome"["FueledCyclicTag", fc2, stepped]]],
			"Introduce"[b, w, rep, stepped],
			"Cases"[as],
			"Introduce"[rep, stepped], "Exact"["falseElimination"["noneNotSome"["FueledCyclicTag", fc2, stepped]]],
			"Introduce"[a, restAs, rep, stepped],
			"Have"[eqFc2, "fueledCyclicTag"["cyclicTagConfiguration"[Join[w, "appendantIf"[b, a]], Join[restAs, {a}]], n] == fc2],
			"Exact"["someInjective"["FueledCyclicTag", "fueledCyclicTag"["cyclicTagConfiguration"[Join[w, "appendantIf"[b, a]], Join[restAs, {a}]], n], fc2, stepped]],
			"Rewrite"["equalitySymmetry"[eqFc2]],
			"Cases"[rep], "Introduce"[bagPart, rulesPart],
			"Cases"[bagPart], "Introduce"[starts, bagBoth], "Cases"[bagBoth], "Introduce"[asc, eqBag],
			"Cases"[rulesPart], "Introduce"[k, rulesBoth], "Cases"[rulesBoth], "Introduce"[bound, eqRules],
			"Cases"[s], "Introduce"[sBag, sRules, eqBag, bound, eqRules],
			"Have"[eqBag2, sBag == "pairsOf"["doubleWord"[Prepend[b][w]], starts]], "Exact"[eqBag],
			"Have"[eqRules2, sRules == "ruleBlocks"["cycleAppendants"[Prepend[a][restAs], n + 1], k + 3]], "Exact"[eqRules],
			"Rewrite"[eqBag2], "Rewrite"[eqRules2],
			"Cases"[starts], "Introduce"[asc, eqBag, eqBag2], "Exact"["falseElimination"[asc]],
			"Introduce"[x1, starts1, asc, eqBag, eqBag2],
			"Cases"[starts1], "Introduce"[asc, eqBag, eqBag2], "Cases"[asc], "Introduce"[hx1, asc1], "Exact"["falseElimination"[asc1]],
			"Introduce"[x2, restStarts, asc, eqBag, eqBag2],
			"Cases"[asc], "Introduce"[hx1, asc1], "Cases"[asc1], "Introduce"[hx12, hAsc],
			"Have"[boundSubst, "allBelowEqual"[k, "pairsOf"["doubleWord"[Prepend[b][w]], Prepend[x1][Prepend[x2][restStarts]]]]],
			"Rewrite"["equalitySymmetry"[eqBag2]], "Exact"[bound],
			"Cases"[b],
			(* b = false *)
			"Introduce"[stepped, eqFc2, eqRules, eqBag, eqBag2, hx12, hAsc, boundSubst],
			"Have"[stepF, And[
				"steps"["system5Step", x2 + 1, "system5Configuration"[
					Prepend[x1][Prepend[x1 + 1][Prepend[x2][Prepend[x2 + 1]["pairsOf"["doubleWord"[w], restStarts]]]]],
					"ruleBlocks"[Prepend[a]["cycleAppendants"[Join[restAs, {a}], n]], k + 3]]] ==
					"some"["system5Configuration"[
						"pairsOf"["doubleWord"[w], "shiftDown"[x2 + 1, restStarts]],
						"ruleBlocks"["cycleAppendants"[Join[restAs, {a}], n], ("appendantCounter"[a, k] + (x2 + 1)) + 3]]],
				And[
					"pairsAsc"[0, "doubleWord"[w], "shiftDown"[x2 + 1, restStarts]],
					"allBelowEqual"["appendantCounter"[a, k] + (x2 + 1), "pairsOf"["doubleWord"[w], "shiftDown"[x2 + 1, restStarts]]]
				]]],
			"Have"[hx1Pos, 1 <= x1], "Exact"[hx1],
			"Have"[hx12F, x1 + 2 <= x2], "Exact"[hx12],
			"Exact"["representsStepFalse"[w, a, "cycleAppendants"[Join[restAs, {a}], n], x1, x2, restStarts, k, hx1Pos, hx12F, hAsc, boundSubst]],
			"Cases"[stepF], "Introduce"[runF, restF], "Cases"[restF], "Introduce"[ascF, boundF],
			"Have"[posF, 1 <= x2 + 1], "LinearArithmetic",
			"Have"[jw, Join[w, "appendantIf"["false", a]] == w], "Exact"["joinEmptyRight"[w]],
			"Rewrite"[jw],
			"Exact"["existsIntroduction"[x2 + 1, "andIntroduction"[posF,
				"existsIntroduction"["system5Configuration"["pairsOf"["doubleWord"[w], "shiftDown"[x2 + 1, restStarts]],
					"ruleBlocks"["cycleAppendants"[Join[restAs, {a}], n], ("appendantCounter"[a, k] + (x2 + 1)) + 3]],
					"andIntroduction"[runF, "andIntroduction"[
						"existsIntroduction"["shiftDown"[x2 + 1, restStarts], "andIntroduction"[ascF, "equalityReflexivity"["pairsOf"["doubleWord"[w], "shiftDown"[x2 + 1, restStarts]]]]],
						"existsIntroduction"["appendantCounter"[a, k] + (x2 + 1), "andIntroduction"[boundF,
							"equalityReflexivity"["ruleBlocks"["cycleAppendants"[Join[restAs, {a}], n], ("appendantCounter"[a, k] + (x2 + 1)) + 3]]]]]]]]]],
			(* b = true *)
			"Introduce"[stepped, eqFc2, eqRules, eqBag, eqBag2, hx12, hAsc, boundSubst],
			"Have"[hx1Pos, 1 <= x1], "Exact"[hx1],
			"Have"[hx12T, x1 + 3 <= x2], "Exact"[hx12],
			"Have"[stepT, Exists[{Typed[newStarts, {NonNegativeIntegers}]}, And[
				"steps"["system5Step", x2 + 2, "system5Configuration"[
					Prepend[x1][Prepend[x1 + 2][Prepend[x2][Prepend[x2 + 2]["pairsOf"["doubleWord"[w], restStarts]]]]],
					"ruleBlocks"[Prepend[a]["cycleAppendants"[Join[restAs, {a}], n]], k + 3]]] ==
					"some"["system5Configuration"[
						"pairsOf"["doubleWord"[Join[w, a]], newStarts],
						"ruleBlocks"["cycleAppendants"[Join[restAs, {a}], n], ("appendantCounter"[a, k] + (x2 + 2)) + 3]]],
				And[
					"pairsAsc"[0, "doubleWord"[Join[w, a]], newStarts],
					"allBelowEqual"["appendantCounter"[a, k] + (x2 + 2), "pairsOf"["doubleWord"[Join[w, a]], newStarts]]
				]]]],
			"Exact"["representsStepTrue"[w, a, "cycleAppendants"[Join[restAs, {a}], n], x1, x2, restStarts, k, hx1Pos, hx12T, hAsc, boundSubst]],
			"Cases"[stepT], "Introduce"[newStarts, bothT],
			"Cases"[bothT], "Introduce"[runT, restT], "Cases"[restT], "Introduce"[ascT, boundT],
			"Have"[posT, 1 <= x2 + 2], "LinearArithmetic",
			"Exact"["existsIntroduction"[x2 + 2, "andIntroduction"[posT,
				"existsIntroduction"["system5Configuration"["pairsOf"["doubleWord"[Join[w, a]], newStarts],
					"ruleBlocks"["cycleAppendants"[Join[restAs, {a}], n], ("appendantCounter"[a, k] + (x2 + 2)) + 3]],
					"andIntroduction"[runT, "andIntroduction"[
						"existsIntroduction"[newStarts, "andIntroduction"[ascT, "equalityReflexivity"["pairsOf"["doubleWord"[Join[w, a]], newStarts]]]],
						"existsIntroduction"["appendantCounter"[a, k] + (x2 + 2), "andIntroduction"[boundT,
							"equalityReflexivity"["ruleBlocks"["cycleAppendants"[Join[restAs, {a}], n], ("appendantCounter"[a, k] + (x2 + 2)) + 3]]]]]]]]]]
		}
	]
}
