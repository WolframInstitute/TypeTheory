(* ::Package:: *)

(*
Rung 4 of Smith's chain of emulations to Wolfram's (2,3) Turing machine: a fueled System 5 configuration
emulated by Smith's System 4, built on System 5 in Wolfram23System5.wl. The design is in
docs/notes/Wolfram23Universality.md.

	"strictlyIncreasing"[xs]         xs is strictly increasing (allowing 0)
	"allSetsStrictlyIncreasing"[K]   every set in K is strictly increasing
	"xorBool", "memNat", "parMem"    Boolean XOR, membership in {Nat}, and XOR-parity across a list of sets
	"hasZero4", "decr4", "decrN4"    zero membership, single decrement (dropping 0), and n-fold decrement
	"System4State",                  Smith's System 4 represented as a zipper (left, right, state) with state4A,
	"System4Element",                state4B, state4C and elements star4, set4[xs]; "system4Step" implements all
	"System4Configuration",          five transition rules
	"system4Step"[c]
	"sets4", "starredEmptyPairs",    tape constructors and the verified run macros: sweep, walk-left, C-phase,
	"system4DStep",                  D-step (two zero-free passes), pre-loop, loop iteration, final pass, and
	"system4PopPhase"                the full pop phase (moving one rule block into the active sets)
	"encodeBag4"[bag]                encodes a positive System 5 bag as even positions 2(e - 1)
	"allInts"[n], "rulePos",         the {0, ..., n-1} toggle set, rule position formula 2k + f + 3 - t,
	"encRuleSet", "encBlock",        encoded rule blocks, and the encoder "system5ToSystem4"[s, f]
	"encBlocks", "system5ToSystem4"
	"noAdjacentStarsFrom",           tape well-formedness predicates and "system5ToSystem4WellFormed" for
	"endsWithSet4", "allTapeSetsOk", Rung 5 (System 4 -> System 3)
	"system5ToSystem4WellFormed"
	"FueledSystem5",                 a System 5 configuration with elapsed step count j and budget h
	"fueledSystem5Step"
	"system4Represents"[f, fs, c]    simulation relation between fueled System 5 and System 4
	"system5ToSystem4Represents"     encoder satisfies "system4Represents" at j = 0
	"leadSets4", "decodeS4Loop",     reads the leading set block back to a System 5 bag (rejecting odd parity
	"decodeS4", "repS4DecodeBand",   as none), with 1-step turn lemma "repS4TurnStep" for Rung 7 decoding
	"repS4TurnStep"
	"repS4Exit", "repS4Terminal"     halting in state4C when rules are empty (budgeted, exposing 1 <= k)
	"repS4DStep", "repS4PStep",      D-step and P-step (double pop phase) simulation lemmas, giving
	"system4Simulation"              ForAll[f, forwardSimulation[fueledSystem5Step, system4Step, system4Represents[f]]]
*)


(* ::Section:: *)
(*PackageExported*)




(* ::Section:: *)
(*PackageScoped*)


PackageScoped[$system4Declarations]


(* ::Section:: *)
(*Usage Messages*)


$system4Declarations::usage = "$system4Declarations is the list of the declarations of rung 4 of Smith's chain (System 5 to System 4), in order, each theorem proved by its tactics in the environment so far."


(* ::Section:: *)
(*Function Definitions*)


$system4Declarations = {
	(* strictlyIncreasing[xs]: strictly increasing {Nat}, allowing 0 *)
	TypeTheoryDefinition["strictlyIncreasing", Typed[
		Function[{Typed[xs, {NonNegativeIntegers}]},
			InductiveRecursor[List][Function[{Typed[q, {NonNegativeIntegers}]}, TypeUniverse[0]], True,
				Function[{Typed[x, NonNegativeIntegers], Typed[rest, {NonNegativeIntegers}], Typed[u, TypeUniverse[0]]},
					"strictlyAbove"[x, rest]], xs]],
		{NonNegativeIntegers} -> TypeUniverse[0]
	]],
	TypeTheoryDefinition["allSetsStrictlyIncreasing", Typed[
		Function[{Typed[K, {{NonNegativeIntegers}}]},
			InductiveRecursor[List][Function[{Typed[q, {{NonNegativeIntegers}}]}, TypeUniverse[0]], True,
				Function[{Typed[s, {NonNegativeIntegers}], Typed[rest, {{NonNegativeIntegers}}], Typed[prev, TypeUniverse[0]]},
					And["strictlyIncreasing"[s], prev]], K]],
		{{NonNegativeIntegers}} -> TypeUniverse[0]
	]],
	machineTheorem["strictlyAboveImpliesIncreasing",
		ForAll[{Typed[lo, NonNegativeIntegers], Typed[xs, {NonNegativeIntegers}]},
			Implies["strictlyAbove"[lo, xs], "strictlyIncreasing"[xs]]],
		{
			"Introduce"[lo, xs], "Cases"[xs],
			"Introduce"[h], "Exact"["trueIntroduction"],
			"Introduce"[x, rest, h], "Cases"[h], "Introduce"[hx, hrest], "Exact"[hrest]
		}
	],
	machineTheorem["strictlyIncreasingTail",
		ForAll[{Typed[x, NonNegativeIntegers], Typed[rest, {NonNegativeIntegers}]},
			Implies["strictlyIncreasing"[Prepend[x][rest]], "strictlyIncreasing"[rest]]],
		{"Introduce"[x, rest, h], "Exact"["strictlyAboveImpliesIncreasing"[x, rest, h]]}
	],
	machineTheorem["allSetsStrictlyIncreasingJoin",
		ForAll[{Typed[K1, {{NonNegativeIntegers}}], Typed[K2, {{NonNegativeIntegers}}]},
			Implies["allSetsStrictlyIncreasing"[K1], Implies["allSetsStrictlyIncreasing"[K2], "allSetsStrictlyIncreasing"[Join[K1, K2]]]]],
		{
			"Introduce"[K1], "Induction"[K1],
			"Introduce"[K2, h1, h2], "Exact"[h2],
			"Introduce"[s, rest, ih, K2, h1, h2], "Cases"[h1], "Introduce"[hs, hrest],
			"Exact"["andIntroduction"[hs, ih[K2, hrest, h2]]]
		}
	],
	(* Boolean XOR *)
	TypeTheoryDefinition["xorBool", Typed[
		Function[{Typed[a, Booleans], Typed[b, Booleans]},
			InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Booleans], b,
				InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Booleans], "true", "false", b], a]],
		Booleans -> Booleans -> Booleans
	]],
	machineTheorem["xorBoolFalseRight",
		ForAll[{Typed[a, Booleans]}, "xorBool"[a, "false"] == a],
		{"Introduce"[a], "Cases"[a], "Reflexivity", "Reflexivity"}
	],
	machineTheorem["xorBoolCommutativity",
		ForAll[{Typed[a, Booleans], Typed[b, Booleans]}, "xorBool"[a, b] == "xorBool"[b, a]],
		{"Introduce"[a, b], "Cases"[a], "Cases"[b], "Reflexivity", "Reflexivity", "Cases"[b], "Reflexivity", "Reflexivity"}
	],
	machineTheorem["xorBoolAssociativity",
		ForAll[{Typed[a, Booleans], Typed[b, Booleans], Typed[c, Booleans]},
			"xorBool"["xorBool"[a, b], c] == "xorBool"[a, "xorBool"[b, c]]],
		{
			"Introduce"[a, b, c], "Cases"[a], "Reflexivity",
			"Cases"[b], "Reflexivity", "Cases"[c], "Reflexivity", "Reflexivity"
		}
	],
	machineTheorem["xorBoolSelf",
		ForAll[{Typed[a, Booleans]}, "xorBool"[a, a] == "false"],
		{"Introduce"[a], "Cases"[a], "Reflexivity", "Reflexivity"}
	],
	(* Membership in {Nat} and parity membership in {{Nat}} *)
	TypeTheoryDefinition["memNat", Typed[
		Function[{Typed[x, NonNegativeIntegers], Typed[xs, {NonNegativeIntegers}]},
			InductiveRecursor[List][Function[{Typed[q, {NonNegativeIntegers}]}, Booleans], "false",
				Function[{Typed[y, NonNegativeIntegers], Typed[rest, {NonNegativeIntegers}], Typed[prev, Booleans]},
					InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Booleans], prev, "true", Decide[x == y]]], xs]],
		NonNegativeIntegers -> {NonNegativeIntegers} -> Booleans
	]],
	TypeTheoryDefinition["parMem", Typed[
		Function[{Typed[x, NonNegativeIntegers], Typed[K, {{NonNegativeIntegers}}]},
			InductiveRecursor[List][Function[{Typed[q, {{NonNegativeIntegers}}]}, Booleans], "false",
				Function[{Typed[s, {NonNegativeIntegers}], Typed[rest, {{NonNegativeIntegers}}], Typed[prev, Booleans]},
					"xorBool"["memNat"[x, s], prev]], K]],
		NonNegativeIntegers -> {{NonNegativeIntegers}} -> Booleans
	]],
	machineTheorem["memNatStrictlyAboveFalse",
		ForAll[{Typed[x, NonNegativeIntegers], Typed[lo, NonNegativeIntegers], Typed[xs, {NonNegativeIntegers}]},
			Implies[x <= lo, Implies["strictlyAbove"[lo, xs], "memNat"[x, xs] == "false"]]],
		{
			"Introduce"[x, lo, xs], "Induction"[xs],
			"Introduce"[le, h], "Reflexivity",
			"Introduce"[y, rest, ih, le, h], "Cases"[h], "Introduce"[hy, hrest],
			"Have"[neq, Not[x == y]], "Introduce"[e], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"[f],
			"Have"[loLeY, lo <= y], "LinearArithmetic",
			"Change"[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Booleans], "memNat"[x, rest], "true", Decide[x == y]] == "false"],
			"Rewrite"["decideEqualFalse"[x, y, neq]],
			"Exact"[ih[le, "strictlyAboveWeaken"[y, lo, rest, loLeY, hrest]]]
		}
	],
	machineTheorem["parMemJoin",
		ForAll[{Typed[x, NonNegativeIntegers], Typed[K1, {{NonNegativeIntegers}}], Typed[K2, {{NonNegativeIntegers}}]},
			"parMem"[x, Join[K1, K2]] == "xorBool"["parMem"[x, K1], "parMem"[x, K2]]],
		{
			"Introduce"[x, K1], "Induction"[K1],
			"Introduce"[K2], "Reflexivity",
			"Introduce"[s, rest, ih, K2],
			"Change"["xorBool"["memNat"[x, s], "parMem"[x, Join[rest, K2]]] == "xorBool"["xorBool"["memNat"[x, s], "parMem"[x, rest]], "parMem"[x, K2]]],
			"Rewrite"[ih[K2]],
			"Exact"["equalitySymmetry"["xorBoolAssociativity"["memNat"[x, s], "parMem"[x, rest], "parMem"[x, K2]]]]
		}
	],
	(* Helper: x != y and !(x + 1 <= y) implies y + 1 <= x *)
	machineTheorem["notEqNotLtGivesGt",
		ForAll[{Typed[x, NonNegativeIntegers], Typed[y, NonNegativeIntegers]},
			Implies[Not[x == y], Implies[Not[x + 1 <= y], y + 1 <= x]]],
		{
			"Introduce"[x, y, neq, nlt],
			"Have"[sp, Or[x <= y, y < x]], "Exact"["lessEqualTotality"[x, y]],
			"Cases"[sp],
			"Introduce"[le],
			"Cases"["lessEqualExistsRight"[x, y, le]], "Introduce"[k, eq],
			"Cases"[k],
			"Introduce"[eq], "Have"[eq0, x == y], "LinearArithmetic", "Exact"["falseElimination"[neq[eq0]]],
			"Introduce"[j, eq], "Have"[lt, x + 1 <= y], "LinearArithmetic", "Exact"["falseElimination"[nlt[lt]]],
			"Introduce"[gt], "LinearArithmetic"
		}
	],
	(* xorMerge preserves strictlyAbove and strictlyIncreasing, and satisfies memNatXorMerge *)
	machineTheorem["xorMergeStrictlyAbove",
		ForAll[{Typed[xs, {NonNegativeIntegers}], Typed[ys, {NonNegativeIntegers}], Typed[lo, NonNegativeIntegers]},
			Implies["strictlyAbove"[lo, xs], Implies["strictlyAbove"[lo, ys], "strictlyAbove"[lo, "xorMerge"[xs, ys]]]]],
		{
			"Introduce"[xs], "Induction"[xs],
			"Introduce"[ys, lo, hx, hy], "Exact"[hy],
			"Introduce"[x, xsRest, ihX, ys], "Induction"[ys],
			"Introduce"[lo, hx, hy], "Exact"[hx],
			"Introduce"[y, ysRest, ihY, lo, hx, hy],
			"Cases"[hx], "Introduce"[xLo, xRestAbove],
			"Cases"[hy], "Introduce"[yLo, yRestAbove],
			"Change"["strictlyAbove"[lo, InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, {NonNegativeIntegers}],
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
			"Have"[yx, y + 1 <= x], "Exact"["notEqNotLtGivesGt"[x, y, neq, nlt]],
			"Exact"["andIntroduction"[yLo, ihY[y, "andIntroduction"[yx, xRestAbove], yRestAbove]]],
			"Introduce"[lt],
			"Exact"["andIntroduction"[xLo, ihX[Prepend[y][ysRest], x, xRestAbove, "andIntroduction"[lt, yRestAbove]]]],
			"Introduce"[eq],
			"Have"[loLeX, lo <= x], "LinearArithmetic",
			"Have"[yRestX, "strictlyAbove"[x, ysRest]], "Rewrite"[eq], "Exact"[yRestAbove],
			"Exact"["strictlyAboveWeaken"[x, lo, "xorMerge"[xsRest, ysRest], loLeX, ihX[ysRest, x, xRestAbove, yRestX]]]
		}
	],
	machineTheorem["xorMergeStrictlyIncreasing",
		ForAll[{Typed[xs, {NonNegativeIntegers}], Typed[ys, {NonNegativeIntegers}]},
			Implies["strictlyIncreasing"[xs], Implies["strictlyIncreasing"[ys], "strictlyIncreasing"["xorMerge"[xs, ys]]]]],
		{
			"Introduce"[xs, ys], "Cases"[xs],
			"Introduce"[hx, hy], "Exact"[hy],
			"Introduce"[x, xsRest], "Cases"[ys],
			"Introduce"[hx, hy], "Exact"[hx],
			"Introduce"[y, ysRest, hx, hy],
			"Change"["strictlyIncreasing"[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, {NonNegativeIntegers}],
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
			"Have"[yx, y + 1 <= x], "Exact"["notEqNotLtGivesGt"[x, y, neq, nlt]],
			"Exact"["xorMergeStrictlyAbove"[Prepend[x][xsRest], ysRest, y, "andIntroduction"[yx, hx], hy]],
			"Introduce"[lt],
			"Exact"["xorMergeStrictlyAbove"[xsRest, Prepend[y][ysRest], x, hx, "andIntroduction"[lt, hy]]],
			"Introduce"[eq],
			"Have"[yRestX, "strictlyAbove"[x, ysRest]], "Rewrite"[eq], "Exact"[hy],
			"Exact"["strictlyAboveImpliesIncreasing"[x, "xorMerge"[xsRest, ysRest], "xorMergeStrictlyAbove"[xsRest, ysRest, x, hx, yRestX]]]
		}
	],
	machineTheorem["memNatXorMerge",
		ForAll[{Typed[z, NonNegativeIntegers], Typed[xs, {NonNegativeIntegers}], Typed[ys, {NonNegativeIntegers}]},
			Implies["strictlyIncreasing"[xs], Implies["strictlyIncreasing"[ys],
				"memNat"[z, "xorMerge"[xs, ys]] == "xorBool"["memNat"[z, xs], "memNat"[z, ys]]]]],
		{
			"Introduce"[z, xs], "Induction"[xs],
			"Introduce"[ys, hx, hy], "Reflexivity",
			"Introduce"[x, xsRest, ihX, ys], "Induction"[ys],
			"Introduce"[hx, hy], "Exact"["equalitySymmetry"["xorBoolFalseRight"["memNat"[z, Prepend[x][xsRest]]]]],
			"Introduce"[y, ysRest, ihY, hx, hy],
			"Change"["memNat"[z, InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, {NonNegativeIntegers}],
				InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, {NonNegativeIntegers}],
					Prepend[y]["xorMerge"[Prepend[x][xsRest], ysRest]],
					Prepend[x]["xorMerge"[xsRest, Prepend[y][ysRest]]],
					Decide[x + 1 <= y]],
				"xorMerge"[xsRest, ysRest],
				Decide[x == y]]] ==
				"xorBool"[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Booleans], "memNat"[z, xsRest], "true", Decide[z == x]],
					InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Booleans], "memNat"[z, ysRest], "true", Decide[z == y]]]],
			"Cases"["naturalNumberEqualityDecidable"[x, y]],
			"Introduce"[neq],
			"Cases"["lessEqualDecidable"[x + 1, y]],
			(* y < x *)
			"Introduce"[nlt],
			"Have"[yx, y + 1 <= x], "Exact"["notEqNotLtGivesGt"[x, y, neq, nlt]],
			"Change"[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Booleans], "memNat"[z, "xorMerge"[Prepend[x][xsRest], ysRest]], "true", Decide[z == y]] ==
				"xorBool"[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Booleans], "memNat"[z, xsRest], "true", Decide[z == x]],
					InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Booleans], "memNat"[z, ysRest], "true", Decide[z == y]]]],
			"Cases"["naturalNumberEqualityDecidable"[z, y]],
			"Introduce"[nzy],
			"Exact"[ihY[hx, "strictlyAboveImpliesIncreasing"[y, ysRest, hy]]],
			"Introduce"[zy],
			"Have"[nzx, Not[z == x]], "Introduce"[zx], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"[f],
			"Have"[zLeX, z <= x], "LinearArithmetic",
			"Rewrite"["decideEqualFalse"[z, x, nzx]],
			"Rewrite"["memNatStrictlyAboveFalse"[z, x, xsRest, zLeX, hx]], "Reflexivity",
			(* x < y *)
			"Introduce"[lt],
			"Change"[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Booleans], "memNat"[z, "xorMerge"[xsRest, Prepend[y][ysRest]]], "true", Decide[z == x]] ==
				"xorBool"[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Booleans], "memNat"[z, xsRest], "true", Decide[z == x]],
					InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Booleans], "memNat"[z, ysRest], "true", Decide[z == y]]]],
			"Cases"["naturalNumberEqualityDecidable"[z, x]],
			"Introduce"[nzx],
			"Exact"[ihX[Prepend[y][ysRest], "strictlyAboveImpliesIncreasing"[x, xsRest, hx], hy]],
			"Introduce"[zx],
			"Have"[nzy, Not[z == y]], "Introduce"[zy], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"[f],
			"Have"[zLeY, z <= y], "LinearArithmetic",
			"Rewrite"["decideEqualFalse"[z, y, nzy]],
			"Rewrite"["memNatStrictlyAboveFalse"[z, y, ysRest, zLeY, hy]], "Reflexivity",
			(* x == y *)
			"Introduce"[eq],
			"Change"["memNat"[z, "xorMerge"[xsRest, ysRest]] ==
				"xorBool"[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Booleans], "memNat"[z, xsRest], "true", Decide[z == x]],
					InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Booleans], "memNat"[z, ysRest], "true", Decide[z == y]]]],
			"Rewrite"[ihX[ysRest, "strictlyAboveImpliesIncreasing"[x, xsRest, hx], "strictlyAboveImpliesIncreasing"[y, ysRest, hy]]],
			"Cases"["naturalNumberEqualityDecidable"[z, x]],
			"Introduce"[nzx],
			"Have"[nzy, Not[z == y]], "Introduce"[zy], "Exact"[nzx["equalityTransitivity"[zy, "equalitySymmetry"[eq]]]],
			"Rewrite"["decideEqualFalse"[z, y, nzy]], "Reflexivity",
			"Introduce"[zx],
			"Have"[zy, z == y], "Exact"["equalityTransitivity"[zx, eq]],
			"Rewrite"["decideEqualTrue"[z, y, zy]],
			"Have"[zLeX, z <= x], "LinearArithmetic",
			"Have"[zLeY, z <= y], "LinearArithmetic",
			"Rewrite"["memNatStrictlyAboveFalse"[z, x, xsRest, zLeX, hx]],
			"Rewrite"["memNatStrictlyAboveFalse"[z, y, ysRest, zLeY, hy]], "Reflexivity"
		}
	],
	(* System 4 set decrement, zero check, and iterated decrement *)
	TypeTheoryDefinition["hasZero4", Typed[
		Function[{Typed[s, {NonNegativeIntegers}]},
			InductiveRecursor[List][Function[{Typed[q, {NonNegativeIntegers}]}, Booleans], "false",
				Function[{Typed[x, NonNegativeIntegers], Typed[rest, {NonNegativeIntegers}], Typed[u, Booleans]},
					InductiveRecursor[NonNegativeIntegers][Function[{Typed[q, NonNegativeIntegers]}, Booleans], "true",
						Function[{Typed[k, NonNegativeIntegers], Typed[u2, Booleans]}, "false"], x]], s]],
		{NonNegativeIntegers} -> Booleans
	]],
	TypeTheoryDefinition["decr4", Typed[
		Function[{Typed[s, {NonNegativeIntegers}]},
			InductiveRecursor[List][Function[{Typed[q, {NonNegativeIntegers}]}, {NonNegativeIntegers}], Typed[{}, {NonNegativeIntegers}],
				Function[{Typed[x, NonNegativeIntegers], Typed[rest, {NonNegativeIntegers}], Typed[u, {NonNegativeIntegers}]},
					InductiveRecursor[NonNegativeIntegers][Function[{Typed[q, NonNegativeIntegers]}, {NonNegativeIntegers}],
						"shiftDown"[1, rest],
						Function[{Typed[k, NonNegativeIntegers], Typed[u2, {NonNegativeIntegers}]}, Prepend[k]["shiftDown"[1, rest]]], x]], s]],
		{NonNegativeIntegers} -> {NonNegativeIntegers}
	]],
	TypeTheoryDefinition["decrN4", Typed[
		Function[{Typed[n, NonNegativeIntegers], Typed[s, {NonNegativeIntegers}]},
			InductiveRecursor[NonNegativeIntegers][Function[{Typed[q, NonNegativeIntegers]}, {NonNegativeIntegers}], s,
				Function[{Typed[k, NonNegativeIntegers], Typed[prev, {NonNegativeIntegers}]}, "decr4"[prev]], n]],
		NonNegativeIntegers -> {NonNegativeIntegers} -> {NonNegativeIntegers}
	]],
	machineTheorem["hasZero4MemNat",
		ForAll[{Typed[s, {NonNegativeIntegers}]},
			Implies["strictlyIncreasing"[s], "hasZero4"[s] == "memNat"[0, s]]],
		{
			"Introduce"[s], "Cases"[s],
			"Introduce"[h], "Reflexivity",
			"Introduce"[x, rest], "Cases"[x],
			"Introduce"[h], "Reflexivity",
			"Introduce"[k, h],
			"Have"[neq, Not[0 == k + 1]], "Introduce"[e], "Exact"["successorNotZero"[k, "equalitySymmetry"[e]]],
			"Change"["false" == InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Booleans], "memNat"[0, rest], "true", Decide[0 == k + 1]]],
			"Rewrite"["decideEqualFalse"[0, k + 1, neq]],
			"Exact"["equalitySymmetry"["memNatStrictlyAboveFalse"[0, k + 1, rest, "lessEqualZero"[k + 1], h]]]
		}
	],
	machineTheorem["decr4StrictlyIncreasing",
		ForAll[{Typed[s, {NonNegativeIntegers}]},
			Implies["strictlyIncreasing"[s], "strictlyIncreasing"["decr4"[s]]]],
		{
			"Introduce"[s], "Cases"[s],
			"Introduce"[h], "Exact"["trueIntroduction"],
			"Introduce"[x, rest], "Cases"[x],
			"Introduce"[h],
			"Cases"[rest], "Introduce"[h], "Exact"["trueIntroduction"],
			"Introduce"[y, r2, h], "Cases"[h], "Introduce"[hy, hr2],
			"Cases"[y], "Introduce"[hy, hr2], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"["falseElimination"[f]],
			"Introduce"[k, hy, hr2],
			"Exact"["shiftDownStrictlyAbove"[r2, 1, k, hr2]],
			"Introduce"[k, h],
			"Exact"["shiftDownStrictlyAbove"[rest, 1, k, h]]
		}
	],
	machineTheorem["decrN4StrictlyIncreasing",
		ForAll[{Typed[n, NonNegativeIntegers], Typed[s, {NonNegativeIntegers}]},
			Implies["strictlyIncreasing"[s], "strictlyIncreasing"["decrN4"[n, s]]]],
		{
			"Introduce"[n], "Induction"[n],
			"Introduce"[s, h], "Exact"[h],
			"Introduce"[k, ih, s, h], "Exact"["decr4StrictlyIncreasing"["decrN4"[k, s], ih[s, h]]]
		}
	],
	machineTheorem["memNatShiftDown1",
		ForAll[{Typed[x, NonNegativeIntegers], Typed[xs, {NonNegativeIntegers}]},
			Implies["strictlyAbove"[0, xs], "memNat"[x, "shiftDown"[1, xs]] == "memNat"[x + 1, xs]]],
		{
			"Introduce"[x, xs], "Induction"[xs],
			"Introduce"[h], "Reflexivity",
			"Introduce"[y, rest, ih, h], "Cases"[h], "Introduce"[hy, hrest],
			"Cases"[y], "Introduce"[hy, hrest], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"["falseElimination"[f]],
			"Introduce"[k, hy, hrest],
			"Have"[hrest0, "strictlyAbove"[0, rest]], "Exact"["strictlyAboveWeaken"[k + 1, 0, rest, "lessEqualZero"[k + 1], hrest]],
			"Change"[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Booleans], "memNat"[x, "shiftDown"[1, rest]], "true", Decide[x == k]] ==
				InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Booleans], "memNat"[x + 1, rest], "true", Decide[x + 1 == k + 1]]],
			"Cases"["naturalNumberEqualityDecidable"[x, k]],
			"Introduce"[neq],
			"Have"[neq1, Not[x + 1 == k + 1]], "Introduce"[e], "Have"[e0, x == k], "LinearArithmetic", "Exact"[neq[e0]],
			"Rewrite"["decideEqualFalse"[x + 1, k + 1, neq1]],
			"Exact"[ih[hrest0]],
			"Introduce"[eq],
			"Have"[eq1, x + 1 == k + 1], "LinearArithmetic",
			"Rewrite"["decideEqualTrue"[x + 1, k + 1, eq1]], "Reflexivity"
		}
	],
	machineTheorem["memNatDecr4",
		ForAll[{Typed[x, NonNegativeIntegers], Typed[s, {NonNegativeIntegers}]},
			Implies["strictlyIncreasing"[s], "memNat"[x, "decr4"[s]] == "memNat"[x + 1, s]]],
		{
			"Introduce"[x, s], "Cases"[s],
			"Introduce"[h], "Reflexivity",
			"Introduce"[y, rest], "Cases"[y],
			"Introduce"[h],
			"Have"[neq, Not[x + 1 == 0]], "Introduce"[e], "Exact"["successorNotZero"[x, e]],
			"Change"["memNat"[x, "shiftDown"[1, rest]] ==
				InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Booleans], "memNat"[x + 1, rest], "true", Decide[x + 1 == 0]]],
			"Rewrite"["decideEqualFalse"[x + 1, 0, neq]],
			"Exact"["memNatShiftDown1"[x, rest, h]],
			"Introduce"[k, h],
			"Have"[hrest0, "strictlyAbove"[0, rest]], "Exact"["strictlyAboveWeaken"[k + 1, 0, rest, "lessEqualZero"[k + 1], h]],
			"Change"[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Booleans], "memNat"[x, "shiftDown"[1, rest]], "true", Decide[x == k]] ==
				InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Booleans], "memNat"[x + 1, rest], "true", Decide[x + 1 == k + 1]]],
			"Cases"["naturalNumberEqualityDecidable"[x, k]],
			"Introduce"[neq],
			"Have"[neq1, Not[x + 1 == k + 1]], "Introduce"[e], "Have"[e0, x == k], "LinearArithmetic", "Exact"[neq[e0]],
			"Rewrite"["decideEqualFalse"[x + 1, k + 1, neq1]],
			"Exact"["memNatShiftDown1"[x, rest, hrest0]],
			"Introduce"[eq],
			"Have"[eq1, x + 1 == k + 1], "LinearArithmetic",
			"Rewrite"["decideEqualTrue"[x + 1, k + 1, eq1]], "Reflexivity"
		}
	],
	machineTheorem["memNatDecrN4",
		ForAll[{Typed[n, NonNegativeIntegers], Typed[x, NonNegativeIntegers], Typed[s, {NonNegativeIntegers}]},
			Implies["strictlyIncreasing"[s], "memNat"[x, "decrN4"[n, s]] == "memNat"[x + n, s]]],
		{
			"Introduce"[n], "Induction"[n],
			"Introduce"[x, s, h], "Reflexivity",
			"Introduce"[k, ih, x, s, h],
			"Change"["memNat"[x, "decr4"["decrN4"[k, s]]] == "memNat"[x + (k + 1), s]],
			"Rewrite"["memNatDecr4"[x, "decrN4"[k, s], "decrN4StrictlyIncreasing"[k, s, h]]],
			"Rewrite"[ih[x + 1, s, h]],
			"Have"[eq, (x + 1) + k == x + (k + 1)], "LinearArithmetic",
			"Rewrite"[eq]
		}
	],
	machineTheorem["decrN4Step",
		ForAll[{Typed[n, NonNegativeIntegers], Typed[s, {NonNegativeIntegers}]},
			"decrN4"[n + 1, s] == "decrN4"[n, "decr4"[s]]],
		{
			"Introduce"[n], "Induction"[n],
			"Introduce"[s], "Reflexivity",
			"Introduce"[k, ih, s],
			"Change"["decr4"["decrN4"[k + 1, s]] == "decr4"["decrN4"[k, "decr4"[s]]]],
			"Rewrite"[ih[s]]
		}
	],
	machineTheorem["allSetsStrictlyIncreasingMapDecr4",
		ForAll[{Typed[K, {{NonNegativeIntegers}}]},
			Implies["allSetsStrictlyIncreasing"[K], "allSetsStrictlyIncreasing"[Map["decr4", K]]]],
		{
			"Introduce"[K], "Induction"[K],
			"Introduce"[h], "Exact"["trueIntroduction"],
			"Introduce"[s, rest, ih, h], "Cases"[h], "Introduce"[hs, hrest],
			"Exact"["andIntroduction"["decr4StrictlyIncreasing"[s, hs], ih[hrest]]]
		}
	],
	machineTheorem["parMemMapDecr4",
		ForAll[{Typed[x, NonNegativeIntegers], Typed[K, {{NonNegativeIntegers}}]},
			Implies["allSetsStrictlyIncreasing"[K], "parMem"[x, Map["decr4", K]] == "parMem"[x + 1, K]]],
		{
			"Introduce"[x, K], "Induction"[K],
			"Introduce"[h], "Reflexivity",
			"Introduce"[s, rest, ih, h], "Cases"[h], "Introduce"[hs, hrest],
			"Change"["xorBool"["memNat"[x, "decr4"[s]], "parMem"[x, Map["decr4", rest]]] == "xorBool"["memNat"[x + 1, s], "parMem"[x + 1, rest]]],
			"Rewrite"["memNatDecr4"[x, s, hs]],
			"Rewrite"[ih[hrest]]
		}
	],
	(* Generic list helpers: revAppend and replicateEmpty *)
	TypeTheoryDefinition["revAppend", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[xs, {A}]},
			InductiveRecursor[List][Function[{Typed[q, {A}]}, {A} -> {A}],
				Function[{Typed[acc, {A}]}, acc],
				Function[{Typed[x, A], Typed[rest, {A}], Typed[prev, {A} -> {A}]},
					Function[{Typed[acc, {A}]}, prev[Prepend[x][acc]]]], xs]],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, {A} -> {A} -> {A}]
	]],
	machineTheorem["revAppendJoin",
		ForAll[{TypedImplicit[A, TypeUniverse[1]], Typed[xs, {A}], Typed[ys, {A}], Typed[acc, {A}]},
			"revAppend"[Join[xs, ys], acc] == "revAppend"[ys, "revAppend"[xs, acc]]],
		{
			"Introduce"[A, xs], "Induction"[xs], "Introduce"[ys, acc], "Reflexivity",
			"Introduce"[x, rest, ih, ys, acc], "Exact"[ih[ys, Prepend[x][acc]]]
		}
	],
	machineTheorem["revAppendSplit",
		ForAll[{TypedImplicit[A, TypeUniverse[1]], Typed[xs, {A}], Typed[acc, {A}]},
			"revAppend"[xs, acc] == Join["revAppend"[xs, Typed[{}, {A}]], acc]],
		{
			"Introduce"[A, xs], "Induction"[xs], "Introduce"[acc], "Reflexivity",
			"Introduce"[x, rest, ih, acc],
			"Change"["revAppend"[rest, Prepend[x][acc]] == Join["revAppend"[rest, {x}], acc]],
			"Rewrite"[ih[Prepend[x][acc]]],
			"Rewrite"[ih[{x}]],
			"Rewrite"["joinAssociativity"["revAppend"[rest, Typed[{}, {A}]], {x}, acc]], "Reflexivity"
		}
	],
	machineTheorem["revAppendInvolution",
		ForAll[{TypedImplicit[A, TypeUniverse[1]], Typed[xs, {A}], Typed[acc, {A}]},
			"revAppend"["revAppend"[xs, Typed[{}, {A}]], acc] == Join[xs, acc]],
		{
			"Introduce"[A, xs], "Induction"[xs], "Introduce"[acc], "Reflexivity",
			"Introduce"[x, rest, ih, acc],
			"Change"["revAppend"["revAppend"[rest, {x}], acc] == Prepend[x][Join[rest, acc]]],
			"Rewrite"["revAppendSplit"[rest, {x}]],
			"Rewrite"["revAppendJoin"["revAppend"[rest, Typed[{}, {A}]], {x}, acc]],
			"Change"[Prepend[x]["revAppend"["revAppend"[rest, Typed[{}, {A}]], acc]] == Prepend[x][Join[rest, acc]]],
			"Rewrite"[ih[acc]]
		}
	],
	machineTheorem["lengthRevAppend",
		ForAll[{TypedImplicit[A, TypeUniverse[1]], Typed[xs, {A}], Typed[acc, {A}]},
			Length["revAppend"[xs, acc]] == Length[xs] + Length[acc]],
		{
			"Introduce"[A, xs], "Induction"[xs], "Introduce"[acc], "Exact"["equalitySymmetry"["additionZeroLeft"[Length[acc]]]],
			"Introduce"[x, rest, ih, acc],
			"Change"[Length["revAppend"[rest, Prepend[x][acc]]] == (Length[rest] + 1) + Length[acc]],
			"Rewrite"[ih[Prepend[x][acc]]],
			"Have"[eq, Length[rest] + (Length[acc] + 1) == (Length[rest] + 1) + Length[acc]], "LinearArithmetic",
			"Exact"[eq]
		}
	],
	machineTheorem["mapRevAppend",
		ForAll[{TypedImplicit[A, TypeUniverse[1]], TypedImplicit[B, TypeUniverse[1]], Typed[f, A -> B], Typed[xs, {A}], Typed[acc, {A}]},
			Map[f, "revAppend"[xs, acc]] == "revAppend"[Map[f, xs], Map[f, acc]]],
		{
			"Introduce"[A, B, f, xs], "Induction"[xs], "Introduce"[acc], "Reflexivity",
			"Introduce"[x, rest, ih, acc], "Exact"[ih[Prepend[x][acc]]]
		}
	],
	TypeTheoryDefinition["replicateEmpty", Typed[
		Function[{Typed[n, NonNegativeIntegers]},
			InductiveRecursor[NonNegativeIntegers][Function[{Typed[q, NonNegativeIntegers]}, {{NonNegativeIntegers}}],
				Typed[{}, {{NonNegativeIntegers}}],
				Function[{Typed[k, NonNegativeIntegers], Typed[prev, {{NonNegativeIntegers}}]}, Prepend[Typed[{}, {NonNegativeIntegers}]][prev]], n]],
		NonNegativeIntegers -> {{NonNegativeIntegers}}
	]],
	machineTheorem["replicateEmptyAppend",
		ForAll[{Typed[n, NonNegativeIntegers]},
			Join["replicateEmpty"[n], {Typed[{}, {NonNegativeIntegers}]}] == Prepend[Typed[{}, {NonNegativeIntegers}]]["replicateEmpty"[n]]],
		{
			"Introduce"[n], "Induction"[n], "Reflexivity",
			"Introduce"[k, ih],
			"Change"[Prepend[Typed[{}, {NonNegativeIntegers}]][Join["replicateEmpty"[k], {Typed[{}, {NonNegativeIntegers}]}]] ==
				Prepend[Typed[{}, {NonNegativeIntegers}]][Prepend[Typed[{}, {NonNegativeIntegers}]]["replicateEmpty"[k]]]],
			"Rewrite"[ih]
		}
	],
	machineTheorem["mapDecr4ReplicateEmpty",
		ForAll[{Typed[n, NonNegativeIntegers]}, Map["decr4", "replicateEmpty"[n]] == "replicateEmpty"[n]],
		{
			"Introduce"[n], "Induction"[n], "Reflexivity",
			"Introduce"[k, ih],
			"Change"[Prepend[Typed[{}, {NonNegativeIntegers}]][Map["decr4", "replicateEmpty"[k]]] ==
				Prepend[Typed[{}, {NonNegativeIntegers}]]["replicateEmpty"[k]]],
			"Rewrite"[ih]
		}
	],
	machineTheorem["allSetsStrictlyIncreasingReplicateEmpty",
		ForAll[{Typed[n, NonNegativeIntegers]}, "allSetsStrictlyIncreasing"["replicateEmpty"[n]]],
		{
			"Introduce"[n], "Induction"[n], "Exact"["trueIntroduction"],
			"Introduce"[k, ih], "Exact"["andIntroduction"["trueIntroduction", ih]]
		}
	],
	machineTheorem["parMemReplicateEmpty",
		ForAll[{Typed[x, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, "parMem"[x, "replicateEmpty"[n]] == "false"],
		{
			"Introduce"[x, n], "Induction"[n], "Reflexivity",
			"Introduce"[k, ih], "Change"["parMem"[x, "replicateEmpty"[k]] == "false"], "Exact"[ih]
		}
	],
	(* System 4 types and 5-rule zipper transition *)
	TypeTheoryInductiveType["System4State", TypeUniverse[1], {
		"state4A" -> "System4State",
		"state4B" -> "System4State",
		"state4C" -> "System4State"
	}],
	TypeTheoryInductiveType["System4Element", TypeUniverse[1], {
		"star4" -> "System4Element",
		"set4" -> ForAll[{Typed[s, {NonNegativeIntegers}]}, "System4Element"]
	}],
	TypeTheoryInductiveType["System4Configuration", TypeUniverse[1], {
		"system4Configuration" -> ForAll[{Typed[left, {"System4Element"}], Typed[right, {"System4Element"}], Typed[state, "System4State"]}, "System4Configuration"]
	}],
	TypeTheoryDefinition["toggleState4", Typed[
		Function[{Typed[st, "System4State"]},
			InductiveRecursor["System4State"][Function[{Typed[q, "System4State"]}, "System4State"], "state4A", "state4C", "state4B", st]],
		"System4State" -> "System4State"
	]],
	TypeTheoryDefinition["flipState4", Typed[
		Function[{Typed[b, Booleans], Typed[st, "System4State"]},
			InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, "System4State"], st, "toggleState4"[st], b]],
		Booleans -> "System4State" -> "System4State"
	]],
	TypeTheoryDefinition["isNotA", Typed[
		Function[{Typed[st, "System4State"]},
			InductiveRecursor["System4State"][Function[{Typed[q, "System4State"]}, TypeUniverse[0]], False, True, True, st]],
		"System4State" -> TypeUniverse[0]
	]],
	machineTheorem["flipState4Flip",
		ForAll[{Typed[a, Booleans], Typed[b, Booleans], Typed[st, "System4State"]},
			"flipState4"[b, "flipState4"[a, st]] == "flipState4"["xorBool"[a, b], st]],
		{
			"Introduce"[a, b, st],
			"Cases"[a], "Cases"[b], "Reflexivity", "Reflexivity",
			"Cases"[b], "Reflexivity", "Cases"[st], "Reflexivity", "Reflexivity", "Reflexivity"
		}
	],
	machineTheorem["flipState4NotA",
		ForAll[{Typed[b, Booleans], Typed[st, "System4State"]},
			Implies["isNotA"[st], "isNotA"["flipState4"[b, st]]]],
		{
			"Introduce"[b, st], "Cases"[st],
			"Introduce"[h], "Exact"["falseElimination"[h]],
			"Introduce"[h], "Cases"[b], "Exact"["trueIntroduction"], "Exact"["trueIntroduction"],
			"Introduce"[h], "Cases"[b], "Exact"["trueIntroduction"], "Exact"["trueIntroduction"]
		}
	],
	TypeTheoryDefinition["system4Step", Typed[
		Function[{Typed[c, "System4Configuration"]},
			InductiveRecursor["System4Configuration"][Function[{Typed[q, "System4Configuration"]}, Option["System4Configuration"]],
				Function[{Typed[left, {"System4Element"}], Typed[right, {"System4Element"}], Typed[st, "System4State"]},
					InductiveRecursor[List][Function[{Typed[q, {"System4Element"}]}, Option["System4Configuration"]],
						Typed["none", Option["System4Configuration"]],
						Function[{Typed[e, "System4Element"], Typed[R, {"System4Element"}], Typed[u1, Option["System4Configuration"]]},
							InductiveRecursor["System4Element"][Function[{Typed[q, "System4Element"]}, Option["System4Configuration"]],
								(* star4 *)
								InductiveRecursor["System4State"][Function[{Typed[q, "System4State"]}, Option["System4Configuration"]],
									(* Rule 2: star4 in A *)
									"some"["system4Configuration"[left, R, "state4B"]],
									(* Rule 4: star4 in B *)
									InductiveRecursor[List][Function[{Typed[q, {"System4Element"}]}, Option["System4Configuration"]],
										Typed["none", Option["System4Configuration"]],
										Function[{Typed[x, "System4Element"], Typed[L, {"System4Element"}], Typed[u2, Option["System4Configuration"]]},
											"some"["system4Configuration"[L, Prepend[x][R], "state4A"]]], left],
									(* Rule 5: star4 in C *)
									InductiveRecursor[List][Function[{Typed[q, {"System4Element"}]}, Option["System4Configuration"]],
										Typed["none", Option["System4Configuration"]],
										Function[{Typed[e2, "System4Element"], Typed[R2, {"System4Element"}], Typed[u2, Option["System4Configuration"]]},
											InductiveRecursor["System4Element"][Function[{Typed[q, "System4Element"]}, Option["System4Configuration"]],
												Typed["none", Option["System4Configuration"]],
												Function[{Typed[s, {NonNegativeIntegers}]},
													"some"["system4Configuration"[Prepend["star4"][left], Prepend["set4"["xorMerge"[{1}, s]]][R2], "state4C"]]],
												e2]], R],
									st],
								(* set4[s] *)
								Function[{Typed[s, {NonNegativeIntegers}]},
									InductiveRecursor["System4State"][Function[{Typed[q, "System4State"]}, Option["System4Configuration"]],
										(* Rule 1: set4 in A *)
										InductiveRecursor[List][Function[{Typed[q, {"System4Element"}]}, Option["System4Configuration"]],
											"some"["system4Configuration"[Typed[{}, {"System4Element"}], Prepend["set4"[s]][R], "state4B"]],
											Function[{Typed[x, "System4Element"], Typed[L, {"System4Element"}], Typed[u2, Option["System4Configuration"]]},
												"some"["system4Configuration"[L, Prepend[x][Prepend["set4"[s]][R]], "state4A"]]], left],
										(* Rule 3: set4 in B *)
										"some"["system4Configuration"[Prepend["set4"["decr4"[s]]][left], R, "flipState4"["hasZero4"[s], "state4B"]]],
										(* Rule 3: set4 in C *)
										"some"["system4Configuration"[Prepend["set4"["decr4"[s]]][left], R, "flipState4"["hasZero4"[s], "state4C"]]],
										st]],
								e]], right]], c]],
		"System4Configuration" -> Option["System4Configuration"]
	]],
	(* Tape helpers *)
	TypeTheoryDefinition["sets4", Typed[
		Function[{Typed[K, {{NonNegativeIntegers}}]}, Map["set4", K]],
		{{NonNegativeIntegers}} -> {"System4Element"}
	]],
	machineTheorem["sets4Join",
		ForAll[{Typed[K1, {{NonNegativeIntegers}}], Typed[K2, {{NonNegativeIntegers}}]},
			"sets4"[Join[K1, K2]] == Join["sets4"[K1], "sets4"[K2]]],
		{"Introduce"[K1, K2], "Exact"["mapJoin"["set4", K1, K2]]}
	],
	TypeTheoryDefinition["starredEmptyPairs", Typed[
		Function[{Typed[n, NonNegativeIntegers]},
			InductiveRecursor[NonNegativeIntegers][Function[{Typed[q, NonNegativeIntegers]}, {"System4Element"}],
				Typed[{}, {"System4Element"}],
				Function[{Typed[k, NonNegativeIntegers], Typed[prev, {"System4Element"}]},
					Prepend["star4"][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][prev]]], n]],
		NonNegativeIntegers -> {"System4Element"}
	]],
	TypeTheoryDefinition["starredZeroPairsRev", Typed[
		Function[{Typed[n, NonNegativeIntegers]},
			InductiveRecursor[NonNegativeIntegers][Function[{Typed[q, NonNegativeIntegers]}, {"System4Element"} -> {"System4Element"}],
				Function[{Typed[acc, {"System4Element"}]}, acc],
				Function[{Typed[k, NonNegativeIntegers], Typed[prev, {"System4Element"} -> {"System4Element"}]},
					Function[{Typed[acc, {"System4Element"}]}, prev[Prepend["set4"[{0}]][Prepend["star4"][acc]]]]], n]],
		NonNegativeIntegers -> {"System4Element"} -> {"System4Element"}
	]],
	machineTheorem["starredZeroPairsRevStep",
		ForAll[{Typed[n, NonNegativeIntegers], Typed[acc, {"System4Element"}]},
			"starredZeroPairsRev"[n + 1, acc] == Prepend["set4"[{0}]][Prepend["star4"]["starredZeroPairsRev"[n, acc]]]],
		{
			"Introduce"[n], "Induction"[n], "Introduce"[acc], "Reflexivity",
			"Introduce"[k, ih, acc], "Exact"[ih[Prepend["set4"[{0}]][Prepend["star4"][acc]]]]
		}
	],
	(* Rule 3 unified in B/C *)
	machineTheorem["system4StepSetBC",
		ForAll[{Typed[L, {"System4Element"}], Typed[s, {NonNegativeIntegers}], Typed[R, {"System4Element"}], Typed[st, "System4State"]},
			Implies["isNotA"[st],
				"system4Step"["system4Configuration"[L, Prepend["set4"[s]][R], st]] ==
					"some"["system4Configuration"[Prepend["set4"["decr4"[s]]][L], R, "flipState4"["hasZero4"[s], st]]]]],
		{
			"Introduce"[L, s, R, st], "Cases"[st],
			"Introduce"[h], "Exact"["falseElimination"[h]],
			"Introduce"[h], "Reflexivity",
			"Introduce"[h], "Reflexivity"
		}
	],
	(* Macro 1: B/C sweep across sets4[K] *)
	machineTheorem["system4Sweep",
		ForAll[{Typed[K, {{NonNegativeIntegers}}], Typed[L, {"System4Element"}], Typed[R, {"System4Element"}], Typed[st, "System4State"]},
			Implies["isNotA"[st], Implies["allSetsStrictlyIncreasing"[K],
				"steps"["system4Step", Length[K], "system4Configuration"[L, Join["sets4"[K], R], st]] ==
					"some"["system4Configuration"["revAppend"["sets4"[Map["decr4", K]], L], R, "flipState4"["parMem"[0, K], st]]]]]],
		{
			"Introduce"[K], "Induction"[K],
			"Introduce"[L, R, st, hNotA, hInc], "Reflexivity",
			"Introduce"[S, rest, ih, L, R, st, hNotA, hInc],
			"Cases"[hInc], "Introduce"[hS, hRest],
			"Change"["steps"["system4Step", Length[rest] + 1, "system4Configuration"[L, Prepend["set4"[S]][Join["sets4"[rest], R]], st]] ==
				"some"["system4Configuration"["revAppend"["sets4"[Map["decr4", rest]], Prepend["set4"["decr4"[S]]][L]], R,
					"flipState4"["xorBool"["memNat"[0, S], "parMem"[0, rest]], st]]]],
			"Rewrite"["additionCommutativity"[Length[rest], 1]],
			"Rewrite"["stepsAdd"["System4Configuration", "system4Step", 1, Length[rest],
				"system4Configuration"[L, Prepend["set4"[S]][Join["sets4"[rest], R]], st]]],
			"Change"["optionBind"["system4Step"["system4Configuration"[L, Prepend["set4"[S]][Join["sets4"[rest], R]], st]],
				Function[{Typed[y, "System4Configuration"]}, "steps"["system4Step", Length[rest], y]]] ==
				"some"["system4Configuration"["revAppend"["sets4"[Map["decr4", rest]], Prepend["set4"["decr4"[S]]][L]], R,
					"flipState4"["xorBool"["memNat"[0, S], "parMem"[0, rest]], st]]]],
			"Rewrite"["system4StepSetBC"[L, S, Join["sets4"[rest], R], st, hNotA]],
			"Rewrite"["hasZero4MemNat"[S, hS]],
			"Change"["steps"["system4Step", Length[rest],
				"system4Configuration"[Prepend["set4"["decr4"[S]]][L], Join["sets4"[rest], R], "flipState4"["memNat"[0, S], st]]] ==
				"some"["system4Configuration"["revAppend"["sets4"[Map["decr4", rest]], Prepend["set4"["decr4"[S]]][L]], R,
					"flipState4"["xorBool"["memNat"[0, S], "parMem"[0, rest]], st]]]],
			"Rewrite"[ih[Prepend["set4"["decr4"[S]]][L], R, "flipState4"["memNat"[0, S], st], "flipState4NotA"["memNat"[0, S], st, hNotA], hRest]],
			"Rewrite"["flipState4Flip"["memNat"[0, S], "parMem"[0, rest], st]]
		}
	],
	(* Macro 2: A walk left across Join[sets4[revK], L] with head set4[S] *)
	machineTheorem["system4WalkLeft",
		ForAll[{Typed[revK, {{NonNegativeIntegers}}], Typed[L, {"System4Element"}], Typed[S, {NonNegativeIntegers}], Typed[R, {"System4Element"}]},
			"steps"["system4Step", Length[revK], "system4Configuration"[Join["sets4"[revK], L], Prepend["set4"[S]][R], "state4A"]] ==
				"some"["system4Configuration"[L, "revAppend"["sets4"[revK], Prepend["set4"[S]][R]], "state4A"]]],
		{
			"Introduce"[revK], "Induction"[revK],
			"Introduce"[L, S, R], "Reflexivity",
			"Introduce"[T, rest, ih, L, S, R],
			"Change"["steps"["system4Step", Length[rest] + 1,
				"system4Configuration"[Prepend["set4"[T]][Join["sets4"[rest], L]], Prepend["set4"[S]][R], "state4A"]] ==
				"some"["system4Configuration"[L, "revAppend"["sets4"[rest], Prepend["set4"[T]][Prepend["set4"[S]][R]]], "state4A"]]],
			"Rewrite"["additionCommutativity"[Length[rest], 1]],
			"Rewrite"["stepsAdd"["System4Configuration", "system4Step", 1, Length[rest],
				"system4Configuration"[Prepend["set4"[T]][Join["sets4"[rest], L]], Prepend["set4"[S]][R], "state4A"]]],
			"Exact"[ih[L, T, Prepend["set4"[S]][R]]]
		}
	],
	(* Convenience corollary: walk left across revAppend[sets4[K], L] in Length[K] steps -> Join[sets4[K], Prepend[set4[S]][R]] *)
	machineTheorem["system4WalkLeftRev",
		ForAll[{Typed[K, {{NonNegativeIntegers}}], Typed[L, {"System4Element"}], Typed[S, {NonNegativeIntegers}], Typed[R, {"System4Element"}]},
			"steps"["system4Step", Length[K], "system4Configuration"["revAppend"["sets4"[K], L], Prepend["set4"[S]][R], "state4A"]] ==
				"some"["system4Configuration"[L, Join["sets4"[K], Prepend["set4"[S]][R]], "state4A"]]],
		{
			"Introduce"[K, L, S, R],
			"Have"[lenEq, Length[K] == Length["revAppend"[K, Typed[{}, {{NonNegativeIntegers}}]]]],
			"Rewrite"["lengthRevAppend"[K, Typed[{}, {{NonNegativeIntegers}}]]], "Reflexivity",
			"Have"[leftEq, "revAppend"["sets4"[K], L] == Join["sets4"["revAppend"[K, Typed[{}, {{NonNegativeIntegers}}]]], L]],
			"Rewrite"["revAppendSplit"["sets4"[K], L]],
			"Change"[Join["revAppend"[Map["set4", K], Typed[{}, {"System4Element"}]], L] == Join[Map["set4", "revAppend"[K, Typed[{}, {{NonNegativeIntegers}}]]], L]],
			"Rewrite"["mapRevAppend"["set4", K, Typed[{}, {{NonNegativeIntegers}}]]], "Reflexivity",
			"Have"[rightEq, "revAppend"["sets4"["revAppend"[K, Typed[{}, {{NonNegativeIntegers}}]]], Prepend["set4"[S]][R]] ==
				Join["sets4"[K], Prepend["set4"[S]][R]]],
			"Change"["revAppend"[Map["set4", "revAppend"[K, Typed[{}, {{NonNegativeIntegers}}]]], Prepend["set4"[S]][R]] ==
				Join["sets4"[K], Prepend["set4"[S]][R]]],
			"Rewrite"["mapRevAppend"["set4", K, Typed[{}, {{NonNegativeIntegers}}]]],
			"Exact"["revAppendInvolution"["sets4"[K], Prepend["set4"[S]][R]]],
			"Rewrite"[lenEq], "Rewrite"[leftEq],
			"Rewrite"["system4WalkLeft"["revAppend"[K, Typed[{}, {{NonNegativeIntegers}}]], L, S, R]],
			"Rewrite"[rightEq]
		}
	],
	(* Macro 3: C-phase across g starredEmptyPairs in g + g steps *)
	machineTheorem["system4CPhase",
		ForAll[{Typed[g, NonNegativeIntegers], Typed[L, {"System4Element"}], Typed[R, {"System4Element"}]},
			"steps"["system4Step", g + g, "system4Configuration"[L, Join["starredEmptyPairs"[g], R], "state4C"]] ==
				"some"["system4Configuration"["starredZeroPairsRev"[g, L], R, "state4C"]]],
		{
			"Introduce"[g], "Induction"[g],
			"Introduce"[L, R], "Reflexivity",
			"Introduce"[k, ih, L, R],
			"Have"[stepEq, (k + 1) + (k + 1) == 2 + (k + k)], "LinearArithmetic",
			"Rewrite"[stepEq],
			"Rewrite"["stepsAdd"["System4Configuration", "system4Step", 2, k + k,
				"system4Configuration"[L, Join["starredEmptyPairs"[k + 1], R], "state4C"]]],
			"Exact"[ih[Prepend["set4"[{0}]][Prepend["star4"][L]], R]]
		}
	],
	(* Split a nonempty list x :: rest into Join[init, {last}] with Length[init] == Length[rest] *)
	machineTheorem["listSplitLast",
		ForAll[{TypedImplicit[A, TypeUniverse[1]], Typed[rest, {A}], Typed[x, A]},
			Exists[{Typed[init, {A}], Typed[last, A]},
				And[Prepend[x][rest] == Join[init, {last}], Length[rest] == Length[init]]]],
		{
			"Introduce"[A, rest], "Induction"[rest],
			"Introduce"[x],
			"Exact"["existsIntroduction"[Typed[{}, {A}], "existsIntroduction"[x,
				"andIntroduction"["equalityReflexivity"[{x}], "equalityReflexivity"[0]]]]],
			"Introduce"[y, tail, ih, x],
			"Cases"[ih[y]], "Introduce"[Ki, ih1], "Cases"[ih1], "Introduce"[Sl, ih2], "Cases"[ih2], "Introduce"[eqK, eqLen],
			"Have"[eq1, Prepend[x][Prepend[y][tail]] == Join[Prepend[x][Ki], {Sl}]],
			"Change"[Prepend[x][Prepend[y][tail]] == Prepend[x][Join[Ki, {Sl}]]],
			"Rewrite"[eqK],
			"Have"[eq2, Length[Prepend[y][tail]] == Length[Prepend[x][Ki]]],
			"Change"[Length[tail] + 1 == Length[Ki] + 1],
			"Rewrite"[eqLen],
			"Exact"["existsIntroduction"[Prepend[x][Ki], "existsIntroduction"[Sl, "andIntroduction"[eq1, eq2]]]]
		}
	],
	(* Hit star4 in state B with left = revAppend[sets4[S0 :: Krest], L], delete star4, walk left across Krest -> left = L, state A *)
	machineTheorem["system4HitStarBAndReturn",
		ForAll[{Typed[S0, {NonNegativeIntegers}], Typed[Krest, {{NonNegativeIntegers}}], Typed[L, {"System4Element"}], Typed[R, {"System4Element"}]},
			"steps"["system4Step", 1 + Length[Krest],
				"system4Configuration"["revAppend"["sets4"[Prepend[S0][Krest]], L],
					Prepend["star4"][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][R]], "state4B"]] ==
				"some"["system4Configuration"[L,
					Join["sets4"[Join[Prepend[S0][Krest], {Typed[{}, {NonNegativeIntegers}]}]], R], "state4A"]]],
		{
			"Introduce"[S0, Krest, L, R],
			"Cases"["listSplitLast"[Krest, S0]], "Introduce"[Kinit, h1], "Cases"[h1], "Introduce"[Slast, h2], "Cases"[h2], "Introduce"[eqK, eqLen],
			"Rewrite"[eqK], "Rewrite"[eqLen],
			"Rewrite"["sets4Join"[Kinit, {Slast}]],
			"Rewrite"["revAppendJoin"["sets4"[Kinit], "sets4"[{Slast}], L]],
			"Change"["steps"["system4Step", 1 + Length[Kinit],
				"system4Configuration"[Prepend["set4"[Slast]]["revAppend"["sets4"[Kinit], L]],
					Prepend["star4"][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][R]], "state4B"]] ==
				"some"["system4Configuration"[L,
					Join["sets4"[Join[Join[Kinit, {Slast}], {Typed[{}, {NonNegativeIntegers}]}]], R], "state4A"]]],
			"Rewrite"["stepsAdd"["System4Configuration", "system4Step", 1, Length[Kinit],
				"system4Configuration"[Prepend["set4"[Slast]]["revAppend"["sets4"[Kinit], L]],
					Prepend["star4"][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][R]], "state4B"]]],
			"Change"["steps"["system4Step", Length[Kinit],
				"system4Configuration"["revAppend"["sets4"[Kinit], L],
					Prepend["set4"[Slast]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][R]], "state4A"]] ==
				"some"["system4Configuration"[L,
					Join["sets4"[Join[Join[Kinit, {Slast}], {Typed[{}, {NonNegativeIntegers}]}]], R], "state4A"]]],
			"Rewrite"["system4WalkLeftRev"[Kinit, L, Slast, Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][R]]],
			"Rewrite"["joinAssociativity"[Kinit, {Slast}, {Typed[{}, {NonNegativeIntegers}]}]],
			"Rewrite"["sets4Join"[Kinit, Join[{Slast}, {Typed[{}, {NonNegativeIntegers}]}]]],
			"Rewrite"["joinAssociativity"["sets4"[Kinit], "sets4"[Join[{Slast}, {Typed[{}, {NonNegativeIntegers}]}]], R]], "Reflexivity"
		}
	],
	(* One no-zero pass: turn (1) + sweep (Length[S0::Krest]) + hit star4 in B & return (1 + Length[Krest]) *)
	machineTheorem["system4PassNoZero",
		ForAll[{Typed[S0, {NonNegativeIntegers}], Typed[Krest, {{NonNegativeIntegers}}], Typed[g, NonNegativeIntegers], Typed[R, {"System4Element"}]},
			Implies["allSetsStrictlyIncreasing"[Prepend[S0][Krest]],
				Implies["parMem"[0, Prepend[S0][Krest]] == "false",
					"steps"["system4Step", (1 + Length[Prepend[S0][Krest]]) + (1 + Length[Krest]),
						"system4Configuration"[Typed[{}, {"System4Element"}],
							Join["sets4"[Prepend[S0][Krest]], Join["starredEmptyPairs"[g + 1], R]], "state4A"]] ==
					"some"["system4Configuration"[Typed[{}, {"System4Element"}],
						Join["sets4"[Join[Map["decr4", Prepend[S0][Krest]], {Typed[{}, {NonNegativeIntegers}]}]],
							Join["starredEmptyPairs"[g], R]], "state4A"]]]]],
		{
			"Introduce"[S0, Krest, g, R, hInc, hPar0],
			"Rewrite"["stepsAdd"["System4Configuration", "system4Step", 1 + Length[Prepend[S0][Krest]], 1 + Length[Krest],
				"system4Configuration"[Typed[{}, {"System4Element"}],
					Join["sets4"[Prepend[S0][Krest]], Join["starredEmptyPairs"[g + 1], R]], "state4A"]]],
			"Rewrite"["stepsAdd"["System4Configuration", "system4Step", 1, Length[Prepend[S0][Krest]],
				"system4Configuration"[Typed[{}, {"System4Element"}],
					Join["sets4"[Prepend[S0][Krest]], Join["starredEmptyPairs"[g + 1], R]], "state4A"]]],
			"Change"["optionBind"["steps"["system4Step", Length[Prepend[S0][Krest]],
				"system4Configuration"[Typed[{}, {"System4Element"}],
					Join["sets4"[Prepend[S0][Krest]], Join["starredEmptyPairs"[g + 1], R]], "state4B"]],
				Function[{Typed[y, "System4Configuration"]}, "steps"["system4Step", 1 + Length[Krest], y]]] ==
				"some"["system4Configuration"[Typed[{}, {"System4Element"}],
					Join["sets4"[Join[Map["decr4", Prepend[S0][Krest]], {Typed[{}, {NonNegativeIntegers}]}]],
						Join["starredEmptyPairs"[g], R]], "state4A"]]],
			"Rewrite"["system4Sweep"[Prepend[S0][Krest], Typed[{}, {"System4Element"}], Join["starredEmptyPairs"[g + 1], R], "state4B", "trueIntroduction", hInc]],
			"Rewrite"[hPar0],
			"Have"[lenMap, Length[Krest] == Length[Map["decr4", Krest]]],
			"Exact"["equalitySymmetry"["lengthMap"["decr4", Krest]]],
			"Change"["steps"["system4Step", 1 + Length[Krest],
				"system4Configuration"["revAppend"["sets4"[Prepend["decr4"[S0]][Map["decr4", Krest]]], Typed[{}, {"System4Element"}]],
					Prepend["star4"][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[g], R]]], "state4B"]] ==
				"some"["system4Configuration"[Typed[{}, {"System4Element"}],
					Join["sets4"[Join[Prepend["decr4"[S0]][Map["decr4", Krest]], {Typed[{}, {NonNegativeIntegers}]}]],
						Join["starredEmptyPairs"[g], R]], "state4A"]]],
			"Rewrite"[lenMap],
			"Exact"["system4HitStarBAndReturn"["decr4"[S0], Map["decr4", Krest], Typed[{}, {"System4Element"}], Join["starredEmptyPairs"[g], R]]]
		}
	],
	(* Macro 4: D-step (two no-zero passes) *)
	machineTheorem["system4DStep",
		ForAll[{Typed[S0, {NonNegativeIntegers}], Typed[Krest, {{NonNegativeIntegers}}], Typed[g, NonNegativeIntegers], Typed[R, {"System4Element"}]},
			Implies["allSetsStrictlyIncreasing"[Prepend[S0][Krest]],
				Implies["parMem"[0, Prepend[S0][Krest]] == "false",
					Implies["parMem"[0, Map["decr4", Prepend[S0][Krest]]] == "false",
						Exists[{Typed[stepsCount, NonNegativeIntegers]}, And[1 <= stepsCount,
							"steps"["system4Step", stepsCount,
								"system4Configuration"[Typed[{}, {"System4Element"}],
									Join["sets4"[Prepend[S0][Krest]], Join["starredEmptyPairs"[g + 2], R]], "state4A"]] ==
								"some"["system4Configuration"[Typed[{}, {"System4Element"}],
									Join["sets4"[Join[Map["decr4", Map["decr4", Prepend[S0][Krest]]], {Typed[{}, {NonNegativeIntegers}], Typed[{}, {NonNegativeIntegers}]}]],
										Join["starredEmptyPairs"[g], R]], "state4A"]]]]]]]],
		{
			"Introduce"[S0, Krest, g, R, hInc, hPar0, hPar1],
			"Have"[hInc1, "allSetsStrictlyIncreasing"[Map["decr4", Prepend[S0][Krest]]]],
			"Exact"["allSetsStrictlyIncreasingMapDecr4"[Prepend[S0][Krest], hInc]],
			"Have"[hInc1e, "allSetsStrictlyIncreasing"[Join[Map["decr4", Prepend[S0][Krest]], {Typed[{}, {NonNegativeIntegers}]}]]],
			"Exact"["allSetsStrictlyIncreasingJoin"[Map["decr4", Prepend[S0][Krest]], {Typed[{}, {NonNegativeIntegers}]}, hInc1, "andIntroduction"["trueIntroduction", "trueIntroduction"]]],
			"Have"[hPar1e, "parMem"[0, Join[Map["decr4", Prepend[S0][Krest]], {Typed[{}, {NonNegativeIntegers}]}]] == "false"],
			"Rewrite"["parMemJoin"[0, Map["decr4", Prepend[S0][Krest]], {Typed[{}, {NonNegativeIntegers}]}]],
			"Rewrite"[hPar1], "Reflexivity",
			"Have"[run, "steps"["system4Step",
				((1 + Length[Prepend[S0][Krest]]) + (1 + Length[Krest])) +
				((1 + Length[Prepend["decr4"[S0]][Join[Map["decr4", Krest], {Typed[{}, {NonNegativeIntegers}]}]]]) + (1 + Length[Join[Map["decr4", Krest], {Typed[{}, {NonNegativeIntegers}]}]])),
				"system4Configuration"[Typed[{}, {"System4Element"}],
					Join["sets4"[Prepend[S0][Krest]], Join["starredEmptyPairs"[g + 2], R]], "state4A"]] ==
				"some"["system4Configuration"[Typed[{}, {"System4Element"}],
					Join["sets4"[Join[Map["decr4", Map["decr4", Prepend[S0][Krest]]], {Typed[{}, {NonNegativeIntegers}], Typed[{}, {NonNegativeIntegers}]}]],
						Join["starredEmptyPairs"[g], R]], "state4A"]]],
			"Rewrite"["stepsAdd"["System4Configuration", "system4Step",
				(1 + Length[Prepend[S0][Krest]]) + (1 + Length[Krest]),
				(1 + Length[Prepend["decr4"[S0]][Join[Map["decr4", Krest], {Typed[{}, {NonNegativeIntegers}]}]]]) + (1 + Length[Join[Map["decr4", Krest], {Typed[{}, {NonNegativeIntegers}]}]]),
				"system4Configuration"[Typed[{}, {"System4Element"}],
					Join["sets4"[Prepend[S0][Krest]], Join["starredEmptyPairs"[g + 2], R]], "state4A"]]],
			"Rewrite"["system4PassNoZero"[S0, Krest, g + 1, R, hInc, hPar0]],
			"Change"["steps"["system4Step",
				(1 + Length[Prepend["decr4"[S0]][Join[Map["decr4", Krest], {Typed[{}, {NonNegativeIntegers}]}]]]) + (1 + Length[Join[Map["decr4", Krest], {Typed[{}, {NonNegativeIntegers}]}]]),
				"system4Configuration"[Typed[{}, {"System4Element"}],
					Join["sets4"[Prepend["decr4"[S0]][Join[Map["decr4", Krest], {Typed[{}, {NonNegativeIntegers}]}]]], Join["starredEmptyPairs"[g + 1], R]], "state4A"]] ==
				"some"["system4Configuration"[Typed[{}, {"System4Element"}],
					Join["sets4"[Join[Map["decr4", Map["decr4", Prepend[S0][Krest]]], {Typed[{}, {NonNegativeIntegers}], Typed[{}, {NonNegativeIntegers}]}]],
						Join["starredEmptyPairs"[g], R]], "state4A"]]],
			"Rewrite"["system4PassNoZero"["decr4"[S0], Join[Map["decr4", Krest], {Typed[{}, {NonNegativeIntegers}]}], g, R, hInc1e, hPar1e]],
			"Have"[mapEq, Join[Map["decr4", Prepend["decr4"[S0]][Join[Map["decr4", Krest], {Typed[{}, {NonNegativeIntegers}]}]]], {Typed[{}, {NonNegativeIntegers}]}] ==
				Join[Map["decr4", Map["decr4", Prepend[S0][Krest]]], {Typed[{}, {NonNegativeIntegers}], Typed[{}, {NonNegativeIntegers}]}]],
			"Change"[Join[Prepend["decr4"["decr4"[S0]]][Map["decr4", Join[Map["decr4", Krest], {Typed[{}, {NonNegativeIntegers}]}]]], {Typed[{}, {NonNegativeIntegers}]}] ==
				Join[Prepend["decr4"["decr4"[S0]]][Map["decr4", Map["decr4", Krest]]], {Typed[{}, {NonNegativeIntegers}], Typed[{}, {NonNegativeIntegers}]}]],
			"Rewrite"["mapJoin"["decr4", Map["decr4", Krest], {Typed[{}, {NonNegativeIntegers}]}]],
			"Change"[Prepend["decr4"["decr4"[S0]]][Join[Join[Map["decr4", Map["decr4", Krest]], {Typed[{}, {NonNegativeIntegers}]}], {Typed[{}, {NonNegativeIntegers}]}]] ==
				Prepend["decr4"["decr4"[S0]]][Join[Map["decr4", Map["decr4", Krest]], {Typed[{}, {NonNegativeIntegers}], Typed[{}, {NonNegativeIntegers}]}]]],
			"Rewrite"["joinAssociativity"[Map["decr4", Map["decr4", Krest]], {Typed[{}, {NonNegativeIntegers}]}, {Typed[{}, {NonNegativeIntegers}]}]], "Reflexivity",
			"Rewrite"[mapEq],
			"Have"[pos, 1 <= ((1 + Length[Prepend[S0][Krest]]) + (1 + Length[Krest])) +
				((1 + Length[Prepend["decr4"[S0]][Join[Map["decr4", Krest], {Typed[{}, {NonNegativeIntegers}]}]]]) + (1 + Length[Join[Map["decr4", Krest], {Typed[{}, {NonNegativeIntegers}]}]]))],
			"LinearArithmetic",
			"Exact"["existsIntroduction"[((1 + Length[Prepend[S0][Krest]]) + (1 + Length[Krest])) +
				((1 + Length[Prepend["decr4"[S0]][Join[Map["decr4", Krest], {Typed[{}, {NonNegativeIntegers}]}]]]) + (1 + Length[Join[Map["decr4", Krest], {Typed[{}, {NonNegativeIntegers}]}]])),
				"andIntroduction"[pos, run]]]
		}
	],
	(* Macro 5: preLoop (8 steps!) *)
	machineTheorem["system4PreLoop",
		ForAll[{Typed[L0, {"System4Element"}], Typed[Z, {NonNegativeIntegers}], Typed[Rs, {NonNegativeIntegers}], Typed[m, NonNegativeIntegers], Typed[R, {"System4Element"}]},
			Implies["hasZero4"["xorMerge"[{1}, Rs]] == "true",
				Implies["hasZero4"["decr4"["xorMerge"[{1}, Rs]]] == "false",
					"steps"["system4Step", 8,
						"system4Configuration"[Prepend["set4"[Z]][L0],
							Prepend["star4"][Prepend["set4"[Rs]][Join["starredEmptyPairs"[m + 2], R]]], "state4C"]] ==
					"some"["system4Configuration"[Prepend["set4"["decr4"["decr4"["xorMerge"[{1}, Rs]]]]][Prepend["set4"[Z]][L0]],
						Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[m], R]]], "state4A"]]]]],
		{
			"Introduce"[L0, Z, Rs, m, R, h0, h1],
			"Rewrite"["stepsAdd"["System4Configuration", "system4Step", 2, 6,
				"system4Configuration"[Prepend["set4"[Z]][L0],
					Prepend["star4"][Prepend["set4"[Rs]][Join["starredEmptyPairs"[m + 2], R]]], "state4C"]]],
			"Change"["optionBind"["some"["system4Configuration"[Prepend["set4"["decr4"["xorMerge"[{1}, Rs]]]][Prepend["star4"][Prepend["set4"[Z]][L0]]],
				Join["starredEmptyPairs"[m + 2], R], "flipState4"["hasZero4"["xorMerge"[{1}, Rs]], "state4C"]]],
				Function[{Typed[y, "System4Configuration"]}, "steps"["system4Step", 6, y]]] ==
				"some"["system4Configuration"[Prepend["set4"["decr4"["decr4"["xorMerge"[{1}, Rs]]]]][Prepend["set4"[Z]][L0]],
					Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[m], R]]], "state4A"]]],
			"Rewrite"[h0],
			"Change"["steps"["system4Step", 6,
				"system4Configuration"[Prepend["set4"["decr4"["xorMerge"[{1}, Rs]]]][Prepend["star4"][Prepend["set4"[Z]][L0]]],
					Join["starredEmptyPairs"[m + 2], R], "state4B"]] ==
				"some"["system4Configuration"[Prepend["set4"["decr4"["decr4"["xorMerge"[{1}, Rs]]]]][Prepend["set4"[Z]][L0]],
					Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[m], R]]], "state4A"]]],
			"Rewrite"["stepsAdd"["System4Configuration", "system4Step", 4, 2,
				"system4Configuration"[Prepend["set4"["decr4"["xorMerge"[{1}, Rs]]]][Prepend["star4"][Prepend["set4"[Z]][L0]]],
					Join["starredEmptyPairs"[m + 2], R], "state4B"]]],
			"Change"["optionBind"["some"["system4Configuration"[Prepend["set4"["decr4"["decr4"["xorMerge"[{1}, Rs]]]]][Prepend["set4"[Z]][L0]],
				Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[m + 1], R]], "flipState4"["hasZero4"["decr4"["xorMerge"[{1}, Rs]]], "state4B"]]],
				Function[{Typed[y, "System4Configuration"]}, "steps"["system4Step", 2, y]]] ==
				"some"["system4Configuration"[Prepend["set4"["decr4"["decr4"["xorMerge"[{1}, Rs]]]]][Prepend["set4"[Z]][L0]],
					Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[m], R]]], "state4A"]]],
			"Rewrite"[h1], "Reflexivity"
		}
	],
	(* loopK and its zipper halves: loopLeft[i, R] = {0} :: replicateEmpty[i] ++ {R}, loopK[i, R] = loopLeft[i, R] ++ replicateEmpty[i + 2] *)
	TypeTheoryDefinition["loopLeft", Typed[
		Function[{Typed[i, NonNegativeIntegers], Typed[R, {NonNegativeIntegers}]},
			Prepend[{0}][Join["replicateEmpty"[i], {R}]]],
		NonNegativeIntegers -> {NonNegativeIntegers} -> {{NonNegativeIntegers}}
	]],
	TypeTheoryDefinition["loopK", Typed[
		Function[{Typed[i, NonNegativeIntegers], Typed[R, {NonNegativeIntegers}]},
			Join["loopLeft"[i, R], "replicateEmpty"[i + 2]]],
		NonNegativeIntegers -> {NonNegativeIntegers} -> {{NonNegativeIntegers}}
	]],
	machineTheorem["allSetsStrictlyIncreasingLoopK",
		ForAll[{Typed[i, NonNegativeIntegers], Typed[R, {NonNegativeIntegers}]},
			Implies["strictlyIncreasing"[R], "allSetsStrictlyIncreasing"["loopK"[i, R]]]],
		{
			"Introduce"[i, R, hR],
			"Exact"["allSetsStrictlyIncreasingJoin"["loopLeft"[i, R], "replicateEmpty"[i + 2],
				"andIntroduction"["trueIntroduction", "allSetsStrictlyIncreasingJoin"["replicateEmpty"[i], {R},
					"allSetsStrictlyIncreasingReplicateEmpty"[i], "andIntroduction"[hR, "trueIntroduction"]]],
				"allSetsStrictlyIncreasingReplicateEmpty"[i + 2]]]
		}
	],
	machineTheorem["parMemLoopK",
		ForAll[{Typed[x, NonNegativeIntegers], Typed[i, NonNegativeIntegers], Typed[R, {NonNegativeIntegers}]},
			"parMem"[x, "loopK"[i, R]] == "xorBool"["memNat"[x, {0}], "memNat"[x, R]]],
		{
			"Introduce"[x, i, R],
			"Change"["parMem"[x, Join[Prepend[{0}][Join["replicateEmpty"[i], {R}]], "replicateEmpty"[i + 2]]] == "xorBool"["memNat"[x, {0}], "memNat"[x, R]]],
			"Rewrite"["parMemJoin"[x, Prepend[{0}][Join["replicateEmpty"[i], {R}]], "replicateEmpty"[i + 2]]],
			"Rewrite"["parMemReplicateEmpty"[x, i + 2]],
			"Rewrite"["xorBoolFalseRight"["parMem"[x, Prepend[{0}][Join["replicateEmpty"[i], {R}]]]]],
			"Change"["xorBool"["memNat"[x, {0}], "parMem"[x, Join["replicateEmpty"[i], {R}]]] == "xorBool"["memNat"[x, {0}], "memNat"[x, R]]],
			"Rewrite"["parMemJoin"[x, "replicateEmpty"[i], {R}]],
			"Rewrite"["parMemReplicateEmpty"[x, i]],
			"Change"["xorBool"["memNat"[x, {0}], "xorBool"["memNat"[x, R], "false"]] == "xorBool"["memNat"[x, {0}], "memNat"[x, R]]],
			"Rewrite"["xorBoolFalseRight"["memNat"[x, R]]]
		}
	],
	machineTheorem["parMemLoopKMapDecr4",
		ForAll[{Typed[x, NonNegativeIntegers], Typed[i, NonNegativeIntegers], Typed[R, {NonNegativeIntegers}]},
			Implies["strictlyIncreasing"[R], "parMem"[x, Map["decr4", "loopK"[i, R]]] == "memNat"[x, "decr4"[R]]]],
		{
			"Introduce"[x, i, R, hR],
			"Rewrite"["parMemMapDecr4"[x, "loopK"[i, R], "allSetsStrictlyIncreasingLoopK"[i, R, hR]]],
			"Rewrite"["parMemLoopK"[x + 1, i, R]],
			"Have"[neq, Not[x + 1 == 0]], "Introduce"[e], "Exact"["successorNotZero"[x, e]],
			"Change"["xorBool"[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Booleans], "false", "true", Decide[x + 1 == 0]], "memNat"[x + 1, R]] == "memNat"[x, "decr4"[R]]],
			"Rewrite"["decideEqualFalse"[x + 1, 0, neq]],
			"Exact"["equalitySymmetry"["memNatDecr4"[x, R, hR]]]
		}
	],
	machineTheorem["loopKStep",
		ForAll[{Typed[i, NonNegativeIntegers], Typed[R, {NonNegativeIntegers}]},
			Prepend[{0}][Map["decr4", "loopK"[i, R]]] == Join["loopLeft"[i + 1, "decr4"[R]], "replicateEmpty"[i + 2]]],
		{
			"Introduce"[i, R],
			"Change"[Prepend[{0}][Map["decr4", Join[Prepend[{0}][Join["replicateEmpty"[i], {R}]], "replicateEmpty"[i + 2]]]] ==
				Join[Prepend[{0}][Join["replicateEmpty"[i + 1], {"decr4"[R]}]], "replicateEmpty"[i + 2]]],
			"Rewrite"["mapJoin"["decr4", Prepend[{0}][Join["replicateEmpty"[i], {R}]], "replicateEmpty"[i + 2]]],
			"Rewrite"["mapDecr4ReplicateEmpty"[i + 2]],
			"Change"[Prepend[{0}][Join[Prepend[Typed[{}, {NonNegativeIntegers}]][Map["decr4", Join["replicateEmpty"[i], {R}]]], "replicateEmpty"[i + 2]]] ==
				Prepend[{0}][Join[Join[Prepend[Typed[{}, {NonNegativeIntegers}]]["replicateEmpty"[i]], {"decr4"[R]}], "replicateEmpty"[i + 2]]]],
			"Rewrite"["mapJoin"["decr4", "replicateEmpty"[i], {R}]],
			"Rewrite"["mapDecr4ReplicateEmpty"[i]], "Reflexivity"
		}
	],
	(* Macro 6: loopIter (one iteration of the loop on the zipper!) *)
	machineTheorem["system4LoopIter",
		ForAll[
			{
				Typed[L0, {"System4Element"}], Typed[n, NonNegativeIntegers], Typed[i, NonNegativeIntegers],
				Typed[Rset, {NonNegativeIntegers}], Typed[m, NonNegativeIntegers], Typed[R, {"System4Element"}]
			},
			Implies["strictlyIncreasing"[Rset],
				Implies["memNat"[0, Rset] == "true",
					Exists[{Typed[k, NonNegativeIntegers]},
						"steps"["system4Step", k,
							"system4Configuration"[
								"revAppend"["sets4"[Join["loopLeft"[i, Rset], "replicateEmpty"[i]]],
									Prepend["star4"]["starredZeroPairsRev"[n + 1, L0]]],
								Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[m + 1], R]]],
								"state4A"]] ==
						"some"["system4Configuration"[
							"revAppend"["sets4"[Join["loopLeft"[i + 1, "decr4"[Rset]], "replicateEmpty"[i + 1]]],
								Prepend["star4"]["starredZeroPairsRev"[n, L0]]],
							Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[m], R]]],
							"state4A"]]]]]
		],
		{
			"Introduce"[L0, n, i, Rset, m, R, hR, hZero],
			(* Step 1: walkLeft across Join[loopLeft[i, Rset], replicateEmpty[i]], then 1 step onto star4, then 1 step delete star4 -> state B *)
			"Have"[leftPart, Join["loopLeft"[i, Rset], "replicateEmpty"[i]] == Join["loopLeft"[i, Rset], "replicateEmpty"[i]]], "Reflexivity",
			"Have"[fullBlock, Join[Join["loopLeft"[i, Rset], "replicateEmpty"[i]], {Typed[{}, {NonNegativeIntegers}], Typed[{}, {NonNegativeIntegers}]}] == "loopK"[i, Rset]],
			"Change"[Join[Join["loopLeft"[i, Rset], "replicateEmpty"[i]], {Typed[{}, {NonNegativeIntegers}], Typed[{}, {NonNegativeIntegers}]}] ==
				Join["loopLeft"[i, Rset], "replicateEmpty"[i + 2]]],
			"Rewrite"["joinAssociativity"["loopLeft"[i, Rset], "replicateEmpty"[i], {Typed[{}, {NonNegativeIntegers}], Typed[{}, {NonNegativeIntegers}]}]],
			"Have"[rep2, Join["replicateEmpty"[i], {Typed[{}, {NonNegativeIntegers}], Typed[{}, {NonNegativeIntegers}]}] == "replicateEmpty"[i + 2]],
			"Change"[Join["replicateEmpty"[i], Join[{Typed[{}, {NonNegativeIntegers}]}, {Typed[{}, {NonNegativeIntegers}]}]] ==
				Prepend[Typed[{}, {NonNegativeIntegers}]][Prepend[Typed[{}, {NonNegativeIntegers}]]["replicateEmpty"[i]]]],
			"Rewrite"["equalitySymmetry"["joinAssociativity"["replicateEmpty"[i], {Typed[{}, {NonNegativeIntegers}]}, {Typed[{}, {NonNegativeIntegers}]}]]],
			"Rewrite"["replicateEmptyAppend"[i]],
			"Change"[Prepend[Typed[{}, {NonNegativeIntegers}]][Join["replicateEmpty"[i], {Typed[{}, {NonNegativeIntegers}]}]] ==
				Prepend[Typed[{}, {NonNegativeIntegers}]][Prepend[Typed[{}, {NonNegativeIntegers}]]["replicateEmpty"[i]]]],
			"Rewrite"["replicateEmptyAppend"[i]],
			"Rewrite"[rep2],
			"Have"[walkBack, "steps"["system4Step", Length[Join["loopLeft"[i, Rset], "replicateEmpty"[i]]] + 2,
				"system4Configuration"[
					"revAppend"["sets4"[Join["loopLeft"[i, Rset], "replicateEmpty"[i]]],
						Prepend["star4"]["starredZeroPairsRev"[n + 1, L0]]],
					Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[m + 1], R]]],
					"state4A"]] ==
				"some"["system4Configuration"["starredZeroPairsRev"[n + 1, L0],
					Join["sets4"["loopK"[i, Rset]], Join["starredEmptyPairs"[m + 1], R]], "state4B"]]],
			"Rewrite"["stepsAdd"["System4Configuration", "system4Step", Length[Join["loopLeft"[i, Rset], "replicateEmpty"[i]]], 2,
				"system4Configuration"[
					"revAppend"["sets4"[Join["loopLeft"[i, Rset], "replicateEmpty"[i]]],
						Prepend["star4"]["starredZeroPairsRev"[n + 1, L0]]],
					Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[m + 1], R]]],
					"state4A"]]],
			"Rewrite"["system4WalkLeftRev"[Join["loopLeft"[i, Rset], "replicateEmpty"[i]],
				Prepend["star4"]["starredZeroPairsRev"[n + 1, L0]],
				Typed[{}, {NonNegativeIntegers}],
				Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[m + 1], R]]]],
			"Change"["steps"["system4Step", 2,
				"system4Configuration"[Prepend["star4"]["starredZeroPairsRev"[n + 1, L0]],
					Prepend["set4"[{0}]][Join["sets4"[Join[Join["replicateEmpty"[i], {Rset}], "replicateEmpty"[i]]],
						Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[m + 1], R]]]]],
					"state4A"]] ==
				"some"["system4Configuration"["starredZeroPairsRev"[n + 1, L0],
					Join["sets4"["loopK"[i, Rset]], Join["starredEmptyPairs"[m + 1], R]], "state4B"]]],
			"Change"["some"["system4Configuration"["starredZeroPairsRev"[n + 1, L0],
				Join["sets4"[Join["loopLeft"[i, Rset], "replicateEmpty"[i]]],
					Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[m + 1], R]]]],
				"state4B"]] ==
				"some"["system4Configuration"["starredZeroPairsRev"[n + 1, L0],
					Join["sets4"["loopK"[i, Rset]], Join["starredEmptyPairs"[m + 1], R]], "state4B"]]],
			"Rewrite"["equalitySymmetry"[fullBlock]],
			"Rewrite"["sets4Join"[Join["loopLeft"[i, Rset], "replicateEmpty"[i]], {Typed[{}, {NonNegativeIntegers}], Typed[{}, {NonNegativeIntegers}]}]],
			"Rewrite"["joinAssociativity"["sets4"[Join["loopLeft"[i, Rset], "replicateEmpty"[i]]],
				"sets4"[{Typed[{}, {NonNegativeIntegers}], Typed[{}, {NonNegativeIntegers}]}],
				Join["starredEmptyPairs"[m + 1], R]]], "Reflexivity",
			(* Step 2: sweep loopK[i, Rset] in state B (parMem 0 == xor[true, true] == false!) + 1 step Rule 4 on star4 *)
			"Have"[par0, "parMem"[0, "loopK"[i, Rset]] == "false"],
			"Rewrite"["parMemLoopK"[0, i, Rset]], "Rewrite"[hZero], "Reflexivity",
			"Have"[sweepAndStar, "steps"["system4Step", Length["loopK"[i, Rset]] + 1,
				"system4Configuration"["starredZeroPairsRev"[n + 1, L0],
					Join["sets4"["loopK"[i, Rset]], Join["starredEmptyPairs"[m + 1], R]], "state4B"]] ==
				"some"["system4Configuration"[
					"revAppend"["sets4"[Join["loopLeft"[i + 1, "decr4"[Rset]], "replicateEmpty"[i + 1]]],
						Prepend["star4"]["starredZeroPairsRev"[n, L0]]],
					Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[m], R]]],
					"state4A"]]],
			"Rewrite"["stepsAdd"["System4Configuration", "system4Step", Length["loopK"[i, Rset]], 1,
				"system4Configuration"["starredZeroPairsRev"[n + 1, L0],
					Join["sets4"["loopK"[i, Rset]], Join["starredEmptyPairs"[m + 1], R]], "state4B"]]],
			"Rewrite"["system4Sweep"["loopK"[i, Rset], "starredZeroPairsRev"[n + 1, L0], Join["starredEmptyPairs"[m + 1], R],
				"state4B", "trueIntroduction", "allSetsStrictlyIncreasingLoopK"[i, Rset, hR]]],
			"Rewrite"[par0],
			"Rewrite"["starredZeroPairsRevStep"[n, L0]],
			"Have"[revShape, "revAppend"["sets4"[Map["decr4", "loopK"[i, Rset]]], Prepend["set4"[{0}]][Prepend["star4"]["starredZeroPairsRev"[n, L0]]]] ==
				Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]]["revAppend"["sets4"[Join["loopLeft"[i + 1, "decr4"[Rset]], "replicateEmpty"[i + 1]]],
					Prepend["star4"]["starredZeroPairsRev"[n, L0]]]]],
			"Change"["revAppend"["sets4"[Prepend[{0}][Map["decr4", "loopK"[i, Rset]]]], Prepend["star4"]["starredZeroPairsRev"[n, L0]]] ==
				Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]]["revAppend"["sets4"[Join["loopLeft"[i + 1, "decr4"[Rset]], "replicateEmpty"[i + 1]]],
					Prepend["star4"]["starredZeroPairsRev"[n, L0]]]]],
			"Rewrite"["loopKStep"[i, Rset]],
			"Have"[splitRep, "replicateEmpty"[i + 2] == Join["replicateEmpty"[i + 1], {Typed[{}, {NonNegativeIntegers}]}]],
			"Exact"["equalitySymmetry"["replicateEmptyAppend"[i + 1]]],
			"Rewrite"[splitRep],
			"Rewrite"["equalitySymmetry"["joinAssociativity"["loopLeft"[i + 1, "decr4"[Rset]], "replicateEmpty"[i + 1], {Typed[{}, {NonNegativeIntegers}]}]]],
			"Rewrite"["sets4Join"[Join["loopLeft"[i + 1, "decr4"[Rset]], "replicateEmpty"[i + 1]], {Typed[{}, {NonNegativeIntegers}]}]],
			"Rewrite"["revAppendJoin"["sets4"[Join["loopLeft"[i + 1, "decr4"[Rset]], "replicateEmpty"[i + 1]]],
				"sets4"[{Typed[{}, {NonNegativeIntegers}]}], Prepend["star4"]["starredZeroPairsRev"[n, L0]]]], "Reflexivity",
			"Rewrite"[revShape], "Reflexivity",
			(* Compose walkBack + sweepAndStar *)
			"Have"[full, "steps"["system4Step", (Length[Join["loopLeft"[i, Rset], "replicateEmpty"[i]]] + 2) + (Length["loopK"[i, Rset]] + 1),
				"system4Configuration"[
					"revAppend"["sets4"[Join["loopLeft"[i, Rset], "replicateEmpty"[i]]],
						Prepend["star4"]["starredZeroPairsRev"[n + 1, L0]]],
					Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[m + 1], R]]],
					"state4A"]] ==
				"some"["system4Configuration"[
					"revAppend"["sets4"[Join["loopLeft"[i + 1, "decr4"[Rset]], "replicateEmpty"[i + 1]]],
						Prepend["star4"]["starredZeroPairsRev"[n, L0]]],
					Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[m], R]]],
					"state4A"]]],
			"Rewrite"["stepsAdd"["System4Configuration", "system4Step", Length[Join["loopLeft"[i, Rset], "replicateEmpty"[i]]] + 2, Length["loopK"[i, Rset]] + 1,
				"system4Configuration"[
					"revAppend"["sets4"[Join["loopLeft"[i, Rset], "replicateEmpty"[i]]],
						Prepend["star4"]["starredZeroPairsRev"[n + 1, L0]]],
					Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[m + 1], R]]],
					"state4A"]]],
			"Rewrite"[walkBack], "Exact"[sweepAndStar],
			"Exact"["existsIntroduction"[(Length[Join["loopLeft"[i, Rset], "replicateEmpty"[i]]] + 2) + (Length["loopK"[i, Rset]] + 1), full]]
		}
	],
	(* Macro 7: loopRun (n iterations of loopIter!) *)
	machineTheorem["system4LoopRun",
		ForAll[
			{
				Typed[n, NonNegativeIntegers], Typed[L0, {"System4Element"}], Typed[i, NonNegativeIntegers],
				Typed[Rset, {NonNegativeIntegers}], Typed[m, NonNegativeIntegers], Typed[R, {"System4Element"}]
			},
			Implies["strictlyIncreasing"[Rset],
				Implies[ForAll[{Typed[q, NonNegativeIntegers]}, Implies[q + 1 <= n, "memNat"[0, "decrN4"[q, Rset]] == "true"]],
					Exists[{Typed[k, NonNegativeIntegers]},
						"steps"["system4Step", k,
							"system4Configuration"[
								"revAppend"["sets4"[Join["loopLeft"[i, Rset], "replicateEmpty"[i]]],
									Prepend["star4"]["starredZeroPairsRev"[n, L0]]],
								Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[m + n], R]]],
								"state4A"]] ==
						"some"["system4Configuration"[
							"revAppend"["sets4"[Join["loopLeft"[i + n, "decrN4"[n, Rset]], "replicateEmpty"[i + n]]],
								Prepend["star4"][L0]],
							Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[m], R]]],
							"state4A"]]]]]
		],
		{
			"Introduce"[n], "Induction"[n],
			"Introduce"[L0, i, Rset, m, R, hR, hLoop],
			"Exact"["existsIntroduction"[0, "equalityReflexivity"["some"["system4Configuration"[
				"revAppend"["sets4"[Join["loopLeft"[i, Rset], "replicateEmpty"[i]]], Prepend["star4"][L0]],
				Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[m], R]]], "state4A"]]]]],
			"Introduce"[n1, ih, L0, i, Rset, m, R, hR, hLoop],
			"Have"[h0, "memNat"[0, Rset] == "true"],
			"Have"[le0, 0 + 1 <= n1 + 1], "LinearArithmetic",
			"Exact"[hLoop[0, le0]],
			"Have"[eqM, m + (n1 + 1) == (m + n1) + 1], "LinearArithmetic",
			"Rewrite"[eqM],
			"Cases"["system4LoopIter"[L0, n1, i, Rset, m + n1, R, hR, h0]], "Introduce"[k1, e1],
			"Have"[hLoopNext, ForAll[{Typed[q, NonNegativeIntegers]}, Implies[q + 1 <= n1, "memNat"[0, "decrN4"[q, "decr4"[Rset]]] == "true"]]],
			"Introduce"[q, hq],
			"Have"[hq1, (q + 1) + 1 <= n1 + 1], "LinearArithmetic",
			"Rewrite"["equalitySymmetry"["decrN4Step"[q, Rset]]],
			"Exact"[hLoop[q + 1, hq1]],
			"Cases"[ih[L0, i + 1, "decr4"[Rset], m, R, "decr4StrictlyIncreasing"[Rset, hR], hLoopNext]], "Introduce"[k2, e2],
			"Have"[eqI, (i + 1) + n1 == i + (n1 + 1)], "LinearArithmetic",
			"Have"[eqD, "decrN4"[n1, "decr4"[Rset]] == "decrN4"[n1 + 1, Rset]],
			"Exact"["equalitySymmetry"["decrN4Step"[n1, Rset]]],
			"Have"[eBoth, "steps"["system4Step", k1 + k2,
				"system4Configuration"[
					"revAppend"["sets4"[Join["loopLeft"[i, Rset], "replicateEmpty"[i]]], Prepend["star4"]["starredZeroPairsRev"[n1 + 1, L0]]],
					Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[(m + n1) + 1], R]]],
					"state4A"]] ==
				"some"["system4Configuration"[
					"revAppend"["sets4"[Join["loopLeft"[i + (n1 + 1), "decrN4"[n1 + 1, Rset]], "replicateEmpty"[i + (n1 + 1)]]], Prepend["star4"][L0]],
					Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[m], R]]],
					"state4A"]]],
			"Rewrite"["stepsAdd"["System4Configuration", "system4Step", k1, k2,
				"system4Configuration"[
					"revAppend"["sets4"[Join["loopLeft"[i, Rset], "replicateEmpty"[i]]], Prepend["star4"]["starredZeroPairsRev"[n1 + 1, L0]]],
					Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[(m + n1) + 1], R]]],
					"state4A"]]],
			"Rewrite"[e1], "Rewrite"["equalitySymmetry"[eqI]], "Rewrite"["equalitySymmetry"[eqD]], "Exact"[e2],
			"Exact"["existsIntroduction"[k1 + k2, eBoth]]
		}
	],
	(* Macro 8: finalPass (walk left across loopLeft + replicateEmpty, delete last star, sweep loopK in state B, hit starB & return across K0 ++ Map[decr4, loopK] to left = {}) *)
	machineTheorem["system4FinalPass",
		ForAll[
			{
				Typed[S0, {NonNegativeIntegers}], Typed[K0rest, {{NonNegativeIntegers}}],
				Typed[i, NonNegativeIntegers], Typed[Rset, {NonNegativeIntegers}],
				Typed[m, NonNegativeIntegers], Typed[R, {"System4Element"}]
			},
			Implies["strictlyIncreasing"[Rset],
				Implies["memNat"[0, Rset] == "true",
					Exists[{Typed[k, NonNegativeIntegers]}, And[1 <= k,
						"steps"["system4Step", k,
							"system4Configuration"[
								"revAppend"["sets4"[Join["loopLeft"[i, Rset], "replicateEmpty"[i]]],
									Prepend["star4"]["revAppend"["sets4"[Prepend[S0][K0rest]], Typed[{}, {"System4Element"}]]]],
								Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[m + 1], R]]],
								"state4A"]] ==
						"some"["system4Configuration"[Typed[{}, {"System4Element"}],
							Join["sets4"[Join[Join[Prepend[S0][K0rest], Map["decr4", "loopK"[i, Rset]]], {Typed[{}, {NonNegativeIntegers}]}]],
								Join["starredEmptyPairs"[m], R]], "state4A"]]]]]]
		],
		{
			"Introduce"[S0, K0rest, i, Rset, m, R, hR, hZero],
			"Have"[fullBlock, Join[Join["loopLeft"[i, Rset], "replicateEmpty"[i]], {Typed[{}, {NonNegativeIntegers}], Typed[{}, {NonNegativeIntegers}]}] == "loopK"[i, Rset]],
			"Change"[Join[Join["loopLeft"[i, Rset], "replicateEmpty"[i]], {Typed[{}, {NonNegativeIntegers}], Typed[{}, {NonNegativeIntegers}]}] ==
				Join["loopLeft"[i, Rset], "replicateEmpty"[i + 2]]],
			"Rewrite"["joinAssociativity"["loopLeft"[i, Rset], "replicateEmpty"[i], {Typed[{}, {NonNegativeIntegers}], Typed[{}, {NonNegativeIntegers}]}]],
			"Have"[rep2, Join["replicateEmpty"[i], {Typed[{}, {NonNegativeIntegers}], Typed[{}, {NonNegativeIntegers}]}] == "replicateEmpty"[i + 2]],
			"Change"[Join["replicateEmpty"[i], Join[{Typed[{}, {NonNegativeIntegers}]}, {Typed[{}, {NonNegativeIntegers}]}]] ==
				Prepend[Typed[{}, {NonNegativeIntegers}]][Prepend[Typed[{}, {NonNegativeIntegers}]]["replicateEmpty"[i]]]],
			"Rewrite"["equalitySymmetry"["joinAssociativity"["replicateEmpty"[i], {Typed[{}, {NonNegativeIntegers}]}, {Typed[{}, {NonNegativeIntegers}]}]]],
			"Rewrite"["replicateEmptyAppend"[i]],
			"Change"[Prepend[Typed[{}, {NonNegativeIntegers}]][Join["replicateEmpty"[i], {Typed[{}, {NonNegativeIntegers}]}]] ==
				Prepend[Typed[{}, {NonNegativeIntegers}]][Prepend[Typed[{}, {NonNegativeIntegers}]]["replicateEmpty"[i]]]],
			"Rewrite"["replicateEmptyAppend"[i]],
			"Rewrite"[rep2],
			"Have"[walkBack, "steps"["system4Step", Length[Join["loopLeft"[i, Rset], "replicateEmpty"[i]]] + 2,
				"system4Configuration"[
					"revAppend"["sets4"[Join["loopLeft"[i, Rset], "replicateEmpty"[i]]],
						Prepend["star4"]["revAppend"["sets4"[Prepend[S0][K0rest]], Typed[{}, {"System4Element"}]]]],
					Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[m + 1], R]]],
					"state4A"]] ==
				"some"["system4Configuration"["revAppend"["sets4"[Prepend[S0][K0rest]], Typed[{}, {"System4Element"}]],
					Join["sets4"["loopK"[i, Rset]], Join["starredEmptyPairs"[m + 1], R]], "state4B"]]],
			"Rewrite"["stepsAdd"["System4Configuration", "system4Step", Length[Join["loopLeft"[i, Rset], "replicateEmpty"[i]]], 2,
				"system4Configuration"[
					"revAppend"["sets4"[Join["loopLeft"[i, Rset], "replicateEmpty"[i]]],
						Prepend["star4"]["revAppend"["sets4"[Prepend[S0][K0rest]], Typed[{}, {"System4Element"}]]]],
					Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[m + 1], R]]],
					"state4A"]]],
			"Rewrite"["system4WalkLeftRev"[Join["loopLeft"[i, Rset], "replicateEmpty"[i]],
				Prepend["star4"]["revAppend"["sets4"[Prepend[S0][K0rest]], Typed[{}, {"System4Element"}]]],
				Typed[{}, {NonNegativeIntegers}],
				Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[m + 1], R]]]],
			"Change"["some"["system4Configuration"["revAppend"["sets4"[Prepend[S0][K0rest]], Typed[{}, {"System4Element"}]],
				Join["sets4"[Join["loopLeft"[i, Rset], "replicateEmpty"[i]]],
					Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[m + 1], R]]]],
				"state4B"]] ==
				"some"["system4Configuration"["revAppend"["sets4"[Prepend[S0][K0rest]], Typed[{}, {"System4Element"}]],
					Join["sets4"["loopK"[i, Rset]], Join["starredEmptyPairs"[m + 1], R]], "state4B"]]],
			"Rewrite"["equalitySymmetry"[fullBlock]],
			"Rewrite"["sets4Join"[Join["loopLeft"[i, Rset], "replicateEmpty"[i]], {Typed[{}, {NonNegativeIntegers}], Typed[{}, {NonNegativeIntegers}]}]],
			"Rewrite"["joinAssociativity"["sets4"[Join["loopLeft"[i, Rset], "replicateEmpty"[i]]],
				"sets4"[{Typed[{}, {NonNegativeIntegers}], Typed[{}, {NonNegativeIntegers}]}],
				Join["starredEmptyPairs"[m + 1], R]]], "Reflexivity",
			"Have"[par0, "parMem"[0, "loopK"[i, Rset]] == "false"],
			"Rewrite"["parMemLoopK"[0, i, Rset]], "Rewrite"[hZero], "Reflexivity",
			"Have"[sweepPart, "steps"["system4Step", Length["loopK"[i, Rset]],
				"system4Configuration"["revAppend"["sets4"[Prepend[S0][K0rest]], Typed[{}, {"System4Element"}]],
					Join["sets4"["loopK"[i, Rset]], Join["starredEmptyPairs"[m + 1], R]], "state4B"]] ==
				"some"["system4Configuration"["revAppend"["sets4"[Join[Prepend[S0][K0rest], Map["decr4", "loopK"[i, Rset]]]], Typed[{}, {"System4Element"}]],
					Prepend["star4"][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[m], R]]], "state4B"]]],
			"Rewrite"["system4Sweep"["loopK"[i, Rset], "revAppend"["sets4"[Prepend[S0][K0rest]], Typed[{}, {"System4Element"}]],
				Join["starredEmptyPairs"[m + 1], R], "state4B", "trueIntroduction", "allSetsStrictlyIncreasingLoopK"[i, Rset, hR]]],
			"Rewrite"[par0],
			"Rewrite"["sets4Join"[Prepend[S0][K0rest], Map["decr4", "loopK"[i, Rset]]]],
			"Rewrite"["revAppendJoin"["sets4"[Prepend[S0][K0rest]], "sets4"[Map["decr4", "loopK"[i, Rset]]], Typed[{}, {"System4Element"}]]], "Reflexivity",
			"Have"[retPart, "steps"["system4Step", 1 + Length[Join[K0rest, Map["decr4", "loopK"[i, Rset]]]],
				"system4Configuration"["revAppend"["sets4"[Join[Prepend[S0][K0rest], Map["decr4", "loopK"[i, Rset]]]], Typed[{}, {"System4Element"}]],
					Prepend["star4"][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[m], R]]], "state4B"]] ==
				"some"["system4Configuration"[Typed[{}, {"System4Element"}],
					Join["sets4"[Join[Join[Prepend[S0][K0rest], Map["decr4", "loopK"[i, Rset]]], {Typed[{}, {NonNegativeIntegers}]}]],
						Join["starredEmptyPairs"[m], R]], "state4A"]]],
			"Exact"["system4HitStarBAndReturn"[S0, Join[K0rest, Map["decr4", "loopK"[i, Rset]]], Typed[{}, {"System4Element"}], Join["starredEmptyPairs"[m], R]]],
			"Have"[full, "steps"["system4Step",
				((Length[Join["loopLeft"[i, Rset], "replicateEmpty"[i]]] + 2) + Length["loopK"[i, Rset]]) + (1 + Length[Join[K0rest, Map["decr4", "loopK"[i, Rset]]]]),
				"system4Configuration"[
					"revAppend"["sets4"[Join["loopLeft"[i, Rset], "replicateEmpty"[i]]],
						Prepend["star4"]["revAppend"["sets4"[Prepend[S0][K0rest]], Typed[{}, {"System4Element"}]]]],
					Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[m + 1], R]]],
					"state4A"]] ==
				"some"["system4Configuration"[Typed[{}, {"System4Element"}],
					Join["sets4"[Join[Join[Prepend[S0][K0rest], Map["decr4", "loopK"[i, Rset]]], {Typed[{}, {NonNegativeIntegers}]}]],
						Join["starredEmptyPairs"[m], R]], "state4A"]]],
			"Rewrite"["stepsAdd"["System4Configuration", "system4Step",
				(Length[Join["loopLeft"[i, Rset], "replicateEmpty"[i]]] + 2) + Length["loopK"[i, Rset]],
				1 + Length[Join[K0rest, Map["decr4", "loopK"[i, Rset]]]],
				"system4Configuration"[
					"revAppend"["sets4"[Join["loopLeft"[i, Rset], "replicateEmpty"[i]]],
						Prepend["star4"]["revAppend"["sets4"[Prepend[S0][K0rest]], Typed[{}, {"System4Element"}]]]],
					Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[m + 1], R]]],
					"state4A"]]],
			"Rewrite"["stepsAdd"["System4Configuration", "system4Step",
				Length[Join["loopLeft"[i, Rset], "replicateEmpty"[i]]] + 2,
				Length["loopK"[i, Rset]],
				"system4Configuration"[
					"revAppend"["sets4"[Join["loopLeft"[i, Rset], "replicateEmpty"[i]]],
						Prepend["star4"]["revAppend"["sets4"[Prepend[S0][K0rest]], Typed[{}, {"System4Element"}]]]],
					Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[m + 1], R]]],
					"state4A"]]],
			"Rewrite"[walkBack], "Change"["optionBind"["steps"["system4Step", Length["loopK"[i, Rset]],
				"system4Configuration"["revAppend"["sets4"[Prepend[S0][K0rest]], Typed[{}, {"System4Element"}]],
					Join["sets4"["loopK"[i, Rset]], Join["starredEmptyPairs"[m + 1], R]], "state4B"]],
				Function[{Typed[y, "System4Configuration"]}, "steps"["system4Step", 1 + Length[Join[K0rest, Map["decr4", "loopK"[i, Rset]]]], y]]] ==
				"some"["system4Configuration"[Typed[{}, {"System4Element"}],
					Join["sets4"[Join[Join[Prepend[S0][K0rest], Map["decr4", "loopK"[i, Rset]]], {Typed[{}, {NonNegativeIntegers}]}]],
						Join["starredEmptyPairs"[m], R]], "state4A"]]],
			"Rewrite"[sweepPart], "Exact"[retPart],
			"Have"[pos, 1 <= ((Length[Join["loopLeft"[i, Rset], "replicateEmpty"[i]]] + 2) + Length["loopK"[i, Rset]]) + (1 + Length[Join[K0rest, Map["decr4", "loopK"[i, Rset]]]])],
			"LinearArithmetic",
			"Exact"["existsIntroduction"[((Length[Join["loopLeft"[i, Rset], "replicateEmpty"[i]]] + 2) + Length["loopK"[i, Rset]]) + (1 + Length[Join[K0rest, Map["decr4", "loopK"[i, Rset]]]]),
				"andIntroduction"[pos, full]]]
		}
	],
	(* Macro 9: Complete popPhase! *)
	machineTheorem["system4PopPhase",
		ForAll[
			{
				Typed[S0, {NonNegativeIntegers}], Typed[Krest, {{NonNegativeIntegers}}],
				Typed[g1, NonNegativeIntegers], Typed[Rs, {NonNegativeIntegers}],
				Typed[mRem, NonNegativeIntegers], Typed[R, {"System4Element"}]
			},
			Implies["allSetsStrictlyIncreasing"[Prepend[S0][Krest]],
				Implies["strictlyIncreasing"[Rs],
					Implies["parMem"[0, Prepend[S0][Krest]] == "true",
						Implies["memNat"[0, "xorMerge"[{1}, Rs]] == "true",
							Implies["memNat"[1, "xorMerge"[{1}, Rs]] == "false",
								Implies[ForAll[{Typed[q, NonNegativeIntegers]}, Implies[q + 1 <= g1 + 1, "memNat"[q + 2, "xorMerge"[{1}, Rs]] == "true"]],
									Exists[{Typed[k, NonNegativeIntegers]}, And[1 <= k,
										"steps"["system4Step", k,
											"system4Configuration"[Typed[{}, {"System4Element"}],
												Join["sets4"[Prepend[S0][Krest]],
													Join["starredEmptyPairs"[g1 + 1],
														Prepend["star4"][Prepend["set4"[Rs]][Join["starredEmptyPairs"[mRem + (g1 + 3)], R]]]]],
												"state4A"]] ==
										"some"["system4Configuration"[Typed[{}, {"System4Element"}],
											Join["sets4"[Join[Join[Map["decr4", Prepend[S0][Krest]],
												Map["decr4", "loopK"[g1, "decrN4"[g1 + 2, "xorMerge"[{1}, Rs]]]]], {Typed[{}, {NonNegativeIntegers}]}]],
												Join["starredEmptyPairs"[mRem], R]],
											"state4A"]]]]]]]]]]
		],
		{
			"Introduce"[S0, Krest, g1, Rs, mRem, R, hInc, hRsInc, hPar0, hX0, hX1, hXloop],
			"Have"[hXInc, "strictlyIncreasing"["xorMerge"[{1}, Rs]]],
			"Exact"["xorMergeStrictlyIncreasing"[{1}, Rs, "trueIntroduction", hRsInc]],
			"Have"[hHas0, "hasZero4"["xorMerge"[{1}, Rs]] == "true"],
			"Rewrite"["hasZero4MemNat"["xorMerge"[{1}, Rs], hXInc]], "Exact"[hX0],
			"Have"[hHas1, "hasZero4"["decr4"["xorMerge"[{1}, Rs]]] == "false"],
			"Rewrite"["hasZero4MemNat"["decr4"["xorMerge"[{1}, Rs]], "decr4StrictlyIncreasing"["xorMerge"[{1}, Rs], hXInc]]],
			"Rewrite"["memNatDecr4"[0, "xorMerge"[{1}, Rs], hXInc]], "Exact"[hX1],
			"Have"[tailAll, "starredEmptyPairs"[mRem + (g1 + 3)] == "starredEmptyPairs"[((mRem + 1) + g1) + 2]],
			"Have"[eqM, mRem + (g1 + 3) == ((mRem + 1) + g1) + 2], "LinearArithmetic", "Rewrite"[eqM],
			"Rewrite"[tailAll],
			(* Part 1: turn (1) + sweep (Length[K]) + cPhase ((g1+1)+(g1+1)) + preLoop (8) *)
			"Have"[p1, "steps"["system4Step", ((1 + Length[Prepend[S0][Krest]]) + ((g1 + 1) + (g1 + 1))) + 8,
				"system4Configuration"[Typed[{}, {"System4Element"}],
					Join["sets4"[Prepend[S0][Krest]],
						Join["starredEmptyPairs"[g1 + 1],
							Prepend["star4"][Prepend["set4"[Rs]][Join["starredEmptyPairs"[((mRem + 1) + g1) + 2], R]]]]],
					"state4A"]] ==
				"some"["system4Configuration"[
					"revAppend"["sets4"[Join["loopLeft"[0, "decr4"["decr4"["xorMerge"[{1}, Rs]]]], "replicateEmpty"[0]]],
						Prepend["star4"]["starredZeroPairsRev"[g1, "revAppend"["sets4"[Map["decr4", Prepend[S0][Krest]]], Typed[{}, {"System4Element"}]]]]],
					Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[(mRem + 1) + g1], R]]],
					"state4A"]]],
			"Rewrite"["stepsAdd"["System4Configuration", "system4Step", (1 + Length[Prepend[S0][Krest]]) + ((g1 + 1) + (g1 + 1)), 8,
				"system4Configuration"[Typed[{}, {"System4Element"}],
					Join["sets4"[Prepend[S0][Krest]],
						Join["starredEmptyPairs"[g1 + 1],
							Prepend["star4"][Prepend["set4"[Rs]][Join["starredEmptyPairs"[((mRem + 1) + g1) + 2], R]]]]],
					"state4A"]]],
			"Rewrite"["stepsAdd"["System4Configuration", "system4Step", 1 + Length[Prepend[S0][Krest]], (g1 + 1) + (g1 + 1),
				"system4Configuration"[Typed[{}, {"System4Element"}],
					Join["sets4"[Prepend[S0][Krest]],
						Join["starredEmptyPairs"[g1 + 1],
							Prepend["star4"][Prepend["set4"[Rs]][Join["starredEmptyPairs"[((mRem + 1) + g1) + 2], R]]]]],
					"state4A"]]],
			"Rewrite"["stepsAdd"["System4Configuration", "system4Step", 1, Length[Prepend[S0][Krest]],
				"system4Configuration"[Typed[{}, {"System4Element"}],
					Join["sets4"[Prepend[S0][Krest]],
						Join["starredEmptyPairs"[g1 + 1],
							Prepend["star4"][Prepend["set4"[Rs]][Join["starredEmptyPairs"[((mRem + 1) + g1) + 2], R]]]]],
					"state4A"]]],
			"Change"["optionBind"["optionBind"["steps"["system4Step", Length[Prepend[S0][Krest]],
				"system4Configuration"[Typed[{}, {"System4Element"}],
					Join["sets4"[Prepend[S0][Krest]],
						Join["starredEmptyPairs"[g1 + 1],
							Prepend["star4"][Prepend["set4"[Rs]][Join["starredEmptyPairs"[((mRem + 1) + g1) + 2], R]]]]],
					"state4B"]],
				Function[{Typed[y, "System4Configuration"]}, "steps"["system4Step", (g1 + 1) + (g1 + 1), y]]],
				Function[{Typed[y, "System4Configuration"]}, "steps"["system4Step", 8, y]]] ==
				"some"["system4Configuration"[
					"revAppend"["sets4"[Join["loopLeft"[0, "decr4"["decr4"["xorMerge"[{1}, Rs]]]], "replicateEmpty"[0]]],
						Prepend["star4"]["starredZeroPairsRev"[g1, "revAppend"["sets4"[Map["decr4", Prepend[S0][Krest]]], Typed[{}, {"System4Element"}]]]]],
					Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[(mRem + 1) + g1], R]]],
					"state4A"]]],
			"Rewrite"["system4Sweep"[Prepend[S0][Krest], Typed[{}, {"System4Element"}],
				Join["starredEmptyPairs"[g1 + 1], Prepend["star4"][Prepend["set4"[Rs]][Join["starredEmptyPairs"[((mRem + 1) + g1) + 2], R]]]],
				"state4B", "trueIntroduction", hInc]],
			"Rewrite"[hPar0],
			"Change"["optionBind"["steps"["system4Step", (g1 + 1) + (g1 + 1),
				"system4Configuration"["revAppend"["sets4"[Map["decr4", Prepend[S0][Krest]]], Typed[{}, {"System4Element"}]],
					Join["starredEmptyPairs"[g1 + 1], Prepend["star4"][Prepend["set4"[Rs]][Join["starredEmptyPairs"[((mRem + 1) + g1) + 2], R]]]],
					"state4C"]],
				Function[{Typed[y, "System4Configuration"]}, "steps"["system4Step", 8, y]]] ==
				"some"["system4Configuration"[
					"revAppend"["sets4"[Join["loopLeft"[0, "decr4"["decr4"["xorMerge"[{1}, Rs]]]], "replicateEmpty"[0]]],
						Prepend["star4"]["starredZeroPairsRev"[g1, "revAppend"["sets4"[Map["decr4", Prepend[S0][Krest]]], Typed[{}, {"System4Element"}]]]]],
					Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[(mRem + 1) + g1], R]]],
					"state4A"]]],
			"Rewrite"["system4CPhase"[g1 + 1, "revAppend"["sets4"[Map["decr4", Prepend[S0][Krest]]], Typed[{}, {"System4Element"}]],
				Prepend["star4"][Prepend["set4"[Rs]][Join["starredEmptyPairs"[((mRem + 1) + g1) + 2], R]]]]],
			"Rewrite"["starredZeroPairsRevStep"[g1, "revAppend"["sets4"[Map["decr4", Prepend[S0][Krest]]], Typed[{}, {"System4Element"}]]]],
			"Change"["steps"["system4Step", 8,
				"system4Configuration"[Prepend["set4"[{0}]][Prepend["star4"]["starredZeroPairsRev"[g1, "revAppend"["sets4"[Map["decr4", Prepend[S0][Krest]]], Typed[{}, {"System4Element"}]]]]],
					Prepend["star4"][Prepend["set4"[Rs]][Join["starredEmptyPairs"[((mRem + 1) + g1) + 2], R]]],
					"state4C"]] ==
				"some"["system4Configuration"[
					Prepend["set4"["decr4"["decr4"["xorMerge"[{1}, Rs]]]]][Prepend["set4"[{0}]][Prepend["star4"]["starredZeroPairsRev"[g1, "revAppend"["sets4"[Map["decr4", Prepend[S0][Krest]]], Typed[{}, {"System4Element"}]]]]]],
					Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[(mRem + 1) + g1], R]]],
					"state4A"]]],
			"Exact"["system4PreLoop"[Prepend["star4"]["starredZeroPairsRev"[g1, "revAppend"["sets4"[Map["decr4", Prepend[S0][Krest]]], Typed[{}, {"System4Element"}]]]],
				{0}, Rs, (mRem + 1) + g1, R, hHas0, hHas1]],
			(* Part 2: loopRun g1 times *)
			"Have"[hD2Inc, "strictlyIncreasing"["decr4"["decr4"["xorMerge"[{1}, Rs]]]]],
			"Exact"["decr4StrictlyIncreasing"["decr4"["xorMerge"[{1}, Rs]], "decr4StrictlyIncreasing"["xorMerge"[{1}, Rs], hXInc]]],
			"Have"[hLoopCond, ForAll[{Typed[q, NonNegativeIntegers]}, Implies[q + 1 <= g1, "memNat"[0, "decrN4"[q, "decr4"["decr4"["xorMerge"[{1}, Rs]]]]] == "true"]]],
			"Introduce"[q, hq],
			"Rewrite"["memNatDecrN4"[q, 0, "decr4"["decr4"["xorMerge"[{1}, Rs]]], hD2Inc]],
			"Rewrite"["additionZeroLeft"[q]],
			"Rewrite"["memNatDecr4"[q, "decr4"["xorMerge"[{1}, Rs]], "decr4StrictlyIncreasing"["xorMerge"[{1}, Rs], hXInc]]],
			"Rewrite"["memNatDecr4"[q + 1, "xorMerge"[{1}, Rs], hXInc]],
			"Have"[hq1, q + 1 <= g1 + 1], "LinearArithmetic",
			"Exact"[hXloop[q, hq1]],
			"Cases"["system4LoopRun"[g1, "revAppend"["sets4"[Map["decr4", Prepend[S0][Krest]]], Typed[{}, {"System4Element"}]],
				0, "decr4"["decr4"["xorMerge"[{1}, Rs]]], mRem + 1, R, hD2Inc, hLoopCond]],
			"Introduce"[kLoop, eLoop],
			(* Simplify decrN4[g1, decr4[decr4[X]]] == decrN4[g1 + 2, X] *)
			"Have"[eqDecr, "decrN4"[g1, "decr4"["decr4"["xorMerge"[{1}, Rs]]]] == "decrN4"[g1 + 2, "xorMerge"[{1}, Rs]]],
			"Rewrite"["decrN4Step"[g1 + 1, "xorMerge"[{1}, Rs]]],
			"Exact"["equalitySymmetry"["decrN4Step"[g1, "decr4"["xorMerge"[{1}, Rs]]]]],
			(* Part 3: finalPass *)
			"Have"[hFinalZero, "memNat"[0, "decrN4"[g1 + 2, "xorMerge"[{1}, Rs]]] == "true"],
			"Rewrite"["memNatDecrN4"[g1 + 2, 0, "xorMerge"[{1}, Rs], hXInc]],
			"Rewrite"["additionZeroLeft"[g1 + 2]],
			"Have"[hqEnd, g1 + 1 <= g1 + 1], "LinearArithmetic",
			"Exact"[hXloop[g1, hqEnd]],
			"Cases"["system4FinalPass"["decr4"[S0], Map["decr4", Krest], g1, "decrN4"[g1 + 2, "xorMerge"[{1}, Rs]], mRem, R,
				"decrN4StrictlyIncreasing"[g1 + 2, "xorMerge"[{1}, Rs], hXInc], hFinalZero]],
			"Introduce"[kFin, finBoth], "Cases"[finBoth], "Introduce"[posFin, eFin],
			(* Compose Part 1 + Part 2 + Part 3 *)
			"Have"[eAll, "steps"["system4Step", ((((1 + Length[Prepend[S0][Krest]]) + ((g1 + 1) + (g1 + 1))) + 8) + kLoop) + kFin,
				"system4Configuration"[Typed[{}, {"System4Element"}],
					Join["sets4"[Prepend[S0][Krest]],
						Join["starredEmptyPairs"[g1 + 1],
							Prepend["star4"][Prepend["set4"[Rs]][Join["starredEmptyPairs"[((mRem + 1) + g1) + 2], R]]]]],
					"state4A"]] ==
				"some"["system4Configuration"[Typed[{}, {"System4Element"}],
					Join["sets4"[Join[Join[Map["decr4", Prepend[S0][Krest]],
						Map["decr4", "loopK"[g1, "decrN4"[g1 + 2, "xorMerge"[{1}, Rs]]]]], {Typed[{}, {NonNegativeIntegers}]}]],
						Join["starredEmptyPairs"[mRem], R]],
					"state4A"]]],
			"Rewrite"["stepsAdd"["System4Configuration", "system4Step",
				(((1 + Length[Prepend[S0][Krest]]) + ((g1 + 1) + (g1 + 1))) + 8) + kLoop, kFin,
				"system4Configuration"[Typed[{}, {"System4Element"}],
					Join["sets4"[Prepend[S0][Krest]],
						Join["starredEmptyPairs"[g1 + 1],
							Prepend["star4"][Prepend["set4"[Rs]][Join["starredEmptyPairs"[((mRem + 1) + g1) + 2], R]]]]],
					"state4A"]]],
			"Rewrite"["stepsAdd"["System4Configuration", "system4Step",
				((1 + Length[Prepend[S0][Krest]]) + ((g1 + 1) + (g1 + 1))) + 8, kLoop,
				"system4Configuration"[Typed[{}, {"System4Element"}],
					Join["sets4"[Prepend[S0][Krest]],
						Join["starredEmptyPairs"[g1 + 1],
							Prepend["star4"][Prepend["set4"[Rs]][Join["starredEmptyPairs"[((mRem + 1) + g1) + 2], R]]]]],
					"state4A"]]],
			"Rewrite"[p1],
			"Change"["optionBind"["steps"["system4Step", kLoop,
				"system4Configuration"[
					"revAppend"["sets4"[Join["loopLeft"[0, "decr4"["decr4"["xorMerge"[{1}, Rs]]]], "replicateEmpty"[0]]],
						Prepend["star4"]["starredZeroPairsRev"[g1, "revAppend"["sets4"[Map["decr4", Prepend[S0][Krest]]], Typed[{}, {"System4Element"}]]]]],
					Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[(mRem + 1) + g1], R]]],
					"state4A"]],
				Function[{Typed[y, "System4Configuration"]}, "steps"["system4Step", kFin, y]]] ==
				"some"["system4Configuration"[Typed[{}, {"System4Element"}],
					Join["sets4"[Join[Join[Map["decr4", Prepend[S0][Krest]],
						Map["decr4", "loopK"[g1, "decrN4"[g1 + 2, "xorMerge"[{1}, Rs]]]]], {Typed[{}, {NonNegativeIntegers}]}]],
						Join["starredEmptyPairs"[mRem], R]],
					"state4A"]]],
			"Rewrite"[eLoop],
			"Rewrite"[eqDecr],
			"Rewrite"["additionZeroLeft"[g1]],
			"Exact"[eFin],
			"Have"[posAll, 1 <= ((((1 + Length[Prepend[S0][Krest]]) + ((g1 + 1) + (g1 + 1))) + 8) + kLoop) + kFin], "LinearArithmetic",
			"Exact"["existsIntroduction"[((((1 + Length[Prepend[S0][Krest]]) + ((g1 + 1) + (g1 + 1))) + 8) + kLoop) + kFin,
				"andIntroduction"[posAll, eAll]]]
		}
	],
	(* Bag encoding: e |-> 2*(e - 1) *)
	TypeTheoryDefinition["encodeBag4", Typed[
		Function[{Typed[bag, {NonNegativeIntegers}]},
			Map[Function[{Typed[e, NonNegativeIntegers]}, Subtract[e, 1] + Subtract[e, 1]], bag]],
		{NonNegativeIntegers} -> {NonNegativeIntegers}
	]],
	TypeTheoryDefinition["doubleList", Typed[
		Function[{Typed[xs, {NonNegativeIntegers}]},
			Map[Function[{Typed[k, NonNegativeIntegers]}, k + k], xs]],
		{NonNegativeIntegers} -> {NonNegativeIntegers}
	]],
	machineTheorem["encodeBag4ShiftUp1",
		ForAll[{Typed[r, {NonNegativeIntegers}]}, "encodeBag4"["shiftUp"[1, r]] == "doubleList"[r]],
		{
			"Introduce"[r], "Induction"[r], "Reflexivity",
			"Introduce"[k, rest, ih],
			"Change"[Prepend[Subtract[k + 1, 1] + Subtract[k + 1, 1]]["encodeBag4"["shiftUp"[1, rest]]] == Prepend[k + k]["doubleList"[rest]]],
			"Rewrite"[ih], "Reflexivity"
		}
	],
	machineTheorem["encodeBag4StrictlyAbove",
		ForAll[{Typed[bag, {NonNegativeIntegers}], Typed[lo, NonNegativeIntegers]},
			Implies[1 <= lo, Implies["strictlyAbove"[lo, bag], "strictlyAbove"[Subtract[lo, 1] + Subtract[lo, 1], "encodeBag4"[bag]]]]],
		{
			"Introduce"[bag], "Induction"[bag],
			"Introduce"[lo, hlo, h], "Exact"["trueIntroduction"],
			"Introduce"[e, rest, ih, lo, hlo, h], "Cases"[h], "Introduce"[he, hrest],
			"Cases"[lo], "Introduce"[hlo, he], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"["falseElimination"[f]],
			"Introduce"[lo1, hlo, he],
			"Cases"[e], "Introduce"[hrest, he], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"["falseElimination"[f]],
			"Introduce"[e1, hrest, he],
			"Have"[lt, (lo1 + lo1) + 1 <= e1 + e1], "LinearArithmetic",
			"Have"[ePos, 1 <= e1 + 1], "LinearArithmetic",
			"Exact"["andIntroduction"[lt, ih[e1 + 1, ePos, hrest]]]
		}
	],
	machineTheorem["encodeBag4StrictlyIncreasing",
		ForAll[{Typed[bag, {NonNegativeIntegers}]},
			Implies["strictlyAbove"[0, bag], "strictlyIncreasing"["encodeBag4"[bag]]]],
		{
			"Introduce"[bag], "Cases"[bag],
			"Introduce"[h], "Exact"["trueIntroduction"],
			"Introduce"[e, rest, h], "Cases"[h], "Introduce"[he, hrest],
			"Exact"["encodeBag4StrictlyAbove"[rest, e, he, hrest]]
		}
	],
	machineTheorem["encodeBag4AllBelowEqual",
		ForAll[{Typed[bag, {NonNegativeIntegers}], Typed[hi, NonNegativeIntegers]},
			Implies["allBelowEqual"[hi, bag], "allBelowEqual"[hi + hi, "encodeBag4"[bag]]]],
		{
			"Introduce"[bag], "Induction"[bag],
			"Introduce"[hi, h], "Exact"["trueIntroduction"],
			"Introduce"[e, rest, ih, hi, h], "Cases"[h], "Introduce"[he, hrest],
			"Cases"[e], "Introduce"[he],
			"Have"[h0, 0 <= hi + hi], "LinearArithmetic",
			"Exact"["andIntroduction"[h0, ih[hi, hrest]]],
			"Introduce"[k, he],
			"Have"[hk, k + k <= hi + hi], "LinearArithmetic",
			"Exact"["andIntroduction"[hk, ih[hi, hrest]]]
		}
	],
	(* Even/odd parity and membership in encodeBag4 / doubleList *)
	machineTheorem["evenOrOdd",
		ForAll[{Typed[x, NonNegativeIntegers]},
			Or[Exists[{Typed[q, NonNegativeIntegers]}, x == q + q], Exists[{Typed[q, NonNegativeIntegers]}, x == (q + q) + 1]]],
		{
			"Introduce"[x], "Induction"[x],
			"Exact"["orIntroductionLeft"["existsIntroduction"[0, "equalityReflexivity"[0]]]],
			"Introduce"[k, ih], "Cases"[ih],
			"Introduce"[ev], "Cases"[ev], "Introduce"[q, eq],
			"Have"[eq1, k + 1 == (q + q) + 1], "LinearArithmetic",
			"Exact"["orIntroductionRight"["existsIntroduction"[q, eq1]]],
			"Introduce"[od], "Cases"[od], "Introduce"[q, eq],
			"Have"[eq1, k + 1 == (q + 1) + (q + 1)], "LinearArithmetic",
			"Exact"["orIntroductionLeft"["existsIntroduction"[q + 1, eq1]]]
		}
	],
	machineTheorem["memNatEncodeBag4Even",
		ForAll[{Typed[q, NonNegativeIntegers], Typed[bag, {NonNegativeIntegers}]},
			Implies["strictlyAbove"[0, bag], "memNat"[q + q, "encodeBag4"[bag]] == "memNat"[q + 1, bag]]],
		{
			"Introduce"[q, bag], "Induction"[bag],
			"Introduce"[h], "Reflexivity",
			"Introduce"[e, rest, ih, h], "Cases"[h], "Introduce"[he, hrest],
			"Cases"[e], "Introduce"[he, hrest], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"["falseElimination"[f]],
			"Introduce"[k, he, hrest],
			"Have"[hrest0, "strictlyAbove"[0, rest]], "Exact"["strictlyAboveWeaken"[k + 1, 0, rest, "lessEqualZero"[k + 1], hrest]],
			"Change"[InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Booleans], "memNat"[q + q, "encodeBag4"[rest]], "true", Decide[q + q == k + k]] ==
				InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Booleans], "memNat"[q + 1, rest], "true", Decide[q + 1 == k + 1]]],
			"Have"[dec, Decidable[q == k]], "Exact"["naturalNumberEqualityDecidable"[q, k]], "Cases"[dec],
			"Introduce"[neq],
			"Have"[neq2, Not[q + q == k + k]], "Introduce"[e2], "Have"[e0, q == k], "LinearArithmetic", "Exact"[neq[e0]],
			"Have"[neq1, Not[q + 1 == k + 1]], "Introduce"[e1], "Have"[e0, q == k], "LinearArithmetic", "Exact"[neq[e0]],
			"Rewrite"["decideEqualFalse"[q + q, k + k, neq2]],
			"Rewrite"["decideEqualFalse"[q + 1, k + 1, neq1]],
			"Exact"[ih[hrest0]],
			"Introduce"[eq],
			"Have"[eq2, q + q == k + k], "LinearArithmetic",
			"Have"[eq1, q + 1 == k + 1], "LinearArithmetic",
			"Rewrite"["decideEqualTrue"[q + q, k + k, eq2]],
			"Rewrite"["decideEqualTrue"[q + 1, k + 1, eq1]], "Reflexivity"
		}
	],
	machineTheorem["memNatEncodeBag4Odd",
		ForAll[{Typed[q, NonNegativeIntegers], Typed[bag, {NonNegativeIntegers}]},
			Implies["strictlyAbove"[0, bag], "memNat"[(q + q) + 1, "encodeBag4"[bag]] == "false"]],
		{
			"Introduce"[q, bag], "Induction"[bag],
			"Introduce"[h], "Reflexivity",
			"Introduce"[e, rest, ih, h], "Cases"[h], "Introduce"[he, hrest],
			"Cases"[e], "Introduce"[he, hrest], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"["falseElimination"[f]],
			"Introduce"[k, he, hrest],
			"Have"[hrest0, "strictlyAbove"[0, rest]], "Exact"["strictlyAboveWeaken"[k + 1, 0, rest, "lessEqualZero"[k + 1], hrest]],
			"Have"[neq, Not[(q + q) + 1 == k + k]],
			"Introduce"[eq],
			"Have"[sp, Or[q <= k, k < q]], "Exact"["lessEqualTotality"[q, k]],
			"Cases"[sp],
			"Introduce"[le], "Cases"["lessEqualExistsRight"[q, k, le]], "Introduce"[d, eqK],
			"Cases"[d], "Introduce"[eqK], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"[f],
			"Introduce"[d1, eqK], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"[f],
			"Introduce"[gt], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"[f],
			"Change"[InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Booleans], "memNat"[(q + q) + 1, "encodeBag4"[rest]], "true", Decide[(q + q) + 1 == k + k]] == "false"],
			"Rewrite"["decideEqualFalse"[(q + q) + 1, k + k, neq]],
			"Exact"[ih[hrest0]]
		}
	],
	machineTheorem["memNatEncodeBag4ShiftDown1",
		ForAll[{Typed[x, NonNegativeIntegers], Typed[bag, {NonNegativeIntegers}]},
			Implies["strictlyAbove"[1, bag], "memNat"[x, "encodeBag4"["shiftDown"[1, bag]]] == "memNat"[x + 2, "encodeBag4"[bag]]]],
		{
			"Introduce"[x, bag, h],
			"Have"[h0, "strictlyAbove"[0, bag]], "Have"[z1, 0 <= 1], "LinearArithmetic", "Exact"["strictlyAboveWeaken"[1, 0, bag, z1, h]],
			"Have"[hD0, "strictlyAbove"[0, "shiftDown"[1, bag]]], "Exact"["shiftDownStrictlyAbove"[bag, 1, 0, h]],
			"Cases"["evenOrOdd"[x]],
			"Introduce"[ev], "Cases"[ev], "Introduce"[q, eq], "Rewrite"[eq],
			"Have"[eq2, (q + q) + 2 == (q + 1) + (q + 1)], "LinearArithmetic",
			"Rewrite"[eq2],
			"Rewrite"["memNatEncodeBag4Even"[q, "shiftDown"[1, bag], hD0]],
			"Rewrite"["memNatEncodeBag4Even"[q + 1, bag, h0]],
			"Exact"["memNatShiftDown1"[q + 1, bag, h0]],
			"Introduce"[od], "Cases"[od], "Introduce"[q, eq], "Rewrite"[eq],
			"Have"[eq2, ((q + q) + 1) + 2 == ((q + 1) + (q + 1)) + 1], "LinearArithmetic",
			"Rewrite"[eq2],
			"Rewrite"["memNatEncodeBag4Odd"[q, "shiftDown"[1, bag], hD0]],
			"Rewrite"["memNatEncodeBag4Odd"[q + 1, bag, h0]]
		}
	],
	machineTheorem["memNatEncodeBag4XorMerge",
		ForAll[{Typed[x, NonNegativeIntegers], Typed[a, {NonNegativeIntegers}], Typed[b, {NonNegativeIntegers}]},
			Implies["strictlyAbove"[0, a], Implies["strictlyAbove"[0, b],
				"memNat"[x, "encodeBag4"["xorMerge"[a, b]]] == "xorBool"["memNat"[x, "encodeBag4"[a]], "memNat"[x, "encodeBag4"[b]]]]]],
		{
			"Introduce"[x, a, b, ha, hb],
			"Have"[hab, "strictlyAbove"[0, "xorMerge"[a, b]]], "Exact"["xorMergeStrictlyAbove"[a, b, 0, ha, hb]],
			"Cases"["evenOrOdd"[x]],
			"Introduce"[ev], "Cases"[ev], "Introduce"[q, eq], "Rewrite"[eq],
			"Rewrite"["memNatEncodeBag4Even"[q, "xorMerge"[a, b], hab]],
			"Rewrite"["memNatEncodeBag4Even"[q, a, ha]],
			"Rewrite"["memNatEncodeBag4Even"[q, b, hb]],
			"Exact"["memNatXorMerge"[q + 1, a, b, "strictlyAboveImpliesIncreasing"[0, a, ha], "strictlyAboveImpliesIncreasing"[0, b, hb]]],
			"Introduce"[od], "Cases"[od], "Introduce"[q, eq], "Rewrite"[eq],
			"Rewrite"["memNatEncodeBag4Odd"[q, "xorMerge"[a, b], hab]],
			"Rewrite"["memNatEncodeBag4Odd"[q, a, ha]],
			"Rewrite"["memNatEncodeBag4Odd"[q, b, hb]], "Reflexivity"
		}
	],
	(* allIntsFrom & allInts *)
	TypeTheoryDefinition["allIntsFrom", Typed[
		Function[{Typed[start, NonNegativeIntegers], Typed[count, NonNegativeIntegers]},
			InductiveRecursor[NonNegativeIntegers][Function[{Typed[q, NonNegativeIntegers]}, NonNegativeIntegers -> {NonNegativeIntegers}],
				Function[{Typed[s, NonNegativeIntegers]}, Typed[{}, {NonNegativeIntegers}]],
				Function[{Typed[k, NonNegativeIntegers], Typed[prev, NonNegativeIntegers -> {NonNegativeIntegers}]},
					Function[{Typed[s, NonNegativeIntegers]}, Prepend[s][prev[s + 1]]]], count][start]],
		NonNegativeIntegers -> NonNegativeIntegers -> {NonNegativeIntegers}
	]],
	TypeTheoryDefinition["allInts", Typed[
		Function[{Typed[n, NonNegativeIntegers]}, "allIntsFrom"[0, n]],
		NonNegativeIntegers -> {NonNegativeIntegers}
	]],
	machineTheorem["allIntsFromStrictlyAbove",
		ForAll[{Typed[count, NonNegativeIntegers], Typed[start, NonNegativeIntegers], Typed[lo, NonNegativeIntegers]},
			Implies[lo + 1 <= start, "strictlyAbove"[lo, "allIntsFrom"[start, count]]]],
		{
			"Introduce"[count], "Induction"[count],
			"Introduce"[start, lo, h], "Exact"["trueIntroduction"],
			"Introduce"[k, ih, start, lo, h],
			"Have"[h1, start + 1 <= start + 1], "LinearArithmetic",
			"Exact"["andIntroduction"[h, ih[start + 1, start, h1]]]
		}
	],
	machineTheorem["allIntsStrictlyIncreasing",
		ForAll[{Typed[n, NonNegativeIntegers]}, "strictlyIncreasing"["allInts"[n]]],
		{
			"Introduce"[n], "Cases"[n], "Exact"["trueIntroduction"],
			"Introduce"[k], "Have"[h1, 0 + 1 <= 1], "LinearArithmetic",
			"Exact"["allIntsFromStrictlyAbove"[k, 1, 0, h1]]
		}
	],
	machineTheorem["allIntsFromAllBelowEqual",
		ForAll[{Typed[count, NonNegativeIntegers], Typed[start, NonNegativeIntegers], Typed[hi, NonNegativeIntegers]},
			Implies[start + count <= hi + 1, "allBelowEqual"[hi, "allIntsFrom"[start, count]]]],
		{
			"Introduce"[count], "Induction"[count],
			"Introduce"[start, hi, h], "Exact"["trueIntroduction"],
			"Introduce"[k, ih, start, hi, h],
			"Have"[hS, start <= hi], "LinearArithmetic",
			"Have"[hNext, (start + 1) + k <= hi + 1], "LinearArithmetic",
			"Exact"["andIntroduction"[hS, ih[start + 1, hi, hNext]]]
		}
	],
	machineTheorem["memNatAllIntsFromTrue",
		ForAll[{Typed[count, NonNegativeIntegers], Typed[start, NonNegativeIntegers], Typed[x, NonNegativeIntegers]},
			Implies[start <= x, Implies[x + 1 <= start + count, "memNat"[x, "allIntsFrom"[start, count]] == "true"]]],
		{
			"Introduce"[count], "Induction"[count],
			"Introduce"[start, x, h1, h2], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"["falseElimination"[f]],
			"Introduce"[k, ih, start, x, h1, h2],
			"Change"[InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Booleans], "memNat"[x, "allIntsFrom"[start + 1, k]], "true", Decide[x == start]] == "true"],
			"Cases"["naturalNumberEqualityDecidable"[x, start]],
			"Introduce"[neq],
			"Have"[ge1, start + 1 <= x],
			"Cases"["lessEqualExistsRight"[start, x, h1]], "Introduce"[d, eq],
			"Cases"[d], "Introduce"[eq], "Have"[e0, x == start], "LinearArithmetic", "Exact"["falseElimination"[neq[e0]]],
			"Introduce"[d1, eq], "LinearArithmetic",
			"Have"[lt1, x + 1 <= (start + 1) + k], "LinearArithmetic",
			"Exact"[ih[start + 1, x, ge1, lt1]],
			"Introduce"[eq], "Reflexivity"
		}
	],
	machineTheorem["memNatAllIntsTrue",
		ForAll[{Typed[n, NonNegativeIntegers], Typed[x, NonNegativeIntegers]},
			Implies[x + 1 <= n, "memNat"[x, "allInts"[n]] == "true"]],
		{
			"Introduce"[n, x, h],
			"Have"[h2, x + 1 <= 0 + n], "LinearArithmetic",
			"Exact"["memNatAllIntsFromTrue"[n, 0, x, "lessEqualZero"[x], h2]]
		}
	],
	(* rulePos, encRuleSet, encBlock, encBlocks, system5ToSystem4 *)
	TypeTheoryDefinition["rulePos", Typed[
		Function[{Typed[f, NonNegativeIntegers], Typed[t, NonNegativeIntegers], Typed[k, NonNegativeIntegers]},
			Subtract[((k + k) + f) + 3, t]],
		NonNegativeIntegers -> NonNegativeIntegers -> NonNegativeIntegers -> NonNegativeIntegers
	]],
	machineTheorem["rulePosShift",
		ForAll[{Typed[f, NonNegativeIntegers], Typed[t, NonNegativeIntegers], Typed[k, NonNegativeIntegers]},
			"rulePos"[f, t + 2, k + 1] == "rulePos"[f, t, k]],
		{
			"Introduce"[f, t, k],
			"Have"[eq, (((k + 1) + (k + 1)) + f) + 3 == ((((k + k) + f) + 3) + 1) + 1], "LinearArithmetic",
			"Change"[Subtract[(((k + 1) + (k + 1)) + f) + 3, (t + 1) + 1] == Subtract[((k + k) + f) + 3, t]],
			"Rewrite"[eq],
			"Rewrite"["subtractionSuccessor"[(((k + k) + f) + 3) + 1, t + 1]],
			"Exact"["subtractionSuccessor"[((k + k) + f) + 3, t]]
		}
	],
	TypeTheoryDefinition["encRulePositions", Typed[
		Function[{Typed[r, {NonNegativeIntegers}], Typed[f, NonNegativeIntegers], Typed[t, NonNegativeIntegers]},
			Map[Function[{Typed[k, NonNegativeIntegers]}, "rulePos"[f, t, k]], r]],
		{NonNegativeIntegers} -> NonNegativeIntegers -> NonNegativeIntegers -> {NonNegativeIntegers}
	]],
	machineTheorem["encRulePositionsShift",
		ForAll[{Typed[r, {NonNegativeIntegers}], Typed[f, NonNegativeIntegers], Typed[t, NonNegativeIntegers]},
			"encRulePositions"["shiftUp"[1, r], f, t + 2] == "encRulePositions"[r, f, t]],
		{
			"Introduce"[r], "Induction"[r], "Introduce"[f, t], "Reflexivity",
			"Introduce"[k, rest, ih, f, t],
			"Change"[Prepend["rulePos"[f, t + 2, k + 1]]["encRulePositions"["shiftUp"[1, rest], f, t + 2]] ==
				Prepend["rulePos"[f, t, k]]["encRulePositions"[rest, f, t]]],
			"Rewrite"["rulePosShift"[f, t, k]], "Rewrite"[ih[f, t]]
		}
	],
	machineTheorem["encRulePositionsStrictlyAbove",
		ForAll[{Typed[r, {NonNegativeIntegers}], Typed[f, NonNegativeIntegers], Typed[t, NonNegativeIntegers], Typed[lo, NonNegativeIntegers]},
			Implies[t <= f, Implies["strictlyAbove"[lo, r], "strictlyAbove"["rulePos"[f, t, lo], "encRulePositions"[r, f, t]]]]],
		{
			"Introduce"[r], "Induction"[r],
			"Introduce"[f, t, lo, htf, h], "Exact"["trueIntroduction"],
			"Introduce"[k, rest, ih, f, t, lo, htf, h], "Cases"[h], "Introduce"[hk, hrest],
			"Cases"["lessEqualExists"[t, f, htf]], "Introduce"[d, eqF],
			"Have"[lt, "rulePos"[f, t, lo] + 1 <= "rulePos"[f, t, k]],
			"Change"[Subtract[((lo + lo) + f) + 3, t] + 1 <= Subtract[((k + k) + f) + 3, t]],
			"Rewrite"[eqF],
			"Have"[e1, ((lo + lo) + (d + t)) + 3 == (((lo + lo) + d) + 3) + t], "LinearArithmetic",
			"Have"[e2, ((k + k) + (d + t)) + 3 == (((k + k) + d) + 3) + t], "LinearArithmetic",
			"Rewrite"[e1], "Rewrite"[e2],
			"Rewrite"["additionSubtractionCancellation"[((lo + lo) + d) + 3, t]],
			"Rewrite"["additionSubtractionCancellation"[((k + k) + d) + 3, t]],
			"LinearArithmetic",
			"Exact"["andIntroduction"[lt, ih[f, t, k, htf, hrest]]]
		}
	],
	machineTheorem["encRulePositionsStrictlyIncreasing",
		ForAll[{Typed[r, {NonNegativeIntegers}], Typed[f, NonNegativeIntegers], Typed[t, NonNegativeIntegers]},
			Implies[t <= f, Implies["strictlyIncreasing"[r], "strictlyIncreasing"["encRulePositions"[r, f, t]]]]],
		{
			"Introduce"[r, f, t, htf], "Cases"[r],
			"Introduce"[h], "Exact"["trueIntroduction"],
			"Introduce"[k, rest, h],
			"Exact"["encRulePositionsStrictlyAbove"[rest, f, t, k, htf, h]]
		}
	],
	machineTheorem["encRulePositionsAllBelowEqual",
		ForAll[{Typed[r, {NonNegativeIntegers}], Typed[f, NonNegativeIntegers], Typed[t, NonNegativeIntegers], Typed[hi, NonNegativeIntegers]},
			Implies[t <= f, Implies["allBelowEqual"[hi, r], "allBelowEqual"[((hi + hi) + f) + 3, "encRulePositions"[r, f, t]]]]],
		{
			"Introduce"[r], "Induction"[r],
			"Introduce"[f, t, hi, htf, h], "Exact"["trueIntroduction"],
			"Introduce"[k, rest, ih, f, t, hi, htf, h], "Cases"[h], "Introduce"[hk, hrest],
			"Cases"["lessEqualExists"[t, f, htf]], "Introduce"[d, eqF],
			"Have"[le, "rulePos"[f, t, k] <= ((hi + hi) + f) + 3],
			"Change"[Subtract[((k + k) + f) + 3, t] <= ((hi + hi) + f) + 3],
			"Rewrite"[eqF],
			"Have"[e1, ((k + k) + (d + t)) + 3 == (((k + k) + d) + 3) + t], "LinearArithmetic",
			"Rewrite"[e1], "Rewrite"["additionSubtractionCancellation"[((k + k) + d) + 3, t]], "LinearArithmetic",
			"Exact"["andIntroduction"[le, ih[f, t, hi, htf, hrest]]]
		}
	],
	(* Membership in encRulePositions: below f+3-t is false; at x + (f-t) + 3 equals memNat[x, doubleList[r]] *)
	machineTheorem["memNatEncRulePositionsLow",
		ForAll[{Typed[r, {NonNegativeIntegers}], Typed[f, NonNegativeIntegers], Typed[t, NonNegativeIntegers], Typed[x, NonNegativeIntegers]},
			Implies[t <= f, Implies[(x + t) + 1 <= f + 3, "memNat"[x, "encRulePositions"[r, f, t]] == "false"]]],
		{
			"Introduce"[r], "Induction"[r],
			"Introduce"[f, t, x, htf, hx], "Reflexivity",
			"Introduce"[k, rest, ih, f, t, x, htf, hx],
			"Cases"["lessEqualExists"[t, f, htf]], "Introduce"[d, eqF],
			"Have"[neq, Not[x == "rulePos"[f, t, k]]],
			"Introduce"[eq],
			"Have"[rpEq, "rulePos"[f, t, k] == ((k + k) + d) + 3],
			"Change"[Subtract[((k + k) + f) + 3, t] == ((k + k) + d) + 3],
			"Rewrite"[eqF],
			"Have"[e1, ((k + k) + (d + t)) + 3 == (((k + k) + d) + 3) + t], "LinearArithmetic",
			"Rewrite"[e1], "Exact"["additionSubtractionCancellation"[((k + k) + d) + 3, t]],
			"Have"[f0, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"[f0],
			"Change"[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Booleans], "memNat"[x, "encRulePositions"[rest, f, t]], "true", Decide[x == "rulePos"[f, t, k]]] == "false"],
			"Rewrite"["decideEqualFalse"[x, "rulePos"[f, t, k], neq]],
			"Exact"[ih[f, t, x, htf, hx]]
		}
	],
	machineTheorem["memNatEncRulePositionsAt",
		ForAll[{Typed[r, {NonNegativeIntegers}], Typed[f, NonNegativeIntegers], Typed[t, NonNegativeIntegers], Typed[x, NonNegativeIntegers]},
			Implies[t <= f, "memNat"[(x + Subtract[f, t]) + 3, "encRulePositions"[r, f, t]] == "memNat"[x, "doubleList"[r]]]],
		{
			"Introduce"[r], "Induction"[r],
			"Introduce"[f, t, x, htf], "Reflexivity",
			"Introduce"[k, rest, ih, f, t, x, htf],
			"Cases"["lessEqualExists"[t, f, htf]], "Introduce"[d, eqF],
			"Have"[subEq, Subtract[f, t] == d], "Rewrite"[eqF], "Exact"["additionSubtractionCancellation"[d, t]],
			"Have"[rpEq, "rulePos"[f, t, k] == ((k + k) + d) + 3],
			"Change"[Subtract[((k + k) + f) + 3, t] == ((k + k) + d) + 3],
			"Rewrite"[eqF],
			"Have"[e1, ((k + k) + (d + t)) + 3 == (((k + k) + d) + 3) + t], "LinearArithmetic",
			"Rewrite"[e1], "Exact"["additionSubtractionCancellation"[((k + k) + d) + 3, t]],
			"Change"[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Booleans], "memNat"[(x + Subtract[f, t]) + 3, "encRulePositions"[rest, f, t]], "true", Decide[(x + Subtract[f, t]) + 3 == "rulePos"[f, t, k]]] ==
				InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Booleans], "memNat"[x, "doubleList"[rest]], "true", Decide[x == k + k]]],
			"Cases"["naturalNumberEqualityDecidable"[x, k + k]],
			"Introduce"[neq],
			"Have"[neq2, Not[(x + Subtract[f, t]) + 3 == "rulePos"[f, t, k]]],
			"Introduce"[e], "Have"[e0, x == k + k], "LinearArithmetic", "Exact"[neq[e0]],
			"Rewrite"["decideEqualFalse"[(x + Subtract[f, t]) + 3, "rulePos"[f, t, k], neq2]],
			"Exact"[ih[f, t, x, htf]],
			"Introduce"[eq],
			"Have"[eq2, (x + Subtract[f, t]) + 3 == "rulePos"[f, t, k]], "LinearArithmetic",
			"Rewrite"["decideEqualTrue"[(x + Subtract[f, t]) + 3, "rulePos"[f, t, k], eq2]], "Reflexivity"
		}
	],
	TypeTheoryDefinition["encRuleSet", Typed[
		Function[{Typed[r, {NonNegativeIntegers}], Typed[f, NonNegativeIntegers], Typed[t, NonNegativeIntegers]},
			"xorMerge"["allInts"[((f + f) + f) + 1], "encRulePositions"[r, f, t]]],
		{NonNegativeIntegers} -> NonNegativeIntegers -> NonNegativeIntegers -> {NonNegativeIntegers}
	]],
	machineTheorem["encRuleSetShift",
		ForAll[{Typed[r, {NonNegativeIntegers}], Typed[f, NonNegativeIntegers], Typed[t, NonNegativeIntegers]},
			"encRuleSet"["shiftUp"[1, r], f, t + 2] == "encRuleSet"[r, f, t]],
		{
			"Introduce"[r, f, t],
			"Change"["xorMerge"["allInts"[((f + f) + f) + 1], "encRulePositions"["shiftUp"[1, r], f, t + 2]] ==
				"xorMerge"["allInts"[((f + f) + f) + 1], "encRulePositions"[r, f, t]]],
			"Rewrite"["encRulePositionsShift"[r, f, t]]
		}
	],
	machineTheorem["encRuleSetStrictlyIncreasing",
		ForAll[{Typed[r, {NonNegativeIntegers}], Typed[f, NonNegativeIntegers], Typed[t, NonNegativeIntegers]},
			Implies[t <= f, Implies["strictlyIncreasing"[r], "strictlyIncreasing"["encRuleSet"[r, f, t]]]]],
		{
			"Introduce"[r, f, t, htf, hr],
			"Exact"["xorMergeStrictlyIncreasing"["allInts"[((f + f) + f) + 1], "encRulePositions"[r, f, t],
				"allIntsStrictlyIncreasing"[((f + f) + f) + 1], "encRulePositionsStrictlyIncreasing"[r, f, t, htf, hr]]]
		}
	],
	machineTheorem["memNatEncRuleSetLow",
		ForAll[{Typed[r, {NonNegativeIntegers}], Typed[f, NonNegativeIntegers], Typed[t, NonNegativeIntegers], Typed[x, NonNegativeIntegers]},
			Implies[t <= f, Implies[2 <= f, Implies["strictlyIncreasing"[r], Implies[(x + t) + 1 <= f + 3,
				"memNat"[x, "encRuleSet"[r, f, t]] == "true"]]]]],
		{
			"Introduce"[r, f, t, x, htf, hf2, hr, hx],
			"Change"["memNat"[x, "xorMerge"["allInts"[((f + f) + f) + 1], "encRulePositions"[r, f, t]]] == "true"],
			"Rewrite"["memNatXorMerge"[x, "allInts"[((f + f) + f) + 1], "encRulePositions"[r, f, t],
				"allIntsStrictlyIncreasing"[((f + f) + f) + 1], "encRulePositionsStrictlyIncreasing"[r, f, t, htf, hr]]],
			"Have"[xBound, x + 1 <= ((f + f) + f) + 1], "LinearArithmetic",
			"Rewrite"["memNatAllIntsTrue"[((f + f) + f) + 1, x, xBound]],
			"Rewrite"["memNatEncRulePositionsLow"[r, f, t, x, htf, hx]], "Reflexivity"
		}
	],
	machineTheorem["memNatEncRuleSetAt",
		ForAll[{Typed[r, {NonNegativeIntegers}], Typed[f, NonNegativeIntegers], Typed[t, NonNegativeIntegers], Typed[x, NonNegativeIntegers]},
			Implies[t <= f, Implies["strictlyIncreasing"[r], Implies[((x + Subtract[f, t]) + 3) + 1 <= ((f + f) + f) + 1,
				"memNat"[(x + Subtract[f, t]) + 3, "encRuleSet"[r, f, t]] == "xorBool"["true", "memNat"[x, "doubleList"[r]]]]]]],
		{
			"Introduce"[r, f, t, x, htf, hr, hBound],
			"Change"["memNat"[(x + Subtract[f, t]) + 3, "xorMerge"["allInts"[((f + f) + f) + 1], "encRulePositions"[r, f, t]]] ==
				"xorBool"["true", "memNat"[x, "doubleList"[r]]]],
			"Rewrite"["memNatXorMerge"[(x + Subtract[f, t]) + 3, "allInts"[((f + f) + f) + 1], "encRulePositions"[r, f, t],
				"allIntsStrictlyIncreasing"[((f + f) + f) + 1], "encRulePositionsStrictlyIncreasing"[r, f, t, htf, hr]]],
			"Rewrite"["memNatAllIntsTrue"[((f + f) + f) + 1, (x + Subtract[f, t]) + 3, hBound]],
			"Rewrite"["memNatEncRulePositionsAt"[r, f, t, x, htf]]
		}
	],
	(* encBlock, encBlocks, encBlocksShift, system5ToSystem4 *)
	TypeTheoryDefinition["encBlock", Typed[
		Function[{Typed[r, {NonNegativeIntegers}], Typed[f, NonNegativeIntegers], Typed[t, NonNegativeIntegers]},
			Join[
				Prepend["star4"][Prepend["set4"["encRuleSet"[r, f, t]]]["starredEmptyPairs"[f + f]]],
				Prepend["star4"][Prepend["set4"["allInts"[((f + f) + f) + 1]]]["starredEmptyPairs"[Subtract[f + f, 2]]]]
			]],
		{NonNegativeIntegers} -> NonNegativeIntegers -> NonNegativeIntegers -> {"System4Element"}
	]],
	TypeTheoryDefinition["encBlocks", Typed[
		Function[{Typed[rs, {{NonNegativeIntegers}}], Typed[f, NonNegativeIntegers], Typed[t, NonNegativeIntegers]},
			InductiveRecursor[List][Function[{Typed[q, {{NonNegativeIntegers}}]}, {"System4Element"}], Typed[{}, {"System4Element"}],
				Function[{Typed[r, {NonNegativeIntegers}], Typed[rest, {{NonNegativeIntegers}}], Typed[prev, {"System4Element"}]},
					Join["encBlock"[r, f, t], prev]], rs]],
		{{NonNegativeIntegers}} -> NonNegativeIntegers -> NonNegativeIntegers -> {"System4Element"}
	]],
	machineTheorem["encBlocksShift",
		ForAll[{Typed[rs, {{NonNegativeIntegers}}], Typed[f, NonNegativeIntegers], Typed[t, NonNegativeIntegers]},
			"encBlocks"["shiftUpRules"[1, rs], f, t + 2] == "encBlocks"[rs, f, t]],
		{
			"Introduce"[rs], "Induction"[rs], "Introduce"[f, t], "Reflexivity",
			"Introduce"[r, rest, ih, f, t],
			"Change"[Join[
				Join[Prepend["star4"][Prepend["set4"["encRuleSet"["shiftUp"[1, r], f, t + 2]]]["starredEmptyPairs"[f + f]]],
					Prepend["star4"][Prepend["set4"["allInts"[((f + f) + f) + 1]]]["starredEmptyPairs"[Subtract[f + f, 2]]]]],
				"encBlocks"["shiftUpRules"[1, rest], f, t + 2]] ==
				Join["encBlock"[r, f, t], "encBlocks"[rest, f, t]]],
			"Rewrite"["encRuleSetShift"[r, f, t]], "Rewrite"[ih[f, t]], "Reflexivity"
		}
	],
	TypeTheoryDefinition["system5ToSystem4", Typed[
		Function[{Typed[s, "System5Configuration"], Typed[f, NonNegativeIntegers]},
			"system4Configuration"[
				Typed[{}, {"System4Element"}],
				Prepend["set4"["encodeBag4"[s[["bag"]]]]][Join["starredEmptyPairs"[f], "encBlocks"[s[["rules"]], f, 0]]],
				"state4A"
			]],
		"System5Configuration" -> NonNegativeIntegers -> "System4Configuration"
	]],
	(* Well-formedness of a System 4 tape for Rung 5 (initAC / rep3_init) *)
	TypeTheoryDefinition["noAdjacentStarsFrom", Typed[
		Function[{Typed[prevStar, Booleans], Typed[xs, {"System4Element"}]},
			InductiveRecursor[List][Function[{Typed[q, {"System4Element"}]}, Booleans -> TypeUniverse[0]],
				Function[{Typed[p, Booleans]}, True],
				Function[{Typed[e, "System4Element"], Typed[rest, {"System4Element"}], Typed[prev, Booleans -> TypeUniverse[0]]},
					Function[{Typed[p, Booleans]},
						InductiveRecursor["System4Element"][Function[{Typed[q, "System4Element"]}, TypeUniverse[0]],
							InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, TypeUniverse[0]], prev["true"], False, p],
							Function[{Typed[s, {NonNegativeIntegers}]}, prev["false"]], e]]], xs][prevStar]],
		Booleans -> {"System4Element"} -> TypeUniverse[0]
	]],
	TypeTheoryDefinition["endsWithSet4", Typed[
		Function[{Typed[xs, {"System4Element"}]},
			InductiveRecursor[List][Function[{Typed[q, {"System4Element"}]}, Booleans -> TypeUniverse[0]],
				Function[{Typed[lastWasSet, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, TypeUniverse[0]], False, True, lastWasSet]],
				Function[{Typed[e, "System4Element"], Typed[rest, {"System4Element"}], Typed[prev, Booleans -> TypeUniverse[0]]},
					Function[{Typed[lastWasSet, Booleans]},
						InductiveRecursor["System4Element"][Function[{Typed[q, "System4Element"]}, TypeUniverse[0]],
							prev["false"],
							Function[{Typed[s, {NonNegativeIntegers}]}, prev["true"]], e]]], xs]["false"]],
		{"System4Element"} -> TypeUniverse[0]
	]],
	TypeTheoryDefinition["allTapeSetsOk", Typed[
		Function[{Typed[hi, NonNegativeIntegers], Typed[xs, {"System4Element"}]},
			InductiveRecursor[List][Function[{Typed[q, {"System4Element"}]}, TypeUniverse[0]], True,
				Function[{Typed[e, "System4Element"], Typed[rest, {"System4Element"}], Typed[prev, TypeUniverse[0]]},
					And[InductiveRecursor["System4Element"][Function[{Typed[q, "System4Element"]}, TypeUniverse[0]],
						True,
						Function[{Typed[s, {NonNegativeIntegers}]}, And["strictlyIncreasing"[s], "allBelowEqual"[hi, s]]], e], prev]], xs]],
		NonNegativeIntegers -> {"System4Element"} -> TypeUniverse[0]
	]],
	machineTheorem["noAdjacentStarsJoin",
		ForAll[{Typed[xs, {"System4Element"}], Typed[ys, {"System4Element"}], Typed[p, Booleans]},
			Implies["noAdjacentStarsFrom"[p, xs], Implies["endsWithSet4"[xs], Implies["noAdjacentStarsFrom"["false", ys], "noAdjacentStarsFrom"[p, Join[xs, ys]]]]]],
		{
			"Introduce"[xs], "Induction"[xs],
			"Introduce"[ys, p, h1, hEnd, h2], "Exact"["falseElimination"[hEnd]],
			"Introduce"[e, rest, ih, ys, p, h1, hEnd, h2],
			"Cases"[rest],
			"Introduce"[ih, h1, hEnd],
			"Cases"[e],
			"Introduce"[h1, hEnd], "Exact"["falseElimination"[hEnd]],
			"Introduce"[s, h1, hEnd], "Exact"[h2],
			"Introduce"[e2, rest2, ih, h1, hEnd],
			"Cases"[e],
			"Introduce"[h1, hEnd], "Cases"[p],
			"Introduce"[h1], "Exact"[ih[ys, "true", h1, hEnd, h2]],
			"Introduce"[h1], "Exact"["falseElimination"[h1]],
			"Introduce"[s, h1, hEnd],
			"Cases"[e2],
			"Introduce"[ih, h1, hEnd], "Exact"[ih[ys, "false", h1, hEnd, h2]],
			"Introduce"[s2, ih, h1, hEnd], "Exact"[ih[ys, "false", h1, hEnd, h2]]
		}
	],
	machineTheorem["endsWithSet4Join",
		ForAll[{Typed[xs, {"System4Element"}], Typed[ys, {"System4Element"}]},
			Implies["endsWithSet4"[ys], "endsWithSet4"[Join[xs, ys]]]],
		{
			"Introduce"[xs, ys, hy],
			"Have"[gen, ForAll[{Typed[l, {"System4Element"}], Typed[b, Booleans]},
				Implies[InductiveRecursor[List][Function[{Typed[q, {"System4Element"}]}, Booleans -> TypeUniverse[0]],
					Function[{Typed[lastWasSet, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, TypeUniverse[0]], False, True, lastWasSet]],
					Function[{Typed[e, "System4Element"], Typed[rest, {"System4Element"}], Typed[prev, Booleans -> TypeUniverse[0]]},
						Function[{Typed[lastWasSet, Booleans]},
							InductiveRecursor["System4Element"][Function[{Typed[q, "System4Element"]}, TypeUniverse[0]],
								prev["false"], Function[{Typed[s, {NonNegativeIntegers}]}, prev["true"]], e]]], ys]["false"],
					InductiveRecursor[List][Function[{Typed[q, {"System4Element"}]}, Booleans -> TypeUniverse[0]],
						Function[{Typed[lastWasSet, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, TypeUniverse[0]], False, True, lastWasSet]],
						Function[{Typed[e, "System4Element"], Typed[rest, {"System4Element"}], Typed[prev, Booleans -> TypeUniverse[0]]},
							Function[{Typed[lastWasSet, Booleans]},
								InductiveRecursor["System4Element"][Function[{Typed[q, "System4Element"]}, TypeUniverse[0]],
									prev["false"], Function[{Typed[s, {NonNegativeIntegers}]}, prev["true"]], e]]], Join[l, ys]][b]]]],
			"Introduce"[l], "Induction"[l],
			"Introduce"[b, h], "Cases"[ys],
			"Introduce"[hy, h], "Exact"["falseElimination"[h]],
			"Introduce"[e, r, hy, h], "Cases"[e], "Introduce"[hy, h], "Exact"[h], "Introduce"[s, hy, h], "Exact"[h],
			"Introduce"[e, r, ih, b, h], "Cases"[e], "Exact"[ih["false", h]], "Introduce"[s], "Exact"[ih["true", h]],
			"Exact"[gen[xs, "false", hy]]
		}
	],
	machineTheorem["allTapeSetsOkJoin",
		ForAll[{Typed[hi, NonNegativeIntegers], Typed[xs, {"System4Element"}], Typed[ys, {"System4Element"}]},
			Implies["allTapeSetsOk"[hi, xs], Implies["allTapeSetsOk"[hi, ys], "allTapeSetsOk"[hi, Join[xs, ys]]]]],
		{
			"Introduce"[hi, xs], "Induction"[xs],
			"Introduce"[ys, hx, hy], "Exact"[hy],
			"Introduce"[e, rest, ih, ys, hx, hy], "Cases"[hx], "Introduce"[he, hrest],
			"Exact"["andIntroduction"[he, ih[ys, hrest, hy]]]
		}
	],
	machineTheorem["starredEmptyPairsNoAdj",
		ForAll[{Typed[n, NonNegativeIntegers]}, "noAdjacentStarsFrom"["false", "starredEmptyPairs"[n]]],
		{
			"Introduce"[n], "Induction"[n], "Exact"["trueIntroduction"],
			"Introduce"[k, ih], "Exact"[ih]
		}
	],
	machineTheorem["starredEmptyPairsEndsSet",
		ForAll[{Typed[n, NonNegativeIntegers]}, Implies[1 <= n, "endsWithSet4"["starredEmptyPairs"[n]]]],
		{
			"Introduce"[n], "Induction"[n],
			"Introduce"[h], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"["falseElimination"[f]],
			"Introduce"[k, ih, h], "Cases"[k],
			"Introduce"[ih, h], "Exact"["trueIntroduction"],
			"Introduce"[k1, ih, h],
			"Have"[pos, 1 <= k1 + 1], "LinearArithmetic",
			"Change"["endsWithSet4"[Join[{"star4", "set4"[Typed[{}, {NonNegativeIntegers}]]}, "starredEmptyPairs"[k1 + 1]]]],
			"Exact"["endsWithSet4Join"[{"star4", "set4"[Typed[{}, {NonNegativeIntegers}]]}, "starredEmptyPairs"[k1 + 1], ih[pos]]]
		}
	],
	machineTheorem["starredEmptyPairsOk",
		ForAll[{Typed[hi, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, "allTapeSetsOk"[hi, "starredEmptyPairs"[n]]],
		{
			"Introduce"[hi, n], "Induction"[n], "Exact"["trueIntroduction"],
			"Introduce"[k, ih],
			"Exact"["andIntroduction"["trueIntroduction", "andIntroduction"["andIntroduction"["trueIntroduction", "trueIntroduction"], ih]]]
		}
	],
	machineTheorem["encBlocksWellFormed",
		ForAll[{Typed[rs, {{NonNegativeIntegers}}], Typed[f, NonNegativeIntegers]},
			Implies[1 <= f, Implies["allSetsStrictlyIncreasing"[rs], Implies["allRulesBelowEqual"[Subtract[f, 1], rs],
				And["noAdjacentStarsFrom"["false", "encBlocks"[rs, f, 0]],
					And[Implies[Not[rs == Typed[{}, {{NonNegativeIntegers}}]], "endsWithSet4"["encBlocks"[rs, f, 0]]],
						"allTapeSetsOk"[((f + f) + f) + 2, "encBlocks"[rs, f, 0]]]]]]]],
		{
			"Introduce"[rs], "Induction"[rs],
			"Introduce"[f, hf, hInc, hBd],
			"Exact"["andIntroduction"["trueIntroduction", "andIntroduction"[
				Function[{Typed[ne, Not[Typed[{}, {{NonNegativeIntegers}}] == Typed[{}, {{NonNegativeIntegers}}]]]},
					"falseElimination"[ne["equalityReflexivity"[Typed[{}, {{NonNegativeIntegers}}]]]]],
				"trueIntroduction"]]],
			"Introduce"[r, rest, ih, f, hf, hInc, hBd],
			"Cases"[hInc], "Introduce"[hrInc, hRestInc],
			"Cases"[hBd], "Introduce"[hrBd, hRestBd],
			"Cases"[ih[f, hf, hRestInc, hRestBd]], "Introduce"[restNoAdj, rest2],
			"Cases"[rest2], "Introduce"[restEnd, restOk],
			"Have"[fPos2, 1 <= f + f], "LinearArithmetic",
			"Have"[part1NoAdj, "noAdjacentStarsFrom"["false", Prepend["star4"][Prepend["set4"["encRuleSet"[r, f, 0]]]["starredEmptyPairs"[f + f]]]]],
			"Exact"["starredEmptyPairsNoAdj"[f + f]],
			"Have"[part1End, "endsWithSet4"[Prepend["star4"][Prepend["set4"["encRuleSet"[r, f, 0]]]["starredEmptyPairs"[f + f]]]]],
			"Change"["endsWithSet4"[Join[{"star4", "set4"["encRuleSet"[r, f, 0]]}, "starredEmptyPairs"[f + f]]]],
			"Exact"["endsWithSet4Join"[{"star4", "set4"["encRuleSet"[r, f, 0]]}, "starredEmptyPairs"[f + f], "starredEmptyPairsEndsSet"[f + f, fPos2]]],
			"Have"[part2NoAdj, "noAdjacentStarsFrom"["false", Prepend["star4"][Prepend["set4"["allInts"[((f + f) + f) + 1]]]["starredEmptyPairs"[Subtract[f + f, 2]]]]]],
			"Exact"["starredEmptyPairsNoAdj"[Subtract[f + f, 2]]],
			"Have"[part2End, "endsWithSet4"[Prepend["star4"][Prepend["set4"["allInts"[((f + f) + f) + 1]]]["starredEmptyPairs"[Subtract[f + f, 2]]]]]],
			"Cases"[Subtract[f + f, 2]],
			"Exact"["trueIntroduction"],
			"Introduce"[m],
			"Have"[mPos, 1 <= m + 1], "LinearArithmetic",
			"Change"["endsWithSet4"[Join[{"star4", "set4"["allInts"[((f + f) + f) + 1]]}, "starredEmptyPairs"[m + 1]]]],
			"Exact"["endsWithSet4Join"[{"star4", "set4"["allInts"[((f + f) + f) + 1]]}, "starredEmptyPairs"[m + 1], "starredEmptyPairsEndsSet"[m + 1, mPos]]],
			"Have"[blkNoAdj, "noAdjacentStarsFrom"["false", "encBlock"[r, f, 0]]],
			"Exact"["noAdjacentStarsJoin"[Prepend["star4"][Prepend["set4"["encRuleSet"[r, f, 0]]]["starredEmptyPairs"[f + f]]],
				Prepend["star4"][Prepend["set4"["allInts"[((f + f) + f) + 1]]]["starredEmptyPairs"[Subtract[f + f, 2]]]],
				"false", part1NoAdj, part1End, part2NoAdj]],
			"Have"[blkEnd, "endsWithSet4"["encBlock"[r, f, 0]]],
			"Exact"["endsWithSet4Join"[Prepend["star4"][Prepend["set4"["encRuleSet"[r, f, 0]]]["starredEmptyPairs"[f + f]]],
				Prepend["star4"][Prepend["set4"["allInts"[((f + f) + f) + 1]]]["starredEmptyPairs"[Subtract[f + f, 2]]]], part2End]],
			"Have"[allNoAdj, "noAdjacentStarsFrom"["false", Join["encBlock"[r, f, 0], "encBlocks"[rest, f, 0]]]],
			"Exact"["noAdjacentStarsJoin"["encBlock"[r, f, 0], "encBlocks"[rest, f, 0], "false", blkNoAdj, blkEnd, restNoAdj]],
			"Have"[allEnd, "endsWithSet4"[Join["encBlock"[r, f, 0], "encBlocks"[rest, f, 0]]]],
			"Cases"[rest], "Introduce"[ih, hRestInc, hRestBd, restNoAdj, restEnd, restOk, allNoAdj],
			"Change"["endsWithSet4"[Join["encBlock"[r, f, 0], Typed[{}, {"System4Element"}]]]],
			"Rewrite"["joinEmptyRight"["encBlock"[r, f, 0]]], "Exact"[blkEnd],
			"Introduce"[r2, rest2, ih, hRestInc, hRestBd, restNoAdj, restEnd, restOk, allNoAdj],
			"Have"[ne2, Not[Prepend[r2][rest2] == Typed[{}, {{NonNegativeIntegers}}]]],
			"Introduce"[eq],
			"Exact"[Construct["equalitySubstitution", {{NonNegativeIntegers}},
				Function[{Typed[l, {{NonNegativeIntegers}}]}, InductiveRecursor[List][Function[{Typed[q, {{NonNegativeIntegers}}]}, TypeUniverse[0]], False, Function[{Typed[h, {NonNegativeIntegers}], Typed[t, {{NonNegativeIntegers}}], Typed[u, TypeUniverse[0]]}, True], l]],
				Prepend[r2][rest2], Typed[{}, {{NonNegativeIntegers}}], eq, "trueIntroduction"]],
			"Exact"["endsWithSet4Join"["encBlock"[r, f, 0], "encBlocks"[Prepend[r2][rest2], f, 0], restEnd[ne2]]],
			(* Bound on allInts and encRuleSet *)
			"Have"[allIntsBd, "allBelowEqual"[((f + f) + f) + 2, "allInts"[((f + f) + f) + 1]]],
			"Have"[leA, 0 + (((f + f) + f) + 1) <= (((f + f) + f) + 2) + 1], "LinearArithmetic",
			"Exact"["allIntsFromAllBelowEqual"[((f + f) + f) + 1, 0, ((f + f) + f) + 2, leA]],
			"Have"[rpBd, "allBelowEqual"[((f + f) + f) + 2, "encRulePositions"[r, f, 0]]],
			"Cases"["lessEqualExists"[1, f, hf]], "Introduce"[f1, eqF],
			"Have"[subF, Subtract[f, 1] == f1], "Rewrite"[eqF], "Exact"["additionSubtractionCancellation"[f1, 1]],
			"Have"[hrBd1, "allBelowEqual"[f1, r]], "Rewrite"["equalitySymmetry"[subF]], "Exact"[hrBd],
			"Have"[leR, ((f1 + f1) + f) + 3 <= ((f + f) + f) + 2], "LinearArithmetic",
			"Exact"["allBelowEqualWeaken"[((f1 + f1) + f) + 3, ((f + f) + f) + 2, "encRulePositions"[r, f, 0], leR,
				"encRulePositionsAllBelowEqual"[r, f, 0, f1, "lessEqualZero"[f], hrBd1]]],
			"Have"[rsOk, And["strictlyIncreasing"["encRuleSet"[r, f, 0]], "allBelowEqual"[((f + f) + f) + 2, "encRuleSet"[r, f, 0]]]],
			"Exact"["andIntroduction"["encRuleSetStrictlyIncreasing"[r, f, 0, "lessEqualZero"[f], hrInc],
				"xorMergeAllBelowEqual"[((f + f) + f) + 2, "allInts"[((f + f) + f) + 1], "encRulePositions"[r, f, 0], allIntsBd, rpBd]]],
			"Have"[aiOk, And["strictlyIncreasing"["allInts"[((f + f) + f) + 1]], "allBelowEqual"[((f + f) + f) + 2, "allInts"[((f + f) + f) + 1]]]],
			"Exact"["andIntroduction"["allIntsStrictlyIncreasing"[((f + f) + f) + 1], allIntsBd]],
			"Have"[blkOk, "allTapeSetsOk"[((f + f) + f) + 2, "encBlock"[r, f, 0]]],
			"Exact"["allTapeSetsOkJoin"[((f + f) + f) + 2,
				Prepend["star4"][Prepend["set4"["encRuleSet"[r, f, 0]]]["starredEmptyPairs"[f + f]]],
				Prepend["star4"][Prepend["set4"["allInts"[((f + f) + f) + 1]]]["starredEmptyPairs"[Subtract[f + f, 2]]]],
				"andIntroduction"["trueIntroduction", "andIntroduction"[rsOk, "starredEmptyPairsOk"[((f + f) + f) + 2, f + f]]],
				"andIntroduction"["trueIntroduction", "andIntroduction"[aiOk, "starredEmptyPairsOk"[((f + f) + f) + 2, Subtract[f + f, 2]]]]]],
			"Exact"["andIntroduction"[allNoAdj, "andIntroduction"[Function[{Typed[u, Not[Prepend[r][rest] == Typed[{}, {{NonNegativeIntegers}}]]]}, allEnd],
				"allTapeSetsOkJoin"[((f + f) + f) + 2, "encBlock"[r, f, 0], "encBlocks"[rest, f, 0], blkOk, restOk]]]]
		}
	],
	(* Complete encoder well-formedness theorem for Rung 5 (initAC / rep3_init) *)
	machineTheorem["system5ToSystem4WellFormed",
		ForAll[{Typed[s, "System5Configuration"], Typed[f, NonNegativeIntegers]},
			Implies[1 <= f,
				Implies["strictlyAbove"[0, s[["bag"]]],
					Implies["allBelowEqual"[Subtract[f, 1], s[["bag"]]],
						Implies["allSetsStrictlyIncreasing"[s[["rules"]]],
							Implies["allRulesBelowEqual"[Subtract[f, 1], s[["rules"]]],
								And[
									"noAdjacentStarsFrom"["false", "system5ToSystem4"[s, f][["right"]]],
									And[
										"endsWithSet4"["system5ToSystem4"[s, f][["right"]]],
										"allTapeSetsOk"[((f + f) + f) + 2, "system5ToSystem4"[s, f][["right"]]]
									]
								]]]]]]],
		{
			"Introduce"[s, f], "Cases"[s], "Introduce"[bag, rules, hf, hBagInc, hBagBd, hRulesInc, hRulesBd],
			"Cases"["encBlocksWellFormed"[rules, f, hf, hRulesInc, hRulesBd]],
			"Introduce"[ebNoAdj, eb2], "Cases"[eb2], "Introduce"[ebEnd, ebOk],
			"Have"[tailNoAdj, "noAdjacentStarsFrom"["false", Join["starredEmptyPairs"[f], "encBlocks"[rules, f, 0]]]],
			"Exact"["noAdjacentStarsJoin"["starredEmptyPairs"[f], "encBlocks"[rules, f, 0], "false",
				"starredEmptyPairsNoAdj"[f], "starredEmptyPairsEndsSet"[f, hf], ebNoAdj]],
			"Have"[tailEnd, "endsWithSet4"[Join["starredEmptyPairs"[f], "encBlocks"[rules, f, 0]]]],
			"Cases"[rules],
			"Introduce"[hBagInc, hBagBd, hRulesInc, hRulesBd, ebNoAdj, ebEnd, ebOk, tailNoAdj],
			"Change"["endsWithSet4"[Join["starredEmptyPairs"[f], Typed[{}, {"System4Element"}]]]],
			"Rewrite"["joinEmptyRight"["starredEmptyPairs"[f]]],
			"Exact"["starredEmptyPairsEndsSet"[f, hf]],
			"Introduce"[r, rest, hBagInc, hBagBd, hRulesInc, hRulesBd, ebNoAdj, ebEnd, ebOk, tailNoAdj],
			"Have"[ne, Not[Prepend[r][rest] == Typed[{}, {{NonNegativeIntegers}}]]],
			"Introduce"[eq],
			"Exact"[Construct["equalitySubstitution", {{NonNegativeIntegers}},
				Function[{Typed[l, {{NonNegativeIntegers}}]}, InductiveRecursor[List][Function[{Typed[q, {{NonNegativeIntegers}}]}, TypeUniverse[0]], False, Function[{Typed[h, {NonNegativeIntegers}], Typed[t, {{NonNegativeIntegers}}], Typed[u, TypeUniverse[0]]}, True], l]],
				Prepend[r][rest], Typed[{}, {{NonNegativeIntegers}}], eq, "trueIntroduction"]],
			"Exact"["endsWithSet4Join"["starredEmptyPairs"[f], "encBlocks"[Prepend[r][rest], f, 0], ebEnd[ne]]],
			"Have"[allEnd, "endsWithSet4"[Prepend["set4"["encodeBag4"[bag]]][Join["starredEmptyPairs"[f], "encBlocks"[rules, f, 0]]]]],
			"Change"["endsWithSet4"[Join[{"set4"["encodeBag4"[bag]]}, Join["starredEmptyPairs"[f], "encBlocks"[rules, f, 0]]]]],
			"Exact"["endsWithSet4Join"[{"set4"["encodeBag4"[bag]]}, Join["starredEmptyPairs"[f], "encBlocks"[rules, f, 0]], tailEnd]],
			"Have"[bagBd, "allBelowEqual"[((f + f) + f) + 2, "encodeBag4"[bag]]],
			"Cases"["lessEqualExists"[1, f, hf]], "Introduce"[f1, eqF],
			"Have"[subF, Subtract[f, 1] == f1], "Rewrite"[eqF], "Exact"["additionSubtractionCancellation"[f1, 1]],
			"Have"[leB, Subtract[f, 1] + Subtract[f, 1] <= ((f + f) + f) + 2], "Rewrite"[subF], "LinearArithmetic",
			"Exact"["allBelowEqualWeaken"[Subtract[f, 1] + Subtract[f, 1], ((f + f) + f) + 2, "encodeBag4"[bag], leB,
				"encodeBag4AllBelowEqual"[bag, Subtract[f, 1], hBagBd]]],
			"Exact"["andIntroduction"[tailNoAdj, "andIntroduction"[allEnd,
				"andIntroduction"["andIntroduction"["encodeBag4StrictlyIncreasing"[bag, hBagInc], bagBd],
					"allTapeSetsOkJoin"[((f + f) + f) + 2, "starredEmptyPairs"[f], "encBlocks"[rules, f, 0],
						"starredEmptyPairsOk"[((f + f) + f) + 2, f], ebOk]]]]]
		}
	],
	TypeTheoryInductiveType["FueledSystem5", TypeUniverse[1], {
		"fueledSystem5" -> ForAll[{Typed[config, "System5Configuration"], Typed[elapsed, NonNegativeIntegers], Typed[budget, NonNegativeIntegers]}, "FueledSystem5"]
	}],
	TypeTheoryDefinition["fueledSystem5Step", Typed[
		Function[{Typed[fs, "FueledSystem5"]},
			InductiveRecursor["FueledSystem5"][Function[{Typed[q, "FueledSystem5"]}, Option["FueledSystem5"]],
				Function[{Typed[s, "System5Configuration"], Typed[j, NonNegativeIntegers], Typed[h, NonNegativeIntegers]},
					InductiveRecursor[NonNegativeIntegers][Function[{Typed[q, NonNegativeIntegers]}, Option["FueledSystem5"]],
						Typed["none", Option["FueledSystem5"]],
						Function[{Typed[h1, NonNegativeIntegers], Typed[u, Option["FueledSystem5"]]},
							"optionMap"[Function[{Typed[s2, "System5Configuration"]}, "fueledSystem5"[s2, j + 1, h1]], "system5Step"[s]]],
						h]], fs]],
		"FueledSystem5" -> Option["FueledSystem5"]
	]],
	(* Simulation relation RepS4 parameterized by f *)
	TypeTheoryDefinition["system4Represents", Typed[
		Function[{Typed[f, NonNegativeIntegers], Typed[fs, "FueledSystem5"], Typed[c, "System4Configuration"]},
			InductiveRecursor["FueledSystem5"][Function[{Typed[q, "FueledSystem5"]}, TypeUniverse[0]],
				Function[{Typed[s, "System5Configuration"], Typed[j, NonNegativeIntegers], Typed[h, NonNegativeIntegers]},
					Exists[{Typed[S0, {NonNegativeIntegers}], Typed[Krest, {{NonNegativeIntegers}}]},
						And[
							"allSetsStrictlyIncreasing"[Prepend[S0][Krest]],
							And[
								c == "system4Configuration"[Typed[{}, {"System4Element"}],
									Join["sets4"[Prepend[S0][Krest]], Join["starredEmptyPairs"[Subtract[f, j + j]], "encBlocks"[s[["rules"]], f, j + j]]],
									"state4A"],
								And[
									((j + j) + (h + h)) + 1 <= f,
									And[
										ForAll[{Typed[x, NonNegativeIntegers]},
											Implies[((x + (j + j)) + 2) + 1 <= f + f,
												"parMem"[x, Prepend[S0][Krest]] == "memNat"[x, "encodeBag4"[s[["bag"]]]]]],
										And[
											"strictlyAbove"[0, s[["bag"]]],
											And[
												"allBelowEqual"[Subtract[f, j + 1], s[["bag"]]],
												And[
													"allSetsStrictlyIncreasing"[s[["rules"]]],
													"allRulesBelowEqual"[Subtract[f, (j + (h + h)) + 1], s[["rules"]]]
												]
											]
										]
									]
								]
							]
						]
					]], fs]],
		NonNegativeIntegers -> "FueledSystem5" -> "System4Configuration" -> TypeUniverse[0]
	]],
	(* Initial condition: system5ToSystem4 satisfies system4Represents at j = 0 *)
	machineTheorem["system5ToSystem4Represents",
		ForAll[{Typed[s, "System5Configuration"], Typed[f, NonNegativeIntegers], Typed[h, NonNegativeIntegers]},
			Implies[(h + h) + 1 <= f,
				Implies["strictlyAbove"[0, s[["bag"]]],
					Implies["allBelowEqual"[Subtract[f, 1], s[["bag"]]],
						Implies["allSetsStrictlyIncreasing"[s[["rules"]]],
							Implies["allRulesBelowEqual"[Subtract[f, (h + h) + 1], s[["rules"]]],
								"system4Represents"[f, "fueledSystem5"[s, 0, h], "system5ToSystem4"[s, f]]]]]]]],
		{
			"Introduce"[s, f, h, hfh, hBagInc, hBagBd, hRulesInc, hRulesBd],
			"Have"[hPar, ForAll[{Typed[x, NonNegativeIntegers]},
				Implies[((x + (0 + 0)) + 2) + 1 <= f + f,
					"parMem"[x, {"encodeBag4"[s[["bag"]]]}] == "memNat"[x, "encodeBag4"[s[["bag"]]]]]]],
			"Introduce"[x, hx],
			"Exact"["xorBoolFalseRight"["memNat"[x, "encodeBag4"[s[["bag"]]]]]],
			"Have"[hf0, ((0 + 0) + (h + h)) + 1 <= f], "LinearArithmetic",
			"Have"[hRB, "allRulesBelowEqual"[Subtract[f, (0 + (h + h)) + 1], s[["rules"]]]],
			"Rewrite"["additionZeroLeft"[h + h]], "Exact"[hRulesBd],
			"Have"[hBB, "allBelowEqual"[Subtract[f, 0 + 1], s[["bag"]]]],
			"Rewrite"["additionZeroLeft"[1]], "Exact"[hBagBd],
			"Exact"["existsIntroduction"["encodeBag4"[s[["bag"]]],
				"existsIntroduction"[Typed[{}, {{NonNegativeIntegers}}],
					"andIntroduction"[
						"andIntroduction"["encodeBag4StrictlyIncreasing"[s[["bag"]], hBagInc], "trueIntroduction"],
						"andIntroduction"[
							"equalityReflexivity"["system5ToSystem4"[s, f]],
							"andIntroduction"[hf0, "andIntroduction"[hPar, "andIntroduction"[hBagInc,
								"andIntroduction"[hBB, "andIntroduction"[hRulesInc, hRB]]]]]]]]]]
		}
	],
	(* Helper: shiftUpRules preserves allSetsStrictlyIncreasing *)
	machineTheorem["shiftUpStrictlyAbove",
		ForAll[{Typed[xs, {NonNegativeIntegers}], Typed[d, NonNegativeIntegers], Typed[lo, NonNegativeIntegers]},
			Implies["strictlyAbove"[lo, xs], "strictlyAbove"[lo + d, "shiftUp"[d, xs]]]],
		{
			"Introduce"[xs], "Induction"[xs],
			"Introduce"[d, lo, h], "Exact"["trueIntroduction"],
			"Introduce"[x, rest, ih, d, lo, h], "Cases"[h], "Introduce"[hx, hrest],
			"Have"[hx2, (lo + d) + 1 <= x + d], "LinearArithmetic",
			"Exact"["andIntroduction"[hx2, ih[d, x, hrest]]]
		}
	],
	machineTheorem["shiftUpStrictlyIncreasing",
		ForAll[{Typed[xs, {NonNegativeIntegers}], Typed[d, NonNegativeIntegers]},
			Implies["strictlyIncreasing"[xs], "strictlyIncreasing"["shiftUp"[d, xs]]]],
		{
			"Introduce"[xs, d], "Cases"[xs],
			"Introduce"[h], "Exact"["trueIntroduction"],
			"Introduce"[x, rest, h],
			"Exact"["shiftUpStrictlyAbove"[rest, d, x, h]]
		}
	],
	machineTheorem["shiftUpRulesStrictlyIncreasing",
		ForAll[{Typed[rs, {{NonNegativeIntegers}}], Typed[d, NonNegativeIntegers]},
			Implies["allSetsStrictlyIncreasing"[rs], "allSetsStrictlyIncreasing"["shiftUpRules"[d, rs]]]],
		{
			"Introduce"[rs], "Induction"[rs],
			"Introduce"[d, h], "Exact"["trueIntroduction"],
			"Introduce"[r, rest, ih, d, h], "Cases"[h], "Introduce"[hr, hrest],
			"Exact"["andIntroduction"["shiftUpStrictlyIncreasing"[r, d, hr], ih[d, hrest]]]
		}
	],
	machineTheorem["allRulesBelowEqualWeaken",
		ForAll[{Typed[hi1, NonNegativeIntegers], Typed[hi2, NonNegativeIntegers], Typed[rs, {{NonNegativeIntegers}}]},
			Implies[hi1 <= hi2, Implies["allRulesBelowEqual"[hi1, rs], "allRulesBelowEqual"[hi2, rs]]]],
		{
			"Introduce"[hi1, hi2, rs], "Induction"[rs],
			"Introduce"[le, h], "Exact"["trueIntroduction"],
			"Introduce"[r, rest, ih, le, h], "Cases"[h], "Introduce"[hr, hrest],
			"Exact"["andIntroduction"["allBelowEqualWeaken"[hi1, hi2, r, le, hr], ih[le, hrest]]]
		}
	],
	machineTheorem["strictlyAbove1FromNo1",
		ForAll[{Typed[xs, {NonNegativeIntegers}]},
			Implies["strictlyAbove"[0, xs],
				Implies["memNat"[1, xs] == "false",
					"strictlyAbove"[1, xs]]]],
		{
			"Introduce"[xs], "Cases"[xs],
			"Introduce"[hInc, hNo1], "Exact"["trueIntroduction"],
			"Introduce"[b, bRest, hInc, hNo1],
			"Cases"[hInc], "Introduce"[hbPos, hbRest],
			"Have"[neq1b, Not[1 == b]],
			"Introduce"[eq1b],
			"Have"[bad, "memNat"[1, Prepend[b][bRest]] == "true"],
			"Change"[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Booleans], "memNat"[1, bRest], "true", Decide[1 == b]] == "true"],
			"Rewrite"["decideEqualTrue"[1, b, eq1b]], "Reflexivity",
			"Have"[ft, "true" == "false"], "Exact"["equalityTransitivity"["equalitySymmetry"[bad], hNo1]],
			"Exact"[Construct["equalitySubstitution", Booleans,
				Function[{Typed[q, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, TypeUniverse[0]], False, True, q]],
				"true", "false", ft, "trueIntroduction"]],
			"Have"[bGe2, 1 + 1 <= b],
			"Cases"["lessEqualExistsRight"[1, b, hbPos]], "Introduce"[db, eqDb],
			"Cases"[db], "Introduce"[eqDb], "Have"[eq1, 1 == b], "LinearArithmetic", "Exact"["falseElimination"[neq1b[eq1]]],
			"Introduce"[db1, eqDb], "LinearArithmetic",
			"Exact"["andIntroduction"[bGe2, hbRest]]
		}
	],
	(* Per-step lemma, D-step case: works even when s.rules == {} (for repS4Terminal!) *)
	machineTheorem["repS4DStep",
		ForAll[{Typed[f, NonNegativeIntegers], Typed[s, "System5Configuration"], Typed[j, NonNegativeIntegers], Typed[h, NonNegativeIntegers], Typed[c, "System4Configuration"]},
			Implies["system4Represents"[f, "fueledSystem5"[s, j, h + 1], c],
				Implies["memNat"[1, s[["bag"]]] == "false",
					Exists[{Typed[k, NonNegativeIntegers]}, And[1 <= k,
						Exists[{Typed[c2, "System4Configuration"]}, And[
							"steps"["system4Step", k, c] == "some"[c2],
							"system4Represents"[f,
								"fueledSystem5"["system5Configuration"["shiftDown"[1, s[["bag"]]], "shiftUpRules"[1, s[["rules"]]]], j + 1, h],
								c2]]]]]]]],
		{
			"Introduce"[f, s, j, h, c, hRep, hNo1],
			"Cases"[hRep], "Introduce"[S0, hRep1], "Cases"[hRep1], "Introduce"[Krest, hRep2],
			"Cases"[hRep2], "Introduce"[hKInc, hRep3],
			"Cases"[hRep3], "Introduce"[eqC, hRep4],
			"Cases"[hRep4], "Introduce"[hBoundF, hRep5],
			"Cases"[hRep5], "Introduce"[hPar, hRep6],
			"Cases"[hRep6], "Introduce"[hBagInc, hRep7],
			"Cases"[hRep7], "Introduce"[hBagBd, hRep8],
			"Cases"[hRep8], "Introduce"[hRulesInc, hRulesBd],
			(* Parity of 0 and 1 in K = S0 :: Krest *)
			"Have"[b0, ((0 + (j + j)) + 2) + 1 <= f + f], "LinearArithmetic",
			"Have"[b1, ((1 + (j + j)) + 2) + 1 <= f + f], "LinearArithmetic",
			"Have"[par0, "parMem"[0, Prepend[S0][Krest]] == "false"],
			"Rewrite"[hPar[0, b0]],
			"Have"[e0, "memNat"[0 + 0, "encodeBag4"[s[["bag"]]]] == "memNat"[0 + 1, s[["bag"]]]],
			"Exact"["memNatEncodeBag4Even"[0, s[["bag"]], hBagInc]],
			"Change"["memNat"[0 + 0, "encodeBag4"[s[["bag"]]]] == "false"],
			"Rewrite"[e0], "Exact"[hNo1],
			"Have"[par1, "parMem"[0, Map["decr4", Prepend[S0][Krest]]] == "false"],
			"Rewrite"["parMemMapDecr4"[0, Prepend[S0][Krest], hKInc]],
			"Change"["parMem"[1, Prepend[S0][Krest]] == "false"],
			"Rewrite"[hPar[1, b1]],
			"Exact"["memNatEncodeBag4Odd"[0, s[["bag"]], hBagInc]],
			(* Split f - 2j = g + 2 where g = f - 2(j + 1) *)
			"Have"[leG, (j + j) + 2 <= f], "LinearArithmetic",
			"Cases"["lessEqualExists"[(j + j) + 2, f, leG]], "Introduce"[g, eqF],
			"Have"[subOld, Subtract[f, j + j] == g + 2],
			"Rewrite"[eqF], "Have"[t1, g + ((j + j) + 2) == (g + 2) + (j + j)], "LinearArithmetic",
			"Rewrite"[t1], "Exact"["additionSubtractionCancellation"[g + 2, j + j]],
			"Have"[subNew, Subtract[f, (j + 1) + (j + 1)] == g],
			"Rewrite"[eqF], "Have"[t2, g + ((j + j) + 2) == g + ((j + 1) + (j + 1))], "LinearArithmetic",
			"Rewrite"[t2], "Exact"["additionSubtractionCancellation"[g, (j + 1) + (j + 1)]],
			(* Run system4DStep *)
			"Cases"["system4DStep"[S0, Krest, g, "encBlocks"[s[["rules"]], f, j + j], hKInc, par0, par1]],
			"Introduce"[kSteps, dBoth], "Cases"[dBoth], "Introduce"[kPos, dRun],
			"Have"[runEq, "steps"["system4Step", kSteps, c] == "some"["system4Configuration"[Typed[{}, {"System4Element"}],
				Join["sets4"[Join[Map["decr4", Map["decr4", Prepend[S0][Krest]]], {Typed[{}, {NonNegativeIntegers}], Typed[{}, {NonNegativeIntegers}]}]],
					Join["starredEmptyPairs"[Subtract[f, (j + 1) + (j + 1)]], "encBlocks"["shiftUpRules"[1, s[["rules"]]], f, (j + 1) + (j + 1)]]],
				"state4A"]]],
			"Rewrite"[eqC], "Rewrite"[subOld], "Rewrite"[subNew],
			"Have"[j2Eq, (j + 1) + (j + 1) == (j + j) + 2], "LinearArithmetic",
			"Rewrite"[j2Eq], "Rewrite"["encBlocksShift"[s[["rules"]], f, j + j]], "Exact"[dRun],
			(* Bag strictlyAbove[1, s.bag] from strictlyAbove[0, s.bag] and memNat[1, s.bag] == false *)
			"Have"[hBag1, "strictlyAbove"[1, s[["bag"]]]],
			"Exact"["strictlyAbove1FromNo1"[s[["bag"]], hBagInc, hNo1]],
			(* Prove new RepS4 invariants *)
			"Have"[hK2Inc, "allSetsStrictlyIncreasing"[Join[Map["decr4", Map["decr4", Prepend[S0][Krest]]], {Typed[{}, {NonNegativeIntegers}], Typed[{}, {NonNegativeIntegers}]}]]],
			"Exact"["allSetsStrictlyIncreasingJoin"[Map["decr4", Map["decr4", Prepend[S0][Krest]]], {Typed[{}, {NonNegativeIntegers}], Typed[{}, {NonNegativeIntegers}]},
				"allSetsStrictlyIncreasingMapDecr4"[Map["decr4", Prepend[S0][Krest]], "allSetsStrictlyIncreasingMapDecr4"[Prepend[S0][Krest], hKInc]],
				"andIntroduction"["trueIntroduction", "andIntroduction"["trueIntroduction", "trueIntroduction"]]]],
			"Have"[hBoundF2, (((j + 1) + (j + 1)) + (h + h)) + 1 <= f], "LinearArithmetic",
			"Have"[hPar2, ForAll[{Typed[x, NonNegativeIntegers]},
				Implies[((x + ((j + 1) + (j + 1))) + 2) + 1 <= f + f,
					"parMem"[x, Join[Map["decr4", Map["decr4", Prepend[S0][Krest]]], {Typed[{}, {NonNegativeIntegers}], Typed[{}, {NonNegativeIntegers}]}]] ==
						"memNat"[x, "encodeBag4"["shiftDown"[1, s[["bag"]]]]]]]],
			"Introduce"[x, hx],
			"Rewrite"["parMemJoin"[x, Map["decr4", Map["decr4", Prepend[S0][Krest]]], {Typed[{}, {NonNegativeIntegers}], Typed[{}, {NonNegativeIntegers}]}]],
			"Change"["xorBool"["parMem"[x, Map["decr4", Map["decr4", Prepend[S0][Krest]]]], "false"] == "memNat"[x, "encodeBag4"["shiftDown"[1, s[["bag"]]]]]],
			"Rewrite"["xorBoolFalseRight"["parMem"[x, Map["decr4", Map["decr4", Prepend[S0][Krest]]]]]],
			"Rewrite"["parMemMapDecr4"[x, Map["decr4", Prepend[S0][Krest]], "allSetsStrictlyIncreasingMapDecr4"[Prepend[S0][Krest], hKInc]]],
			"Rewrite"["parMemMapDecr4"[x + 1, Prepend[S0][Krest], hKInc]],
			"Have"[hx2, (((x + 2) + (j + j)) + 2) + 1 <= f + f], "LinearArithmetic",
			"Change"["parMem"[x + 2, Prepend[S0][Krest]] == "memNat"[x, "encodeBag4"["shiftDown"[1, s[["bag"]]]]]],
			"Rewrite"[hPar[x + 2, hx2]],
			"Exact"["equalitySymmetry"["memNatEncodeBag4ShiftDown1"[x, s[["bag"]], hBag1]]],
			"Have"[hNewBagInc, "strictlyAbove"[0, "shiftDown"[1, s[["bag"]]]]],
			"Exact"["shiftDownStrictlyAbove"[s[["bag"]], 1, 0, hBag1]],
			"Have"[hNewBagBd, "allBelowEqual"[Subtract[f, (j + 1) + 1], "shiftDown"[1, s[["bag"]]]]],
			"Have"[subBagEq, Subtract[f, (j + 1) + 1] + 1 == Subtract[f, j + 1]],
			"Rewrite"[eqF],
			"Have"[ea, g + ((j + j) + 2) == (g + j) + ((j + 1) + 1)], "LinearArithmetic",
			"Have"[eb, g + ((j + j) + 2) == ((g + j) + 1) + (j + 1)], "LinearArithmetic",
			"Rewrite"[ea], "Rewrite"["additionSubtractionCancellation"[g + j, (j + 1) + 1]],
			"Have"[ec, (g + j) + ((j + 1) + 1) == ((g + j) + 1) + (j + 1)], "LinearArithmetic",
			"Rewrite"[ec], "Rewrite"["additionSubtractionCancellation"[(g + j) + 1, j + 1]],
			"Have"[hBB2, "allBelowEqual"[Subtract[f, (j + 1) + 1] + 1, s[["bag"]]]],
			"Rewrite"[subBagEq], "Exact"[hBagBd],
			"Exact"["shiftDownAllBelowEqual"[s[["bag"]], 1, Subtract[f, (j + 1) + 1], hBB2]],
			"Have"[hNewRulesBd, "allRulesBelowEqual"[Subtract[f, ((j + 1) + (h + h)) + 1], "shiftUpRules"[1, s[["rules"]]]]],
			"Have"[subRuleEq, Subtract[f, (j + ((h + 1) + (h + 1))) + 1] + 1 == Subtract[f, ((j + 1) + (h + h)) + 1]],
			"Have"[leR, (j + ((h + 1) + (h + 1))) + 1 <= f], "LinearArithmetic",
			"Cases"["lessEqualExists"[(j + ((h + 1) + (h + 1))) + 1, f, leR]], "Introduce"[dr, eqFr],
			"Rewrite"[eqFr],
			"Have"[er1, dr + ((j + ((h + 1) + (h + 1))) + 1) == (dr + 1) + (((j + 1) + (h + h)) + 1)], "LinearArithmetic",
			"Rewrite"["additionSubtractionCancellation"[dr, (j + ((h + 1) + (h + 1))) + 1]],
			"Rewrite"[er1], "Rewrite"["additionSubtractionCancellation"[dr + 1, ((j + 1) + (h + h)) + 1]],
			"Rewrite"["equalitySymmetry"[subRuleEq]],
			"Exact"["shiftUpRulesAllBelowEqual"[s[["rules"]], 1, Subtract[f, (j + ((h + 1) + (h + 1))) + 1], hRulesBd]],
			(* Assemble witness! *)
			"Exact"["existsIntroduction"[kSteps, "andIntroduction"[kPos,
				"existsIntroduction"[
					"system4Configuration"[Typed[{}, {"System4Element"}],
						Join["sets4"[Join[Map["decr4", Map["decr4", Prepend[S0][Krest]]], {Typed[{}, {NonNegativeIntegers}], Typed[{}, {NonNegativeIntegers}]}]],
							Join["starredEmptyPairs"[Subtract[f, (j + 1) + (j + 1)]], "encBlocks"["shiftUpRules"[1, s[["rules"]]], f, (j + 1) + (j + 1)]]],
						"state4A"],
					"andIntroduction"[runEq,
						"existsIntroduction"["decr4"["decr4"[S0]],
							"existsIntroduction"[Join[Map["decr4", Map["decr4", Krest]], {Typed[{}, {NonNegativeIntegers}], Typed[{}, {NonNegativeIntegers}]}],
								"andIntroduction"[hK2Inc,
									"andIntroduction"[
										"equalityReflexivity"["system4Configuration"[Typed[{}, {"System4Element"}],
											Join["sets4"[Join[Map["decr4", Map["decr4", Prepend[S0][Krest]]], {Typed[{}, {NonNegativeIntegers}], Typed[{}, {NonNegativeIntegers}]}]],
												Join["starredEmptyPairs"[Subtract[f, (j + 1) + (j + 1)]], "encBlocks"["shiftUpRules"[1, s[["rules"]]], f, (j + 1) + (j + 1)]]],
											"state4A"]],
										"andIntroduction"[hBoundF2,
											"andIntroduction"[hPar2,
												"andIntroduction"[hNewBagInc,
													"andIntroduction"[hNewBagBd,
														"andIntroduction"["shiftUpRulesStrictlyIncreasing"[s[["rules"]], 1, hRulesInc], hNewRulesBd]]]]]]]]]]]]]]
		}
	],
	(* Decoder: leadSets4, decodeS4Loop (with odd-parity vacuity guard!), decodeS4, repS4DecodeBand, repS4TurnStep *)
	TypeTheoryDefinition["leadSets4", Typed[
		Function[{Typed[xs, {"System4Element"}]},
			InductiveRecursor[List][Function[{Typed[q, {"System4Element"}]}, {{NonNegativeIntegers}}], Typed[{}, {{NonNegativeIntegers}}],
				Function[{Typed[e, "System4Element"], Typed[rest, {"System4Element"}], Typed[prev, {{NonNegativeIntegers}}]},
					InductiveRecursor["System4Element"][Function[{Typed[q, "System4Element"]}, {{NonNegativeIntegers}}],
						Typed[{}, {{NonNegativeIntegers}}],
						Function[{Typed[s, {NonNegativeIntegers}]}, Prepend[s][prev]], e]], xs]],
		{"System4Element"} -> {{NonNegativeIntegers}}
	]],
	machineTheorem["leadSets4SetsStar",
		ForAll[{Typed[K, {{NonNegativeIntegers}}], Typed[R, {"System4Element"}]},
			"leadSets4"[Join["sets4"[K], Prepend["star4"][R]]] == K],
		{
			"Introduce"[K], "Induction"[K],
			"Introduce"[R], "Reflexivity",
			"Introduce"[s, rest, ih, R],
			"Change"[Prepend[s]["leadSets4"[Join["sets4"[rest], Prepend["star4"][R]]]] == Prepend[s][rest]],
			"Rewrite"[ih[R]]
		}
	],
	TypeTheoryDefinition["decodeS4Loop", Typed[
		Function[{Typed[K, {{NonNegativeIntegers}}], Typed[count, NonNegativeIntegers]},
			InductiveRecursor[NonNegativeIntegers][Function[{Typed[q, NonNegativeIntegers]}, NonNegativeIntegers -> Booleans -> NonNegativeIntegers -> Option[{NonNegativeIntegers}]],
				Function[{Typed[x, NonNegativeIntegers], Typed[isEven, Booleans], Typed[q, NonNegativeIntegers]}, "some"[Typed[{}, {NonNegativeIntegers}]]],
				Function[{Typed[k, NonNegativeIntegers], Typed[prev, NonNegativeIntegers -> Booleans -> NonNegativeIntegers -> Option[{NonNegativeIntegers}]]},
					Function[{Typed[x, NonNegativeIntegers], Typed[isEven, Booleans], Typed[q, NonNegativeIntegers]},
						InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Option[{NonNegativeIntegers}]],
							(* odd: x = 2q + 1 — vacuity guard: reject if parMem[x, K] == true! *)
							InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Option[{NonNegativeIntegers}]],
								prev[x + 1, "true", q + 1],
								Typed["none", Option[{NonNegativeIntegers}]],
								"parMem"[x, K]],
							(* even: x = 2q — if parMem[x, K] == true, prepend q + 1 *)
							InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Option[{NonNegativeIntegers}]],
								prev[x + 1, "false", q],
								"optionMap"[Function[{Typed[rest, {NonNegativeIntegers}]}, Prepend[q + 1][rest]], prev[x + 1, "false", q]],
								"parMem"[x, K]],
							isEven]]], count]],
		{{NonNegativeIntegers}} -> NonNegativeIntegers -> NonNegativeIntegers -> Booleans -> NonNegativeIntegers -> Option[{NonNegativeIntegers}]
	]],
	TypeTheoryDefinition["decodeS4", Typed[
		Function[{Typed[c, "System4Configuration"], Typed[bound, NonNegativeIntegers]},
			"decodeS4Loop"["leadSets4"[c[["right"]]], bound, 0, "true", 0]],
		"System4Configuration" -> NonNegativeIntegers -> Option[{NonNegativeIntegers}]
	]],
	(* Helper: decodeS4Loop recovers bag from any starting position x = 2q (isEven=true) or x = 2q+1 (isEven=false) *)
	machineTheorem["decodeS4LoopBag",
		ForAll[{Typed[count, NonNegativeIntegers], Typed[K, {{NonNegativeIntegers}}], Typed[bag, {NonNegativeIntegers}],
				Typed[x, NonNegativeIntegers], Typed[isEven, Booleans], Typed[q, NonNegativeIntegers]},
			Implies[InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, TypeUniverse[0]], x == (q + q) + 1, x == q + q, isEven],
				Implies[ForAll[{Typed[y, NonNegativeIntegers]}, Implies[x <= y, Implies[y + 1 <= x + count, "parMem"[y, K] == "memNat"[y, "encodeBag4"[bag]]]]],
					Implies["strictlyAbove"[InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, NonNegativeIntegers], q + 1, q, isEven], bag],
						Implies["allBelowEqual"[x + count, "encodeBag4"[bag]],
							Implies[ForAll[{Typed[e, NonNegativeIntegers]}, Implies["memNat"[e, bag] == "true", (Subtract[e, 1] + Subtract[e, 1]) + 1 <= x + count]],
								"decodeS4Loop"[K, count, x, isEven, q] == "some"[bag]]]]]]],
		{
			"Introduce"[count], "Induction"[count],
			"Introduce"[K, bag, x, isEven, q, hX, hPar, hAbove, hAllBd, hMemBd],
			"Cases"[bag], "Introduce"[hPar, hAbove, hAllBd, hMemBd], "Reflexivity",
			"Introduce"[e, rest, hPar, hAbove, hAllBd, hMemBd],
			"Have"[me, "memNat"[e, Prepend[e][rest]] == "true"],
			"Change"[InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Booleans], "memNat"[e, rest], "true", Decide[e == e]] == "true"],
			"Rewrite"["decideEqualTrue"[e, e, "equalityReflexivity"[e]]], "Reflexivity",
			"Have"[eLt, (Subtract[e, 1] + Subtract[e, 1]) + 1 <= x + 0], "Exact"[hMemBd[e, me]],
			"Cases"[isEven],
			"Introduce"[hX, hAbove],
			"Have"[hX2, x == (q + q) + 1], "Exact"[hX],
			"Have"[hAbove2, "strictlyAbove"[q + 1, Prepend[e][rest]]], "Exact"[hAbove],
			"Cases"[hAbove2], "Introduce"[he, hrest],
			"Cases"[e], "Introduce"[hPar, hAllBd, hMemBd, me, eLt, hAbove, he, hrest], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"["falseElimination"[f]],
			"Introduce"[e1, hPar, hAllBd, hMemBd, me, eLt, hAbove, he, hrest],
			"Have"[eLt2, (e1 + e1) + 1 <= x + 0], "Exact"[eLt],
			"Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"["falseElimination"[f]],
			"Introduce"[hX, hAbove],
			"Have"[hX2, x == q + q], "Exact"[hX],
			"Have"[hAbove2, "strictlyAbove"[q, Prepend[e][rest]]], "Exact"[hAbove],
			"Cases"[hAbove2], "Introduce"[he, hrest],
			"Cases"[e], "Introduce"[hPar, hAllBd, hMemBd, me, eLt, hAbove, he, hrest], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"["falseElimination"[f]],
			"Introduce"[e1, hPar, hAllBd, hMemBd, me, eLt, hAbove, he, hrest],
			"Have"[eLt2, (e1 + e1) + 1 <= x + 0], "Exact"[eLt],
			"Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"["falseElimination"[f]],
			(* Induction step: count = k + 1 *)
			"Introduce"[k, ih, K, bag, x, isEven, q, hX, hPar, hAbove, hAllBd, hMemBd],
			"Have"[xLe, x <= x], "LinearArithmetic",
			"Have"[xLt, x + 1 <= x + (k + 1)], "LinearArithmetic",
			"Have"[hParX, "parMem"[x, K] == "memNat"[x, "encodeBag4"[bag]]], "Exact"[hPar[x, xLe, xLt]],
			"Have"[hParNext, ForAll[{Typed[y, NonNegativeIntegers]}, Implies[x + 1 <= y, Implies[y + 1 <= (x + 1) + k, "parMem"[y, K] == "memNat"[y, "encodeBag4"[bag]]]]]],
			"Introduce"[y, hy1, hy2],
			"Have"[ya, x <= y], "LinearArithmetic", "Have"[yb, y + 1 <= x + (k + 1)], "LinearArithmetic",
			"Exact"[hPar[y, ya, yb]],
			"Have"[eqSum, x + (k + 1) == (x + 1) + k], "LinearArithmetic",
			"Cases"[isEven],
			(* isEven = false: x = 2q + 1 *)
			"Introduce"[hX, hAbove],
			"Have"[hX2, x == (q + q) + 1], "Exact"[hX],
			"Have"[hAbove2, "strictlyAbove"[q + 1, bag]], "Exact"[hAbove],
			"Have"[hBag0, "strictlyAbove"[0, bag]], "Exact"["strictlyAboveWeaken"[q + 1, 0, bag, "lessEqualZero"[q + 1], hAbove2]],
			"Have"[hParOdd, "parMem"[x, K] == "false"],
			"Rewrite"[hParX], "Rewrite"[hX2], "Exact"["memNatEncodeBag4Odd"[q, bag, hBag0]],
			"Change"[InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Option[{NonNegativeIntegers}]],
				"decodeS4Loop"[K, k, x + 1, "true", q + 1], Typed["none", Option[{NonNegativeIntegers}]], "parMem"[x, K]] == "some"[bag]],
			"Rewrite"[hParOdd],
			"Have"[hXNext, x + 1 == (q + 1) + (q + 1)], "LinearArithmetic",
			"Have"[hAllNext, "allBelowEqual"[(x + 1) + k, "encodeBag4"[bag]]], "Rewrite"["equalitySymmetry"[eqSum]], "Exact"[hAllBd],
			"Have"[hMemNext, ForAll[{Typed[e, NonNegativeIntegers]}, Implies["memNat"[e, bag] == "true", (Subtract[e, 1] + Subtract[e, 1]) + 1 <= (x + 1) + k]]],
			"Introduce"[e, me], "Rewrite"["equalitySymmetry"[eqSum]], "Exact"[hMemBd[e, me]],
			"Exact"[ih[K, bag, x + 1, "true", q + 1, hXNext, hParNext, hAbove2, hAllNext, hMemNext]],
			(* isEven = true: x = 2q *)
			"Introduce"[hX, hAbove],
			"Have"[hX2, x == q + q], "Exact"[hX],
			"Have"[hAbove2, "strictlyAbove"[q, bag]], "Exact"[hAbove],
			"Have"[hBag0, "strictlyAbove"[0, bag]], "Exact"["strictlyAboveWeaken"[q, 0, bag, "lessEqualZero"[q], hAbove2]],
			"Have"[hParEven, "parMem"[x, K] == "memNat"[q + 1, bag]],
			"Rewrite"[hParX], "Rewrite"[hX2], "Exact"["memNatEncodeBag4Even"[q, bag, hBag0]],
			"Change"[InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Option[{NonNegativeIntegers}]],
				"decodeS4Loop"[K, k, x + 1, "false", q],
				"optionMap"[Function[{Typed[rest, {NonNegativeIntegers}]}, Prepend[q + 1][rest]], "decodeS4Loop"[K, k, x + 1, "false", q]],
				"parMem"[x, K]] == "some"[bag]],
			"Rewrite"[hParEven],
			"Cases"[bag],
			"Introduce"[hPar, hAllBd, hMemBd, hParX, hParNext, hAbove, hAbove2, hBag0, hParEven],
			"Have"[hXNext, x + 1 == (q + q) + 1], "LinearArithmetic",
			"Have"[hMemEmpty, ForAll[{Typed[e, NonNegativeIntegers]}, Implies["memNat"[e, Typed[{}, {NonNegativeIntegers}]] == "true", (Subtract[e, 1] + Subtract[e, 1]) + 1 <= (x + 1) + k]]],
			"Introduce"[e, me], "Exact"["falseElimination"[Construct["equalitySubstitution", Booleans,
				Function[{Typed[b, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, TypeUniverse[0]], True, False, b]],
				"false", "true", me, "trueIntroduction"]]],
			"Exact"[ih[K, Typed[{}, {NonNegativeIntegers}], x + 1, "false", q, hXNext, hParNext, "trueIntroduction", "trueIntroduction", hMemEmpty]],
			"Introduce"[e, bRest, hPar, hAllBd, hMemBd, hParX, hParNext, hAbove, hAbove2, hBag0, hParEven],
			"Cases"[hAbove2], "Introduce"[he, hRestAbove],
			"Have"[hXNext, x + 1 == (q + q) + 1], "LinearArithmetic",
			"Have"[dec, Decidable[q + 1 == e]], "Exact"["naturalNumberEqualityDecidable"[q + 1, e]], "Cases"[dec],
			(* q + 1 != e, so e >= q + 2 *)
			"Introduce"[neq],
			"Have"[eGe2, (q + 1) + 1 <= e],
			"Cases"["lessEqualExistsRight"[q + 1, e, he]], "Introduce"[d, eqE],
			"Cases"[d], "Introduce"[eqE], "Have"[eq1, q + 1 == e], "LinearArithmetic", "Exact"["falseElimination"[neq[eq1]]],
			"Introduce"[d1, eqE], "LinearArithmetic",
			"Have"[notInRest, "memNat"[q + 1, bRest] == "false"],
			"Have"[leE, q + 1 <= e], "LinearArithmetic",
			"Exact"["memNatStrictlyAboveFalse"[q + 1, e, bRest, leE, hRestAbove]],
			"Change"[InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Option[{NonNegativeIntegers}]],
				"decodeS4Loop"[K, k, x + 1, "false", q],
				"optionMap"[Function[{Typed[rest, {NonNegativeIntegers}]}, Prepend[q + 1][rest]], "decodeS4Loop"[K, k, x + 1, "false", q]],
				InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Booleans], "memNat"[q + 1, bRest], "true", Decide[q + 1 == e]]] == "some"[Prepend[e][bRest]]],
			"Rewrite"["decideEqualFalse"[q + 1, e, neq]], "Rewrite"[notInRest],
			"Have"[hAllNext, "allBelowEqual"[(x + 1) + k, "encodeBag4"[Prepend[e][bRest]]]], "Rewrite"["equalitySymmetry"[eqSum]], "Exact"[hAllBd],
			"Have"[hMemNext, ForAll[{Typed[u, NonNegativeIntegers]}, Implies["memNat"[u, Prepend[e][bRest]] == "true", (Subtract[u, 1] + Subtract[u, 1]) + 1 <= (x + 1) + k]]],
			"Introduce"[u, mu], "Rewrite"["equalitySymmetry"[eqSum]], "Exact"[hMemBd[u, mu]],
			"Exact"[ih[K, Prepend[e][bRest], x + 1, "false", q, hXNext, hParNext, "andIntroduction"[eGe2, hRestAbove], hAllNext, hMemNext]],
			(* q + 1 == e: pop e off bag, recurse on bRest! *)
			"Introduce"[eq],
			"Change"[InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Option[{NonNegativeIntegers}]],
				"decodeS4Loop"[K, k, x + 1, "false", q],
				"optionMap"[Function[{Typed[rest, {NonNegativeIntegers}]}, Prepend[q + 1][rest]], "decodeS4Loop"[K, k, x + 1, "false", q]],
				InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Booleans], "memNat"[q + 1, bRest], "true", Decide[q + 1 == e]]] == "some"[Prepend[e][bRest]]],
			"Rewrite"["decideEqualTrue"[q + 1, e, eq]],
			"Have"[hParRest, ForAll[{Typed[y, NonNegativeIntegers]}, Implies[x + 1 <= y, Implies[y + 1 <= (x + 1) + k, "parMem"[y, K] == "memNat"[y, "encodeBag4"[bRest]]]]]],
			"Introduce"[y, hy1, hy2],
			"Rewrite"[hParNext[y, hy1, hy2]],
			"Have"[neqY, Not[y == Subtract[e, 1] + Subtract[e, 1]]],
			"Introduce"[eqY],
			"Have"[eSub, Subtract[e, 1] == q], "Rewrite"["equalitySymmetry"[eq]], "Reflexivity",
			"Have"[yEq, y == q + q], "Rewrite"[eqY], "Rewrite"[eSub],
			"Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"[f],
			"Change"[InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Booleans], "memNat"[y, "encodeBag4"[bRest]], "true", Decide[y == Subtract[e, 1] + Subtract[e, 1]]] == "memNat"[y, "encodeBag4"[bRest]]],
			"Rewrite"["decideEqualFalse"[y, Subtract[e, 1] + Subtract[e, 1], neqY]], "Reflexivity",
			"Have"[hRestAbove2, "strictlyAbove"[q + 1, bRest]], "Rewrite"[eq], "Exact"[hRestAbove],
			"Cases"[hAllBd], "Introduce"[heBd, hRestAllBd],
			"Have"[hAllNext, "allBelowEqual"[(x + 1) + k, "encodeBag4"[bRest]]], "Rewrite"["equalitySymmetry"[eqSum]], "Exact"[hRestAllBd],
			"Have"[hMemNext, ForAll[{Typed[u, NonNegativeIntegers]}, Implies["memNat"[u, bRest] == "true", (Subtract[u, 1] + Subtract[u, 1]) + 1 <= (x + 1) + k]]],
			"Introduce"[u, mu],
			"Have"[muBig, "memNat"[u, Prepend[e][bRest]] == "true"],
			"Change"[InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Booleans], "memNat"[u, bRest], "true", Decide[u == e]] == "true"],
			"Have"[dec, Decidable[u == e]], "Exact"["naturalNumberEqualityDecidable"[u, e]], "Cases"[dec],
			"Introduce"[nu], "Rewrite"["decideEqualFalse"[u, e, nu]], "Exact"[mu],
			"Introduce"[eu], "Rewrite"["decideEqualTrue"[u, e, eu]], "Reflexivity",
			"Rewrite"["equalitySymmetry"[eqSum]], "Exact"[hMemBd[u, muBig]],
			"Change"["optionMap"[Function[{Typed[rest, {NonNegativeIntegers}]}, Prepend[q + 1][rest]], "decodeS4Loop"[K, k, x + 1, "false", q]] == "some"[Prepend[e][bRest]]],
			"Rewrite"[ih[K, bRest, x + 1, "false", q, hXNext, hParRest, hRestAbove2, hAllNext, hMemNext]],
			"Rewrite"[eq], "Reflexivity"
		}
	],
	(* RepS4_decode_band: literal equality decodeS4[c, b] == some[s.bag]! *)
	machineTheorem["repS4DecodeBand",
		ForAll[{Typed[f, NonNegativeIntegers], Typed[s, "System5Configuration"], Typed[j, NonNegativeIntegers], Typed[h, NonNegativeIntegers],
				Typed[c, "System4Configuration"], Typed[b, NonNegativeIntegers]},
			Implies["system4Represents"[f, "fueledSystem5"[s, j, h], c],
				Implies[(b + (j + j)) + 2 <= f + f,
					Implies[ForAll[{Typed[e, NonNegativeIntegers]}, Implies["memNat"[e, s[["bag"]]] == "true", (Subtract[e, 1] + Subtract[e, 1]) + 1 <= b]],
						"decodeS4"[c, b] == "some"[s[["bag"]]]]]]],
		{
			"Introduce"[f, s, j, h, c, b, hRep, hBand, hBagLt],
			"Cases"[hRep], "Introduce"[S0, hRep1], "Cases"[hRep1], "Introduce"[Krest, hRep2],
			"Cases"[hRep2], "Introduce"[hKInc, hRep3],
			"Cases"[hRep3], "Introduce"[eqC, hRep4],
			"Cases"[hRep4], "Introduce"[hBoundF, hRep5],
			"Cases"[hRep5], "Introduce"[hPar, hRep6],
			"Cases"[hRep6], "Introduce"[hBagInc, hRep7],
			"Rewrite"[eqC],
			"Have"[leG, (j + j) + 1 <= f], "LinearArithmetic",
			"Cases"["lessEqualExists"[(j + j) + 1, f, leG]], "Introduce"[g1, eqF],
			"Have"[subG, Subtract[f, j + j] == g1 + 1],
			"Rewrite"[eqF], "Have"[t1, g1 + ((j + j) + 1) == (g1 + 1) + (j + j)], "LinearArithmetic",
			"Rewrite"[t1], "Exact"["additionSubtractionCancellation"[g1 + 1, j + j]],
			"Change"["decodeS4Loop"["leadSets4"[Join["sets4"[Prepend[S0][Krest]], Join["starredEmptyPairs"[Subtract[f, j + j]], "encBlocks"[s[["rules"]], f, j + j]]]], b, 0, "true", 0] == "some"[s[["bag"]]]],
			"Rewrite"[subG],
			"Change"["decodeS4Loop"["leadSets4"[Join["sets4"[Prepend[S0][Krest]], Prepend["star4"][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[g1], "encBlocks"[s[["rules"]], f, j + j]]]]]], b, 0, "true", 0] == "some"[s[["bag"]]]],
			"Rewrite"["leadSets4SetsStar"[Prepend[S0][Krest], Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[g1], "encBlocks"[s[["rules"]], f, j + j]]]]],
			"Have"[hParB, ForAll[{Typed[y, NonNegativeIntegers]}, Implies[0 <= y, Implies[y + 1 <= 0 + b, "parMem"[y, Prepend[S0][Krest]] == "memNat"[y, "encodeBag4"[s[["bag"]]]]]]]],
			"Introduce"[y, hy0, hyb],
			"Have"[hyF, ((y + (j + j)) + 2) + 1 <= f + f], "LinearArithmetic",
			"Exact"[hPar[y, hyF]],
			"Have"[hAllBd, "allBelowEqual"[0 + b, "encodeBag4"[s[["bag"]]]]],
			"Have"[genBd, ForAll[{Typed[l, {NonNegativeIntegers}]},
				Implies[ForAll[{Typed[e, NonNegativeIntegers]}, Implies["memNat"[e, l] == "true", (Subtract[e, 1] + Subtract[e, 1]) + 1 <= b]],
					"allBelowEqual"[0 + b, "encodeBag4"[l]]]]],
			"Introduce"[l], "Induction"[l], "Introduce"[hl], "Exact"["trueIntroduction"],
			"Introduce"[e, rest, ih, hl],
			"Have"[me, "memNat"[e, Prepend[e][rest]] == "true"],
			"Change"[InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Booleans], "memNat"[e, rest], "true", Decide[e == e]] == "true"],
			"Rewrite"["decideEqualTrue"[e, e, "equalityReflexivity"[e]]], "Reflexivity",
			"Have"[heLt, (Subtract[e, 1] + Subtract[e, 1]) + 1 <= b], "Exact"[hl[e, me]],
			"Have"[heLe, Subtract[e, 1] + Subtract[e, 1] <= 0 + b], "LinearArithmetic",
			"Have"[hRestL, ForAll[{Typed[u, NonNegativeIntegers]}, Implies["memNat"[u, rest] == "true", (Subtract[u, 1] + Subtract[u, 1]) + 1 <= b]]],
			"Introduce"[u, mu],
			"Have"[muBig, "memNat"[u, Prepend[e][rest]] == "true"],
			"Change"[InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Booleans], "memNat"[u, rest], "true", Decide[u == e]] == "true"],
			"Have"[dec, Decidable[u == e]], "Exact"["naturalNumberEqualityDecidable"[u, e]], "Cases"[dec],
			"Introduce"[nu], "Rewrite"["decideEqualFalse"[u, e, nu]], "Exact"[mu],
			"Introduce"[eu], "Rewrite"["decideEqualTrue"[u, e, eu]], "Reflexivity",
			"Exact"[hl[u, muBig]],
			"Exact"["andIntroduction"[heLe, ih[hRestL]]],
			"Exact"[genBd[s[["bag"]], hBagLt]],
			"Have"[hMem0, ForAll[{Typed[e, NonNegativeIntegers]}, Implies["memNat"[e, s[["bag"]]] == "true", (Subtract[e, 1] + Subtract[e, 1]) + 1 <= 0 + b]]],
			"Introduce"[e, me], "Rewrite"["additionZeroLeft"[b]], "Exact"[hBagLt[e, me]],
			"Exact"["decodeS4LoopBag"[b, Prepend[S0][Krest], s[["bag"]], 0, "true", 0, "equalityReflexivity"[0], hParB, hBagInc, hAllBd, hMem0]]
		}
	],
	(* Turing's hook #2: 1-step turn from system4Represents gives state4B at left = {}, right = sets4[K] ++ star4 :: R, with identical decodeS4 *)
	machineTheorem["repS4TurnStep",
		ForAll[{Typed[f, NonNegativeIntegers], Typed[s, "System5Configuration"], Typed[j, NonNegativeIntegers], Typed[h, NonNegativeIntegers], Typed[c, "System4Configuration"]},
			Implies["system4Represents"[f, "fueledSystem5"[s, j, h], c],
				Exists[{Typed[S0, {NonNegativeIntegers}], Typed[Krest, {{NonNegativeIntegers}}], Typed[R, {"System4Element"}]},
					And["system4Step"[c] == "some"["system4Configuration"[Typed[{}, {"System4Element"}], Join["sets4"[Prepend[S0][Krest]], Prepend["star4"][R]], "state4B"]],
						ForAll[{Typed[b, NonNegativeIntegers]},
							"decodeS4"["system4Configuration"[Typed[{}, {"System4Element"}], Join["sets4"[Prepend[S0][Krest]], Prepend["star4"][R]], "state4B"], b] == "decodeS4"[c, b]]]]]],
		{
			"Introduce"[f, s, j, h, c, hRep],
			"Cases"[hRep], "Introduce"[S0, hRep1], "Cases"[hRep1], "Introduce"[Krest, hRep2],
			"Cases"[hRep2], "Introduce"[hKInc, hRep3],
			"Cases"[hRep3], "Introduce"[eqC, hRep4],
			"Cases"[hRep4], "Introduce"[hBoundF, hRep5],
			"Rewrite"[eqC],
			"Have"[leG, (j + j) + 1 <= f], "LinearArithmetic",
			"Cases"["lessEqualExists"[(j + j) + 1, f, leG]], "Introduce"[g1, eqF],
			"Have"[subG, Subtract[f, j + j] == g1 + 1],
			"Rewrite"[eqF], "Have"[t1, g1 + ((j + j) + 1) == (g1 + 1) + (j + j)], "LinearArithmetic",
			"Rewrite"[t1], "Exact"["additionSubtractionCancellation"[g1 + 1, j + j]],
			"Rewrite"[subG],
			"Exact"["existsIntroduction"[S0, "existsIntroduction"[Krest,
				"existsIntroduction"[Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[g1], "encBlocks"[s[["rules"]], f, j + j]]],
					"andIntroduction"[
						"equalityReflexivity"["some"["system4Configuration"[Typed[{}, {"System4Element"}],
							Join["sets4"[Prepend[S0][Krest]], Prepend["star4"][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[g1], "encBlocks"[s[["rules"]], f, j + j]]]]], "state4B"]]],
						Function[{Typed[b, NonNegativeIntegers]}, "equalityReflexivity"["decodeS4"["system4Configuration"[Typed[{}, {"System4Element"}],
							Join["sets4"[Prepend[S0][Krest]], Prepend["star4"][Prepend["set4"[Typed[{}, {NonNegativeIntegers}]]][Join["starredEmptyPairs"[g1], "encBlocks"[s[["rules"]], f, j + j]]]]], "state4B"], b]]]]]]]]
		}
	],
	machineTheorem["memNatAllBelowEqual",
		ForAll[{Typed[hi, NonNegativeIntegers], Typed[x, NonNegativeIntegers], Typed[xs, {NonNegativeIntegers}]},
			Implies["allBelowEqual"[hi, xs], Implies["memNat"[x, xs] == "true", x <= hi]]],
		{
			"Introduce"[hi, x, xs], "Induction"[xs],
			"Introduce"[hBd, hMem],
			"Exact"["falseElimination"[Construct["equalitySubstitution", Booleans,
				Function[{Typed[b, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, TypeUniverse[0]], True, False, b]],
				"false", "true", hMem, "trueIntroduction"]]],
			"Introduce"[a, rest, ih, hBd, hMem],
			"Cases"[hBd], "Introduce"[ha, hrest],
			"Have"[dec, Decidable[x == a]], "Exact"["naturalNumberEqualityDecidable"[x, a]], "Cases"[dec],
			"Introduce"[neq],
			"Have"[mStepEq, "memNat"[x, Prepend[a][rest]] == "memNat"[x, rest]],
			"Change"[InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Booleans], "memNat"[x, rest], "true", Decide[x == a]] == "memNat"[x, rest]],
			"Rewrite"["decideEqualFalse"[x, a, neq]], "Reflexivity",
			"Exact"[ih[hrest, "equalityTransitivity"["equalitySymmetry"[mStepEq], hMem]]],
			"Introduce"[eq], "Rewrite"[eq], "Exact"[ha]
		}
	],
	machineTheorem["boolEqTrueOrFalse",
		ForAll[{Typed[b, Booleans]}, Or[b == "false", b == "true"]],
		{
			"Introduce"[b], "Cases"[b],
			"Exact"["orIntroductionLeft"["equalityReflexivity"["false"]]],
			"Exact"["orIntroductionRight"["equalityReflexivity"["true"]]]
		}
	],
	(* Exit in state C when rules == {} and 1 is in s.bag (exposes 1 <= k per Turing's hook #1!) *)
	machineTheorem["repS4Exit",
		ForAll[{Typed[f, NonNegativeIntegers], Typed[s, "System5Configuration"], Typed[j, NonNegativeIntegers], Typed[h, NonNegativeIntegers], Typed[c, "System4Configuration"]},
			Implies["system4Represents"[f, "fueledSystem5"[s, j, h], c],
				Implies[s[["rules"]] == Typed[{}, {{NonNegativeIntegers}}],
					Implies["memNat"[1, s[["bag"]]] == "true",
						Exists[{Typed[k, NonNegativeIntegers]}, And[1 <= k,
							Exists[{Typed[c2, "System4Configuration"]}, And[
								"steps"["system4Step", k, c] == "some"[c2],
								And[c2[["state"]] == "state4C",
									And[c2[["right"]] == Typed[{}, {"System4Element"}],
										"system4Step"[c2] == Typed["none", Option["System4Configuration"]]]]]]]]]]]],
		{
			"Introduce"[f, s, j, h, c, hRep, hRulesEmpty, hHas1],
			"Cases"[hRep], "Introduce"[S0, hRep1], "Cases"[hRep1], "Introduce"[Krest, hRep2],
			"Cases"[hRep2], "Introduce"[hKInc, hRep3],
			"Cases"[hRep3], "Introduce"[eqC, hRep4],
			"Cases"[hRep4], "Introduce"[hBoundF, hRep5],
			"Cases"[hRep5], "Introduce"[hPar, hRep6],
			"Cases"[hRep6], "Introduce"[hBagInc, hRep7],
			"Cases"[hRep7], "Introduce"[hBagBd, hRep8],
			"Have"[oneLeSub, 1 <= Subtract[f, j + 1]], "Exact"["memNatAllBelowEqual"[Subtract[f, j + 1], 1, s[["bag"]], hBagBd, hHas1]],
			"Have"[leJ1, j + 1 <= f], "LinearArithmetic",
			"Cases"["lessEqualExists"[j + 1, f, leJ1]], "Introduce"[df, eqDf],
			"Have"[oneLeDf, 1 <= df],
			"Rewrite"["equalitySymmetry"["additionSubtractionCancellation"[df, j + 1]]],
			"Rewrite"["equalitySymmetry"[eqDf]], "Exact"[oneLeSub],
			"Have"[b0, ((0 + (j + j)) + 2) + 1 <= f + f], "LinearArithmetic",
			"Have"[par0, "parMem"[0, Prepend[S0][Krest]] == "true"],
			"Rewrite"[hPar[0, b0]],
			"Change"["memNat"[0 + 0, "encodeBag4"[s[["bag"]]]] == "true"],
			"Rewrite"["memNatEncodeBag4Even"[0, s[["bag"]], hBagInc]],
			"Exact"[hHas1],
			"Have"[stepsRun, "steps"["system4Step", (1 + Length[Prepend[S0][Krest]]) + (Subtract[f, j + j] + Subtract[f, j + j]), c] ==
				"some"["system4Configuration"["starredZeroPairsRev"[Subtract[f, j + j], "revAppend"["sets4"[Map["decr4", Prepend[S0][Krest]]], Typed[{}, {"System4Element"}]]],
					Typed[{}, {"System4Element"}], "state4C"]]],
			"Rewrite"[eqC], "Rewrite"[hRulesEmpty],
			"Change"["steps"["system4Step", (1 + Length[Prepend[S0][Krest]]) + (Subtract[f, j + j] + Subtract[f, j + j]),
				"system4Configuration"[Typed[{}, {"System4Element"}],
					Join["sets4"[Prepend[S0][Krest]], Join["starredEmptyPairs"[Subtract[f, j + j]], Typed[{}, {"System4Element"}]]], "state4A"]] ==
				"some"["system4Configuration"["starredZeroPairsRev"[Subtract[f, j + j], "revAppend"["sets4"[Map["decr4", Prepend[S0][Krest]]], Typed[{}, {"System4Element"}]]],
					Typed[{}, {"System4Element"}], "state4C"]]],
			"Rewrite"["stepsAdd"["System4Configuration", "system4Step", 1 + Length[Prepend[S0][Krest]], Subtract[f, j + j] + Subtract[f, j + j],
				"system4Configuration"[Typed[{}, {"System4Element"}],
					Join["sets4"[Prepend[S0][Krest]], Join["starredEmptyPairs"[Subtract[f, j + j]], Typed[{}, {"System4Element"}]]], "state4A"]]],
			"Rewrite"["stepsAdd"["System4Configuration", "system4Step", 1, Length[Prepend[S0][Krest]],
				"system4Configuration"[Typed[{}, {"System4Element"}],
					Join["sets4"[Prepend[S0][Krest]], Join["starredEmptyPairs"[Subtract[f, j + j]], Typed[{}, {"System4Element"}]]], "state4A"]]],
			"Change"["optionBind"["steps"["system4Step", Length[Prepend[S0][Krest]],
				"system4Configuration"[Typed[{}, {"System4Element"}],
					Join["sets4"[Prepend[S0][Krest]], Join["starredEmptyPairs"[Subtract[f, j + j]], Typed[{}, {"System4Element"}]]], "state4B"]],
				Function[{Typed[y, "System4Configuration"]}, "steps"["system4Step", Subtract[f, j + j] + Subtract[f, j + j], y]]] ==
				"some"["system4Configuration"["starredZeroPairsRev"[Subtract[f, j + j], "revAppend"["sets4"[Map["decr4", Prepend[S0][Krest]]], Typed[{}, {"System4Element"}]]],
					Typed[{}, {"System4Element"}], "state4C"]]],
			"Rewrite"["system4Sweep"[Prepend[S0][Krest], Typed[{}, {"System4Element"}],
				Join["starredEmptyPairs"[Subtract[f, j + j]], Typed[{}, {"System4Element"}]], "state4B", "trueIntroduction", hKInc]],
			"Rewrite"[par0],
			"Exact"["system4CPhase"[Subtract[f, j + j], "revAppend"["sets4"[Map["decr4", Prepend[S0][Krest]]], Typed[{}, {"System4Element"}]], Typed[{}, {"System4Element"}]]],
			"Have"[posK, 1 <= (1 + Length[Prepend[S0][Krest]]) + (Subtract[f, j + j] + Subtract[f, j + j])], "LinearArithmetic",
			"Exact"["existsIntroduction"[(1 + Length[Prepend[S0][Krest]]) + (Subtract[f, j + j] + Subtract[f, j + j]),
				"andIntroduction"[posK,
					"existsIntroduction"[
						"system4Configuration"["starredZeroPairsRev"[Subtract[f, j + j], "revAppend"["sets4"[Map["decr4", Prepend[S0][Krest]]], Typed[{}, {"System4Element"}]]],
							Typed[{}, {"System4Element"}], "state4C"],
						"andIntroduction"[stepsRun, "andIntroduction"["equalityReflexivity"["state4C"],
							"andIntroduction"["equalityReflexivity"[Typed[{}, {"System4Element"}]],
								"equalityReflexivity"[Typed["none", Option["System4Configuration"]]]]]]]]]]
		}
	],
	(* Terminal phase (Turing's hook #1: budgeted M decrements then exit in state C with 1 <= k!) *)
	machineTheorem["repS4Terminal",
		ForAll[{Typed[M, NonNegativeIntegers], Typed[f, NonNegativeIntegers], Typed[s, "System5Configuration"], Typed[j, NonNegativeIntegers], Typed[h, NonNegativeIntegers], Typed[c, "System4Configuration"]},
			Implies["system4Represents"[f, "fueledSystem5"[s, j, h + M], c],
				Implies[s[["rules"]] == Typed[{}, {{NonNegativeIntegers}}],
					Implies[Exists[{Typed[e, NonNegativeIntegers]}, And["memNat"[e, s[["bag"]]] == "true", e <= M + 1]],
						Exists[{Typed[k, NonNegativeIntegers]}, And[1 <= k,
							Exists[{Typed[c2, "System4Configuration"]}, And[
								"steps"["system4Step", k, c] == "some"[c2],
								And[c2[["state"]] == "state4C",
									And[c2[["right"]] == Typed[{}, {"System4Element"}],
										"system4Step"[c2] == Typed["none", Option["System4Configuration"]]]]]]]]]]]],
		{
			"Introduce"[M], "Induction"[M],
			(* M = 0: e <= 1 and strictlyAbove[0, bag] => e == 1 => memNat[1, bag] == true *)
			"Introduce"[f, s, j, h, c, hRep, hRulesEmpty, hEx],
			"Cases"[hEx], "Introduce"[e, hBoth], "Cases"[hBoth], "Introduce"[hMemE, hLe1],
			"Cases"[hRep], "Introduce"[S0, hr1], "Cases"[hr1], "Introduce"[Krest, hr2],
			"Cases"[hr2], "Introduce"[hKInc, hr3], "Cases"[hr3], "Introduce"[eqC, hr4],
			"Cases"[hr4], "Introduce"[hBoundF, hr5], "Cases"[hr5], "Introduce"[hPar, hr6],
			"Cases"[hr6], "Introduce"[hBagInc, hr7],
			"Have"[hEPos, 1 <= e],
			"Cases"[e], "Introduce"[hMemE, hLe1],
			"Have"[m0, "memNat"[0, s[["bag"]]] == "false"],
			"Exact"["memNatStrictlyAboveFalse"[0, 0, s[["bag"]], "lessEqualReflexivity", hBagInc]],
			"Have"[ft, "false" == "true"], "Exact"["equalityTransitivity"["equalitySymmetry"[m0], hMemE]],
			"Exact"["falseElimination"[Construct["equalitySubstitution", Booleans,
				Function[{Typed[b, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, TypeUniverse[0]], True, False, b]],
				"false", "true", ft, "trueIntroduction"]]],
			"Introduce"[e1, hMemE, hLe1], "LinearArithmetic",
			"Have"[eqE1, e == 1], "LinearArithmetic",
			"Have"[hHas1, "memNat"[1, s[["bag"]]] == "true"], "Rewrite"["equalitySymmetry"[eqE1]], "Exact"[hMemE],
			"Exact"["repS4Exit"[f, s, j, h + 0, c, "existsIntroduction"[S0, "existsIntroduction"[Krest,
				"andIntroduction"[hKInc, "andIntroduction"[eqC, "andIntroduction"[hBoundF, "andIntroduction"[hPar, "andIntroduction"[hBagInc, hr7]]]]]]],
				hRulesEmpty, hHas1]],
			(* M = m + 1 *)
			"Introduce"[m, ih, f, s, j, h, c, hRep, hRulesEmpty, hEx],
			"Cases"["boolEqTrueOrFalse"["memNat"[1, s[["bag"]]]]],
			(* memNat[1, s.bag] == false: do one D-step and recurse on m! *)
			"Introduce"[eq1],
			"Have"[hRepStep, "system4Represents"[f, "fueledSystem5"[s, j, (h + m) + 1], c]],
			"Have"[eqHM, h + (m + 1) == (h + m) + 1], "LinearArithmetic",
			"Rewrite"["equalitySymmetry"[eqHM]], "Exact"[hRep],
			"Cases"["repS4DStep"[f, s, j, h + m, c, hRepStep, eq1]],
			"Introduce"[k1, d1], "Cases"[d1], "Introduce"[pos1, d2], "Cases"[d2], "Introduce"[c1, d3], "Cases"[d3], "Introduce"[run1, rep1],
			"Cases"[hEx], "Introduce"[e, hBoth], "Cases"[hBoth], "Introduce"[hMemE, hLe],
			"Have"[hBag0, "strictlyAbove"[0, s[["bag"]]]],
			"Cases"[hRep], "Introduce"[S0, hr1], "Cases"[hr1], "Introduce"[Krest, hr2],
			"Cases"[hr2], "Introduce"[hKInc, hr3], "Cases"[hr3], "Introduce"[eqC, hr4],
			"Cases"[hr4], "Introduce"[hBoundF, hr5], "Cases"[hr5], "Introduce"[hPar, hr6],
			"Cases"[hr6], "Introduce"[hBagInc, hr7], "Exact"[hBagInc],
			"Have"[hEGe2, 2 <= e],
			"Cases"[e], "Introduce"[hMemE, hLe],
			"Have"[m0, "memNat"[0, s[["bag"]]] == "false"], "Exact"["memNatStrictlyAboveFalse"[0, 0, s[["bag"]], "lessEqualReflexivity", hBag0]],
			"Have"[ft, "false" == "true"], "Exact"["equalityTransitivity"["equalitySymmetry"[m0], hMemE]],
			"Exact"["falseElimination"[Construct["equalitySubstitution", Booleans,
				Function[{Typed[b, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, TypeUniverse[0]], True, False, b]],
				"false", "true", ft, "trueIntroduction"]]],
			"Introduce"[e1, hMemE, hLe], "Cases"[e1], "Introduce"[hMemE, hLe],
			"Have"[ft, "false" == "true"], "Exact"["equalityTransitivity"["equalitySymmetry"[eq1], hMemE]],
			"Exact"["falseElimination"[Construct["equalitySubstitution", Booleans,
				Function[{Typed[b, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, TypeUniverse[0]], True, False, b]],
				"false", "true", ft, "trueIntroduction"]]],
			"Introduce"[e2, hMemE, hLe], "LinearArithmetic",
			"Have"[eGe1, 1 <= e], "LinearArithmetic",
			"Cases"["lessEqualExists"[1, e, eGe1]], "Introduce"[ep, eqEp],
			"Have"[hMemEp, "memNat"[ep, "shiftDown"[1, s[["bag"]]]] == "true"],
			"Rewrite"["memNatShiftDown1"[ep, s[["bag"]], hBag0]], "Rewrite"["equalitySymmetry"[eqEp]], "Exact"[hMemE],
			"Have"[hEpLe, ep <= m + 1], "LinearArithmetic",
			"Have"[hRules1, "shiftUpRules"[1, s[["rules"]]] == Typed[{}, {{NonNegativeIntegers}}]], "Rewrite"[hRulesEmpty], "Reflexivity",
			"Cases"[ih[f, "system5Configuration"["shiftDown"[1, s[["bag"]]], "shiftUpRules"[1, s[["rules"]]]], j + 1, h, c1, rep1, hRules1,
				"existsIntroduction"[ep, "andIntroduction"[hMemEp, hEpLe]]]],
			"Introduce"[k2, r2], "Cases"[r2], "Introduce"[pos2, r3], "Cases"[r3], "Introduce"[c2, r4], "Cases"[r4], "Introduce"[run2, exit2],
			"Have"[runAll, "steps"["system4Step", k1 + k2, c] == "some"[c2]],
			"Rewrite"["stepsAdd"["System4Configuration", "system4Step", k1, k2, c]], "Rewrite"[run1], "Exact"[run2],
			"Have"[posAll, 1 <= k1 + k2], "LinearArithmetic",
			"Exact"["existsIntroduction"[k1 + k2, "andIntroduction"[posAll, "existsIntroduction"[c2, "andIntroduction"[runAll, exit2]]]]],
			(* memNat[1, s.bag] == true: exit immediately! *)
			"Introduce"[eq1],
			"Exact"["repS4Exit"[f, s, j, h + (m + 1), c, hRep, hRulesEmpty, eq1]]
		}
	],
	(* Helper: xorBool[xorBool[a, xorBool[true, b]], true] == xorBool[a, b] *)
	machineTheorem["xorBoolCancelTrue",
		ForAll[{Typed[a, Booleans], Typed[b, Booleans]},
			"xorBool"["xorBool"[a, "xorBool"["true", b]], "true"] == "xorBool"[a, b]],
		{
			"Introduce"[a, b], "Cases"[a], "Cases"[b], "Reflexivity", "Reflexivity",
			"Cases"[b], "Reflexivity", "Reflexivity"
		}
	],
	(* Helper: memNat[z, xorMerge[{1}, s]] == memNat[z, s] whenever z != 1 and strictlyIncreasing[s] *)
	machineTheorem["memNatXorOneOther",
		ForAll[{Typed[z, NonNegativeIntegers], Typed[s, {NonNegativeIntegers}]},
			Implies[Not[z == 1], Implies["strictlyIncreasing"[s], "memNat"[z, "xorMerge"[{1}, s]] == "memNat"[z, s]]]],
		{
			"Introduce"[z, s, neq, hs],
			"Rewrite"["memNatXorMerge"[z, {1}, s, "trueIntroduction", hs]],
			"Change"["xorBool"[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Booleans], "false", "true", Decide[z == 1]], "memNat"[z, s]] == "memNat"[z, s]],
			"Rewrite"["decideEqualFalse"[z, 1, neq]], "Reflexivity"
		}
	],
	machineTheorem["shiftUp1StrictlyAbove0",
		ForAll[{Typed[xs, {NonNegativeIntegers}]},
			Implies["strictlyIncreasing"[xs], "strictlyAbove"[0, "shiftUp"[1, xs]]]],
		{
			"Introduce"[xs], "Cases"[xs],
			"Introduce"[h], "Exact"["trueIntroduction"],
			"Introduce"[x, rest, h],
			"Have"[xPos, 0 + 1 <= x + 1], "LinearArithmetic",
			"Exact"["andIntroduction"[xPos, "shiftUpStrictlyAbove"[rest, 1, x, h]]]
		}
	],
	(* Per-step lemma, P-step case (1 in bag, rule r popped): two system4PopPhase runs! *)
	machineTheorem["repS4PStep",
		ForAll[
			{
				Typed[f, NonNegativeIntegers], Typed[restBag, {NonNegativeIntegers}],
				Typed[r, {NonNegativeIntegers}], Typed[restRules, {{NonNegativeIntegers}}],
				Typed[j, NonNegativeIntegers], Typed[h, NonNegativeIntegers], Typed[c, "System4Configuration"]
			},
			Implies["system4Represents"[f, "fueledSystem5"["system5Configuration"[Prepend[1][restBag], Prepend[r][restRules]], j, h + 1], c],
				Exists[{Typed[k, NonNegativeIntegers]}, And[1 <= k,
					Exists[{Typed[c2, "System4Configuration"]}, And[
						"steps"["system4Step", k, c] == "some"[c2],
						"system4Represents"[f,
							"fueledSystem5"["system5Configuration"["xorMerge"["shiftDown"[1, restBag], "shiftUp"[1, r]], "shiftUpRules"[1, restRules]], j + 1, h],
							c2]]]]]]
		],
		{
			"Introduce"[f, restBag, r, restRules, j, h, c, hRep],
			"Cases"[hRep], "Introduce"[S0, hRep1], "Cases"[hRep1], "Introduce"[Krest, hRep2],
			"Cases"[hRep2], "Introduce"[hKInc, hRep3],
			"Cases"[hRep3], "Introduce"[eqC, hRep4],
			"Cases"[hRep4], "Introduce"[hBoundF, hRep5],
			"Cases"[hRep5], "Introduce"[hPar, hRep6],
			"Cases"[hRep6], "Introduce"[hBagInc, hRep7],
			"Cases"[hRep7], "Introduce"[hBagBd, hRep8],
			"Cases"[hRep8], "Introduce"[hRulesInc, hRulesBd],
			"Cases"[hBagInc], "Introduce"[h1Pos, hRestBag1],
			"Cases"[hBagBd], "Introduce"[h1Bd, hRestBagBd],
			"Cases"[hRulesInc], "Introduce"[hrInc, hRestRulesInc],
			"Cases"[hRulesBd], "Introduce"[hrBd, hRestRulesBd],
			(* Zero-Subtract parameterization: f == g0 + ((j + j) + 3) *)
			"Have"[leF3, (j + j) + 3 <= f], "LinearArithmetic",
			"Cases"["lessEqualExists"[(j + j) + 3, f, leF3]], "Introduce"[g0, eqF],
			"Have"[j2LeF, j + j <= f], "LinearArithmetic",
			"Have"[fGe2, 2 <= f], "LinearArithmetic",
			"Have"[subOld, Subtract[f, j + j] == (g0 + 2) + 1],
			"Rewrite"[eqF], "Have"[t1, g0 + ((j + j) + 3) == ((g0 + 2) + 1) + (j + j)], "LinearArithmetic",
			"Rewrite"[t1], "Exact"["additionSubtractionCancellation"[(g0 + 2) + 1, j + j]],
			"Have"[subNew, Subtract[f, (j + 1) + (j + 1)] == g0 + 1],
			"Rewrite"[eqF], "Have"[t2, g0 + ((j + j) + 3) == (g0 + 1) + ((j + 1) + (j + 1))], "LinearArithmetic",
			"Rewrite"[t2], "Exact"["additionSubtractionCancellation"[g0 + 1, (j + 1) + (j + 1)]],
			"Have"[f2Split, f + f == ((g0 + ((j + j) + (j + j))) + 1) + ((g0 + 2) + 3)], "LinearArithmetic",
			"Have"[f2m2Split, Subtract[f + f, 2] == (g0 + 1) + ((g0 + ((j + j) + (j + j))) + 3)],
			"Rewrite"[eqF],
			"Have"[t3, (g0 + ((j + j) + 3)) + (g0 + ((j + j) + 3)) == ((g0 + 1) + ((g0 + ((j + j) + (j + j))) + 3)) + 2], "LinearArithmetic",
			"Rewrite"[t3], "Exact"["additionSubtractionCancellation"[(g0 + 1) + ((g0 + ((j + j) + (j + j))) + 3), 2]],
			(* Phase 1 preconditions *)
			"Have"[b0, ((0 + (j + j)) + 2) + 1 <= f + f], "LinearArithmetic",
			"Have"[par0, "parMem"[0, Prepend[S0][Krest]] == "true"],
			"Rewrite"[hPar[0, b0]], "Reflexivity",
			"Have"[hRs1Inc, "strictlyIncreasing"["encRuleSet"[r, f, j + j]]],
			"Exact"["encRuleSetStrictlyIncreasing"[r, f, j + j, j2LeF, hrInc]],
			"Have"[hX1Inc, "strictlyIncreasing"["xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]],
			"Exact"["xorMergeStrictlyIncreasing"[{1}, "encRuleSet"[r, f, j + j], "trueIntroduction", hRs1Inc]],
			"Have"[hX1Zero, "memNat"[0, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]] == "true"],
			"Have"[n01, Not[0 == 1]], "Introduce"[e], "Exact"["successorNotZero"[0, "equalitySymmetry"[e]]],
			"Rewrite"["memNatXorOneOther"[0, "encRuleSet"[r, f, j + j], n01, hRs1Inc]],
			"Have"[low0, (0 + (j + j)) + 1 <= f + 3], "LinearArithmetic",
			"Exact"["memNatEncRuleSetLow"[r, f, j + j, 0, j2LeF, fGe2, hrInc, low0]],
			"Have"[hX1One, "memNat"[1, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]] == "false"],
			"Rewrite"["memNatXorMerge"[1, {1}, "encRuleSet"[r, f, j + j], "trueIntroduction", hRs1Inc]],
			"Have"[low1, (1 + (j + j)) + 1 <= f + 3], "LinearArithmetic",
			"Rewrite"["memNatEncRuleSetLow"[r, f, j + j, 1, j2LeF, fGe2, hrInc, low1]], "Reflexivity",
			"Have"[hX1Loop, ForAll[{Typed[q, NonNegativeIntegers]}, Implies[q + 1 <= (g0 + 2) + 1, "memNat"[q + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]] == "true"]]],
			"Introduce"[q, hq],
			"Have"[nq1, Not[q + 2 == 1]], "Introduce"[e], "Have"[f0, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"[f0],
			"Rewrite"["memNatXorOneOther"[q + 2, "encRuleSet"[r, f, j + j], nq1, hRs1Inc]],
			"Have"[lowQ, ((q + 2) + (j + j)) + 1 <= f + 3], "LinearArithmetic",
			"Exact"["memNatEncRuleSetLow"[r, f, j + j, q + 2, j2LeF, fGe2, hrInc, lowQ]],
			(* Run Phase 1! *)
			"Cases"["system4PopPhase"[S0, Krest, g0 + 2, "encRuleSet"[r, f, j + j], (g0 + ((j + j) + (j + j))) + 1,
				Join[Prepend["star4"][Prepend["set4"["allInts"[((f + f) + f) + 1]]]["starredEmptyPairs"[Subtract[f + f, 2]]]], "encBlocks"[restRules, f, j + j]],
				hKInc, hRs1Inc, par0, hX1Zero, hX1One, hX1Loop]],
			"Introduce"[k1, p1Both], "Cases"[p1Both], "Introduce"[pos1, run1],
			(* K1 = Map[decr4, K] ++ Map[decr4, loopK[g0+2, decrN4[g0+4, X1]]] ++ {{}} *)
			"Have"[hK1Inc, "allSetsStrictlyIncreasing"[Prepend["decr4"[S0]][Join[Join[Map["decr4", Krest],
				Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]]], {Typed[{}, {NonNegativeIntegers}]}]]]],
			"Exact"["allSetsStrictlyIncreasingJoin"[
				Join[Map["decr4", Prepend[S0][Krest]],
					Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]]],
				{Typed[{}, {NonNegativeIntegers}]},
				"allSetsStrictlyIncreasingJoin"[Map["decr4", Prepend[S0][Krest]],
					Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]],
					"allSetsStrictlyIncreasingMapDecr4"[Prepend[S0][Krest], hKInc],
					"allSetsStrictlyIncreasingMapDecr4"["loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]],
						"allSetsStrictlyIncreasingLoopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]],
							"decrN4StrictlyIncreasing"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]], hX1Inc]]]],
				"andIntroduction"["trueIntroduction", "trueIntroduction"]]],
			(* parMem[0, K1] == true! *)
			"Have"[parK1Zero, "parMem"[0, Prepend["decr4"[S0]][Join[Join[Map["decr4", Krest],
				Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]]], {Typed[{}, {NonNegativeIntegers}]}]]] == "true"],
			"Change"["parMem"[0, Join[Join[Map["decr4", Prepend[S0][Krest]],
				Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]]], {Typed[{}, {NonNegativeIntegers}]}]] == "true"],
			"Rewrite"["parMemJoin"[0, Join[Map["decr4", Prepend[S0][Krest]],
				Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]]], {Typed[{}, {NonNegativeIntegers}]}]],
			"Change"["xorBool"["parMem"[0, Join[Map["decr4", Prepend[S0][Krest]],
				Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]]]], "false"] == "true"],
			"Rewrite"["xorBoolFalseRight"["parMem"[0, Join[Map["decr4", Prepend[S0][Krest]],
				Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]]]]]],
			"Rewrite"["parMemJoin"[0, Map["decr4", Prepend[S0][Krest]],
				Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]]]],
			"Rewrite"["parMemMapDecr4"[0, Prepend[S0][Krest], hKInc]],
			"Have"[b1, ((1 + (j + j)) + 2) + 1 <= f + f], "LinearArithmetic",
			"Change"["xorBool"["parMem"[1, Prepend[S0][Krest]], "parMem"[0, Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]]]] == "true"],
			"Rewrite"[hPar[1, b1]],
			"Rewrite"["memNatEncodeBag4Odd"[0, Prepend[1][restBag], "andIntroduction"[h1Pos, hRestBag1]]],
			"Rewrite"["parMemLoopKMapDecr4"[0, g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]],
				"decrN4StrictlyIncreasing"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]], hX1Inc]]],
			"Rewrite"["memNatDecr4"[0, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]],
				"decrN4StrictlyIncreasing"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]], hX1Inc]]],
			"Rewrite"["memNatDecrN4"[(g0 + 2) + 2, 1, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]], hX1Inc]],
			"Have"[n51, Not[1 + ((g0 + 2) + 2) == 1]], "Introduce"[e], "Have"[f0, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"[f0],
			"Rewrite"["memNatXorOneOther"[1 + ((g0 + 2) + 2), "encRuleSet"[r, f, j + j], n51, hRs1Inc]],
			"Have"[low5, ((1 + ((g0 + 2) + 2)) + (j + j)) + 1 <= f + 3], "LinearArithmetic",
			"Rewrite"["memNatEncRuleSetLow"[r, f, j + j, 1 + ((g0 + 2) + 2), j2LeF, fGe2, hrInc, low5]], "Reflexivity",
			(* Phase 2 preconditions on U = allInts[3f + 1] *)
			"Have"[hUInc, "strictlyIncreasing"["allInts"[((f + f) + f) + 1]]],
			"Exact"["allIntsStrictlyIncreasing"[((f + f) + f) + 1]],
			"Have"[hX2Inc, "strictlyIncreasing"["xorMerge"[{1}, "allInts"[((f + f) + f) + 1]]]],
			"Exact"["xorMergeStrictlyIncreasing"[{1}, "allInts"[((f + f) + f) + 1], "trueIntroduction", hUInc]],
			"Have"[hX2Zero, "memNat"[0, "xorMerge"[{1}, "allInts"[((f + f) + f) + 1]]] == "true"],
			"Have"[n01, Not[0 == 1]], "Introduce"[e], "Exact"["successorNotZero"[0, "equalitySymmetry"[e]]],
			"Rewrite"["memNatXorOneOther"[0, "allInts"[((f + f) + f) + 1], n01, hUInc]],
			"Have"[u0, 0 + 1 <= ((f + f) + f) + 1], "LinearArithmetic",
			"Exact"["memNatAllIntsTrue"[((f + f) + f) + 1, 0, u0]],
			"Have"[hX2One, "memNat"[1, "xorMerge"[{1}, "allInts"[((f + f) + f) + 1]]] == "false"],
			"Rewrite"["memNatXorMerge"[1, {1}, "allInts"[((f + f) + f) + 1], "trueIntroduction", hUInc]],
			"Have"[u1, 1 + 1 <= ((f + f) + f) + 1], "LinearArithmetic",
			"Rewrite"["memNatAllIntsTrue"[((f + f) + f) + 1, 1, u1]], "Reflexivity",
			"Have"[hX2Loop, ForAll[{Typed[q, NonNegativeIntegers]}, Implies[q + 1 <= (g0 + ((j + j) + (j + j))) + 1, "memNat"[q + 2, "xorMerge"[{1}, "allInts"[((f + f) + f) + 1]]] == "true"]]],
			"Introduce"[q, hq],
			"Have"[nq1, Not[q + 2 == 1]], "Introduce"[e], "Have"[f0, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"[f0],
			"Rewrite"["memNatXorOneOther"[q + 2, "allInts"[((f + f) + f) + 1], nq1, hUInc]],
			"Have"[uQ, (q + 2) + 1 <= ((f + f) + f) + 1], "LinearArithmetic",
			"Exact"["memNatAllIntsTrue"[((f + f) + f) + 1, q + 2, uQ]],
			(* Run Phase 2! *)
			"Cases"["system4PopPhase"["decr4"[S0],
				Join[Join[Map["decr4", Krest], Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]]], {Typed[{}, {NonNegativeIntegers}]}],
				g0 + ((j + j) + (j + j)), "allInts"[((f + f) + f) + 1], g0 + 1, "encBlocks"[restRules, f, j + j],
				hK1Inc, hUInc, parK1Zero, hX2Zero, hX2One, hX2Loop]],
			"Introduce"[k2, p2Both], "Cases"[p2Both], "Introduce"[pos2, run2],
			(* Compose Phase 1 + Phase 2 *)
			"Have"[runAll, "steps"["system4Step", k1 + k2, c] ==
				"some"["system4Configuration"[Typed[{}, {"System4Element"}],
					Join["sets4"[Join[Join[
						Map["decr4", Prepend["decr4"[S0]][Join[Join[Map["decr4", Krest],
							Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]]], {Typed[{}, {NonNegativeIntegers}]}]]],
						Map["decr4", "loopK"[g0 + ((j + j) + (j + j)), "decrN4"[(g0 + ((j + j) + (j + j))) + 2, "xorMerge"[{1}, "allInts"[((f + f) + f) + 1]]]]]],
						{Typed[{}, {NonNegativeIntegers}]}]],
						Join["starredEmptyPairs"[Subtract[f, (j + 1) + (j + 1)]], "encBlocks"["shiftUpRules"[1, restRules], f, (j + 1) + (j + 1)]]],
					"state4A"]]],
			"Rewrite"[eqC],
			"Rewrite"["stepsAdd"["System4Configuration", "system4Step", k1, k2,
				"system4Configuration"[Typed[{}, {"System4Element"}],
					Join["sets4"[Prepend[S0][Krest]], Join["starredEmptyPairs"[Subtract[f, j + j]], "encBlocks"[Prepend[r][restRules], f, j + j]]],
					"state4A"]]],
			"Rewrite"[subOld], "Rewrite"[subNew],
			"Have"[j2Eq, (j + 1) + (j + 1) == (j + j) + 2], "LinearArithmetic",
			"Rewrite"[j2Eq], "Rewrite"["encBlocksShift"[restRules, f, j + j]],
			"Have"[tape1Eq, Join["starredEmptyPairs"[(g0 + 2) + 1], "encBlocks"[Prepend[r][restRules], f, j + j]] ==
				Join["starredEmptyPairs"[(g0 + 2) + 1],
					Prepend["star4"][Prepend["set4"["encRuleSet"[r, f, j + j]]][Join["starredEmptyPairs"[((g0 + ((j + j) + (j + j))) + 1) + ((g0 + 2) + 3)],
						Join[Prepend["star4"][Prepend["set4"["allInts"[((f + f) + f) + 1]]]["starredEmptyPairs"[Subtract[f + f, 2]]]], "encBlocks"[restRules, f, j + j]]]]]]],
			"Change"[Join["starredEmptyPairs"[(g0 + 2) + 1],
				Join[Join[Prepend["star4"][Prepend["set4"["encRuleSet"[r, f, j + j]]]["starredEmptyPairs"[f + f]]],
					Prepend["star4"][Prepend["set4"["allInts"[((f + f) + f) + 1]]]["starredEmptyPairs"[Subtract[f + f, 2]]]]],
					"encBlocks"[restRules, f, j + j]]] ==
				Join["starredEmptyPairs"[(g0 + 2) + 1],
					Prepend["star4"][Prepend["set4"["encRuleSet"[r, f, j + j]]][Join["starredEmptyPairs"[((g0 + ((j + j) + (j + j))) + 1) + ((g0 + 2) + 3)],
						Join[Prepend["star4"][Prepend["set4"["allInts"[((f + f) + f) + 1]]]["starredEmptyPairs"[Subtract[f + f, 2]]]], "encBlocks"[restRules, f, j + j]]]]]]],
			"Rewrite"["joinAssociativity"[Prepend["star4"][Prepend["set4"["encRuleSet"[r, f, j + j]]]["starredEmptyPairs"[f + f]]],
				Prepend["star4"][Prepend["set4"["allInts"[((f + f) + f) + 1]]]["starredEmptyPairs"[Subtract[f + f, 2]]]],
				"encBlocks"[restRules, f, j + j]]],
			"Rewrite"[f2Split], "Reflexivity",
			"Rewrite"[tape1Eq],
			"Rewrite"[run1],
			"Change"["steps"["system4Step", k2,
				"system4Configuration"[Typed[{}, {"System4Element"}],
					Join["sets4"[Prepend["decr4"[S0]][Join[Join[Map["decr4", Krest],
						Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]]], {Typed[{}, {NonNegativeIntegers}]}]]],
						Join["starredEmptyPairs"[(g0 + ((j + j) + (j + j))) + 1],
							Prepend["star4"][Prepend["set4"["allInts"[((f + f) + f) + 1]]][Join["starredEmptyPairs"[Subtract[f + f, 2]], "encBlocks"[restRules, f, j + j]]]]]],
					"state4A"]] ==
				"some"["system4Configuration"[Typed[{}, {"System4Element"}],
					Join["sets4"[Join[Join[
						Map["decr4", Prepend["decr4"[S0]][Join[Join[Map["decr4", Krest],
							Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]]], {Typed[{}, {NonNegativeIntegers}]}]]],
						Map["decr4", "loopK"[g0 + ((j + j) + (j + j)), "decrN4"[(g0 + ((j + j) + (j + j))) + 2, "xorMerge"[{1}, "allInts"[((f + f) + f) + 1]]]]]],
						{Typed[{}, {NonNegativeIntegers}]}]],
						Join["starredEmptyPairs"[g0 + 1], "encBlocks"[restRules, f, j + j]]],
					"state4A"]]],
			"Rewrite"[f2m2Split], "Exact"[run2],
			(* Prove K2 invariants! *)
			"Have"[hK2Inc, "allSetsStrictlyIncreasing"[Join[Join[
				Map["decr4", Prepend["decr4"[S0]][Join[Join[Map["decr4", Krest],
					Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]]], {Typed[{}, {NonNegativeIntegers}]}]]],
				Map["decr4", "loopK"[g0 + ((j + j) + (j + j)), "decrN4"[(g0 + ((j + j) + (j + j))) + 2, "xorMerge"[{1}, "allInts"[((f + f) + f) + 1]]]]]],
				{Typed[{}, {NonNegativeIntegers}]}]]],
			"Exact"["allSetsStrictlyIncreasingJoin"[
				Join[Map["decr4", Prepend["decr4"[S0]][Join[Join[Map["decr4", Krest],
					Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]]], {Typed[{}, {NonNegativeIntegers}]}]]],
					Map["decr4", "loopK"[g0 + ((j + j) + (j + j)), "decrN4"[(g0 + ((j + j) + (j + j))) + 2, "xorMerge"[{1}, "allInts"[((f + f) + f) + 1]]]]]],
				{Typed[{}, {NonNegativeIntegers}]},
				"allSetsStrictlyIncreasingJoin"[
					Map["decr4", Prepend["decr4"[S0]][Join[Join[Map["decr4", Krest],
						Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]]], {Typed[{}, {NonNegativeIntegers}]}]]],
					Map["decr4", "loopK"[g0 + ((j + j) + (j + j)), "decrN4"[(g0 + ((j + j) + (j + j))) + 2, "xorMerge"[{1}, "allInts"[((f + f) + f) + 1]]]]],
					"allSetsStrictlyIncreasingMapDecr4"[Prepend["decr4"[S0]][Join[Join[Map["decr4", Krest],
						Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]]], {Typed[{}, {NonNegativeIntegers}]}]], hK1Inc],
					"allSetsStrictlyIncreasingMapDecr4"["loopK"[g0 + ((j + j) + (j + j)), "decrN4"[(g0 + ((j + j) + (j + j))) + 2, "xorMerge"[{1}, "allInts"[((f + f) + f) + 1]]]],
						"allSetsStrictlyIncreasingLoopK"[g0 + ((j + j) + (j + j)), "decrN4"[(g0 + ((j + j) + (j + j))) + 2, "xorMerge"[{1}, "allInts"[((f + f) + f) + 1]]],
							"decrN4StrictlyIncreasing"[(g0 + ((j + j) + (j + j))) + 2, "xorMerge"[{1}, "allInts"[((f + f) + f) + 1]], hX2Inc]]]],
				"andIntroduction"["trueIntroduction", "trueIntroduction"]]],
			"Have"[hBoundF2, (((j + 1) + (j + 1)) + (h + h)) + 1 <= f], "LinearArithmetic",
			"Have"[hShRestBagInc, "strictlyAbove"[0, "shiftDown"[1, restBag]]],
			"Exact"["shiftDownStrictlyAbove"[restBag, 1, 0, hRestBag1]],
			"Have"[hShRInc, "strictlyAbove"[0, "shiftUp"[1, r]]],
			"Exact"["shiftUp1StrictlyAbove0"[r, hrInc]],
			(* Parity agreement for K2 below 2f - 2(j+1) - 2! *)
			"Have"[hPar2, ForAll[{Typed[x, NonNegativeIntegers]},
				Implies[((x + ((j + 1) + (j + 1))) + 2) + 1 <= f + f,
					"parMem"[x, Join[Join[
						Map["decr4", Prepend["decr4"[S0]][Join[Join[Map["decr4", Krest],
							Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]]], {Typed[{}, {NonNegativeIntegers}]}]]],
						Map["decr4", "loopK"[g0 + ((j + j) + (j + j)), "decrN4"[(g0 + ((j + j) + (j + j))) + 2, "xorMerge"[{1}, "allInts"[((f + f) + f) + 1]]]]]],
						{Typed[{}, {NonNegativeIntegers}]}]] ==
					"memNat"[x, "encodeBag4"["xorMerge"["shiftDown"[1, restBag], "shiftUp"[1, r]]]]]]],
			"Introduce"[x, hx],
			"Rewrite"["parMemJoin"[x, Join[
				Map["decr4", Prepend["decr4"[S0]][Join[Join[Map["decr4", Krest],
					Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]]], {Typed[{}, {NonNegativeIntegers}]}]]],
				Map["decr4", "loopK"[g0 + ((j + j) + (j + j)), "decrN4"[(g0 + ((j + j) + (j + j))) + 2, "xorMerge"[{1}, "allInts"[((f + f) + f) + 1]]]]]],
				{Typed[{}, {NonNegativeIntegers}]}]],
			"Change"["xorBool"["parMem"[x, Join[
				Map["decr4", Prepend["decr4"[S0]][Join[Join[Map["decr4", Krest],
					Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]]], {Typed[{}, {NonNegativeIntegers}]}]]],
				Map["decr4", "loopK"[g0 + ((j + j) + (j + j)), "decrN4"[(g0 + ((j + j) + (j + j))) + 2, "xorMerge"[{1}, "allInts"[((f + f) + f) + 1]]]]]]], "false"] ==
				"memNat"[x, "encodeBag4"["xorMerge"["shiftDown"[1, restBag], "shiftUp"[1, r]]]]],
			"Rewrite"["xorBoolFalseRight"["parMem"[x, Join[
				Map["decr4", Prepend["decr4"[S0]][Join[Join[Map["decr4", Krest],
					Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]]], {Typed[{}, {NonNegativeIntegers}]}]]],
				Map["decr4", "loopK"[g0 + ((j + j) + (j + j)), "decrN4"[(g0 + ((j + j) + (j + j))) + 2, "xorMerge"[{1}, "allInts"[((f + f) + f) + 1]]]]]]]]],
			"Rewrite"["parMemJoin"[x,
				Map["decr4", Prepend["decr4"[S0]][Join[Join[Map["decr4", Krest],
					Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]]], {Typed[{}, {NonNegativeIntegers}]}]]],
				Map["decr4", "loopK"[g0 + ((j + j) + (j + j)), "decrN4"[(g0 + ((j + j) + (j + j))) + 2, "xorMerge"[{1}, "allInts"[((f + f) + f) + 1]]]]]]],
			"Rewrite"["parMemMapDecr4"[x, Prepend["decr4"[S0]][Join[Join[Map["decr4", Krest],
				Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]]], {Typed[{}, {NonNegativeIntegers}]}]], hK1Inc]],
			"Change"["xorBool"["parMem"[x + 1, Join[Join[Map["decr4", Prepend[S0][Krest]],
				Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]]], {Typed[{}, {NonNegativeIntegers}]}]],
				"parMem"[x, Map["decr4", "loopK"[g0 + ((j + j) + (j + j)), "decrN4"[(g0 + ((j + j) + (j + j))) + 2, "xorMerge"[{1}, "allInts"[((f + f) + f) + 1]]]]]]] ==
				"memNat"[x, "encodeBag4"["xorMerge"["shiftDown"[1, restBag], "shiftUp"[1, r]]]]],
			"Rewrite"["parMemJoin"[x + 1, Join[Map["decr4", Prepend[S0][Krest]],
				Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]]], {Typed[{}, {NonNegativeIntegers}]}]],
			"Change"["xorBool"["xorBool"["parMem"[x + 1, Join[Map["decr4", Prepend[S0][Krest]],
				Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]]]], "false"],
				"parMem"[x, Map["decr4", "loopK"[g0 + ((j + j) + (j + j)), "decrN4"[(g0 + ((j + j) + (j + j))) + 2, "xorMerge"[{1}, "allInts"[((f + f) + f) + 1]]]]]]] ==
				"memNat"[x, "encodeBag4"["xorMerge"["shiftDown"[1, restBag], "shiftUp"[1, r]]]]],
			"Rewrite"["xorBoolFalseRight"["parMem"[x + 1, Join[Map["decr4", Prepend[S0][Krest]],
				Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]]]]]],
			"Rewrite"["parMemJoin"[x + 1, Map["decr4", Prepend[S0][Krest]],
				Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]]]],
			"Rewrite"["parMemMapDecr4"[x + 1, Prepend[S0][Krest], hKInc]],
			"Rewrite"["parMemLoopKMapDecr4"[x + 1, g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]],
				"decrN4StrictlyIncreasing"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]], hX1Inc]]],
			"Rewrite"["memNatDecr4"[x + 1, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]],
				"decrN4StrictlyIncreasing"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]], hX1Inc]]],
			"Rewrite"["memNatDecrN4"[(g0 + 2) + 2, (x + 1) + 1, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]], hX1Inc]],
			"Rewrite"["parMemLoopKMapDecr4"[x, g0 + ((j + j) + (j + j)), "decrN4"[(g0 + ((j + j) + (j + j))) + 2, "xorMerge"[{1}, "allInts"[((f + f) + f) + 1]]],
				"decrN4StrictlyIncreasing"[(g0 + ((j + j) + (j + j))) + 2, "xorMerge"[{1}, "allInts"[((f + f) + f) + 1]], hX2Inc]]],
			"Rewrite"["memNatDecr4"[x, "decrN4"[(g0 + ((j + j) + (j + j))) + 2, "xorMerge"[{1}, "allInts"[((f + f) + f) + 1]]],
				"decrN4StrictlyIncreasing"[(g0 + ((j + j) + (j + j))) + 2, "xorMerge"[{1}, "allInts"[((f + f) + f) + 1]], hX2Inc]]],
			"Rewrite"["memNatDecrN4"[(g0 + ((j + j) + (j + j))) + 2, x + 1, "xorMerge"[{1}, "allInts"[((f + f) + f) + 1]], hX2Inc]],
			"Have"[nA1, Not[((x + 1) + 1) + ((g0 + 2) + 2) == 1]], "Introduce"[e], "Have"[f0, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"[f0],
			"Have"[nB1, Not[(x + 1) + ((g0 + ((j + j) + (j + j))) + 2) == 1]], "Introduce"[e], "Have"[f0, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"[f0],
			"Rewrite"["memNatXorOneOther"[((x + 1) + 1) + ((g0 + 2) + 2), "encRuleSet"[r, f, j + j], nA1, hRs1Inc]],
			"Rewrite"["memNatXorOneOther"[(x + 1) + ((g0 + ((j + j) + (j + j))) + 2), "allInts"[((f + f) + f) + 1], nB1, hUInc]],
			"Have"[uX, ((x + 1) + ((g0 + ((j + j) + (j + j))) + 2)) + 1 <= ((f + f) + f) + 1], "LinearArithmetic",
			"Rewrite"["memNatAllIntsTrue"[((f + f) + f) + 1, (x + 1) + ((g0 + ((j + j) + (j + j))) + 2), uX]],
			"Have"[idxEq, ((x + 1) + 1) + ((g0 + 2) + 2) == (x + Subtract[f, j + j]) + 3],
			"Rewrite"[subOld], "LinearArithmetic",
			"Rewrite"[idxEq],
			"Have"[rsX, ((x + Subtract[f, j + j]) + 3) + 1 <= ((f + f) + f) + 1],
			"Rewrite"[subOld], "LinearArithmetic",
			"Rewrite"["memNatEncRuleSetAt"[r, f, j + j, x, j2LeF, hrInc, rsX]],
			"Rewrite"["xorBoolCancelTrue"["parMem"[(x + 1) + 1, Prepend[S0][Krest]], "memNat"[x, "doubleList"[r]]]],
			"Have"[hx2, (((x + 2) + (j + j)) + 2) + 1 <= f + f], "LinearArithmetic",
			"Change"["xorBool"["parMem"[x + 2, Prepend[S0][Krest]], "memNat"[x, "doubleList"[r]]] ==
				"memNat"[x, "encodeBag4"["xorMerge"["shiftDown"[1, restBag], "shiftUp"[1, r]]]]],
			"Rewrite"[hPar[x + 2, hx2]],
			"Rewrite"["memNatEncodeBag4XorMerge"[x, "shiftDown"[1, restBag], "shiftUp"[1, r], hShRestBagInc, hShRInc]],
			"Rewrite"["encodeBag4ShiftUp1"[r]],
			"Have"[bagEq, "memNat"[x + 2, "encodeBag4"[Prepend[1][restBag]]] == "memNat"[x, "encodeBag4"["shiftDown"[1, restBag]]]],
			"Have"[neqX2, Not[x + 2 == 0]], "Introduce"[e], "Have"[f0, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"[f0],
			"Change"[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Booleans], "memNat"[x + 2, "encodeBag4"[restBag]], "true", Decide[x + 2 == 0]] ==
				"memNat"[x, "encodeBag4"["shiftDown"[1, restBag]]]],
			"Rewrite"["decideEqualFalse"[x + 2, 0, neqX2]],
			"Exact"["equalitySymmetry"["memNatEncodeBag4ShiftDown1"[x, restBag, hRestBag1]]],
			"Rewrite"[bagEq],
			(* Bounds on new bag and new rules *)
			"Have"[hNewBagBd, "allBelowEqual"[Subtract[f, (j + 1) + 1], "xorMerge"["shiftDown"[1, restBag], "shiftUp"[1, r]]]],
			"Have"[subBagEq, Subtract[f, (j + 1) + 1] + 1 == Subtract[f, j + 1]],
			"Rewrite"[eqF],
			"Have"[ea, g0 + ((j + j) + 3) == ((g0 + j) + 1) + ((j + 1) + 1)], "LinearArithmetic",
			"Have"[eb, g0 + ((j + j) + 3) == ((g0 + j) + 2) + (j + 1)], "LinearArithmetic",
			"Rewrite"[ea], "Rewrite"["additionSubtractionCancellation"[(g0 + j) + 1, (j + 1) + 1]],
			"Have"[ec, ((g0 + j) + 1) + ((j + 1) + 1) == ((g0 + j) + 2) + (j + 1)], "LinearArithmetic",
			"Rewrite"[ec], "Rewrite"["additionSubtractionCancellation"[(g0 + j) + 2, j + 1]], "Reflexivity",
			"Have"[hRestBd2, "allBelowEqual"[Subtract[f, (j + 1) + 1] + 1, restBag]],
			"Rewrite"[subBagEq], "Exact"[hRestBagBd],
			"Have"[hShRestBd, "allBelowEqual"[Subtract[f, (j + 1) + 1], "shiftDown"[1, restBag]]],
			"Exact"["shiftDownAllBelowEqual"[restBag, 1, Subtract[f, (j + 1) + 1], hRestBd2]],
			"Have"[hShRBd, "allBelowEqual"[Subtract[f, (j + 1) + 1], "shiftUp"[1, r]]],
			"Have"[leR2B, Subtract[f, (j + ((h + 1) + (h + 1))) + 1] + 1 <= Subtract[f, (j + 1) + 1]],
			"Have"[leR, (j + ((h + 1) + (h + 1))) + 1 <= f], "LinearArithmetic",
			"Cases"["lessEqualExists"[(j + ((h + 1) + (h + 1))) + 1, f, leR]], "Introduce"[dr, eqFr],
			"Rewrite"[eqFr],
			"Have"[er1, dr + ((j + ((h + 1) + (h + 1))) + 1) == ((dr + (h + h)) + 1) + ((j + 1) + 1)], "LinearArithmetic",
			"Rewrite"["additionSubtractionCancellation"[dr, (j + ((h + 1) + (h + 1))) + 1]],
			"Rewrite"[er1], "Rewrite"["additionSubtractionCancellation"[(dr + (h + h)) + 1, (j + 1) + 1]], "LinearArithmetic",
			"Exact"["allBelowEqualWeaken"[Subtract[f, (j + ((h + 1) + (h + 1))) + 1] + 1, Subtract[f, (j + 1) + 1], "shiftUp"[1, r], leR2B,
				"shiftUpAllBelowEqual"[r, 1, Subtract[f, (j + ((h + 1) + (h + 1))) + 1], hrBd]]],
			"Exact"["xorMergeAllBelowEqual"[Subtract[f, (j + 1) + 1], "shiftDown"[1, restBag], "shiftUp"[1, r], hShRestBd, hShRBd]],
			"Have"[hNewRulesBd, "allRulesBelowEqual"[Subtract[f, ((j + 1) + (h + h)) + 1], "shiftUpRules"[1, restRules]]],
			"Have"[subRuleEq, Subtract[f, (j + ((h + 1) + (h + 1))) + 1] + 1 == Subtract[f, ((j + 1) + (h + h)) + 1]],
			"Have"[leR, (j + ((h + 1) + (h + 1))) + 1 <= f], "LinearArithmetic",
			"Cases"["lessEqualExists"[(j + ((h + 1) + (h + 1))) + 1, f, leR]], "Introduce"[dr, eqFr],
			"Rewrite"[eqFr],
			"Have"[er1, dr + ((j + ((h + 1) + (h + 1))) + 1) == (dr + 1) + (((j + 1) + (h + h)) + 1)], "LinearArithmetic",
			"Rewrite"["additionSubtractionCancellation"[dr, (j + ((h + 1) + (h + 1))) + 1]],
			"Rewrite"[er1], "Rewrite"["additionSubtractionCancellation"[dr + 1, ((j + 1) + (h + h)) + 1]],
			"Rewrite"["equalitySymmetry"[subRuleEq]],
			"Exact"["shiftUpRulesAllBelowEqual"[restRules, 1, Subtract[f, (j + ((h + 1) + (h + 1))) + 1], hRestRulesBd]],
			"Have"[posAll, 1 <= k1 + k2], "LinearArithmetic",
			(* Assemble witness! *)
			"Exact"["existsIntroduction"[k1 + k2, "andIntroduction"[posAll,
				"existsIntroduction"[
					"system4Configuration"[Typed[{}, {"System4Element"}],
						Join["sets4"[Join[Join[
							Map["decr4", Prepend["decr4"[S0]][Join[Join[Map["decr4", Krest],
								Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]]], {Typed[{}, {NonNegativeIntegers}]}]]],
							Map["decr4", "loopK"[g0 + ((j + j) + (j + j)), "decrN4"[(g0 + ((j + j) + (j + j))) + 2, "xorMerge"[{1}, "allInts"[((f + f) + f) + 1]]]]]],
							{Typed[{}, {NonNegativeIntegers}]}]],
							Join["starredEmptyPairs"[Subtract[f, (j + 1) + (j + 1)]], "encBlocks"["shiftUpRules"[1, restRules], f, (j + 1) + (j + 1)]]],
						"state4A"],
					"andIntroduction"[runAll,
						"existsIntroduction"["decr4"["decr4"[S0]],
							"existsIntroduction"[Join[Join[
								Map["decr4", Join[Join[Map["decr4", Krest],
									Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]]], {Typed[{}, {NonNegativeIntegers}]}]],
								Map["decr4", "loopK"[g0 + ((j + j) + (j + j)), "decrN4"[(g0 + ((j + j) + (j + j))) + 2, "xorMerge"[{1}, "allInts"[((f + f) + f) + 1]]]]]],
								{Typed[{}, {NonNegativeIntegers}]}],
								"andIntroduction"[hK2Inc,
									"andIntroduction"[
										"equalityReflexivity"["system4Configuration"[Typed[{}, {"System4Element"}],
											Join["sets4"[Join[Join[
												Map["decr4", Prepend["decr4"[S0]][Join[Join[Map["decr4", Krest],
													Map["decr4", "loopK"[g0 + 2, "decrN4"[(g0 + 2) + 2, "xorMerge"[{1}, "encRuleSet"[r, f, j + j]]]]]], {Typed[{}, {NonNegativeIntegers}]}]]],
												Map["decr4", "loopK"[g0 + ((j + j) + (j + j)), "decrN4"[(g0 + ((j + j) + (j + j))) + 2, "xorMerge"[{1}, "allInts"[((f + f) + f) + 1]]]]]],
												{Typed[{}, {NonNegativeIntegers}]}]],
												Join["starredEmptyPairs"[Subtract[f, (j + 1) + (j + 1)]], "encBlocks"["shiftUpRules"[1, restRules], f, (j + 1) + (j + 1)]]],
											"state4A"]],
										"andIntroduction"[hBoundF2,
											"andIntroduction"[hPar2,
												"andIntroduction"["xorMergeStrictlyAbove"["shiftDown"[1, restBag], "shiftUp"[1, r], 0, hShRestBagInc, hShRInc],
													"andIntroduction"[hNewBagBd,
														"andIntroduction"["shiftUpRulesStrictlyIncreasing"[restRules, 1, hRestRulesInc], hNewRulesBd]]]]]]]]]]]]]]
		}
	],
	(* Rung 4 main theorem: System 4 forward-simulates fueled System 5! *)
	machineTheorem["system4Simulation",
		ForAll[{Typed[f, NonNegativeIntegers]}, "forwardSimulation"["fueledSystem5Step", "system4Step", "system4Represents"[f]]],
		{
			"Introduce"[f, fs, c, fs2],
			"Cases"[fs], "Introduce"[s, j, h],
			"Cases"[h],
			"Introduce"[hRep, stepped], "Exact"["falseElimination"["noneNotSome"["FueledSystem5", fs2, stepped]]],
			"Introduce"[h1, hRep, stepped],
			"Cases"[s], "Introduce"[bag, rules, hRep, stepped],
			"Cases"[bag],
			"Introduce"[hRep, stepped], "Exact"["falseElimination"["noneNotSome"["FueledSystem5", fs2, stepped]]],
			"Introduce"[b, restBag, hRep, stepped],
			"Cases"[rules],
			"Introduce"[hRep, stepped], "Exact"["falseElimination"["noneNotSome"["FueledSystem5", fs2, stepped]]],
			"Introduce"[r, restRules, hRep, stepped],
			"Cases"[b],
			"Introduce"[hRep, stepped], "Exact"["falseElimination"["noneNotSome"["FueledSystem5", fs2, stepped]]],
			"Introduce"[bPred, hRep, stepped],
			"Cases"[bPred],
			(* b = 1: P-step! *)
			"Introduce"[hRep, stepped],
			"Have"[eqFs2, "fueledSystem5"["system5Configuration"["xorMerge"["shiftDown"[1, restBag], "shiftUp"[1, r]], "shiftUpRules"[1, restRules]], j + 1, h1] == fs2],
			"Exact"["someInjective"["FueledSystem5", "fueledSystem5"["system5Configuration"["xorMerge"["shiftDown"[1, restBag], "shiftUp"[1, r]], "shiftUpRules"[1, restRules]], j + 1, h1], fs2, stepped]],
			"Rewrite"["equalitySymmetry"[eqFs2]],
			"Exact"["repS4PStep"[f, restBag, r, restRules, j, h1, c, hRep]],
			(* b = k + 2: D-step! *)
			"Introduce"[bk, hRep, stepped],
			"Have"[eqFs2, "fueledSystem5"["system5Configuration"[Prepend[bk + 1]["shiftDown"[1, restBag]], "shiftUpRules"[1, Prepend[r][restRules]]], j + 1, h1] == fs2],
			"Exact"["someInjective"["FueledSystem5", "fueledSystem5"["system5Configuration"[Prepend[bk + 1]["shiftDown"[1, restBag]], "shiftUpRules"[1, Prepend[r][restRules]]], j + 1, h1], fs2, stepped]],
			"Rewrite"["equalitySymmetry"[eqFs2]],
			"Have"[hBagInc, "strictlyAbove"[0, Prepend[(bk + 1) + 1][restBag]]],
			"Cases"[hRep], "Introduce"[S0, hr1], "Cases"[hr1], "Introduce"[Krest, hr2],
			"Cases"[hr2], "Introduce"[hKInc, hr3], "Cases"[hr3], "Introduce"[eqC, hr4],
			"Cases"[hr4], "Introduce"[hBoundF, hr5], "Cases"[hr5], "Introduce"[hPar, hr6],
			"Cases"[hr6], "Introduce"[hBI, hr7], "Exact"[hBI],
			"Cases"[hBagInc], "Introduce"[hbkPos, hRestAbove],
			"Have"[no1, "memNat"[1, Prepend[(bk + 1) + 1][restBag]] == "false"],
			"Have"[neq1, Not[1 == (bk + 1) + 1]], "Introduce"[e], "Have"[f0, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"[f0],
			"Have"[le1, 1 <= (bk + 1) + 1], "LinearArithmetic",
			"Change"[InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Booleans], "memNat"[1, restBag], "true", Decide[1 == (bk + 1) + 1]] == "false"],
			"Rewrite"["decideEqualFalse"[1, (bk + 1) + 1, neq1]],
			"Exact"["memNatStrictlyAboveFalse"[1, (bk + 1) + 1, restBag, le1, hRestAbove]],
			"Exact"["repS4DStep"[f, "system5Configuration"[Prepend[(bk + 1) + 1][restBag], Prepend[r][restRules]], j, h1, c, hRep, no1]]
		}
	]
}
