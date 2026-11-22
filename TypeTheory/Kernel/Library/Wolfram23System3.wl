(* ::Package:: *)

(*
Rung 5 of Smith's chain of emulations to Wolfram's (2,3) Turing machine: a fueled System 4 configuration
emulated by Smith's System 3 via width-2^w Rule-60 parity blocks, built on System 4 in Wolfram23System4.wl.
The design is in docs/notes/Wolfram23Universality.md.

	"iterateFn", "xorBits",          GF(2) bit-vector algebra, prefix-XOR transducer "scanB", Rule-60 step
	"zerosBits", "onesBits",         "stepR", Frobenius identity "stepRIteratePow2" (stepR^(2^w) = shiftR^(2^w)
	"scanB", "stepR", "rowBits",     xor id), and orthogonality "parAtRowBits" (parAt[rowBits[2^w, i], k] ==
	"parAt", "parAtRowBits"          Decide[k == i])
	"toCell", "ofBits",              System 3 lookahead run macros: left walk, turn in state A, star-B step,
	"sys3WalkLeft", "sys3TurnA",     and full block scans in states B and C
	"sys3StarB", "sys3ScanBlock"
	"TapeItem", "LeftEnd",           abstract zipper configuration "AbstractConfig" with parametric left end
	"Closing", "Focus3",             and right closing (preserving the T6 hooks), decoding invariant
	"AbstractConfig", "acToSystem4", "decodesBits", and direct zipper maps "acToSystem4" and "acToSystem3"
	"acToSystem3", "acOk"
	"FueledSystem4",                 fueled System 4 stepping and simulation relation "system3Represents",
	"fueledSystem4Step",             proved via "scanRun", "turnRun", all seven focus/state step cases,
	"system3Represents",             "acStep", "system3Simulation", and the rung 5+6 composition
	"system3Simulation",             "system0SimulatesSystem4"
	"system0SimulatesSystem4"
	"baseSet", "encSet", "initAC",   initial parity-block encoder guaranteeing leading true ("firstTrueEncSet"),
	"rep3Init"                       decoding ("decodesEncSet"), and initial representation ("rep3Init")
	"rep3Exit", "phiExit",           halting exit lemmas into System 3 state C on closing 1, relabeling to
	"phi2StateNotC",                 Wolfram's (2,3) state B on color2, and the final exit step to blank color0
	"wolfram23ExitStep"              in state A
	"decodeBlocks", "decodeW23",     Wolfram (2,3) tape decoder (checking non-zero cells, positive multiple of
	"colorOccurs", "rep3Decode"      block width, and even parity below bound) and "rep3Decode"
*)


(* ::Section:: *)
(*PackageExported*)




(* ::Section:: *)
(*PackageScoped*)


PackageScoped[$system3Declarations]


(* ::Section:: *)
(*Usage Messages*)


$system3Declarations::usage = "$system3Declarations is the list of the declarations of rung 5 of Smith's chain (System 4 to System 3), in order, each theorem proved by its tactics in the environment so far."


(* ::Section:: *)
(*Function Definitions*)


$system3Declarations = {
	(* === Part A: ParityBlocks (Rule 60 / prefix-XOR algebra over GF(2)) === *)
	TypeTheoryDefinition["iterateFn", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[f, A -> A], Typed[n, NonNegativeIntegers], Typed[x, A]},
			InductiveRecursor[NonNegativeIntegers][Function[{Typed[q, NonNegativeIntegers]}, A], x,
				Function[{Typed[k, NonNegativeIntegers], Typed[prev, A]}, f[prev]], n]],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, (A -> A) -> NonNegativeIntegers -> A -> A]
	]],
	machineTheorem["iterateFnStep",
		ForAll[{TypedImplicit[A, TypeUniverse[1]], Typed[f, A -> A], Typed[n, NonNegativeIntegers], Typed[x, A]},
			"iterateFn"[f, n + 1, x] == "iterateFn"[f, n, f[x]]],
		{
			"Introduce"[A, f, n, x], "Induction"[n],
			"Reflexivity",
			"Introduce"[k, ih],
			"Change"[f["iterateFn"[f, k + 1, x]] == f["iterateFn"[f, k, f[x]]]],
			"Rewrite"[ih]
		}
	],
	machineTheorem["iterateFnAdd",
		ForAll[{TypedImplicit[A, TypeUniverse[1]], Typed[f, A -> A], Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers], Typed[x, A]},
			"iterateFn"[f, m + n, x] == "iterateFn"[f, n, "iterateFn"[f, m, x]]],
		{
			"Introduce"[A, f, m, n, x], "Induction"[n],
			"Reflexivity",
			"Introduce"[k, ih],
			"Change"[f["iterateFn"[f, m + k, x]] == f["iterateFn"[f, k, "iterateFn"[f, m, x]]]],
			"Rewrite"[ih]
		}
	],
	(* Pointwise XOR of bit lists *)
	TypeTheoryDefinition["xorBits", Typed[
		Function[{Typed[xs, {Booleans}]},
			InductiveRecursor[List][Function[{Typed[q, {Booleans}]}, {Booleans} -> {Booleans}],
				Function[{Typed[ys, {Booleans}]}, Typed[{}, {Booleans}]],
				Function[{Typed[a, Booleans], Typed[xRest, {Booleans}], Typed[prev, {Booleans} -> {Booleans}]},
					Function[{Typed[ys, {Booleans}]},
						InductiveRecursor[List][Function[{Typed[q, {Booleans}]}, {Booleans}], Typed[{}, {Booleans}],
							Function[{Typed[b, Booleans], Typed[yRest, {Booleans}], Typed[u, {Booleans}]},
								Prepend["xorBool"[a, b]][prev[yRest]]], ys]]], xs]],
		{Booleans} -> {Booleans} -> {Booleans}
	]],
	TypeTheoryDefinition["replicateBool", Typed[
		Function[{Typed[n, NonNegativeIntegers], Typed[b, Booleans]},
			InductiveRecursor[NonNegativeIntegers][Function[{Typed[q, NonNegativeIntegers]}, {Booleans}], Typed[{}, {Booleans}],
				Function[{Typed[k, NonNegativeIntegers], Typed[prev, {Booleans}]}, Prepend[b][prev]], n]],
		NonNegativeIntegers -> Booleans -> {Booleans}
	]],
	TypeTheoryDefinition["zerosBits", Typed[Function[{Typed[n, NonNegativeIntegers]}, "replicateBool"[n, "false"]], NonNegativeIntegers -> {Booleans}]],
	TypeTheoryDefinition["onesBits", Typed[Function[{Typed[n, NonNegativeIntegers]}, "replicateBool"[n, "true"]], NonNegativeIntegers -> {Booleans}]],
	machineTheorem["lengthReplicateBool",
		ForAll[{Typed[n, NonNegativeIntegers], Typed[b, Booleans]}, Length["replicateBool"[n, b]] == n],
		{
			"Introduce"[n, b], "Induction"[n], "Reflexivity",
			"Introduce"[k, ih], "Change"[Length["replicateBool"[k, b]] + 1 == k + 1], "Rewrite"[ih]
		}
	],
	machineTheorem["lengthZerosBits",
		ForAll[{Typed[n, NonNegativeIntegers]}, Length["zerosBits"[n]] == n],
		{"Introduce"[n], "Exact"["lengthReplicateBool"[n, "false"]]}
	],
	machineTheorem["lengthOnesBits",
		ForAll[{Typed[n, NonNegativeIntegers]}, Length["onesBits"[n]] == n],
		{"Introduce"[n], "Exact"["lengthReplicateBool"[n, "true"]]}
	],
	machineTheorem["replicateBoolAdd",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers], Typed[b, Booleans]},
			"replicateBool"[m + n, b] == Join["replicateBool"[m, b], "replicateBool"[n, b]]],
		{
			"Introduce"[m, n, b], "Induction"[m],
			"Change"["replicateBool"[0 + n, b] == "replicateBool"[n, b]],
			"Rewrite"["additionZeroLeft"[n]],
			"Introduce"[k, ih],
			"Have"[eq, (k + 1) + n == (k + n) + 1], "LinearArithmetic",
			"Rewrite"[eq],
			"Change"[Prepend[b]["replicateBool"[k + n, b]] == Prepend[b][Join["replicateBool"[k, b], "replicateBool"[n, b]]]],
			"Rewrite"[ih]
		}
	],
	machineTheorem["lengthXorBits",
		ForAll[{Typed[xs, {Booleans}], Typed[ys, {Booleans}]},
			Implies[Length[xs] == Length[ys], Length["xorBits"[xs, ys]] == Length[xs]]],
		{
			"Introduce"[xs], "Induction"[xs],
			"Introduce"[ys, h], "Reflexivity",
			"Introduce"[a, xRest, ih, ys], "Cases"[ys],
			"Introduce"[h], "Exact"["falseElimination"["successorNotZero"[Length[xRest], h]]],
			"Introduce"[b, yRest, h],
			"Have"[hl, Length[xRest] == Length[yRest]], "Exact"["successorInjectivity"[h]],
			"Change"[Length["xorBits"[xRest, yRest]] + 1 == Length[xRest] + 1],
			"Rewrite"[ih[yRest, hl]]
		}
	],
	machineTheorem["xorBitsNilRight",
		ForAll[{Typed[xs, {Booleans}]}, "xorBits"[xs, Typed[{}, {Booleans}]] == Typed[{}, {Booleans}]],
		{"Introduce"[xs], "Cases"[xs], "Reflexivity", "Introduce"[a, rest], "Reflexivity"}
	],
	machineTheorem["xorBitsCommutativity",
		ForAll[{Typed[xs, {Booleans}], Typed[ys, {Booleans}]}, "xorBits"[xs, ys] == "xorBits"[ys, xs]],
		{
			"Introduce"[xs], "Induction"[xs],
			"Introduce"[ys], "Cases"[ys], "Reflexivity", "Introduce"[b, yRest], "Reflexivity",
			"Introduce"[a, xRest, ih, ys], "Cases"[ys], "Reflexivity",
			"Introduce"[b, yRest],
			"Change"[Prepend["xorBool"[a, b]]["xorBits"[xRest, yRest]] == Prepend["xorBool"[b, a]]["xorBits"[yRest, xRest]]],
			"Rewrite"["xorBoolCommutativity"[a, b]], "Rewrite"[ih[yRest]]
		}
	],
	machineTheorem["xorBitsAssociativity",
		ForAll[{Typed[xs, {Booleans}], Typed[ys, {Booleans}], Typed[zs, {Booleans}]},
			"xorBits"["xorBits"[xs, ys], zs] == "xorBits"[xs, "xorBits"[ys, zs]]],
		{
			"Introduce"[xs], "Induction"[xs],
			"Introduce"[ys, zs], "Reflexivity",
			"Introduce"[a, xRest, ih, ys], "Cases"[ys],
			"Introduce"[zs], "Reflexivity",
			"Introduce"[b, yRest, zs], "Cases"[zs], "Reflexivity",
			"Introduce"[c, zRest],
			"Change"[Prepend["xorBool"["xorBool"[a, b], c]]["xorBits"["xorBits"[xRest, yRest], zRest]] ==
				Prepend["xorBool"[a, "xorBool"[b, c]]]["xorBits"[xRest, "xorBits"[yRest, zRest]]]],
			"Rewrite"["xorBoolAssociativity"[a, b, c]], "Rewrite"[ih[yRest, zRest]]
		}
	],
	machineTheorem["xorBitsSelf",
		ForAll[{Typed[xs, {Booleans}]}, "xorBits"[xs, xs] == "zerosBits"[Length[xs]]],
		{
			"Introduce"[xs], "Induction"[xs], "Reflexivity",
			"Introduce"[a, rest, ih],
			"Change"[Prepend["xorBool"[a, a]]["xorBits"[rest, rest]] == Prepend["false"]["zerosBits"[Length[rest]]]],
			"Rewrite"["xorBoolSelf"[a]], "Rewrite"[ih]
		}
	],
	machineTheorem["xorBitsZerosRight",
		ForAll[{Typed[xs, {Booleans}]}, "xorBits"[xs, "zerosBits"[Length[xs]]] == xs],
		{
			"Introduce"[xs], "Induction"[xs], "Reflexivity",
			"Introduce"[a, rest, ih],
			"Change"[Prepend["xorBool"[a, "false"]]["xorBits"[rest, "zerosBits"[Length[rest]]]] == Prepend[a][rest]],
			"Rewrite"["xorBoolFalseRight"[a]], "Rewrite"[ih]
		}
	],
	machineTheorem["xorBitsZerosLeft",
		ForAll[{Typed[xs, {Booleans}]}, "xorBits"["zerosBits"[Length[xs]], xs] == xs],
		{
			"Introduce"[xs],
			"Rewrite"["xorBitsCommutativity"["zerosBits"[Length[xs]], xs]],
			"Exact"["xorBitsZerosRight"[xs]]
		}
	],
	machineTheorem["xorBitsJoin",
		ForAll[{Typed[x1, {Booleans}], Typed[x2, {Booleans}], Typed[y1, {Booleans}], Typed[y2, {Booleans}]},
			Implies[Length[x1] == Length[y1],
				"xorBits"[Join[x1, x2], Join[y1, y2]] == Join["xorBits"[x1, y1], "xorBits"[x2, y2]]]],
		{
			"Introduce"[x1], "Induction"[x1],
			"Introduce"[x2, y1, y2], "Cases"[y1],
			"Introduce"[h], "Reflexivity",
			"Introduce"[b, yRest, h], "Exact"["falseElimination"["successorNotZero"[Length[yRest], "equalitySymmetry"[h]]]],
			"Introduce"[a, xRest, ih, x2, y1, y2], "Cases"[y1],
			"Introduce"[h], "Exact"["falseElimination"["successorNotZero"[Length[xRest], h]]],
			"Introduce"[b, yRest, h],
			"Have"[hl, Length[xRest] == Length[yRest]], "Exact"["successorInjectivity"[h]],
			"Change"[Prepend["xorBool"[a, b]]["xorBits"[Join[xRest, x2], Join[yRest, y2]]] == Prepend["xorBool"[a, b]][Join["xorBits"[xRest, yRest], "xorBits"[x2, y2]]]],
			"Rewrite"[ih[x2, yRest, y2, hl]]
		}
	],
	(* dropLastBits, lastBit, shiftR *)
	TypeTheoryDefinition["dropLastBits", Typed[
		Function[{Typed[xs, {Booleans}]},
			InductiveRecursor[List][Function[{Typed[q, {Booleans}]}, {Booleans}], Typed[{}, {Booleans}],
				Function[{Typed[a, Booleans], Typed[rest, {Booleans}], Typed[prev, {Booleans}]},
					InductiveRecursor[List][Function[{Typed[q, {Booleans}]}, {Booleans}], Typed[{}, {Booleans}],
						Function[{Typed[b, Booleans], Typed[rest2, {Booleans}], Typed[u, {Booleans}]}, Prepend[a][prev]], rest]], xs]],
		{Booleans} -> {Booleans}
	]],
	TypeTheoryDefinition["lastBit", Typed[
		Function[{Typed[xs, {Booleans}]},
			InductiveRecursor[List][Function[{Typed[q, {Booleans}]}, Booleans], "false",
				Function[{Typed[a, Booleans], Typed[rest, {Booleans}], Typed[prev, Booleans]},
					InductiveRecursor[List][Function[{Typed[q, {Booleans}]}, Booleans], a,
						Function[{Typed[b, Booleans], Typed[rest2, {Booleans}], Typed[u, Booleans]}, prev], rest]], xs]],
		{Booleans} -> Booleans
	]],
	TypeTheoryDefinition["shiftR", Typed[
		Function[{Typed[xs, {Booleans}]}, "dropLastBits"[Prepend["false"][xs]]],
		{Booleans} -> {Booleans}
	]],
	machineTheorem["dropLastBitsJoinSingle",
		ForAll[{Typed[xs, {Booleans}], Typed[b, Booleans]}, "dropLastBits"[Join[xs, {b}]] == xs],
		{
			"Introduce"[xs, b], "Induction"[xs], "Reflexivity",
			"Introduce"[a, rest, ih], "Cases"[rest], "Introduce"[ih], "Reflexivity",
			"Introduce"[c, rest2, ih],
			"Change"[Prepend[a]["dropLastBits"[Join[Prepend[c][rest2], {b}]]] == Prepend[a][Prepend[c][rest2]]],
			"Rewrite"[ih]
		}
	],
	machineTheorem["lastBitJoinSingle",
		ForAll[{Typed[xs, {Booleans}], Typed[b, Booleans]}, "lastBit"[Join[xs, {b}]] == b],
		{
			"Introduce"[xs, b], "Induction"[xs], "Reflexivity",
			"Introduce"[a, rest, ih], "Cases"[rest], "Introduce"[ih], "Reflexivity",
			"Introduce"[c, rest2, ih],
			"Change"["lastBit"[Join[Prepend[c][rest2], {b}]] == b],
			"Exact"[ih]
		}
	],
	machineTheorem["lengthShiftR",
		ForAll[{Typed[xs, {Booleans}]}, Length["shiftR"[xs]] == Length[xs]],
		{
			"Introduce"[xs], "Induction"[xs], "Reflexivity",
			"Introduce"[a, rest, ih],
			"Cases"[rest], "Introduce"[ih], "Reflexivity",
			"Introduce"[b, rest2, ih],
			"Change"[Length["dropLastBits"[Prepend[a][Prepend[b][rest2]]]] + 1 == Length[Prepend[a][Prepend[b][rest2]]]],
			"Have"[eq, Length["dropLastBits"[Prepend[a][Prepend[b][rest2]]]] == Length["dropLastBits"[Prepend["false"][Prepend[b][rest2]]]]],
			"Reflexivity",
			"Rewrite"[eq],
			"Change"[Length["shiftR"[Prepend[b][rest2]]] + 1 == Length[Prepend[b][rest2]] + 1],
			"Rewrite"[ih]
		}
	],
	machineTheorem["dropLastBitsXorBits",
		ForAll[{Typed[xs, {Booleans}], Typed[ys, {Booleans}]},
			Implies[Length[xs] == Length[ys], "dropLastBits"["xorBits"[xs, ys]] == "xorBits"["dropLastBits"[xs], "dropLastBits"[ys]]]],
		{
			"Introduce"[xs], "Induction"[xs],
			"Introduce"[ys, h], "Reflexivity",
			"Introduce"[a, xRest, ih, ys], "Cases"[ys],
			"Introduce"[h], "Exact"["falseElimination"["successorNotZero"[Length[xRest], h]]],
			"Introduce"[b, yRest, h],
			"Cases"[xRest],
			"Introduce"[ih, h], "Cases"[yRest], "Introduce"[h], "Reflexivity",
			"Introduce"[y2, yRest2, h], "Exact"["falseElimination"["successorNotZero"[Length[yRest2], "equalitySymmetry"["successorInjectivity"[h]]]]],
			"Introduce"[x2, xRest2, ih, h], "Cases"[yRest],
			"Introduce"[h], "Exact"["falseElimination"["successorNotZero"[Length[xRest2], "successorInjectivity"[h]]]],
			"Introduce"[y2, yRest2, h],
			"Have"[hl, Length[Prepend[x2][xRest2]] == Length[Prepend[y2][yRest2]]], "Exact"["successorInjectivity"[h]],
			"Change"[Prepend["xorBool"[a, b]]["dropLastBits"["xorBits"[Prepend[x2][xRest2], Prepend[y2][yRest2]]]] ==
				Prepend["xorBool"[a, b]]["xorBits"["dropLastBits"[Prepend[x2][xRest2]], "dropLastBits"[Prepend[y2][yRest2]]]]],
			"Rewrite"[ih[Prepend[y2][yRest2], hl]]
		}
	],
	machineTheorem["shiftRXor",
		ForAll[{Typed[xs, {Booleans}], Typed[ys, {Booleans}]},
			Implies[Length[xs] == Length[ys], "shiftR"["xorBits"[xs, ys]] == "xorBits"["shiftR"[xs], "shiftR"[ys]]]],
		{
			"Introduce"[xs, ys, hl],
			"Have"[hl1, Length[Prepend["false"][xs]] == Length[Prepend["false"][ys]]], "Change"[Length[xs] + 1 == Length[ys] + 1], "Rewrite"[hl],
			"Change"["dropLastBits"["xorBits"[Prepend["false"][xs], Prepend["false"][ys]]] == "xorBits"["dropLastBits"[Prepend["false"][xs]], "dropLastBits"[Prepend["false"][ys]]]],
			"Exact"["dropLastBitsXorBits"[Prepend["false"][xs], Prepend["false"][ys], hl1]]
		}
	],
	machineTheorem["dropLastBitsJoinNonEmpty",
		ForAll[{Typed[xs, {Booleans}], Typed[b, Booleans], Typed[ys, {Booleans}]},
			"dropLastBits"[Join[xs, Prepend[b][ys]]] == Join[xs, "dropLastBits"[Prepend[b][ys]]]],
		{
			"Introduce"[xs, b, ys], "Induction"[xs], "Reflexivity",
			"Introduce"[a, rest, ih], "Cases"[rest], "Introduce"[ih], "Reflexivity",
			"Introduce"[c, rest2, ih],
			"Change"[Prepend[a]["dropLastBits"[Join[Prepend[c][rest2], Prepend[b][ys]]]] == Prepend[a][Join[Prepend[c][rest2], "dropLastBits"[Prepend[b][ys]]]]],
			"Rewrite"[ih]
		}
	],
	machineTheorem["dropLastBitsReplicate",
		ForAll[{Typed[n, NonNegativeIntegers], Typed[b, Booleans]},
			"dropLastBits"["replicateBool"[n + 1, b]] == "replicateBool"[n, b]],
		{
			"Introduce"[n, b], "Induction"[n], "Reflexivity",
			"Introduce"[k, ih],
			"Change"[Prepend[b]["dropLastBits"["replicateBool"[k + 1, b]]] == Prepend[b]["replicateBool"[k, b]]],
			"Rewrite"[ih]
		}
	],
	machineTheorem["dropLastBitsZeros",
		ForAll[{Typed[n, NonNegativeIntegers]}, "dropLastBits"["zerosBits"[n + 1]] == "zerosBits"[n]],
		{"Introduce"[n], "Exact"["dropLastBitsReplicate"[n, "false"]]}
	],
	machineTheorem["dropLastBitsOnes",
		ForAll[{Typed[n, NonNegativeIntegers]}, "dropLastBits"["onesBits"[n + 1]] == "onesBits"[n]],
		{"Introduce"[n], "Exact"["dropLastBitsReplicate"[n, "true"]]}
	],
	(* scanFrom, scanB (T), parityBits *)
	TypeTheoryDefinition["scanFrom", Typed[
		Function[{Typed[s, Booleans], Typed[xs, {Booleans}]},
			InductiveRecursor[List][Function[{Typed[q, {Booleans}]}, Booleans -> {Booleans}],
				Function[{Typed[st, Booleans]}, Typed[{}, {Booleans}]],
				Function[{Typed[b, Booleans], Typed[rest, {Booleans}], Typed[prev, Booleans -> {Booleans}]},
					Function[{Typed[st, Booleans]}, Prepend["xorBool"[st, b]][prev["xorBool"[st, b]]]]], xs][s]],
		Booleans -> {Booleans} -> {Booleans}
	]],
	TypeTheoryDefinition["scanB", Typed[Function[{Typed[xs, {Booleans}]}, "scanFrom"["false", xs]], {Booleans} -> {Booleans}]],
	TypeTheoryDefinition["parityBits", Typed[
		Function[{Typed[xs, {Booleans}]},
			InductiveRecursor[List][Function[{Typed[q, {Booleans}]}, Booleans], "false",
				Function[{Typed[b, Booleans], Typed[rest, {Booleans}], Typed[prev, Booleans]}, "xorBool"[b, prev]], xs]],
		{Booleans} -> Booleans
	]],
	machineTheorem["lengthScanFrom",
		ForAll[{Typed[xs, {Booleans}], Typed[s, Booleans]}, Length["scanFrom"[s, xs]] == Length[xs]],
		{
			"Introduce"[xs], "Induction"[xs],
			"Introduce"[s], "Reflexivity",
			"Introduce"[b, rest, ih, s],
			"Change"[Length["scanFrom"["xorBool"[s, b], rest]] + 1 == Length[rest] + 1],
			"Rewrite"[ih["xorBool"[s, b]]]
		}
	],
	machineTheorem["xorBoolFourSwap",
		ForAll[{Typed[s, Booleans], Typed[t, Booleans], Typed[a, Booleans], Typed[b, Booleans]},
			"xorBool"["xorBool"[s, t], "xorBool"[a, b]] == "xorBool"["xorBool"[s, a], "xorBool"[t, b]]],
		{
			"Introduce"[s, t, a, b],
			"Cases"[s], "Cases"[t], "Cases"[a], "Cases"[b], "Reflexivity", "Reflexivity", "Cases"[b], "Reflexivity", "Reflexivity",
			"Cases"[a], "Cases"[b], "Reflexivity", "Reflexivity", "Cases"[b], "Reflexivity", "Reflexivity",
			"Cases"[t], "Cases"[a], "Cases"[b], "Reflexivity", "Reflexivity", "Cases"[b], "Reflexivity", "Reflexivity",
			"Cases"[a], "Cases"[b], "Reflexivity", "Reflexivity", "Cases"[b], "Reflexivity", "Reflexivity"
		}
	],
	machineTheorem["scanFromXor",
		ForAll[{Typed[xs, {Booleans}], Typed[ys, {Booleans}], Typed[s, Booleans], Typed[t, Booleans]},
			Implies[Length[xs] == Length[ys],
				"scanFrom"["xorBool"[s, t], "xorBits"[xs, ys]] == "xorBits"["scanFrom"[s, xs], "scanFrom"[t, ys]]]],
		{
			"Introduce"[xs], "Induction"[xs],
			"Introduce"[ys, s, t], "Cases"[ys], "Introduce"[h], "Reflexivity",
			"Introduce"[b, yRest, h], "Exact"["falseElimination"["successorNotZero"[Length[yRest], "equalitySymmetry"[h]]]],
			"Introduce"[a, xRest, ih, ys, s, t], "Cases"[ys],
			"Introduce"[h], "Exact"["falseElimination"["successorNotZero"[Length[xRest], h]]],
			"Introduce"[b, yRest, h],
			"Have"[hl, Length[xRest] == Length[yRest]], "Exact"["successorInjectivity"[h]],
			"Change"[Prepend["xorBool"["xorBool"[s, t], "xorBool"[a, b]]]["scanFrom"["xorBool"["xorBool"[s, t], "xorBool"[a, b]], "xorBits"[xRest, yRest]]] ==
				Prepend["xorBool"["xorBool"[s, a], "xorBool"[t, b]]]["xorBits"["scanFrom"["xorBool"[s, a], xRest], "scanFrom"["xorBool"[t, b], yRest]]]],
			"Rewrite"["xorBoolFourSwap"[s, t, a, b]],
			"Rewrite"[ih[yRest, "xorBool"[s, a], "xorBool"[t, b], hl]]
		}
	],
	machineTheorem["scanBXor",
		ForAll[{Typed[xs, {Booleans}], Typed[ys, {Booleans}]},
			Implies[Length[xs] == Length[ys], "scanB"["xorBits"[xs, ys]] == "xorBits"["scanB"[xs], "scanB"[ys]]]],
		{"Introduce"[xs, ys, h], "Exact"["scanFromXor"[xs, ys, "false", "false", h]]}
	],
	machineTheorem["scanFromZeros",
		ForAll[{Typed[n, NonNegativeIntegers], Typed[s, Booleans]}, "scanFrom"[s, "zerosBits"[n]] == "replicateBool"[n, s]],
		{
			"Introduce"[n, s], "Induction"[n], "Reflexivity",
			"Introduce"[k, ih],
			"Change"[Prepend["xorBool"[s, "false"]]["scanFrom"["xorBool"[s, "false"], "zerosBits"[k]]] == Prepend[s]["replicateBool"[k, s]]],
			"Rewrite"["xorBoolFalseRight"[s]], "Rewrite"[ih]
		}
	],
	machineTheorem["scanCEq",
		ForAll[{Typed[xs, {Booleans}]}, "scanFrom"["true", xs] == "xorBits"["scanB"[xs], "onesBits"[Length[xs]]]],
		{
			"Introduce"[xs],
			"Have"[hl, Length[xs] == Length["zerosBits"[Length[xs]]]], "Exact"["equalitySymmetry"["lengthZerosBits"[Length[xs]]]],
			"Have"[h, "scanFrom"["true", "xorBits"[xs, "zerosBits"[Length[xs]]]] ==
				"xorBits"["scanB"[xs], "scanFrom"["true", "zerosBits"[Length[xs]]]]],
			"Exact"["scanFromXor"[xs, "zerosBits"[Length[xs]], "false", "true", hl]],
			"Exact"["equalityTransitivity"[
				"equalityCongruence"[Function[{Typed[z, {Booleans}]}, "scanFrom"["true", z]], "equalitySymmetry"["xorBitsZerosRight"[xs]]],
				"equalityTransitivity"[h,
					"equalityCongruence"[Function[{Typed[z, {Booleans}]}, "xorBits"["scanB"[xs], z]], "scanFromZeros"[Length[xs], "true"]]]]]
		}
	],
	machineTheorem["scanFromDropLast",
		ForAll[{Typed[xs, {Booleans}], Typed[s, Booleans]}, "scanFrom"[s, "dropLastBits"[xs]] == "dropLastBits"["scanFrom"[s, xs]]],
		{
			"Introduce"[xs], "Induction"[xs], "Introduce"[s], "Reflexivity",
			"Introduce"[a, rest, ih, s], "Cases"[rest], "Introduce"[ih], "Reflexivity",
			"Introduce"[b, rest2, ih],
			"Change"[Prepend["xorBool"[s, a]]["scanFrom"["xorBool"[s, a], "dropLastBits"[Prepend[b][rest2]]]] ==
				Prepend["xorBool"[s, a]]["dropLastBits"["scanFrom"["xorBool"[s, a], Prepend[b][rest2]]]]],
			"Rewrite"[ih["xorBool"[s, a]]]
		}
	],
	machineTheorem["scanBShiftR",
		ForAll[{Typed[xs, {Booleans}]}, "scanB"["shiftR"[xs]] == "shiftR"["scanB"[xs]]],
		{
			"Introduce"[xs],
			"Change"["scanFrom"["false", "dropLastBits"[Prepend["false"][xs]]] == "dropLastBits"[Prepend["false"]["scanFrom"["false", xs]]]],
			"Rewrite"["scanFromDropLast"[Prepend["false"][xs], "false"]],
			"Reflexivity"
		}
	],
	machineTheorem["parityBitsJoin",
		ForAll[{Typed[xs, {Booleans}], Typed[ys, {Booleans}]},
			"parityBits"[Join[xs, ys]] == "xorBool"["parityBits"[xs], "parityBits"[ys]]],
		{
			"Introduce"[xs, ys], "Induction"[xs], "Reflexivity",
			"Introduce"[a, rest, ih],
			"Change"["xorBool"[a, "parityBits"[Join[rest, ys]]] == "xorBool"["xorBool"[a, "parityBits"[rest]], "parityBits"[ys]]],
			"Rewrite"[ih], "Exact"["equalitySymmetry"["xorBoolAssociativity"[a, "parityBits"[rest], "parityBits"[ys]]]]
		}
	],
	machineTheorem["parityBitsXor",
		ForAll[{Typed[xs, {Booleans}], Typed[ys, {Booleans}]},
			Implies[Length[xs] == Length[ys], "parityBits"["xorBits"[xs, ys]] == "xorBool"["parityBits"[xs], "parityBits"[ys]]]],
		{
			"Introduce"[xs], "Induction"[xs],
			"Introduce"[ys, h], "Cases"[ys], "Introduce"[h], "Reflexivity",
			"Introduce"[b, yRest, h], "Exact"["falseElimination"["successorNotZero"[Length[yRest], "equalitySymmetry"[h]]]],
			"Introduce"[a, xRest, ih, ys], "Cases"[ys],
			"Introduce"[h], "Exact"["falseElimination"["successorNotZero"[Length[xRest], h]]],
			"Introduce"[b, yRest, h],
			"Have"[hl, Length[xRest] == Length[yRest]], "Exact"["successorInjectivity"[h]],
			"Change"["xorBool"["xorBool"[a, b], "parityBits"["xorBits"[xRest, yRest]]] == "xorBool"["xorBool"[a, "parityBits"[xRest]], "xorBool"[b, "parityBits"[yRest]]]],
			"Rewrite"[ih[yRest, hl]], "Exact"["xorBoolFourSwap"[a, b, "parityBits"[xRest], "parityBits"[yRest]]]
		}
	],
	machineTheorem["parityBitsZeros",
		ForAll[{Typed[n, NonNegativeIntegers]}, "parityBits"["zerosBits"[n]] == "false"],
		{"Introduce"[n], "Induction"[n], "Reflexivity", "Introduce"[k, ih], "Exact"[ih]}
	],
	machineTheorem["lastBitScanFrom",
		ForAll[{Typed[xs, {Booleans}], Typed[a, Booleans], Typed[s, Booleans]},
			"lastBit"["scanFrom"[s, Prepend[a][xs]]] == "xorBool"[s, "parityBits"[Prepend[a][xs]]]],
		{
			"Introduce"[xs], "Induction"[xs],
			"Introduce"[a, s],
			"Change"["xorBool"[s, a] == "xorBool"[s, "xorBool"[a, "false"]]],
			"Rewrite"["xorBoolFalseRight"[a]],
			"Introduce"[b, rest, ih, a, s],
			"Change"["lastBit"["scanFrom"["xorBool"[s, a], Prepend[b][rest]]] == "xorBool"[s, "xorBool"[a, "parityBits"[Prepend[b][rest]]]]],
			"Rewrite"[ih[b, "xorBool"[s, a]]],
			"Exact"["xorBoolAssociativity"[s, a, "parityBits"[Prepend[b][rest]]]]
		}
	],
	machineTheorem["lastBitScanB",
		ForAll[{Typed[xs, {Booleans}]}, Implies[1 <= Length[xs], "lastBit"["scanB"[xs]] == "parityBits"[xs]]],
		{
			"Introduce"[xs], "Cases"[xs],
			"Introduce"[h], "Have"[h0, 1 <= 0], "Exact"[h], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"["falseElimination"[f]],
			"Introduce"[a, rest, h], "Exact"["lastBitScanFrom"[rest, a, "false"]]
		}
	],
	(* stepR, unitBits, pow2, rowBits, Frobenius identity *)
	TypeTheoryDefinition["stepR", Typed[Function[{Typed[xs, {Booleans}]}, "xorBits"["shiftR"[xs], xs]], {Booleans} -> {Booleans}]],
	TypeTheoryDefinition["unitBits", Typed[Function[{Typed[n, NonNegativeIntegers]}, Prepend["true"]["zerosBits"[Subtract[n, 1]]]], NonNegativeIntegers -> {Booleans}]],
	TypeTheoryDefinition["pow2", Typed[
		Function[{Typed[w, NonNegativeIntegers]},
			InductiveRecursor[NonNegativeIntegers][Function[{Typed[q, NonNegativeIntegers]}, NonNegativeIntegers], 1,
				Function[{Typed[k, NonNegativeIntegers], Typed[prev, NonNegativeIntegers]}, prev + prev], w]],
		NonNegativeIntegers -> NonNegativeIntegers
	]],
	machineTheorem["pow2Pos",
		ForAll[{Typed[w, NonNegativeIntegers]}, 1 <= "pow2"[w]],
		{
			"Introduce"[w], "Induction"[w], "Exact"["lessEqualReflexivity"],
			"Introduce"[k, ih], "Change"[1 <= "pow2"[k] + "pow2"[k]], "LinearArithmetic"
		}
	],
	TypeTheoryDefinition["rowBits", Typed[
		Function[{Typed[n, NonNegativeIntegers], Typed[i, NonNegativeIntegers]}, "iterateFn"["stepR", i, "unitBits"[n]]],
		NonNegativeIntegers -> NonNegativeIntegers -> {Booleans}
	]],
	machineTheorem["lengthUnitBits",
		ForAll[{Typed[n, NonNegativeIntegers]}, Implies[1 <= n, Length["unitBits"[n]] == n]],
		{
			"Introduce"[n], "Cases"[n],
			"Introduce"[h], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"["falseElimination"[f]],
			"Introduce"[m, h],
			"Change"[Length["zerosBits"[m]] + 1 == m + 1],
			"Rewrite"["lengthZerosBits"[m]]
		}
	],
	machineTheorem["lengthStepR",
		ForAll[{Typed[xs, {Booleans}]}, Length["stepR"[xs]] == Length[xs]],
		{
			"Introduce"[xs],
			"Change"[Length["xorBits"["shiftR"[xs], xs]] == Length[xs]],
			"Rewrite"["lengthXorBits"["shiftR"[xs], xs, "lengthShiftR"[xs]]],
			"Exact"["lengthShiftR"[xs]]
		}
	],
	machineTheorem["lengthIterateStepR",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[xs, {Booleans}]}, Length["iterateFn"["stepR", m, xs]] == Length[xs]],
		{
			"Introduce"[m, xs], "Induction"[m], "Reflexivity",
			"Introduce"[k, ih], "Change"[Length["stepR"["iterateFn"["stepR", k, xs]]] == Length[xs]],
			"Rewrite"["lengthStepR"["iterateFn"["stepR", k, xs]]], "Exact"[ih]
		}
	],
	machineTheorem["lengthIterateShiftR",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[xs, {Booleans}]}, Length["iterateFn"["shiftR", m, xs]] == Length[xs]],
		{
			"Introduce"[m, xs], "Induction"[m], "Reflexivity",
			"Introduce"[k, ih], "Change"[Length["shiftR"["iterateFn"["shiftR", k, xs]]] == Length[xs]],
			"Rewrite"["lengthShiftR"["iterateFn"["shiftR", k, xs]]], "Exact"[ih]
		}
	],
	machineTheorem["lengthRowBits",
		ForAll[{Typed[n, NonNegativeIntegers], Typed[i, NonNegativeIntegers]}, Implies[1 <= n, Length["rowBits"[n, i]] == n]],
		{
			"Introduce"[n, i, hn],
			"Change"[Length["iterateFn"["stepR", i, "unitBits"[n]]] == n],
			"Rewrite"["lengthIterateStepR"[i, "unitBits"[n]]],
			"Exact"["lengthUnitBits"[n, hn]]
		}
	],
	machineTheorem["stepRXor",
		ForAll[{Typed[xs, {Booleans}], Typed[ys, {Booleans}]},
			Implies[Length[xs] == Length[ys], "stepR"["xorBits"[xs, ys]] == "xorBits"["stepR"[xs], "stepR"[ys]]]],
		{
			"Introduce"[xs, ys, hl],
			"Change"["xorBits"["shiftR"["xorBits"[xs, ys]], "xorBits"[xs, ys]] == "xorBits"["xorBits"["shiftR"[xs], xs], "xorBits"["shiftR"[ys], ys]]],
			"Rewrite"["shiftRXor"[xs, ys, hl]],
			"Rewrite"["xorBitsAssociativity"["shiftR"[xs], "shiftR"[ys], "xorBits"[xs, ys]]],
			"Rewrite"["xorBitsAssociativity"["shiftR"[xs], xs, "xorBits"["shiftR"[ys], ys]]],
			"Have"[mid, "xorBits"["shiftR"[ys], "xorBits"[xs, ys]] == "xorBits"[xs, "xorBits"["shiftR"[ys], ys]]],
			"Rewrite"["equalitySymmetry"["xorBitsAssociativity"["shiftR"[ys], xs, ys]]],
			"Rewrite"["xorBitsCommutativity"["shiftR"[ys], xs]],
			"Exact"["xorBitsAssociativity"[xs, "shiftR"[ys], ys]],
			"Rewrite"[mid]
		}
	],
	machineTheorem["stepRShiftR",
		ForAll[{Typed[xs, {Booleans}]}, "stepR"["shiftR"[xs]] == "shiftR"["stepR"[xs]]],
		{
			"Introduce"[xs],
			"Exact"["equalitySymmetry"["shiftRXor"["shiftR"[xs], xs, "lengthShiftR"[xs]]]]
		}
	],
	machineTheorem["scanBStepR",
		ForAll[{Typed[xs, {Booleans}]}, "scanB"["stepR"[xs]] == "stepR"["scanB"[xs]]],
		{
			"Introduce"[xs],
			"Change"["scanB"["xorBits"["shiftR"[xs], xs]] == "xorBits"["shiftR"["scanB"[xs]], "scanB"[xs]]],
			"Rewrite"["scanBXor"["shiftR"[xs], xs, "lengthShiftR"[xs]]],
			"Rewrite"["scanBShiftR"[xs]]
		}
	],
	machineTheorem["scanBUnitBits",
		ForAll[{Typed[n, NonNegativeIntegers]}, Implies[1 <= n, "scanB"["unitBits"[n]] == "onesBits"[n]]],
		{
			"Introduce"[n], "Cases"[n],
			"Introduce"[h], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"["falseElimination"[f]],
			"Introduce"[m, h],
			"Change"[Prepend["true"]["scanFrom"["true", "zerosBits"[m]]] == Prepend["true"]["replicateBool"[m, "true"]]],
			"Rewrite"["scanFromZeros"[m, "true"]]
		}
	],
	machineTheorem["stepROnesBits",
		ForAll[{Typed[n, NonNegativeIntegers]}, Implies[1 <= n, "stepR"["onesBits"[n]] == "unitBits"[n]]],
		{
			"Introduce"[n], "Cases"[n],
			"Introduce"[h], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"["falseElimination"[f]],
			"Introduce"[m, h],
			"Change"["xorBits"["dropLastBits"[Prepend["false"]["onesBits"[m + 1]]], Prepend["true"]["onesBits"[m]]] == Prepend["true"]["zerosBits"[m]]],
			"Change"["xorBits"[Prepend["false"]["dropLastBits"["onesBits"[m + 1]]], Prepend["true"]["onesBits"[m]]] == Prepend["true"]["zerosBits"[m]]],
			"Rewrite"["dropLastBitsOnes"[m]],
			"Change"[Prepend["true"]["xorBits"["onesBits"[m], "onesBits"[m]]] == Prepend["true"]["zerosBits"[m]]],
			"Rewrite"["xorBitsSelf"["onesBits"[m]]],
			"Rewrite"["lengthOnesBits"[m]]
		}
	],
	machineTheorem["scanBRowSucc",
		ForAll[{Typed[n, NonNegativeIntegers], Typed[i, NonNegativeIntegers]},
			Implies[1 <= n, "scanB"["rowBits"[n, i + 1]] == "rowBits"[n, i]]],
		{
			"Introduce"[n, i, hn], "Induction"[i],
			"Change"["scanB"["stepR"["unitBits"[n]]] == "unitBits"[n]],
			"Rewrite"["scanBStepR"["unitBits"[n]]],
			"Rewrite"["scanBUnitBits"[n, hn]],
			"Exact"["stepROnesBits"[n, hn]],
			"Introduce"[k, ih],
			"Change"["scanB"["stepR"["rowBits"[n, k + 1]]] == "stepR"["rowBits"[n, k]]],
			"Rewrite"["scanBStepR"["rowBits"[n, k + 1]]],
			"Rewrite"[ih]
		}
	],
	machineTheorem["scanBIterateRow",
		ForAll[{Typed[n, NonNegativeIntegers], Typed[k, NonNegativeIntegers], Typed[i, NonNegativeIntegers]},
			Implies[1 <= n, Implies[k <= i, "iterateFn"["scanB", k, "rowBits"[n, i]] == "rowBits"[n, Subtract[i, k]]]]],
		{
			"Introduce"[n, k], "Induction"[k],
			"Introduce"[i, hn, h0], "Reflexivity",
			"Introduce"[m, ih, i, hn, hm],
			"Cases"["lessEqualExists"[m + 1, i, hm]], "Introduce"[d, eqI],
			"Have"[eqI2, i == (d + m) + 1], "LinearArithmetic",
			"Rewrite"[eqI2],
			"Rewrite"["iterateFnStep"["scanB", m, "rowBits"[n, (d + m) + 1]]],
			"Rewrite"["scanBRowSucc"[n, d + m, hn]],
			"Have"[leM, m <= d + m], "LinearArithmetic",
			"Rewrite"[ih[d + m, hn, leM]],
			"Have"[eqS1, Subtract[d + m, m] == d], "Exact"["additionSubtractionCancellation"[d, m]],
			"Have"[eqS2, Subtract[(d + m) + 1, m + 1] == d],
			"Have"[t, (d + m) + 1 == d + (m + 1)], "LinearArithmetic", "Rewrite"[t],
			"Exact"["additionSubtractionCancellation"[d, m + 1]],
			"Rewrite"[eqS1], "Rewrite"[eqS2]
		}
	],
	machineTheorem["iterateStepRXor",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[xs, {Booleans}], Typed[ys, {Booleans}]},
			Implies[Length[xs] == Length[ys], "iterateFn"["stepR", m, "xorBits"[xs, ys]] == "xorBits"["iterateFn"["stepR", m, xs], "iterateFn"["stepR", m, ys]]]],
		{
			"Introduce"[m, xs, ys, hl], "Induction"[m], "Reflexivity",
			"Introduce"[k, ih],
			"Change"["stepR"["iterateFn"["stepR", k, "xorBits"[xs, ys]]] == "xorBits"["stepR"["iterateFn"["stepR", k, xs]], "stepR"["iterateFn"["stepR", k, ys]]]],
			"Rewrite"[ih],
			"Have"[hlk, Length["iterateFn"["stepR", k, xs]] == Length["iterateFn"["stepR", k, ys]]],
			"Rewrite"["lengthIterateStepR"[k, xs]], "Rewrite"["lengthIterateStepR"[k, ys]], "Exact"[hl],
			"Exact"["stepRXor"["iterateFn"["stepR", k, xs], "iterateFn"["stepR", k, ys], hlk]]
		}
	],
	machineTheorem["iterateShiftRXor",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[xs, {Booleans}], Typed[ys, {Booleans}]},
			Implies[Length[xs] == Length[ys], "iterateFn"["shiftR", m, "xorBits"[xs, ys]] == "xorBits"["iterateFn"["shiftR", m, xs], "iterateFn"["shiftR", m, ys]]]],
		{
			"Introduce"[m, xs, ys, hl], "Induction"[m], "Reflexivity",
			"Introduce"[k, ih],
			"Change"["shiftR"["iterateFn"["shiftR", k, "xorBits"[xs, ys]]] == "xorBits"["shiftR"["iterateFn"["shiftR", k, xs]], "shiftR"["iterateFn"["shiftR", k, ys]]]],
			"Rewrite"[ih],
			"Have"[hlk, Length["iterateFn"["shiftR", k, xs]] == Length["iterateFn"["shiftR", k, ys]]],
			"Rewrite"["lengthIterateShiftR"[k, xs]], "Rewrite"["lengthIterateShiftR"[k, ys]], "Exact"[hl],
			"Exact"["shiftRXor"["iterateFn"["shiftR", k, xs], "iterateFn"["shiftR", k, ys], hlk]]
		}
	],
	machineTheorem["stepRIterateShiftR",
		ForAll[{Typed[k, NonNegativeIntegers], Typed[xs, {Booleans}]},
			"stepR"["iterateFn"["shiftR", k, xs]] == "iterateFn"["shiftR", k, "stepR"[xs]]],
		{
			"Introduce"[k, xs], "Induction"[k], "Reflexivity",
			"Introduce"[m, ih],
			"Change"["stepR"["shiftR"["iterateFn"["shiftR", m, xs]]] == "shiftR"["iterateFn"["shiftR", m, "stepR"[xs]]]],
			"Rewrite"["stepRShiftR"["iterateFn"["shiftR", m, xs]]], "Rewrite"[ih]
		}
	],
	machineTheorem["iterateStepRIterateShiftR",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[k, NonNegativeIntegers], Typed[xs, {Booleans}]},
			"iterateFn"["stepR", m, "iterateFn"["shiftR", k, xs]] == "iterateFn"["shiftR", k, "iterateFn"["stepR", m, xs]]],
		{
			"Introduce"[m, k, xs], "Induction"[m], "Reflexivity",
			"Introduce"[j, ih],
			"Change"["stepR"["iterateFn"["stepR", j, "iterateFn"["shiftR", k, xs]]] == "iterateFn"["shiftR", k, "stepR"["iterateFn"["stepR", j, xs]]]],
			"Rewrite"[ih], "Exact"["stepRIterateShiftR"[k, "iterateFn"["stepR", j, xs]]]
		}
	],
	(* Frobenius identity over GF(2): stepR^[2^w] x = shiftR^[2^w] x XOR x *)
	machineTheorem["stepRIteratePow2",
		ForAll[{Typed[w, NonNegativeIntegers], Typed[xs, {Booleans}]},
			"iterateFn"["stepR", "pow2"[w], xs] == "xorBits"["iterateFn"["shiftR", "pow2"[w], xs], xs]],
		{
			"Introduce"[w], "Induction"[w],
			"Introduce"[xs], "Reflexivity",
			"Introduce"[k, ih, xs],
			"Have"[hl1, Length["iterateFn"["shiftR", "pow2"[k], xs]] == Length[xs]], "Exact"["lengthIterateShiftR"["pow2"[k], xs]],
			"Change"["iterateFn"["stepR", "pow2"[k] + "pow2"[k], xs] == "xorBits"["iterateFn"["shiftR", "pow2"[k] + "pow2"[k], xs], xs]],
			"Rewrite"["iterateFnAdd"["stepR", "pow2"[k], "pow2"[k], xs]],
			"Rewrite"[ih[xs]],
			"Rewrite"["iterateStepRXor"["pow2"[k], "iterateFn"["shiftR", "pow2"[k], xs], xs, hl1]],
			"Rewrite"["iterateStepRIterateShiftR"["pow2"[k], "pow2"[k], xs]],
			"Rewrite"[ih[xs]],
			"Rewrite"["iterateShiftRXor"["pow2"[k], "iterateFn"["shiftR", "pow2"[k], xs], xs, hl1]],
			"Rewrite"["equalitySymmetry"["iterateFnAdd"["shiftR", "pow2"[k], "pow2"[k], xs]]],
			"Rewrite"["xorBitsAssociativity"["iterateFn"["shiftR", "pow2"[k] + "pow2"[k], xs], "iterateFn"["shiftR", "pow2"[k], xs], "xorBits"["iterateFn"["shiftR", "pow2"[k], xs], xs]]],
			"Rewrite"["equalitySymmetry"["xorBitsAssociativity"["iterateFn"["shiftR", "pow2"[k], xs], "iterateFn"["shiftR", "pow2"[k], xs], xs]]],
			"Rewrite"["xorBitsSelf"["iterateFn"["shiftR", "pow2"[k], xs]]],
			"Rewrite"[hl1],
			"Rewrite"["xorBitsZerosLeft"[xs]]
		}
	],
	(* shiftR^[m] annihilates any bit list of length <= m *)
	machineTheorem["shiftRIterateZerosAux",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[k, NonNegativeIntegers], Typed[xs, {Booleans}]},
			Implies[Length[xs] <= m, "iterateFn"["shiftR", m, Join["zerosBits"[k], xs]] == "zerosBits"[k + Length[xs]]]],
		{
			"Introduce"[m], "Induction"[m],
			"Introduce"[k, xs], "Cases"[xs],
			"Introduce"[h], "Rewrite"["joinEmptyRight"["zerosBits"[k]]], "Reflexivity",
			"Introduce"[a, rest, h], "Have"[h2, Length[rest] + 1 <= 0], "Exact"[h], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"["falseElimination"[f]],
			"Introduce"[j, ih, k, xs, hle],
			"Rewrite"["iterateFnStep"["shiftR", j, Join["zerosBits"[k], xs]]],
			"Cases"[xs],
			"Introduce"[hle],
			"Have"[shZ, "shiftR"[Join["zerosBits"[k], Typed[{}, {Booleans}]]] == Join["zerosBits"[k], Typed[{}, {Booleans}]]],
			"Rewrite"["joinEmptyRight"["zerosBits"[k]]],
			"Exact"["dropLastBitsReplicate"[k, "false"]],
			"Rewrite"[shZ],
			"Have"[le0, Length[Typed[{}, {Booleans}]] <= j], "Change"[0 <= j], "LinearArithmetic",
			"Exact"[ih[k, Typed[{}, {Booleans}], le0]],
			"Introduce"[a, rest, hle],
			"Cases"["listSplitLast"[rest, a]],
			"Introduce"[ys, ex2], "Cases"[ex2], "Introduce"[lastB, ex3], "Cases"[ex3], "Introduce"[eqSplit, eqLenR],
			"Rewrite"[eqSplit],
			"Have"[shStep, "shiftR"[Join["zerosBits"[k], Join[ys, {lastB}]]] == Join["zerosBits"[k + 1], ys]],
			"Change"["dropLastBits"[Join["zerosBits"[k + 1], Join[ys, {lastB}]]] == Join["zerosBits"[k + 1], ys]],
			"Rewrite"["equalitySymmetry"["joinAssociativity"["zerosBits"[k + 1], ys, {lastB}]]],
			"Exact"["dropLastBitsJoinSingle"[Join["zerosBits"[k + 1], ys], lastB]],
			"Rewrite"[shStep],
			"Have"[hle2, Length[rest] + 1 <= j + 1], "Exact"[hle],
			"Have"[leY, Length[ys] <= j], "LinearArithmetic",
			"Rewrite"[ih[k + 1, ys, leY]],
			"Have"[eqK, (k + 1) + Length[ys] == k + Length[Join[ys, {lastB}]]],
			"Rewrite"["lengthJoin"[ys, {lastB}]], "Change"[(k + 1) + Length[ys] == k + (Length[ys] + 1)], "LinearArithmetic",
			"Rewrite"[eqK]
		}
	],
	machineTheorem["shiftRIterateZeros",
		ForAll[{Typed[m, NonNegativeIntegers], Typed[xs, {Booleans}]},
			Implies[Length[xs] <= m, "iterateFn"["shiftR", m, xs] == "zerosBits"[Length[xs]]]],
		{
			"Introduce"[m, xs, hle],
			"Rewrite"["equalitySymmetry"["additionZeroLeft"[Length[xs]]]],
			"Exact"["shiftRIterateZerosAux"[m, 0, xs, hle]]
		}
	],
	machineTheorem["rowBitsPow2",
		ForAll[{Typed[w, NonNegativeIntegers]}, "rowBits"["pow2"[w], "pow2"[w]] == "rowBits"["pow2"[w], 0]],
		{
			"Introduce"[w],
			"Change"["iterateFn"["stepR", "pow2"[w], "unitBits"["pow2"[w]]] == "unitBits"["pow2"[w]]],
			"Rewrite"["stepRIteratePow2"[w, "unitBits"["pow2"[w]]]],
			"Have"[hle, Length["unitBits"["pow2"[w]]] <= "pow2"[w]],
			"Rewrite"["lengthUnitBits"["pow2"[w], "pow2Pos"[w]]], "LinearArithmetic",
			"Rewrite"["shiftRIterateZeros"["pow2"[w], "unitBits"["pow2"[w]], hle]],
			"Exact"["xorBitsZerosLeft"["unitBits"["pow2"[w]]]]
		}
	],
	machineTheorem["scanBRowZero",
		ForAll[{Typed[w, NonNegativeIntegers]}, "scanB"["rowBits"["pow2"[w], 0]] == "rowBits"["pow2"[w], Subtract["pow2"[w], 1]]],
		{
			"Introduce"[w],
			"Rewrite"["equalitySymmetry"["rowBitsPow2"[w]]],
			"Cases"["lessEqualExists"[1, "pow2"[w], "pow2Pos"[w]]], "Introduce"[m, eqP],
			"Have"[subEq, Subtract["pow2"[w], 1] == m], "Rewrite"[eqP], "Exact"["additionSubtractionCancellation"[m, 1]],
			"Rewrite"[subEq],
			"Have"[eq1, "rowBits"["pow2"[w], "pow2"[w]] == "rowBits"["pow2"[w], m + 1]], "Rewrite"[eqP],
			"Rewrite"[eq1],
			"Exact"["scanBRowSucc"["pow2"[w], m, "pow2Pos"[w]]]
		}
	],
	machineTheorem["rowBitsLastOnes",
		ForAll[{Typed[w, NonNegativeIntegers]}, "rowBits"["pow2"[w], Subtract["pow2"[w], 1]] == "onesBits"["pow2"[w]]],
		{
			"Introduce"[w],
			"Rewrite"["equalitySymmetry"["scanBRowZero"[w]]],
			"Exact"["scanBUnitBits"["pow2"[w], "pow2Pos"[w]]]
		}
	],
	(* Trailing zeros of rowBits[n, i]: avoids any getElem indexing! *)
	machineTheorem["rowBitsTrailingZeros",
		ForAll[{Typed[i, NonNegativeIntegers], Typed[k, NonNegativeIntegers]},
			Exists[{Typed[p, {Booleans}]}, And[Length[p] == i + 1, "rowBits"[(i + 1) + k, i] == Join[p, "zerosBits"[k]]]]],
		{
			"Introduce"[i], "Induction"[i],
			"Introduce"[k],
			"Have"[subEq, Subtract[1 + k, 1] == k],
			"Have"[eq1, 1 + k == k + 1], "LinearArithmetic", "Rewrite"[eq1],
			"Exact"["additionSubtractionCancellation"[k, 1]],
			"Have"[eqU, "unitBits"[1 + k] == Join[{"true"}, "zerosBits"[k]]],
			"Change"[Prepend["true"]["zerosBits"[Subtract[1 + k, 1]]] == Prepend["true"]["zerosBits"[k]]],
			"Rewrite"[subEq],
			"Exact"["existsIntroduction"[{"true"}, "andIntroduction"["equalityReflexivity"[1], eqU]]],
			"Introduce"[j, ih, k],
			"Have"[eqSum, ((j + 1) + 1) + k == (j + 1) + (k + 1)], "LinearArithmetic",
			"Rewrite"[eqSum],
			"Cases"[ih[k + 1]], "Introduce"[p, hp], "Cases"[hp], "Introduce"[lenP, eqRow],
			"Have"[eqStep, "rowBits"[(j + 1) + (k + 1), j + 1] ==
				Join["xorBits"[Prepend["false"][p], Join[p, {"false"}]], "zerosBits"[k]]],
			"Change"["xorBits"["shiftR"["rowBits"[(j + 1) + (k + 1), j]], "rowBits"[(j + 1) + (k + 1), j]] ==
				Join["xorBits"[Prepend["false"][p], Join[p, {"false"}]], "zerosBits"[k]]],
			"Rewrite"[eqRow],
			"Have"[shEq, "shiftR"[Join[p, "zerosBits"[k + 1]]] == Join[Prepend["false"][p], "zerosBits"[k]]],
			"Change"["dropLastBits"[Join[Prepend["false"][p], Prepend["false"]["zerosBits"[k]]]] == Join[Prepend["false"][p], "zerosBits"[k]]],
			"Rewrite"["dropLastBitsJoinNonEmpty"[Prepend["false"][p], "false", "zerosBits"[k]]],
			"Change"[Join[Prepend["false"][p], "dropLastBits"["zerosBits"[k + 1]]] == Join[Prepend["false"][p], "zerosBits"[k]]],
			"Rewrite"["dropLastBitsZeros"[k]],
			"Have"[rhsEq, Join[p, "zerosBits"[k + 1]] == Join[Join[p, {"false"}], "zerosBits"[k]]],
			"Rewrite"["joinAssociativity"[p, {"false"}, "zerosBits"[k]]], "Reflexivity",
			"Rewrite"[shEq], "Rewrite"[rhsEq],
			"Have"[lenEq, Length[Prepend["false"][p]] == Length[Join[p, {"false"}]]],
			"Change"[Length[p] + 1 == Length[Join[p, {"false"}]]],
			"Rewrite"["lengthJoin"[p, {"false"}]], "Reflexivity",
			"Rewrite"["xorBitsJoin"[Prepend["false"][p], "zerosBits"[k], Join[p, {"false"}], "zerosBits"[k], lenEq]],
			"Rewrite"["xorBitsSelf"["zerosBits"[k]]],
			"Rewrite"["lengthZerosBits"[k]],
			"Have"[lenNew, Length["xorBits"[Prepend["false"][p], Join[p, {"false"}]]] == (j + 1) + 1],
			"Have"[lenEq2, Length[Prepend["false"][p]] == Length[Join[p, {"false"}]]],
			"Change"[Length[p] + 1 == Length[Join[p, {"false"}]]],
			"Rewrite"["lengthJoin"[p, {"false"}]], "Reflexivity",
			"Rewrite"["lengthXorBits"[Prepend["false"][p], Join[p, {"false"}], lenEq2]],
			"Change"[Length[p] + 1 == (j + 1) + 1], "LinearArithmetic",
			"Exact"["existsIntroduction"["xorBits"[Prepend["false"][p], Join[p, {"false"}]], "andIntroduction"[lenNew, eqStep]]]
		}
	],
	machineTheorem["lastBitRowBitsFalse",
		ForAll[{Typed[n, NonNegativeIntegers], Typed[i, NonNegativeIntegers]},
			Implies[(i + 1) + 1 <= n, "lastBit"["rowBits"[n, i]] == "false"]],
		{
			"Introduce"[n, i, hle],
			"Cases"["lessEqualExists"[(i + 1) + 1, n, hle]], "Introduce"[d, eqN],
			"Have"[eqN2, n == (i + 1) + (d + 1)], "LinearArithmetic",
			"Rewrite"[eqN2],
			"Cases"["rowBitsTrailingZeros"[i, d + 1]], "Introduce"[p, hp], "Cases"[hp], "Introduce"[lenP, eqRow],
			"Rewrite"[eqRow],
			"Have"[eqZ, "zerosBits"[d + 1] == Join["zerosBits"[d], {"false"}]],
			"Exact"["replicateBoolAdd"[d, 1, "false"]],
			"Rewrite"[eqZ],
			"Rewrite"["equalitySymmetry"["joinAssociativity"[p, "zerosBits"[d], {"false"}]]],
			"Exact"["lastBitJoinSingle"[Join[p, "zerosBits"[d]], "false"]]
		}
	],
	machineTheorem["parityRowBits",
		ForAll[{Typed[n, NonNegativeIntegers], Typed[i, NonNegativeIntegers]},
			Implies[1 <= n, Implies[i + 1 <= n, "parityBits"["rowBits"[n, i]] == Decide[i == 0]]]],
		{
			"Introduce"[n, i, hn], "Cases"[i],
			"Introduce"[h0],
			"Change"["xorBool"["true", "parityBits"["zerosBits"[Subtract[n, 1]]]] == "true"],
			"Rewrite"["parityBitsZeros"[Subtract[n, 1]]], "Reflexivity",
			"Introduce"[j, hle],
			"Have"[hNeq, Not[j + 1 == 0]], "Introduce"[e], "Exact"["successorNotZero"[j, e]],
			"Rewrite"["decideEqualFalse"[j + 1, 0, hNeq]],
			"Have"[hLen, 1 <= Length["rowBits"[n, j + 1]]],
			"Rewrite"["lengthRowBits"[n, j + 1, hn]], "Exact"[hn],
			"Rewrite"["equalitySymmetry"["lastBitScanB"["rowBits"[n, j + 1], hLen]]],
			"Rewrite"["scanBRowSucc"[n, j, hn]],
			"Exact"["lastBitRowBitsFalse"[n, j, hle]]
		}
	],
	(* parAt: parity at k-th B-scan *)
	TypeTheoryDefinition["parAt", Typed[
		Function[{Typed[xs, {Booleans}], Typed[k, NonNegativeIntegers]}, "parityBits"["iterateFn"["scanB", k, xs]]],
		{Booleans} -> NonNegativeIntegers -> Booleans
	]],
	machineTheorem["lengthIterateScanB",
		ForAll[{Typed[k, NonNegativeIntegers], Typed[xs, {Booleans}]}, Length["iterateFn"["scanB", k, xs]] == Length[xs]],
		{
			"Introduce"[k, xs], "Induction"[k], "Reflexivity",
			"Introduce"[m, ih], "Change"[Length["scanFrom"["false", "iterateFn"["scanB", m, xs]]] == Length[xs]],
			"Rewrite"["lengthScanFrom"["iterateFn"["scanB", m, xs], "false"]], "Exact"[ih]
		}
	],
	machineTheorem["iterateScanBXor",
		ForAll[{Typed[k, NonNegativeIntegers], Typed[xs, {Booleans}], Typed[ys, {Booleans}]},
			Implies[Length[xs] == Length[ys], "iterateFn"["scanB", k, "xorBits"[xs, ys]] == "xorBits"["iterateFn"["scanB", k, xs], "iterateFn"["scanB", k, ys]]]],
		{
			"Introduce"[k, xs, ys, hl], "Induction"[k], "Reflexivity",
			"Introduce"[m, ih],
			"Change"["scanB"["iterateFn"["scanB", m, "xorBits"[xs, ys]]] == "xorBits"["scanB"["iterateFn"["scanB", m, xs]], "scanB"["iterateFn"["scanB", m, ys]]]],
			"Rewrite"[ih],
			"Have"[hlm, Length["iterateFn"["scanB", m, xs]] == Length["iterateFn"["scanB", m, ys]]],
			"Rewrite"["lengthIterateScanB"[m, xs]], "Rewrite"["lengthIterateScanB"[m, ys]], "Exact"[hl],
			"Exact"["scanBXor"["iterateFn"["scanB", m, xs], "iterateFn"["scanB", m, ys], hlm]]
		}
	],
	machineTheorem["parAtXor",
		ForAll[{Typed[xs, {Booleans}], Typed[ys, {Booleans}], Typed[k, NonNegativeIntegers]},
			Implies[Length[xs] == Length[ys], "parAt"["xorBits"[xs, ys], k] == "xorBool"["parAt"[xs, k], "parAt"[ys, k]]]],
		{
			"Introduce"[xs, ys, k, hl],
			"Change"["parityBits"["iterateFn"["scanB", k, "xorBits"[xs, ys]]] == "xorBool"["parityBits"["iterateFn"["scanB", k, xs]], "parityBits"["iterateFn"["scanB", k, ys]]]],
			"Rewrite"["iterateScanBXor"[k, xs, ys, hl]],
			"Have"[hlk, Length["iterateFn"["scanB", k, xs]] == Length["iterateFn"["scanB", k, ys]]],
			"Rewrite"["lengthIterateScanB"[k, xs]], "Rewrite"["lengthIterateScanB"[k, ys]], "Exact"[hl],
			"Exact"["parityBitsXor"["iterateFn"["scanB", k, xs], "iterateFn"["scanB", k, ys], hlk]]
		}
	],
	machineTheorem["parAtScanB",
		ForAll[{Typed[xs, {Booleans}], Typed[k, NonNegativeIntegers]}, "parAt"["scanB"[xs], k] == "parAt"[xs, k + 1]],
		{
			"Introduce"[xs, k],
			"Change"["parityBits"["iterateFn"["scanB", k, "scanB"[xs]]] == "parityBits"["iterateFn"["scanB", k + 1, xs]]],
			"Rewrite"["iterateFnStep"["scanB", k, xs]]
		}
	],
	machineTheorem["parAtZeros",
		ForAll[{Typed[n, NonNegativeIntegers], Typed[k, NonNegativeIntegers]}, "parAt"["zerosBits"[n], k] == "false"],
		{
			"Introduce"[n, k],
			"Have"[itZ, "iterateFn"["scanB", k, "zerosBits"[n]] == "zerosBits"[n]],
			"Induction"[k], "Reflexivity",
			"Introduce"[m, ih], "Change"["scanFrom"["false", "iterateFn"["scanB", m, "zerosBits"[n]]] == "zerosBits"[n]],
			"Rewrite"[ih], "Exact"["scanFromZeros"[n, "false"]],
			"Change"["parityBits"["iterateFn"["scanB", k, "zerosBits"[n]]] == "false"],
			"Rewrite"[itZ], "Exact"["parityBitsZeros"[n]]
		}
	],
	machineTheorem["parAtRowBits",
		ForAll[{Typed[w, NonNegativeIntegers], Typed[i, NonNegativeIntegers], Typed[k, NonNegativeIntegers]},
			Implies[i + 1 <= "pow2"[w], Implies[k + 1 <= "pow2"[w], "parAt"["rowBits"["pow2"[w], i], k] == Decide[k == i]]]],
		{
			"Introduce"[w, i, k, hi, hk],
			"Cases"["lessEqualTotality"[k, i]],
			(* k <= i *)
			"Introduce"[kLeI],
			"Change"["parityBits"["iterateFn"["scanB", k, "rowBits"["pow2"[w], i]]] == Decide[k == i]],
			"Rewrite"["scanBIterateRow"["pow2"[w], k, i, "pow2Pos"[w], kLeI]],
			"Cases"["lessEqualExists"[k, i, kLeI]], "Introduce"[d, eqI],
			"Have"[subEq, Subtract[i, k] == d], "Rewrite"[eqI], "Exact"["additionSubtractionCancellation"[d, k]],
			"Rewrite"[subEq],
			"Have"[dLt, d + 1 <= "pow2"[w]], "LinearArithmetic",
			"Rewrite"["parityRowBits"["pow2"[w], d, "pow2Pos"[w], dLt]],
			"Cases"[d], "Introduce"[eqI, subEq, dLt],
			"Have"[eqKI, k == i], "LinearArithmetic",
			"Rewrite"["decideEqualTrue"[k, i, eqKI]], "Reflexivity",
			"Introduce"[d1, eqI, subEq, dLt],
			"Have"[neq1, Not[d1 + 1 == 0]], "Introduce"[e], "Exact"["successorNotZero"[d1, e]],
			"Have"[neq2, Not[k == i]], "Introduce"[e], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"[f],
			"Rewrite"["decideEqualFalse"[d1 + 1, 0, neq1]], "Rewrite"["decideEqualFalse"[k, i, neq2]],
			(* i < k, i.e., i + 1 <= k *)
			"Introduce"[iLtK],
			"Cases"["lessEqualExists"[i + 1, k, iLtK]], "Introduce"[d1, eqK],
			"Have"[neqKI, Not[k == i]], "Introduce"[e], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"[f],
			"Rewrite"["decideEqualFalse"[k, i, neqKI]],
			"Have"[eqK2, k == i + (d1 + 1)], "LinearArithmetic",
			"Change"["parityBits"["iterateFn"["scanB", k, "rowBits"["pow2"[w], i]]] == "false"],
			"Rewrite"[eqK2],
			"Rewrite"["iterateFnAdd"["scanB", i, d1 + 1, "rowBits"["pow2"[w], i]]],
			"Rewrite"["scanBIterateRow"["pow2"[w], i, i, "pow2Pos"[w], "lessEqualReflexivity"]],
			"Have"[s0, Subtract[i, i] == 0],
			"Exact"["equalityTransitivity"["equalityCongruence"[Function[{Typed[z, NonNegativeIntegers]}, Subtract[z, i]], "equalitySymmetry"["additionZeroLeft"[i]]], "additionSubtractionCancellation"[0, i]]],
			"Rewrite"[s0],
			"Rewrite"["iterateFnStep"["scanB", d1, "rowBits"["pow2"[w], 0]]],
			"Rewrite"["scanBRowZero"[w]],
			"Cases"["lessEqualExists"[1, "pow2"[w], "pow2Pos"[w]]], "Introduce"[p1, eqP],
			"Have"[subP, Subtract["pow2"[w], 1] == p1], "Rewrite"[eqP], "Exact"["additionSubtractionCancellation"[p1, 1]],
			"Rewrite"[subP],
			"Have"[d1LeP1, d1 <= p1], "LinearArithmetic",
			"Rewrite"["scanBIterateRow"["pow2"[w], d1, p1, "pow2Pos"[w], d1LeP1]],
			"Cases"["lessEqualExists"[d1, p1, d1LeP1]], "Introduce"[r, eqP1],
			"Have"[subR, Subtract[p1, d1] == r], "Rewrite"[eqP1], "Exact"["additionSubtractionCancellation"[r, d1]],
			"Rewrite"[subR],
			"Have"[rLt, r + 1 <= "pow2"[w]], "LinearArithmetic",
			"Rewrite"["parityRowBits"["pow2"[w], r, "pow2Pos"[w], rLt]],
			"Have"[neqR, Not[r == 0]], "Introduce"[e], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"[f],
			"Exact"["decideEqualFalse"[r, 0, neqR]]
		}
	],
	(* === Part B: System3Runs (zipper runs of lookaheadStep["system3"]) === *)
	TypeTheoryDefinition["toCell", Typed[
		Function[{Typed[b, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, "Color"], "color1", "color2", b]],
		Booleans -> "Color"
	]],
	TypeTheoryDefinition["ofBits", Typed[Function[{Typed[xs, {Booleans}]}, Map["toCell", xs]], {Booleans} -> {"Color"}]],
	TypeTheoryDefinition["stB", Typed[
		Function[{Typed[s, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, "LookaheadState"], "stateB", "stateC", s]],
		Booleans -> "LookaheadState"
	]],
	TypeTheoryDefinition["allNonZeroColors", Typed[
		Function[{Typed[P, {"Color"}]},
			InductiveRecursor[List][Function[{Typed[q, {"Color"}]}, TypeUniverse[0]], True,
				Function[{Typed[c, "Color"], Typed[rest, {"Color"}], Typed[prev, TypeUniverse[0]]},
					And[Not[c == "color0"], prev]], P]],
		{"Color"} -> TypeUniverse[0]
	]],
	machineTheorem["toCellNotZero",
		ForAll[{Typed[b, Booleans]}, Not["toCell"[b] == "color0"]],
		{
			"Introduce"[b], "Cases"[b],
			"Introduce"[eq],
			"Exact"[Construct["equalitySubstitution", "Color",
				Function[{Typed[c, "Color"]}, InductiveRecursor["Color"][Function[{Typed[q, "Color"]}, TypeUniverse[0]], False, True, False, c]],
				"color1", "color0", eq, "trueIntroduction"]],
			"Introduce"[eq],
			"Exact"[Construct["equalitySubstitution", "Color",
				Function[{Typed[c, "Color"]}, InductiveRecursor["Color"][Function[{Typed[q, "Color"]}, TypeUniverse[0]], False, False, True, c]],
				"color2", "color0", eq, "trueIntroduction"]]
		}
	],
	machineTheorem["ofBitsNonZero",
		ForAll[{Typed[xs, {Booleans}]}, "allNonZeroColors"["ofBits"[xs]]],
		{
			"Introduce"[xs], "Induction"[xs], "Exact"["trueIntroduction"],
			"Introduce"[b, rest, ih], "Exact"["andIntroduction"["toCellNotZero"[b], ih]]
		}
	],
	machineTheorem["ofBitsJoin",
		ForAll[{Typed[xs, {Booleans}], Typed[ys, {Booleans}]}, "ofBits"[Join[xs, ys]] == Join["ofBits"[xs], "ofBits"[ys]]],
		{"Introduce"[xs, ys], "Exact"["mapJoin"["toCell", xs, ys]]}
	],
	(* Walk left in state A over non-zero cells *)
	machineTheorem["sys3WalkLeft",
		ForAll[{Typed[P, {"Color"}], Typed[z, "Color"], Typed[L, {"Color"}], Typed[a, "Color"], Typed[R, {"Color"}]},
			Implies["allNonZeroColors"[P], Implies[Not[a == "color0"],
				"steps"["lookaheadStep"["system3"], Length[P] + 1, "lookaheadConfiguration"[Join[P, Prepend[z][L]], a, R, "stateA"]] ==
					"some"["lookaheadConfiguration"[L, z, "revAppend"[P, Prepend[a][R]], "stateA"]]]]],
		{
			"Introduce"[P], "Induction"[P],
			"Introduce"[z, L, a, R, hP, ha],
			"Cases"[a],
			"Introduce"[ha], "Exact"["falseElimination"[ha["equalityReflexivity"["color0"]]]],
			"Introduce"[ha], "Cases"[R], "Reflexivity", "Introduce"[r1, rRest], "Cases"[r1], "Reflexivity", "Reflexivity", "Reflexivity",
			"Introduce"[ha], "Cases"[R], "Reflexivity", "Introduce"[r1, rRest], "Cases"[r1], "Reflexivity", "Reflexivity", "Reflexivity",
			"Introduce"[c, rest, ih, z, L, a, R, hP, ha],
			"Cases"[hP], "Introduce"[hc, hRest],
			"Have"[step1, "lookaheadStep"["system3", "lookaheadConfiguration"[Prepend[c][Join[rest, Prepend[z][L]]], a, R, "stateA"]] ==
				"some"["lookaheadConfiguration"[Join[rest, Prepend[z][L]], c, Prepend[a][R], "stateA"]]],
			"Cases"[a],
			"Introduce"[ha], "Exact"["falseElimination"[ha["equalityReflexivity"["color0"]]]],
			"Introduce"[ha], "Cases"[R], "Reflexivity", "Introduce"[r1, rRest], "Cases"[r1], "Reflexivity", "Reflexivity", "Reflexivity",
			"Introduce"[ha], "Cases"[R], "Reflexivity", "Introduce"[r1, rRest], "Cases"[r1], "Reflexivity", "Reflexivity", "Reflexivity",
			"Have"[eqLen, Length[Prepend[c][rest]] + 1 == 1 + (Length[rest] + 1)], "Change"[(Length[rest] + 1) + 1 == 1 + (Length[rest] + 1)], "LinearArithmetic",
			"Rewrite"[eqLen],
			"Rewrite"["stepsAdd"["LookaheadConfiguration", "lookaheadStep"["system3"], 1, Length[rest] + 1,
				"lookaheadConfiguration"[Join[Prepend[c][rest], Prepend[z][L]], a, R, "stateA"]]],
			"Change"["optionBind"["lookaheadStep"["system3", "lookaheadConfiguration"[Prepend[c][Join[rest, Prepend[z][L]]], a, R, "stateA"]],
				Function[{Typed[y, "LookaheadConfiguration"]}, "steps"["lookaheadStep"["system3"], Length[rest] + 1, y]]] ==
				"some"["lookaheadConfiguration"[L, z, "revAppend"[rest, Prepend[c][Prepend[a][R]]], "stateA"]]],
			"Rewrite"[step1],
			"Exact"[ih[z, L, c, Prepend[a][R], hRest, hc]]
		}
	],
	machineTheorem["sys3TurnA",
		ForAll[{Typed[L, {"Color"}], Typed[b, "Color"], Typed[R, {"Color"}]},
			"lookaheadStep"["system3", "lookaheadConfiguration"[L, "color0", Prepend[b][R], "stateA"]] ==
				"some"["lookaheadConfiguration"[Prepend["color2"][L], b, R, "stateB"]]],
		{"Introduce"[L, b, R], "Cases"[b], "Reflexivity", "Reflexivity", "Reflexivity"}
	],
	machineTheorem["sys3StarB",
		ForAll[{Typed[c, "Color"], Typed[L, {"Color"}], Typed[R, {"Color"}]},
			"lookaheadStep"["system3", "lookaheadConfiguration"[Prepend[c][L], "color0", R, "stateB"]] ==
				"some"["lookaheadConfiguration"[L, c, Prepend["color2"][R], "stateA"]]],
		{"Introduce"[c, L, R], "Cases"[R], "Reflexivity", "Introduce"[r1, rRest], "Cases"[r1], "Reflexivity", "Reflexivity", "Reflexivity"}
	],
	machineTheorem["sys3ScanStep",
		ForAll[{Typed[L, {"Color"}], Typed[s, Booleans], Typed[a, Booleans], Typed[b, "Color"], Typed[R, {"Color"}]},
			Implies[Not[b == "color0"],
				"lookaheadStep"["system3", "lookaheadConfiguration"[L, "toCell"[a], Prepend[b][R], "stB"[s]]] ==
					"some"["lookaheadConfiguration"[Prepend["toCell"["xorBool"[s, a]]][L], b, R, "stB"["xorBool"[s, a]]]]]],
		{
			"Introduce"[L, s, a, b, R, hb],
			"Cases"[b], "Introduce"[hb], "Exact"["falseElimination"[hb["equalityReflexivity"["color0"]]]],
			"Introduce"[hb], "Cases"[s], "Cases"[a], "Reflexivity", "Reflexivity", "Cases"[a], "Reflexivity", "Reflexivity",
			"Introduce"[hb], "Cases"[s], "Cases"[a], "Reflexivity", "Reflexivity", "Cases"[a], "Reflexivity", "Reflexivity"
		}
	],
	machineTheorem["sys3ScanLastB",
		ForAll[{Typed[L, {"Color"}], Typed[s, Booleans], Typed[a, Booleans], Typed[R, {"Color"}]},
			Implies["xorBool"[s, a] == "false",
				"lookaheadStep"["system3", "lookaheadConfiguration"[L, "toCell"[a], Prepend["color0"][R], "stB"[s]]] ==
					"some"["lookaheadConfiguration"[Prepend["toCell"["xorBool"[s, a]]][L], "color0", R, "stateB"]]]],
		{
			"Introduce"[L, s, a, R, h],
			"Cases"[s], "Cases"[a], "Introduce"[h], "Reflexivity",
			"Introduce"[h], "Exact"["falseElimination"[Construct["equalitySubstitution", Booleans,
				Function[{Typed[q, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, TypeUniverse[0]], False, True, q]],
				"true", "false", h, "trueIntroduction"]]],
			"Cases"[a],
			"Introduce"[h], "Exact"["falseElimination"[Construct["equalitySubstitution", Booleans,
				Function[{Typed[q, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, TypeUniverse[0]], False, True, q]],
				"true", "false", h, "trueIntroduction"]]],
			"Introduce"[h], "Reflexivity"
		}
	],
	machineTheorem["sys3ScanLastC",
		ForAll[{Typed[L, {"Color"}], Typed[s, Booleans], Typed[a, Booleans], Typed[R, {"Color"}]},
			Implies["xorBool"[s, a] == "true",
				"lookaheadStep"["system3", "lookaheadConfiguration"[L, "toCell"[a], Prepend["color0"][R], "stB"[s]]] ==
					"some"["lookaheadConfiguration"[Prepend["color0"][L], "color0", R, "stateA"]]]],
		{
			"Introduce"[L, s, a, R, h],
			"Cases"[s], "Cases"[a],
			"Introduce"[h], "Exact"["falseElimination"[Construct["equalitySubstitution", Booleans,
				Function[{Typed[q, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, TypeUniverse[0]], True, False, q]],
				"false", "true", h, "trueIntroduction"]]],
			"Introduce"[h], "Reflexivity",
			"Cases"[a],
			"Introduce"[h], "Reflexivity",
			"Introduce"[h], "Exact"["falseElimination"[Construct["equalitySubstitution", Booleans,
				Function[{Typed[q, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, TypeUniverse[0]], True, False, q]],
				"false", "true", h, "trueIntroduction"]]]
		}
	],
	machineTheorem["sys3ScanBlock",
		ForAll[{Typed[x, {Booleans}], Typed[L, {"Color"}], Typed[s, Booleans], Typed[a, Booleans], Typed[c, "Color"], Typed[R, {"Color"}]},
			Implies[Not[c == "color0"],
				"steps"["lookaheadStep"["system3"], Length[x] + 1, "lookaheadConfiguration"[L, "toCell"[a], Join["ofBits"[x], Prepend[c][R]], "stB"[s]]] ==
					"some"["lookaheadConfiguration"["revAppend"["ofBits"["scanFrom"[s, Prepend[a][x]]], L], c, R, "stB"["xorBool"[s, "parityBits"[Prepend[a][x]]]]]]]],
		{
			"Introduce"[x], "Induction"[x],
			"Introduce"[L, s, a, c, R, hc],
			"Change"["lookaheadStep"["system3", "lookaheadConfiguration"[L, "toCell"[a], Prepend[c][R], "stB"[s]]] ==
				"some"["lookaheadConfiguration"[Prepend["toCell"["xorBool"[s, a]]][L], c, R, "stB"["xorBool"[s, "xorBool"[a, "false"]]]]]],
			"Rewrite"["xorBoolFalseRight"[a]],
			"Exact"["sys3ScanStep"[L, s, a, c, R, hc]],
			"Introduce"[b, rest, ih, L, s, a, c, R, hc],
			"Have"[eqLen, Length[Prepend[b][rest]] + 1 == 1 + (Length[rest] + 1)], "Change"[(Length[rest] + 1) + 1 == 1 + (Length[rest] + 1)], "LinearArithmetic",
			"Rewrite"[eqLen],
			"Rewrite"["stepsAdd"["LookaheadConfiguration", "lookaheadStep"["system3"], 1, Length[rest] + 1,
				"lookaheadConfiguration"[L, "toCell"[a], Join["ofBits"[Prepend[b][rest]], Prepend[c][R]], "stB"[s]]]],
			"Change"["optionBind"["lookaheadStep"["system3", "lookaheadConfiguration"[L, "toCell"[a], Prepend["toCell"[b]][Join["ofBits"[rest], Prepend[c][R]]], "stB"[s]]],
				Function[{Typed[y, "LookaheadConfiguration"]}, "steps"["lookaheadStep"["system3"], Length[rest] + 1, y]]] ==
				"some"["lookaheadConfiguration"["revAppend"["ofBits"["scanFrom"["xorBool"[s, a], Prepend[b][rest]]], Prepend["toCell"["xorBool"[s, a]]][L]], c, R,
					"stB"["xorBool"[s, "xorBool"[a, "parityBits"[Prepend[b][rest]]]]]]]],
			"Rewrite"["sys3ScanStep"[L, s, a, "toCell"[b], Join["ofBits"[rest], Prepend[c][R]], "toCellNotZero"[b]]],
			"Rewrite"["equalitySymmetry"["xorBoolAssociativity"[s, a, "parityBits"[Prepend[b][rest]]]]],
			"Exact"[ih[Prepend["toCell"["xorBool"[s, a]]][L], "xorBool"[s, a], b, c, R, hc]]
		}
	],
	machineTheorem["sys3ScanBlock0B",
		ForAll[{Typed[x, {Booleans}], Typed[L, {"Color"}], Typed[s, Booleans], Typed[a, Booleans], Typed[R, {"Color"}]},
			Implies["xorBool"[s, "parityBits"[Prepend[a][x]]] == "false",
				"steps"["lookaheadStep"["system3"], Length[x] + 1, "lookaheadConfiguration"[L, "toCell"[a], Join["ofBits"[x], Prepend["color0"][R]], "stB"[s]]] ==
					"some"["lookaheadConfiguration"["revAppend"["ofBits"["scanFrom"[s, Prepend[a][x]]], L], "color0", R, "stateB"]]]],
		{
			"Introduce"[x], "Induction"[x],
			"Introduce"[L, s, a, R, h],
			"Have"[h0, "xorBool"[s, a] == "false"],
			"Rewrite"["equalitySymmetry"["xorBoolFalseRight"[a]]], "Exact"[h],
			"Exact"["sys3ScanLastB"[L, s, a, R, h0]],
			"Introduce"[b, rest, ih, L, s, a, R, h],
			"Have"[hNext, "xorBool"["xorBool"[s, a], "parityBits"[Prepend[b][rest]]] == "false"],
			"Rewrite"["xorBoolAssociativity"[s, a, "parityBits"[Prepend[b][rest]]]], "Exact"[h],
			"Have"[eqLen, Length[Prepend[b][rest]] + 1 == 1 + (Length[rest] + 1)], "Change"[(Length[rest] + 1) + 1 == 1 + (Length[rest] + 1)], "LinearArithmetic",
			"Rewrite"[eqLen],
			"Rewrite"["stepsAdd"["LookaheadConfiguration", "lookaheadStep"["system3"], 1, Length[rest] + 1,
				"lookaheadConfiguration"[L, "toCell"[a], Join["ofBits"[Prepend[b][rest]], Prepend["color0"][R]], "stB"[s]]]],
			"Change"["optionBind"["lookaheadStep"["system3", "lookaheadConfiguration"[L, "toCell"[a], Prepend["toCell"[b]][Join["ofBits"[rest], Prepend["color0"][R]]], "stB"[s]]],
				Function[{Typed[y, "LookaheadConfiguration"]}, "steps"["lookaheadStep"["system3"], Length[rest] + 1, y]]] ==
				"some"["lookaheadConfiguration"["revAppend"["ofBits"["scanFrom"["xorBool"[s, a], Prepend[b][rest]]], Prepend["toCell"["xorBool"[s, a]]][L]], "color0", R, "stateB"]]],
			"Rewrite"["sys3ScanStep"[L, s, a, "toCell"[b], Join["ofBits"[rest], Prepend["color0"][R]], "toCellNotZero"[b]]],
			"Exact"[ih[Prepend["toCell"["xorBool"[s, a]]][L], "xorBool"[s, a], b, R, hNext]]
		}
	],
	machineTheorem["sys3ScanBlock0C",
		ForAll[{Typed[x, {Booleans}], Typed[L, {"Color"}], Typed[s, Booleans], Typed[a, Booleans], Typed[R, {"Color"}]},
			Implies["xorBool"[s, "parityBits"[Prepend[a][x]]] == "true",
				"steps"["lookaheadStep"["system3"], Length[x] + 1, "lookaheadConfiguration"[L, "toCell"[a], Join["ofBits"[x], Prepend["color0"][R]], "stB"[s]]] ==
					"some"["lookaheadConfiguration"[Prepend["color0"]["revAppend"["ofBits"["dropLastBits"["scanFrom"[s, Prepend[a][x]]]], L]], "color0", R, "stateA"]]]],
		{
			"Introduce"[x], "Induction"[x],
			"Introduce"[L, s, a, R, h],
			"Have"[h0, "xorBool"[s, a] == "true"],
			"Rewrite"["equalitySymmetry"["xorBoolFalseRight"[a]]], "Exact"[h],
			"Exact"["sys3ScanLastC"[L, s, a, R, h0]],
			"Introduce"[b, rest, ih, L, s, a, R, h],
			"Have"[hNext, "xorBool"["xorBool"[s, a], "parityBits"[Prepend[b][rest]]] == "true"],
			"Rewrite"["xorBoolAssociativity"[s, a, "parityBits"[Prepend[b][rest]]]], "Exact"[h],
			"Have"[eqLen, Length[Prepend[b][rest]] + 1 == 1 + (Length[rest] + 1)], "Change"[(Length[rest] + 1) + 1 == 1 + (Length[rest] + 1)], "LinearArithmetic",
			"Rewrite"[eqLen],
			"Rewrite"["stepsAdd"["LookaheadConfiguration", "lookaheadStep"["system3"], 1, Length[rest] + 1,
				"lookaheadConfiguration"[L, "toCell"[a], Join["ofBits"[Prepend[b][rest]], Prepend["color0"][R]], "stB"[s]]]],
			"Change"["optionBind"["lookaheadStep"["system3", "lookaheadConfiguration"[L, "toCell"[a], Prepend["toCell"[b]][Join["ofBits"[rest], Prepend["color0"][R]]], "stB"[s]]],
				Function[{Typed[y, "LookaheadConfiguration"]}, "steps"["lookaheadStep"["system3"], Length[rest] + 1, y]]] ==
				"some"["lookaheadConfiguration"[Prepend["color0"]["revAppend"["ofBits"["dropLastBits"["scanFrom"["xorBool"[s, a], Prepend[b][rest]]]], Prepend["toCell"["xorBool"[s, a]]][L]]], "color0", R, "stateA"]]],
			"Rewrite"["sys3ScanStep"[L, s, a, "toCell"[b], Join["ofBits"[rest], Prepend["color0"][R]], "toCellNotZero"[b]]],
			"Exact"[ih[Prepend["toCell"["xorBool"[s, a]]][L], "xorBool"[s, a], b, R, hNext]]
		}
	],

	(* Polymorphic list helpers: reverseList, tailList, headDefault *)
	TypeTheoryDefinition["reverseList", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[xs, {A}]}, "revAppend"[xs, Typed[{}, {A}]]],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, {A} -> {A}]
	]],
	TypeTheoryDefinition["tailList", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[xs, {A}]},
			InductiveRecursor[List][Function[{Typed[q, {A}]}, {A}], Typed[{}, {A}],
				Function[{Typed[h, A], Typed[t, {A}], Typed[u, {A}]}, t], xs]],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, {A} -> {A}]
	]],
	TypeTheoryDefinition["headBool", Typed[
		Function[{Typed[xs, {Booleans}]},
			InductiveRecursor[List][Function[{Typed[q, {Booleans}]}, Booleans], "false",
				Function[{Typed[h, Booleans], Typed[t, {Booleans}], Typed[u, Booleans]}, h], xs]],
		{Booleans} -> Booleans
	]],
	machineTheorem["reverseListJoin",
		ForAll[{TypedImplicit[A, TypeUniverse[1]], Typed[xs, {A}], Typed[ys, {A}]},
			"reverseList"[Join[xs, ys]] == Join["reverseList"[ys], "reverseList"[xs]]],
		{
			"Introduce"[A, xs, ys],
			"Change"["revAppend"[Join[xs, ys], Typed[{}, {A}]] == Join["revAppend"[ys, Typed[{}, {A}]], "revAppend"[xs, Typed[{}, {A}]]]],
			"Rewrite"["revAppendJoin"[xs, ys, Typed[{}, {A}]]],
			"Exact"["revAppendSplit"[ys, "revAppend"[xs, Typed[{}, {A}]]]]
		}
	],
	machineTheorem["reverseListInvolution",
		ForAll[{TypedImplicit[A, TypeUniverse[1]], Typed[xs, {A}]}, "reverseList"["reverseList"[xs]] == xs],
		{
			"Introduce"[A, xs],
			"Change"["revAppend"["revAppend"[xs, Typed[{}, {A}]], Typed[{}, {A}]] == xs],
			"Rewrite"["revAppendInvolution"[xs, Typed[{}, {A}]]],
			"Exact"["joinEmptyRight"[xs]]
		}
	],
	machineTheorem["reverseListPrepend",
		ForAll[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[xs, {A}]},
			"reverseList"[Prepend[x][xs]] == Join["reverseList"[xs], {x}]],
		{"Introduce"[A, x, xs], "Exact"["revAppendSplit"[xs, {x}]]}
	],
	machineTheorem["lengthReverseList",
		ForAll[{TypedImplicit[A, TypeUniverse[1]], Typed[xs, {A}]}, Length["reverseList"[xs]] == Length[xs]],
		{
			"Introduce"[A, xs],
			"Change"[Length["revAppend"[xs, Typed[{}, {A}]]] == Length[xs]],
			"Rewrite"["lengthRevAppend"[xs, Typed[{}, {A}]]], "Reflexivity"
		}
	],
	machineTheorem["revAppendMap",
		ForAll[{TypedImplicit[A, TypeUniverse[1]], TypedImplicit[B, TypeUniverse[1]], Typed[f, A -> B], Typed[xs, {A}], Typed[acc, {A}]},
			Map[f, "revAppend"[xs, acc]] == "revAppend"[Map[f, xs], Map[f, acc]]],
		{
			"Introduce"[A, B, f, xs], "Induction"[xs],
			"Introduce"[acc], "Reflexivity",
			"Introduce"[x, rest, ih, acc], "Exact"[ih[Prepend[x][acc]]]
		}
	],
	machineTheorem["ofBitsReverseList",
		ForAll[{Typed[xs, {Booleans}]}, "ofBits"["reverseList"[xs]] == "reverseList"["ofBits"[xs]]],
		{
			"Introduce"[xs],
			"Change"[Map["toCell", "revAppend"[xs, Typed[{}, {Booleans}]]] == "revAppend"[Map["toCell", xs], Typed[{}, {"Color"}]]],
			"Exact"["revAppendMap"["toCell", xs, Typed[{}, {Booleans}]]]
		}
	],
	machineTheorem["tailReverseListDropLast",
		ForAll[{Typed[xs, {Booleans}]}, "tailList"["reverseList"[xs]] == "reverseList"["dropLastBits"[xs]]],
		{
			"Introduce"[xs], "Cases"[xs], "Reflexivity",
			"Introduce"[a, rest],
			"Cases"["listSplitLast"[rest, a]], "Introduce"[init, h1], "Cases"[h1], "Introduce"[lastB, h2], "Cases"[h2], "Introduce"[eqSplit, eqLen],
			"Rewrite"[eqSplit],
			"Rewrite"["reverseListJoin"[init, {lastB}]],
			"Rewrite"["dropLastBitsJoinSingle"[init, lastB]],
			"Reflexivity"
		}
	],
	machineTheorem["tailOfBitsReverseDropLast",
		ForAll[{Typed[xs, {Booleans}]}, "tailList"["reverseList"["ofBits"[xs]]] == "reverseList"["ofBits"["dropLastBits"[xs]]]],
		{
			"Introduce"[xs],
			"Rewrite"["equalitySymmetry"["ofBitsReverseList"[xs]]],
			"Rewrite"["equalitySymmetry"["ofBitsReverseList"["dropLastBits"[xs]]]],
			"Rewrite"["equalitySymmetry"["tailReverseListDropLast"[xs]]],
			"Cases"["reverseList"[xs]], "Reflexivity", "Introduce"[h, t], "Reflexivity"
		}
	],
	machineTheorem["headReverseListLastBit",
		ForAll[{Typed[xs, {Booleans}]}, "headBool"["reverseList"[xs]] == "lastBit"[xs]],
		{
			"Introduce"[xs], "Induction"[xs], "Reflexivity",
			"Introduce"[a, rest, ih], "Cases"[rest], "Introduce"[ih], "Reflexivity",
			"Introduce"[b, rest2, ih],
			"Change"["headBool"["reverseList"[Prepend[a][Prepend[b][rest2]]]] == "lastBit"[Prepend[b][rest2]]],
			"Rewrite"["reverseListPrepend"[a, Prepend[b][rest2]]],
			"Cases"["listSplitLast"[rest2, b]], "Introduce"[init, h1], "Cases"[h1], "Introduce"[lastB, h2], "Cases"[h2], "Introduce"[eqSplit, eqLen],
			"Rewrite"[eqSplit],
			"Rewrite"["reverseListJoin"[init, {lastB}]],
			"Rewrite"["lastBitJoinSingle"[init, lastB]],
			"Reflexivity"
		}
	],
	(* First/last bit predicates *)
	TypeTheoryDefinition["firstTrue", Typed[
		Function[{Typed[xs, {Booleans}]},
			InductiveRecursor[List][Function[{Typed[q, {Booleans}]}, TypeUniverse[0]], False,
				Function[{Typed[a, Booleans], Typed[rest, {Booleans}], Typed[u, TypeUniverse[0]]}, a == "true"], xs]],
		{Booleans} -> TypeUniverse[0]
	]],
	TypeTheoryDefinition["lastTrue", Typed[
		Function[{Typed[xs, {Booleans}]}, "firstTrue"["reverseList"[xs]]],
		{Booleans} -> TypeUniverse[0]
	]],
	machineTheorem["firstTrueCons",
		ForAll[{Typed[xs, {Booleans}]}, Implies["firstTrue"[xs], Exists[{Typed[rest, {Booleans}]}, xs == Prepend["true"][rest]]]],
		{
			"Introduce"[xs], "Cases"[xs],
			"Introduce"[h], "Exact"["falseElimination"[h]],
			"Introduce"[a, rest, h],
			"Rewrite"[h],
			"Exact"["existsIntroduction"[rest, "equalityReflexivity"[Prepend["true"][rest]]]]
		}
	],
	machineTheorem["lastTrueFromLastBit",
		ForAll[{Typed[xs, {Booleans}]}, Implies[1 <= Length[xs], Implies["lastBit"[xs] == "true", "lastTrue"[xs]]]],
		{
			"Introduce"[xs, hLen, hLast],
			"Have"[hHead, "headBool"["reverseList"[xs]] == "true"],
			"Rewrite"["headReverseListLastBit"[xs]], "Exact"[hLast],
			"Have"[hLenRev, 1 <= Length["reverseList"[xs]]],
			"Rewrite"["lengthReverseList"[xs]], "Exact"[hLen],
			"Have"[gen, ForAll[{Typed[ys, {Booleans}]}, Implies[1 <= Length[ys], Implies["headBool"[ys] == "true", "firstTrue"[ys]]]]],
			"Introduce"[ys], "Cases"[ys],
			"Introduce"[h1, h2], "Have"[h0, 1 <= 0], "Exact"[h1], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"["falseElimination"[f]],
			"Introduce"[a, rest, h1, h2], "Exact"[h2],
			"Exact"[gen["reverseList"[xs], hLenRev, hHead]]
		}
	],
	(* === Abstract Configuration & Rep3 Definitions === *)
	TypeTheoryDefinition["decodesBits", Typed[
		Function[{Typed[x, {Booleans}], Typed[s, {NonNegativeIntegers}], Typed[k, NonNegativeIntegers]},
			ForAll[{Typed[j, NonNegativeIntegers]}, Implies[j + 1 <= k, "parAt"[x, j] == "memNat"[j, s]]]],
		{Booleans} -> {NonNegativeIntegers} -> NonNegativeIntegers -> TypeUniverse[0]
	]],
	TypeTheoryInductiveType["TapeItem", TypeUniverse[1], {
		"itemSet" -> ForAll[{Typed[bits, {Booleans}], Typed[set, {NonNegativeIntegers}]}, "TapeItem"],
		"itemStar" -> "TapeItem"
	}],
	TypeTheoryDefinition["itemToElem", Typed[
		Function[{Typed[it, "TapeItem"]},
			InductiveRecursor["TapeItem"][Function[{Typed[q, "TapeItem"]}, "System4Element"],
				Function[{Typed[x, {Booleans}], Typed[s, {NonNegativeIntegers}]}, "set4"[s]], "star4", it]],
		"TapeItem" -> "System4Element"
	]],
	TypeTheoryDefinition["itemOk", Typed[
		Function[{Typed[N, NonNegativeIntegers], Typed[k, NonNegativeIntegers], Typed[it, "TapeItem"]},
			InductiveRecursor["TapeItem"][Function[{Typed[q, "TapeItem"]}, TypeUniverse[0]],
				Function[{Typed[x, {Booleans}], Typed[s, {NonNegativeIntegers}]},
					And[Length[x] == N, And["strictlyIncreasing"[s], "decodesBits"[x, s, k]]]],
				True, it]],
		NonNegativeIntegers -> NonNegativeIntegers -> "TapeItem" -> TypeUniverse[0]
	]],
	TypeTheoryDefinition["allItemsOk", Typed[
		Function[{Typed[N, NonNegativeIntegers], Typed[k, NonNegativeIntegers], Typed[its, {"TapeItem"}]},
			InductiveRecursor[List][Function[{Typed[q, {"TapeItem"}]}, TypeUniverse[0]], True,
				Function[{Typed[it, "TapeItem"], Typed[rest, {"TapeItem"}], Typed[prev, TypeUniverse[0]]},
					And["itemOk"[N, k, it], prev]], its]],
		NonNegativeIntegers -> NonNegativeIntegers -> {"TapeItem"} -> TypeUniverse[0]
	]],
	TypeTheoryDefinition["renderR", Typed[
		Function[{Typed[dropFirst, Booleans], Typed[its, {"TapeItem"}]},
			InductiveRecursor[List][Function[{Typed[q, {"TapeItem"}]}, Booleans -> {"Color"}],
				Function[{Typed[d, Booleans]}, Typed[{}, {"Color"}]],
				Function[{Typed[it, "TapeItem"], Typed[rest, {"TapeItem"}], Typed[prev, Booleans -> {"Color"}]},
					Function[{Typed[d, Booleans]},
						InductiveRecursor["TapeItem"][Function[{Typed[q, "TapeItem"]}, {"Color"}],
							Function[{Typed[x, {Booleans}], Typed[s, {NonNegativeIntegers}]},
								InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, {"Color"}],
									Join["ofBits"[x], prev["false"]],
									Join["tailList"["ofBits"[x]], prev["false"]],
									d]],
							Prepend["color0"][prev["true"]],
							it]]], its][dropFirst]],
		Booleans -> {"TapeItem"} -> {"Color"}
	]],
	TypeTheoryDefinition["renderL", Typed[
		Function[{Typed[dropLast, Booleans], Typed[its, {"TapeItem"}]},
			InductiveRecursor[List][Function[{Typed[q, {"TapeItem"}]}, Booleans -> {"Color"}],
				Function[{Typed[d, Booleans]}, Typed[{}, {"Color"}]],
				Function[{Typed[it, "TapeItem"], Typed[rest, {"TapeItem"}], Typed[prev, Booleans -> {"Color"}]},
					Function[{Typed[d, Booleans]},
						InductiveRecursor["TapeItem"][Function[{Typed[q, "TapeItem"]}, {"Color"}],
							Function[{Typed[x, {Booleans}], Typed[s, {NonNegativeIntegers}]},
								InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, {"Color"}],
									Join["ofBits"["reverseList"[x]], prev["false"]],
									Join["tailList"["ofBits"["reverseList"[x]]], prev["false"]],
									d]],
							Prepend["color0"][prev["true"]],
							it]]], its][dropLast]],
		Booleans -> {"TapeItem"} -> {"Color"}
	]],
	TypeTheoryDefinition["replicateColor", Typed[
		Function[{Typed[n, NonNegativeIntegers], Typed[c, "Color"]},
			InductiveRecursor[NonNegativeIntegers][Function[{Typed[q, NonNegativeIntegers]}, {"Color"}], Typed[{}, {"Color"}],
				Function[{Typed[k, NonNegativeIntegers], Typed[prev, {"Color"}]}, Prepend[c][prev]], n]],
		NonNegativeIntegers -> "Color" -> {"Color"}
	]],
	TypeTheoryDefinition["leftEndRev", Typed[
		Function[{Typed[m, NonNegativeIntegers], Typed[t, NonNegativeIntegers]},
			Join["replicateColor"[t, "color1"], Prepend["color2"][Prepend["color2"]["replicateColor"[m, "color0"]]]]],
		NonNegativeIntegers -> NonNegativeIntegers -> {"Color"}
	]],
	TypeTheoryInductiveType["LeftEnd", TypeUniverse[1], {
		"leftEndZeros" -> ForAll[{Typed[m, NonNegativeIntegers], Typed[t, NonNegativeIntegers]}, "LeftEnd"],
		"leftEndJunk" -> ForAll[{Typed[cells, {"Color"}]}, "LeftEnd"]
	}],
	TypeTheoryDefinition["leftEndRender", Typed[
		Function[{Typed[le, "LeftEnd"]},
			InductiveRecursor["LeftEnd"][Function[{Typed[q, "LeftEnd"]}, {"Color"}],
				Function[{Typed[m, NonNegativeIntegers], Typed[t, NonNegativeIntegers]}, "leftEndRev"[m, t]],
				Function[{Typed[cells, {"Color"}]}, cells], le]],
		"LeftEnd" -> {"Color"}
	]],
	TypeTheoryDefinition["leftEndIsJunk", Typed[
		Function[{Typed[le, "LeftEnd"]},
			InductiveRecursor["LeftEnd"][Function[{Typed[q, "LeftEnd"]}, Booleans],
				Function[{Typed[m, NonNegativeIntegers], Typed[t, NonNegativeIntegers]}, "false"],
				Function[{Typed[cells, {"Color"}]}, "true"], le]],
		"LeftEnd" -> Booleans
	]],
	TypeTheoryInductiveType["Closing", TypeUniverse[1], {
		"closingOne" -> "Closing",
		"closingZero" -> ForAll[{Typed[cells, {"Color"}]}, "Closing"]
	}],
	TypeTheoryDefinition["closingRender", Typed[
		Function[{Typed[rc, "Closing"]},
			InductiveRecursor["Closing"][Function[{Typed[q, "Closing"]}, {"Color"}],
				{"color1"},
				Function[{Typed[cells, {"Color"}]}, Prepend["color0"][cells]], rc]],
		"Closing" -> {"Color"}
	]],
	TypeTheoryDefinition["safeC", Typed[
		Function[{Typed[h, NonNegativeIntegers], Typed[c, "System4Configuration"]},
			ForAll[{Typed[j, NonNegativeIntegers]}, Implies[j <= h,
				ForAll[{Typed[c2, "System4Configuration"]}, Implies["steps"["system4Step", j, c] == "some"[c2],
					Or[Not[c2[["left"]] == Typed[{}, {"System4Element"}]], c2[["state"]] == "state4C"]]]]]],
		NonNegativeIntegers -> "System4Configuration" -> TypeUniverse[0]
	]],
	machineTheorem["safeCStep",
		ForAll[{Typed[h, NonNegativeIntegers], Typed[c, "System4Configuration"], Typed[c2, "System4Configuration"]},
			Implies["system4Step"[c] == "some"[c2], Implies["safeC"[h + 1, c], "safeC"[h, c2]]]],
		{
			"Introduce"[h, c, c2, hs, hS, j, hj, c3, hc3],
			"Have"[jLe, 1 + j <= h + 1], "LinearArithmetic",
			"Have"[run, "steps"["system4Step", 1 + j, c] == "some"[c3]],
			"Rewrite"["stepsAdd"["System4Configuration", "system4Step", 1, j, c]],
			"Change"["optionBind"["system4Step"[c], Function[{Typed[y, "System4Configuration"]}, "steps"["system4Step", j, y]]] == "some"[c3]],
			"Rewrite"[hs], "Exact"[hc3],
			"Exact"[hS[1 + j, jLe, c3, run]]
		}
	],
	machineTheorem["safeCNow",
		ForAll[{Typed[h, NonNegativeIntegers], Typed[c, "System4Configuration"]},
			Implies["safeC"[h, c], Or[Not[c[["left"]] == Typed[{}, {"System4Element"}]], c[["state"]] == "state4C"]]],
		{"Introduce"[h, c, hS], "Exact"[hS[0, "lessEqualZero"[h], c, "equalityReflexivity"["some"[c]]]]}
	],
	TypeTheoryDefinition["leftEndOk", Typed[
		Function[{Typed[h, NonNegativeIntegers], Typed[c4, "System4Configuration"], Typed[le, "LeftEnd"]},
			InductiveRecursor["LeftEnd"][Function[{Typed[q, "LeftEnd"]}, TypeUniverse[0]],
				Function[{Typed[m, NonNegativeIntegers], Typed[t, NonNegativeIntegers]}, And[h <= m, 1 <= t]],
				Function[{Typed[cells, {"Color"}]}, "safeC"[h, c4]], le]],
		NonNegativeIntegers -> "System4Configuration" -> "LeftEnd" -> TypeUniverse[0]
	]],
	machineTheorem["leftEndOkStep",
		ForAll[{Typed[le, "LeftEnd"], Typed[h, NonNegativeIntegers], Typed[c4, "System4Configuration"], Typed[c4p, "System4Configuration"]},
			Implies["system4Step"[c4] == "some"[c4p], Implies["leftEndOk"[h + 1, c4, le], "leftEndOk"[h, c4p, le]]]],
		{
			"Introduce"[le, h, c4, c4p, hs], "Cases"[le],
			"Introduce"[m, t, hOk], "Cases"[hOk], "Introduce"[hm, ht],
			"Have"[hm2, h <= m], "LinearArithmetic", "Exact"["andIntroduction"[hm2, ht]],
			"Introduce"[cells, hOk], "Exact"["safeCStep"[h, c4, c4p, hs, hOk]]
		}
	],
	(* Head and list well-formedness predicates *)
	TypeTheoryDefinition["headSet", Typed[
		Function[{Typed[its, {"TapeItem"}]},
			InductiveRecursor[List][Function[{Typed[q, {"TapeItem"}]}, TypeUniverse[0]], False,
				Function[{Typed[it, "TapeItem"], Typed[rest, {"TapeItem"}], Typed[u, TypeUniverse[0]]},
					InductiveRecursor["TapeItem"][Function[{Typed[q, "TapeItem"]}, TypeUniverse[0]],
						Function[{Typed[x, {Booleans}], Typed[s, {NonNegativeIntegers}]}, True], False, it]], its]],
		{"TapeItem"} -> TypeUniverse[0]
	]],
	TypeTheoryDefinition["headFirstTrue", Typed[
		Function[{Typed[its, {"TapeItem"}]},
			InductiveRecursor[List][Function[{Typed[q, {"TapeItem"}]}, TypeUniverse[0]], False,
				Function[{Typed[it, "TapeItem"], Typed[rest, {"TapeItem"}], Typed[u, TypeUniverse[0]]},
					InductiveRecursor["TapeItem"][Function[{Typed[q, "TapeItem"]}, TypeUniverse[0]],
						Function[{Typed[x, {Booleans}], Typed[s, {NonNegativeIntegers}]}, "firstTrue"[x]], False, it]], its]],
		{"TapeItem"} -> TypeUniverse[0]
	]],
	TypeTheoryDefinition["headLastTrue", Typed[
		Function[{Typed[its, {"TapeItem"}]},
			InductiveRecursor[List][Function[{Typed[q, {"TapeItem"}]}, TypeUniverse[0]], False,
				Function[{Typed[it, "TapeItem"], Typed[rest, {"TapeItem"}], Typed[u, TypeUniverse[0]]},
					InductiveRecursor["TapeItem"][Function[{Typed[q, "TapeItem"]}, TypeUniverse[0]],
						Function[{Typed[x, {Booleans}], Typed[s, {NonNegativeIntegers}]}, "lastTrue"[x]], False, it]], its]],
		{"TapeItem"} -> TypeUniverse[0]
	]],
	TypeTheoryDefinition["leftLast", Typed[
		Function[{Typed[j, Booleans], Typed[ls, {"TapeItem"}]},
			Or["headLastTrue"[ls], And[ls == Typed[{}, {"TapeItem"}], j == "true"]]],
		Booleans -> {"TapeItem"} -> TypeUniverse[0]
	]],
	TypeTheoryDefinition["leftItemsOk", Typed[
		Function[{Typed[j, Booleans], Typed[ls, {"TapeItem"}]},
			InductiveRecursor[List][Function[{Typed[q, {"TapeItem"}]}, TypeUniverse[0]], True,
				Function[{Typed[it, "TapeItem"], Typed[rest, {"TapeItem"}], Typed[prev, TypeUniverse[0]]},
					InductiveRecursor["TapeItem"][Function[{Typed[q, "TapeItem"]}, TypeUniverse[0]],
						Function[{Typed[x, {Booleans}], Typed[s, {NonNegativeIntegers}]}, prev],
						And["leftLast"[j, rest], prev], it]], ls]],
		Booleans -> {"TapeItem"} -> TypeUniverse[0]
	]],
	TypeTheoryDefinition["rightItemsOk", Typed[
		Function[{Typed[rs, {"TapeItem"}]},
			InductiveRecursor[List][Function[{Typed[q, {"TapeItem"}]}, TypeUniverse[0]], True,
				Function[{Typed[it, "TapeItem"], Typed[rest, {"TapeItem"}], Typed[prev, TypeUniverse[0]]},
					InductiveRecursor["TapeItem"][Function[{Typed[q, "TapeItem"]}, TypeUniverse[0]],
						Function[{Typed[x, {Booleans}], Typed[s, {NonNegativeIntegers}]}, prev],
						And["headFirstTrue"[rest], prev], it]], rs]],
		{"TapeItem"} -> TypeUniverse[0]
	]],
	(* Focus3, AbstractConfig, acToSystem4 (direct zipper!), acToSystem3, acOk, system3Represents *)
	TypeTheoryInductiveType["Focus3", TypeUniverse[1], {
		"focusSetA" -> ForAll[{Typed[xl, {Booleans}], Typed[b, Booleans], Typed[xr, {Booleans}], Typed[set, {NonNegativeIntegers}]}, "Focus3"],
		"focusSetB" -> ForAll[{Typed[x0, Booleans], Typed[xRest, {Booleans}], Typed[set, {NonNegativeIntegers}]}, "Focus3"],
		"focusSetT" -> ForAll[{Typed[x1, Booleans], Typed[xRest, {Booleans}], Typed[set, {NonNegativeIntegers}]}, "Focus3"],
		"focusStar" -> "Focus3",
		"focusOff" -> "Focus3"
	}],
	TypeTheoryInductiveType["AbstractConfig", TypeUniverse[1], {
		"abstractConfig" -> ForAll[{
			Typed[ls, {"TapeItem"}], Typed[rs, {"TapeItem"}],
			Typed[le, "LeftEnd"], Typed[rc, "Closing"],
			Typed[st, "System4State"], Typed[foc, "Focus3"]
		}, "AbstractConfig"]
	}],
	TypeTheoryDefinition["st3", Typed[
		Function[{Typed[st, "System4State"]},
			InductiveRecursor["System4State"][Function[{Typed[q, "System4State"]}, "LookaheadState"],
				"stateA", "stateB", "stateC", st]],
		"System4State" -> "LookaheadState"
	]],
	TypeTheoryDefinition["acToSystem4", Typed[
		Function[{Typed[a, "AbstractConfig"]},
			InductiveRecursor["AbstractConfig"][Function[{Typed[q, "AbstractConfig"]}, "System4Configuration"],
				Function[{Typed[ls, {"TapeItem"}], Typed[rs, {"TapeItem"}], Typed[le, "LeftEnd"], Typed[rc, "Closing"], Typed[st, "System4State"], Typed[foc, "Focus3"]},
					InductiveRecursor["Focus3"][Function[{Typed[q, "Focus3"]}, "System4Configuration"],
						Function[{Typed[xl, {Booleans}], Typed[b, Booleans], Typed[xr, {Booleans}], Typed[s, {NonNegativeIntegers}]},
							"system4Configuration"[Map["itemToElem", ls], Prepend["set4"[s]][Map["itemToElem", rs]], st]],
						Function[{Typed[x0, Booleans], Typed[xRest, {Booleans}], Typed[s, {NonNegativeIntegers}]},
							"system4Configuration"[Map["itemToElem", ls], Prepend["set4"[s]][Map["itemToElem", rs]], st]],
						Function[{Typed[x1, Booleans], Typed[xRest, {Booleans}], Typed[s, {NonNegativeIntegers}]},
							"system4Configuration"[Map["itemToElem", ls], Prepend["set4"[s]][Map["itemToElem", rs]], st]],
						"system4Configuration"[Map["itemToElem", ls], Prepend["star4"][Map["itemToElem", rs]], st],
						"system4Configuration"[Map["itemToElem", ls], Map["itemToElem", rs], st],
						foc]], a]],
		"AbstractConfig" -> "System4Configuration"
	]],
	TypeTheoryDefinition["acToSystem3", Typed[
		Function[{Typed[a, "AbstractConfig"]},
			InductiveRecursor["AbstractConfig"][Function[{Typed[q, "AbstractConfig"]}, "LookaheadConfiguration"],
				Function[{Typed[ls, {"TapeItem"}], Typed[rs, {"TapeItem"}], Typed[le, "LeftEnd"], Typed[rc, "Closing"], Typed[st, "System4State"], Typed[foc, "Focus3"]},
					InductiveRecursor["Focus3"][Function[{Typed[q, "Focus3"]}, "LookaheadConfiguration"],
						Function[{Typed[xl, {Booleans}], Typed[b, Booleans], Typed[xr, {Booleans}], Typed[s, {NonNegativeIntegers}]},
							"lookaheadConfiguration"[Join["ofBits"[xl], Join["renderL"["false", ls], "leftEndRender"[le]]], "toCell"[b],
								Join["ofBits"[xr], Join["renderR"["false", rs], "closingRender"[rc]]], "stateA"]],
						Function[{Typed[x0, Booleans], Typed[xRest, {Booleans}], Typed[s, {NonNegativeIntegers}]},
							"lookaheadConfiguration"[Join["renderL"["false", ls], "leftEndRender"[le]], "toCell"[x0],
								Join["ofBits"[xRest], Join["renderR"["false", rs], "closingRender"[rc]]], "st3"[st]]],
						Function[{Typed[x1, Booleans], Typed[xRest, {Booleans}], Typed[s, {NonNegativeIntegers}]},
							"lookaheadConfiguration"[Prepend["color2"][Join["renderL"["false", ls], "leftEndRender"[le]]], "toCell"[x1],
								Join["ofBits"[xRest], Join["renderR"["false", rs], "closingRender"[rc]]], "stateB"]],
						InductiveRecursor["System4State"][Function[{Typed[q, "System4State"]}, "LookaheadConfiguration"],
							"lookaheadConfiguration"[Join["renderL"["true", ls], "leftEndRender"[le]], "color0", Join["renderR"["false", rs], "closingRender"[rc]], "stateA"],
							"lookaheadConfiguration"[Join["renderL"["false", ls], "leftEndRender"[le]], "color0", Join["renderR"["true", rs], "closingRender"[rc]], "stateB"],
							"lookaheadConfiguration"[Prepend["color0"][Join["renderL"["true", ls], "leftEndRender"[le]]], "color0", Join["renderR"["true", rs], "closingRender"[rc]], "stateA"],
							st],
						InductiveRecursor["Closing"][Function[{Typed[q, "Closing"]}, "LookaheadConfiguration"],
							"lookaheadConfiguration"[Join["renderL"["false", ls], "leftEndRender"[le]], "color1", Typed[{}, {"Color"}], "st3"[st]],
							Function[{Typed[cells, {"Color"}]},
								InductiveRecursor["System4State"][Function[{Typed[q, "System4State"]}, "LookaheadConfiguration"],
									"lookaheadConfiguration"[Join["renderL"["false", ls], "leftEndRender"[le]], "color0", cells, "stateB"],
									"lookaheadConfiguration"[Join["renderL"["false", ls], "leftEndRender"[le]], "color0", cells, "stateB"],
									"lookaheadConfiguration"[Prepend["color0"][Join["renderL"["true", ls], "leftEndRender"[le]]], "color0", cells, "stateA"],
									st]],
							rc],
						foc]], a]],
		"AbstractConfig" -> "LookaheadConfiguration"
	]],
	TypeTheoryDefinition["focusOk", Typed[
		Function[{Typed[N, NonNegativeIntegers], Typed[k, NonNegativeIntegers], Typed[j, Booleans],
				Typed[st, "System4State"], Typed[ls, {"TapeItem"}], Typed[rs, {"TapeItem"}], Typed[foc, "Focus3"]},
			InductiveRecursor["Focus3"][Function[{Typed[q, "Focus3"]}, TypeUniverse[0]],
				Function[{Typed[xl, {Booleans}], Typed[b, Booleans], Typed[xr, {Booleans}], Typed[s, {NonNegativeIntegers}]},
					And[st == "state4A", "itemOk"[N, k, "itemSet"[Join["reverseList"[xl], Prepend[b][xr]], s]]]],
				Function[{Typed[x0, Booleans], Typed[xRest, {Booleans}], Typed[s, {NonNegativeIntegers}]},
					And[Not[st == "state4A"], "itemOk"[N, k, "itemSet"[Prepend[x0][xRest], s]]]],
				Function[{Typed[x1, Booleans], Typed[xRest, {Booleans}], Typed[s, {NonNegativeIntegers}]},
					And[st == "state4C", And["strictlyIncreasing"[s],
						And[Length[Prepend["true"][Prepend[x1][xRest]]] == N,
							"decodesBits"[Prepend["true"][Prepend[x1][xRest]], "xorMerge"[{1}, s], k]]]]],
				InductiveRecursor["System4State"][Function[{Typed[q, "System4State"]}, TypeUniverse[0]],
					And["headLastTrue"[ls], "headSet"[rs]],
					And["headSet"[ls], "headFirstTrue"[rs]],
					And["leftLast"[j, ls], "headFirstTrue"[rs]],
					st],
				rs == Typed[{}, {"TapeItem"}],
				foc]],
		NonNegativeIntegers -> NonNegativeIntegers -> Booleans -> "System4State" -> {"TapeItem"} -> {"TapeItem"} -> "Focus3" -> TypeUniverse[0]
	]],
	TypeTheoryDefinition["acOk", Typed[
		Function[{Typed[w, NonNegativeIntegers], Typed[h, NonNegativeIntegers], Typed[a, "AbstractConfig"]},
			InductiveRecursor["AbstractConfig"][Function[{Typed[q, "AbstractConfig"]}, TypeUniverse[0]],
				Function[{Typed[ls, {"TapeItem"}], Typed[rs, {"TapeItem"}], Typed[le, "LeftEnd"], Typed[rc, "Closing"], Typed[st, "System4State"], Typed[foc, "Focus3"]},
					And[h + 3 <= "pow2"[w],
						And["leftEndOk"[h, "acToSystem4"["abstractConfig"[ls, rs, le, rc, st, foc]], le],
							And["allItemsOk"["pow2"[w], h + 1, ls],
								And["allItemsOk"["pow2"[w], h + 1, rs],
									And["leftItemsOk"["leftEndIsJunk"[le], ls],
										And["rightItemsOk"[rs],
											"focusOk"["pow2"[w], h + 1, "leftEndIsJunk"[le], st, ls, rs, foc]]]]]]]], a]],
		NonNegativeIntegers -> NonNegativeIntegers -> "AbstractConfig" -> TypeUniverse[0]
	]],
	TypeTheoryInductiveType["FueledSystem4", TypeUniverse[1], {
		"fueledSystem4" -> ForAll[{Typed[config, "System4Configuration"], Typed[budget, NonNegativeIntegers]}, "FueledSystem4"]
	}],
	TypeTheoryDefinition["fueledSystem4Step", Typed[
		Function[{Typed[fs, "FueledSystem4"]},
			InductiveRecursor["FueledSystem4"][Function[{Typed[q, "FueledSystem4"]}, Option["FueledSystem4"]],
				Function[{Typed[c, "System4Configuration"], Typed[h, NonNegativeIntegers]},
					InductiveRecursor[NonNegativeIntegers][Function[{Typed[q, NonNegativeIntegers]}, Option["FueledSystem4"]],
						Typed["none", Option["FueledSystem4"]],
						Function[{Typed[h1, NonNegativeIntegers], Typed[u, Option["FueledSystem4"]]},
							"optionMap"[Function[{Typed[c2, "System4Configuration"]}, "fueledSystem4"[c2, h1]], "system4Step"[c]]], h]], fs]],
		"FueledSystem4" -> Option["FueledSystem4"]
	]],
	TypeTheoryDefinition["system3Represents", Typed[
		Function[{Typed[w, NonNegativeIntegers], Typed[rc, "Closing"], Typed[fs, "FueledSystem4"], Typed[c3, "LookaheadConfiguration"]},
			Exists[{Typed[a, "AbstractConfig"]},
				And[a[["rc"]] == rc,
					And["acOk"[w, fs[["budget"]], a],
						And[c3 == "acToSystem3"[a], fs[["config"]] == "acToSystem4"[a]]]]]],
		NonNegativeIntegers -> "Closing" -> "FueledSystem4" -> "LookaheadConfiguration" -> TypeUniverse[0]
	]],
	(* === Rendering & monotonicity helpers === *)
	machineTheorem["renderROfHeadFirstTrue",
		ForAll[{Typed[rs, {"TapeItem"}]},
			Implies["headFirstTrue"[rs], Prepend["color2"]["renderR"["true", rs]] == "renderR"["false", rs]]],
		{
			"Introduce"[rs], "Cases"[rs],
			"Introduce"[h], "Exact"["falseElimination"[h]],
			"Introduce"[it, rest], "Cases"[it],
			"Introduce"[x, s, h],
			"Cases"["firstTrueCons"[x, h]], "Introduce"[xRest, eqX],
			"Rewrite"[eqX], "Reflexivity",
			"Introduce"[h], "Exact"["falseElimination"[h]]
		}
	],
	machineTheorem["renderLOfHeadLastTrue",
		ForAll[{Typed[ls, {"TapeItem"}]},
			Implies["headLastTrue"[ls], Prepend["color2"]["renderL"["true", ls]] == "renderL"["false", ls]]],
		{
			"Introduce"[ls], "Cases"[ls],
			"Introduce"[h], "Exact"["falseElimination"[h]],
			"Introduce"[it, rest], "Cases"[it],
			"Introduce"[x, s, h],
			"Cases"["firstTrueCons"["reverseList"[x], h]], "Introduce"[xr, eqR],
			"Change"[Prepend["color2"][Join["tailList"["ofBits"["reverseList"[x]]], "renderL"["false", rest]]] ==
				Join["ofBits"["reverseList"[x]], "renderL"["false", rest]]],
			"Rewrite"[eqR], "Reflexivity",
			"Introduce"[h], "Exact"["falseElimination"[h]]
		}
	],
	machineTheorem["decodesMono",
		ForAll[{Typed[x, {Booleans}], Typed[s, {NonNegativeIntegers}], Typed[j, NonNegativeIntegers], Typed[k, NonNegativeIntegers]},
			Implies["decodesBits"[x, s, k], Implies[j <= k, "decodesBits"[x, s, j]]]],
		{
			"Introduce"[x, s, j, k, h, hjk, i, hi],
			"Have"[hik, i + 1 <= k], "LinearArithmetic",
			"Exact"[h[i, hik]]
		}
	],
	machineTheorem["itemOkMono",
		ForAll[{Typed[N, NonNegativeIntegers], Typed[j, NonNegativeIntegers], Typed[k, NonNegativeIntegers], Typed[it, "TapeItem"]},
			Implies["itemOk"[N, k, it], Implies[j <= k, "itemOk"[N, j, it]]]],
		{
			"Introduce"[N, j, k, it], "Cases"[it],
			"Introduce"[x, s, h, hjk], "Cases"[h], "Introduce"[hl, h2], "Cases"[h2], "Introduce"[hs, hd],
			"Exact"["andIntroduction"[hl, "andIntroduction"[hs, "decodesMono"[x, s, j, k, hd, hjk]]]],
			"Introduce"[h, hjk], "Exact"["trueIntroduction"]
		}
	],
	machineTheorem["allItemsOkMono",
		ForAll[{Typed[N, NonNegativeIntegers], Typed[j, NonNegativeIntegers], Typed[k, NonNegativeIntegers], Typed[its, {"TapeItem"}]},
			Implies["allItemsOk"[N, k, its], Implies[j <= k, "allItemsOk"[N, j, its]]]],
		{
			"Introduce"[N, j, k, its], "Induction"[its],
			"Introduce"[h, hjk], "Exact"["trueIntroduction"],
			"Introduce"[it, rest, ih, h, hjk], "Cases"[h], "Introduce"[hit, hrest],
			"Exact"["andIntroduction"["itemOkMono"[N, j, k, it, hit, hjk], ih[hrest, hjk]]]
		}
	],
	(* === Decodes algebraic lemmas (pure Nat!) === *)
	machineTheorem["decodesParity",
		ForAll[{Typed[x, {Booleans}], Typed[s, {NonNegativeIntegers}], Typed[k, NonNegativeIntegers]},
			Implies["strictlyIncreasing"[s], Implies["decodesBits"[x, s, k + 1], "parityBits"[x] == "hasZero4"[s]]]],
		{
			"Introduce"[x, s, k, hs, h],
			"Have"[h0, 0 + 1 <= k + 1], "LinearArithmetic",
			"Rewrite"["hasZero4MemNat"[s, hs]],
			"Exact"[h[0, h0]]
		}
	],
	machineTheorem["decodesScanB",
		ForAll[{Typed[x, {Booleans}], Typed[s, {NonNegativeIntegers}], Typed[k, NonNegativeIntegers]},
			Implies["strictlyIncreasing"[s], Implies["decodesBits"[x, s, k + 1], "decodesBits"["scanB"[x], "decr4"[s], k]]]],
		{
			"Introduce"[x, s, k, hs, hd, j, hj],
			"Rewrite"["parAtScanB"[x, j]],
			"Rewrite"["memNatDecr4"[j, s, hs]],
			"Have"[hj1, (j + 1) + 1 <= k + 1], "LinearArithmetic",
			"Exact"[hd[j + 1, hj1]]
		}
	],
	machineTheorem["parAtToggleFirst",
		ForAll[{Typed[w, NonNegativeIntegers], Typed[a, Booleans], Typed[x, {Booleans}], Typed[j, NonNegativeIntegers]},
			Implies[Length[Prepend[a][x]] == "pow2"[w], Implies[j + 1 <= "pow2"[w],
				"parAt"[Prepend["xorBool"["true", a]][x], j] == "xorBool"["parAt"[Prepend[a][x], j], Decide[j == 0]]]]],
		{
			"Introduce"[w, a, x, j, hx, hj],
			"Have"[subLen, Length[x] == Subtract["pow2"[w], 1]],
			"Cases"["lessEqualExists"[1, "pow2"[w], "pow2Pos"[w]]], "Introduce"[m, eqP],
			"Have"[s1, Subtract["pow2"[w], 1] == m], "Rewrite"[eqP], "Exact"["additionSubtractionCancellation"[m, 1]],
			"Rewrite"[s1],
			"Have"[hx2, Length[x] + 1 == "pow2"[w]], "Exact"[hx],
			"LinearArithmetic",
			"Have"[hXor, Prepend["xorBool"["true", a]][x] == "xorBits"[Prepend[a][x], "unitBits"["pow2"[w]]]],
			"Change"[Prepend["xorBool"["true", a]][x] == Prepend["xorBool"[a, "true"]]["xorBits"[x, "zerosBits"[Subtract["pow2"[w], 1]]]]],
			"Rewrite"["equalitySymmetry"[subLen]],
			"Rewrite"["xorBitsZerosRight"[x]],
			"Rewrite"["xorBoolCommutativity"["true", a]],
			"Rewrite"[hXor],
			"Have"[hl, Length[Prepend[a][x]] == Length["unitBits"["pow2"[w]]]],
			"Rewrite"[hx], "Exact"["equalitySymmetry"["lengthUnitBits"["pow2"[w], "pow2Pos"[w]]]],
			"Rewrite"["parAtXor"[Prepend[a][x], "unitBits"["pow2"[w]], j, hl]],
			"Have"[hUnit, "parAt"["unitBits"["pow2"[w]], j] == Decide[j == 0]],
			"Exact"["parAtRowBits"[w, 0, j, "pow2Pos"[w], hj]],
			"Rewrite"[hUnit]
		}
	],
	machineTheorem["decodesScanC",
		ForAll[{Typed[w, NonNegativeIntegers], Typed[a, Booleans], Typed[x, {Booleans}], Typed[s, {NonNegativeIntegers}], Typed[k, NonNegativeIntegers]},
			Implies[Length[Prepend[a][x]] == "pow2"[w],
				Implies["strictlyIncreasing"[s],
					Implies[(k + 1) + 1 <= "pow2"[w],
						Implies["decodesBits"[Prepend[a][x], s, k + 1],
							"decodesBits"["scanFrom"["true", Prepend[a][x]], "decr4"[s], k]]]]]],
		{
			"Introduce"[w, a, x, s, k, hx, hs, hk, hd, j, hj],
			"Change"["parAt"["scanB"[Prepend["xorBool"["true", a]][x]], j] == "memNat"[j, "decr4"[s]]],
			"Rewrite"["parAtScanB"[Prepend["xorBool"["true", a]][x], j]],
			"Have"[hj1, (j + 1) + 1 <= "pow2"[w]], "LinearArithmetic",
			"Rewrite"["parAtToggleFirst"[w, a, x, j + 1, hx, hj1]],
			"Have"[neq0, Not[j + 1 == 0]], "Introduce"[e], "Exact"["successorNotZero"[j, e]],
			"Rewrite"["decideEqualFalse"[j + 1, 0, neq0]],
			"Rewrite"["xorBoolFalseRight"["parAt"[Prepend[a][x], j + 1]]],
			"Have"[hjK, (j + 1) + 1 <= k + 1], "LinearArithmetic",
			"Rewrite"[hd[j + 1, hjK]],
			"Exact"["equalitySymmetry"["memNatDecr4"[j, s, hs]]]
		}
	],
	machineTheorem["decodesTransient",
		ForAll[{Typed[w, NonNegativeIntegers], Typed[x, {Booleans}], Typed[s, {NonNegativeIntegers}], Typed[k, NonNegativeIntegers]},
			Implies[Length[Prepend["true"][x]] == "pow2"[w],
				Implies["strictlyIncreasing"[s],
					Implies[(k + 1) + 1 <= "pow2"[w],
						Implies["decodesBits"[Prepend["true"][x], "xorMerge"[{1}, s], k + 1],
							"decodesBits"[Prepend["true"]["scanFrom"["false", x]], "decr4"[s], k]]]]]],
		{
			"Introduce"[w, x, s, k, hx, hs, hk, hd, j, hj],
			"Have"[hl, Length[Prepend["false"]["scanFrom"["false", x]]] == "pow2"[w]],
			"Change"[Length["scanFrom"["false", x]] + 1 == "pow2"[w]],
			"Rewrite"["lengthScanFrom"[x, "false"]], "Exact"[hx],
			"Have"[hjW, j + 1 <= "pow2"[w]], "LinearArithmetic",
			"Have"[hj1W, (j + 1) + 1 <= "pow2"[w]], "LinearArithmetic",
			"Change"["parAt"[Prepend["xorBool"["true", "false"]]["scanFrom"["false", x]], j] == "memNat"[j, "decr4"[s]]],
			"Rewrite"["parAtToggleFirst"[w, "false", "scanFrom"["false", x], j, hl, hjW]],
			"Change"["xorBool"["parAt"["scanB"[Prepend["false"][x]], j], Decide[j == 0]] == "memNat"[j, "decr4"[s]]],
			"Rewrite"["parAtScanB"[Prepend["false"][x], j]],
			"Change"["xorBool"["parAt"[Prepend["xorBool"["true", "true"]][x], j + 1], Decide[j == 0]] == "memNat"[j, "decr4"[s]]],
			"Rewrite"["parAtToggleFirst"[w, "true", x, j + 1, hx, hj1W]],
			"Have"[neq0, Not[j + 1 == 0]], "Introduce"[e], "Exact"["successorNotZero"[j, e]],
			"Rewrite"["decideEqualFalse"[j + 1, 0, neq0]],
			"Rewrite"["xorBoolFalseRight"["parAt"[Prepend["true"][x], j + 1]]],
			"Have"[hjK, (j + 1) + 1 <= k + 1], "LinearArithmetic",
			"Rewrite"[hd[j + 1, hjK]],
			"Rewrite"["memNatDecr4"[j, s, hs]],
			"Rewrite"["memNatXorMerge"[j + 1, {1}, s, "trueIntroduction", hs]],
			"Cases"[j], "Introduce"[hj, hjW, hj1W, neq0, hjK],
			"Change"["xorBool"["xorBool"["true", "memNat"[1, s]], "true"] == "memNat"[1, s]],
			"Rewrite"["xorBoolCommutativity"["true", "memNat"[1, s]]],
			"Rewrite"["xorBoolAssociativity"["memNat"[1, s], "true", "true"]],
			"Rewrite"["xorBoolSelf"["true"]], "Exact"["xorBoolFalseRight"["memNat"[1, s]]],
			"Introduce"[j1, hj, hjW, hj1W, neq0, hjK],
			"Have"[n1, Not[(j1 + 1) + 1 == 1]], "Introduce"[e], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"[f],
			"Have"[n0, Not[j1 + 1 == 0]], "Introduce"[e], "Exact"["successorNotZero"[j1, e]],
			"Change"["xorBool"["xorBool"[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Booleans], "false", "true", Decide[(j1 + 1) + 1 == 1]], "memNat"[(j1 + 1) + 1, s]], Decide[j1 + 1 == 0]] == "memNat"[(j1 + 1) + 1, s]],
			"Rewrite"["decideEqualFalse"[(j1 + 1) + 1, 1, n1]],
			"Rewrite"["decideEqualFalse"[j1 + 1, 0, n0]],
			"Change"["xorBool"["memNat"[(j1 + 1) + 1, s], "false"] == "memNat"[(j1 + 1) + 1, s]],
			"Exact"["xorBoolFalseRight"["memNat"[(j1 + 1) + 1, s]]]
		}
	],
	machineTheorem["decodesXorOneTwice",
		ForAll[{Typed[x, {Booleans}], Typed[s, {NonNegativeIntegers}], Typed[k, NonNegativeIntegers]},
			Implies["strictlyIncreasing"[s], Implies["decodesBits"[x, s, k], "decodesBits"[x, "xorMerge"[{1}, "xorMerge"[{1}, s]], k]]]],
		{
			"Introduce"[x, s, k, hs, hd, j, hj],
			"Rewrite"[hd[j, hj]],
			"Rewrite"["memNatXorMerge"[j, {1}, "xorMerge"[{1}, s], "trueIntroduction", "xorMergeStrictlyIncreasing"[{1}, s, "trueIntroduction", hs]]],
			"Rewrite"["memNatXorMerge"[j, {1}, s, "trueIntroduction", hs]],
			"Rewrite"["equalitySymmetry"["xorBoolAssociativity"["memNat"[j, {1}], "memNat"[j, {1}], "memNat"[j, s]]]],
			"Rewrite"["xorBoolSelf"["memNat"[j, {1}]]], "Reflexivity"
		}
	],
	machineTheorem["decodesTransientParity",
		ForAll[{Typed[x, {Booleans}], Typed[s, {NonNegativeIntegers}], Typed[k, NonNegativeIntegers]},
			Implies["strictlyIncreasing"[s],
				Implies["decodesBits"[Prepend["true"][x], "xorMerge"[{1}, s], k + 1],
					"parityBits"[x] == "xorBool"["true", "hasZero4"[s]]]]],
		{
			"Introduce"[x, s, k, hs, hd],
			"Have"[hXorInc, "strictlyIncreasing"["xorMerge"[{1}, s]]],
			"Exact"["xorMergeStrictlyIncreasing"[{1}, s, "trueIntroduction", hs]],
			"Have"[p1, "parityBits"[Prepend["true"][x]] == "hasZero4"["xorMerge"[{1}, s]]],
			"Exact"["decodesParity"[Prepend["true"][x], "xorMerge"[{1}, s], k, hXorInc, hd]],
			"Have"[h0, "hasZero4"["xorMerge"[{1}, s]] == "hasZero4"[s]],
			"Rewrite"["hasZero4MemNat"["xorMerge"[{1}, s], hXorInc]],
			"Rewrite"["hasZero4MemNat"[s, hs]],
			"Have"[n01, Not[0 == 1]], "Introduce"[e], "Exact"["successorNotZero"[0, "equalitySymmetry"[e]]],
			"Exact"["memNatXorOneOther"[0, s, n01, hs]],
			"Have"[p2, "xorBool"["true", "parityBits"[x]] == "hasZero4"[s]],
			"Exact"["equalityTransitivity"[p1, h0]],
			"Rewrite"["equalitySymmetry"[p2]],
			"Rewrite"["equalitySymmetry"["xorBoolAssociativity"["true", "true", "parityBits"[x]]]],
			"Rewrite"["xorBoolSelf"["true"]], "Reflexivity"
		}
	],
	(* === Scan landing and afterScan === *)
	TypeTheoryDefinition["landing", Typed[
		Function[{Typed[L, {"Color"}], Typed[rs, {"TapeItem"}], Typed[rc, "Closing"], Typed[z, {Booleans}], Typed[e, Booleans]},
			InductiveRecursor[List][Function[{Typed[q, {"TapeItem"}]}, "LookaheadConfiguration"],
				InductiveRecursor["Closing"][Function[{Typed[q, "Closing"]}, "LookaheadConfiguration"],
					"lookaheadConfiguration"["revAppend"["ofBits"[z], L], "color1", Typed[{}, {"Color"}], "stB"[e]],
					Function[{Typed[cells, {"Color"}]},
						InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, "LookaheadConfiguration"],
							"lookaheadConfiguration"["revAppend"["ofBits"[z], L], "color0", cells, "stateB"],
							"lookaheadConfiguration"[Prepend["color0"]["revAppend"["ofBits"["dropLastBits"[z]], L]], "color0", cells, "stateA"],
							e]],
					rc],
				Function[{Typed[it, "TapeItem"], Typed[rsRest, {"TapeItem"}], Typed[u, "LookaheadConfiguration"]},
					InductiveRecursor["TapeItem"][Function[{Typed[q, "TapeItem"]}, "LookaheadConfiguration"],
						Function[{Typed[y, {Booleans}], Typed[U, {NonNegativeIntegers}]},
							"lookaheadConfiguration"["revAppend"["ofBits"[z], L], "toCell"["headBool"[y]],
								Join["tailList"["ofBits"[y]], Join["renderR"["false", rsRest], "closingRender"[rc]]], "stB"[e]]],
						InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, "LookaheadConfiguration"],
							"lookaheadConfiguration"["revAppend"["ofBits"[z], L], "color0", Join["renderR"["true", rsRest], "closingRender"[rc]], "stateB"],
							"lookaheadConfiguration"[Prepend["color0"]["revAppend"["ofBits"["dropLastBits"[z]], L]], "color0", Join["renderR"["true", rsRest], "closingRender"[rc]], "stateA"],
							e],
						it]], rs]],
		{"Color"} -> {"TapeItem"} -> "Closing" -> {Booleans} -> Booleans -> "LookaheadConfiguration"
	]],
	machineTheorem["scanRun",
		ForAll[{Typed[L, {"Color"}], Typed[s, Booleans], Typed[a, Booleans], Typed[x, {Booleans}], Typed[rs, {"TapeItem"}], Typed[rc, "Closing"]},
			Implies[ForAll[{Typed[y, {Booleans}], Typed[U, {NonNegativeIntegers}], Typed[rsRest, {"TapeItem"}]},
					Implies[rs == Prepend["itemSet"[y, U]][rsRest], 1 <= Length[y]]],
				"steps"["lookaheadStep"["system3"], Length[x] + 1,
					"lookaheadConfiguration"[L, "toCell"[a], Join["ofBits"[x], Join["renderR"["false", rs], "closingRender"[rc]]], "stB"[s]]] ==
				"some"["landing"[L, rs, rc, "scanFrom"[s, Prepend[a][x]], "xorBool"[s, "parityBits"[Prepend[a][x]]]]]]],
		{
			"Introduce"[L, s, a, x, rs, rc], "Cases"[rs],
			(* rs = {} *)
			"Introduce"[hrs], "Cases"[rc],
			"Change"["steps"["lookaheadStep"["system3"], Length[x] + 1,
				"lookaheadConfiguration"[L, "toCell"[a], Join["ofBits"[x], {"color1"}], "stB"[s]]] ==
				"some"["lookaheadConfiguration"["revAppend"["ofBits"["scanFrom"[s, Prepend[a][x]]], L], "color1", Typed[{}, {"Color"}], "stB"["xorBool"[s, "parityBits"[Prepend[a][x]]]]]]],
			"Exact"["sys3ScanBlock"[x, L, s, a, "color1", Typed[{}, {"Color"}], "toCellNotZero"["false"]]],
			"Introduce"[cells],
			"Cases"["boolEqTrueOrFalse"["xorBool"[s, "parityBits"[Prepend[a][x]]]]],
			"Introduce"[hFalse],
			"Change"["steps"["lookaheadStep"["system3"], Length[x] + 1,
				"lookaheadConfiguration"[L, "toCell"[a], Join["ofBits"[x], Prepend["color0"][cells]], "stB"[s]]] ==
				"some"[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, "LookaheadConfiguration"],
					"lookaheadConfiguration"["revAppend"["ofBits"["scanFrom"[s, Prepend[a][x]]], L], "color0", cells, "stateB"],
					"lookaheadConfiguration"[Prepend["color0"]["revAppend"["ofBits"["dropLastBits"["scanFrom"[s, Prepend[a][x]]]], L]], "color0", cells, "stateA"],
					"xorBool"[s, "parityBits"[Prepend[a][x]]]]]],
			"Rewrite"[hFalse],
			"Exact"["sys3ScanBlock0B"[x, L, s, a, cells, hFalse]],
			"Introduce"[hTrue],
			"Change"["steps"["lookaheadStep"["system3"], Length[x] + 1,
				"lookaheadConfiguration"[L, "toCell"[a], Join["ofBits"[x], Prepend["color0"][cells]], "stB"[s]]] ==
				"some"[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, "LookaheadConfiguration"],
					"lookaheadConfiguration"["revAppend"["ofBits"["scanFrom"[s, Prepend[a][x]]], L], "color0", cells, "stateB"],
					"lookaheadConfiguration"[Prepend["color0"]["revAppend"["ofBits"["dropLastBits"["scanFrom"[s, Prepend[a][x]]]], L]], "color0", cells, "stateA"],
					"xorBool"[s, "parityBits"[Prepend[a][x]]]]]],
			"Rewrite"[hTrue],
			"Exact"["sys3ScanBlock0C"[x, L, s, a, cells, hTrue]],
			(* rs = it :: rsRest *)
			"Introduce"[it, rsRest, hrs], "Cases"[it],
			(* it = itemSet[y, U] *)
			"Introduce"[y, U, hrs],
			"Have"[hyLen, 1 <= Length[y]], "Exact"[hrs[y, U, rsRest, "equalityReflexivity"[Prepend["itemSet"[y, U]][rsRest]]]],
			"Cases"[y],
			"Introduce"[hrs, hyLen], "Have"[h0, 1 <= 0], "Exact"[hyLen], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"["falseElimination"[f]],
			"Introduce"[y0, yRest, hrs, hyLen],
			"Change"["steps"["lookaheadStep"["system3"], Length[x] + 1,
				"lookaheadConfiguration"[L, "toCell"[a], Join["ofBits"[x], Join[Join[Prepend["toCell"[y0]]["ofBits"[yRest]], "renderR"["false", rsRest]], "closingRender"[rc]]], "stB"[s]]] ==
				"some"["lookaheadConfiguration"["revAppend"["ofBits"["scanFrom"[s, Prepend[a][x]]], L], "toCell"[y0],
					Join["ofBits"[yRest], Join["renderR"["false", rsRest], "closingRender"[rc]]], "stB"["xorBool"[s, "parityBits"[Prepend[a][x]]]]]]],
			"Rewrite"["joinAssociativity"[Prepend["toCell"[y0]]["ofBits"[yRest]], "renderR"["false", rsRest], "closingRender"[rc]]],
			"Exact"["sys3ScanBlock"[x, L, s, a, "toCell"[y0], Join["ofBits"[yRest], Join["renderR"["false", rsRest], "closingRender"[rc]]], "toCellNotZero"[y0]]],
			(* it = itemStar *)
			"Introduce"[hrs],
			"Cases"["boolEqTrueOrFalse"["xorBool"[s, "parityBits"[Prepend[a][x]]]]],
			"Introduce"[hFalse],
			"Change"["steps"["lookaheadStep"["system3"], Length[x] + 1,
				"lookaheadConfiguration"[L, "toCell"[a], Join["ofBits"[x], Prepend["color0"][Join["renderR"["true", rsRest], "closingRender"[rc]]]], "stB"[s]]] ==
				"some"[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, "LookaheadConfiguration"],
					"lookaheadConfiguration"["revAppend"["ofBits"["scanFrom"[s, Prepend[a][x]]], L], "color0", Join["renderR"["true", rsRest], "closingRender"[rc]], "stateB"],
					"lookaheadConfiguration"[Prepend["color0"]["revAppend"["ofBits"["dropLastBits"["scanFrom"[s, Prepend[a][x]]]], L]], "color0", Join["renderR"["true", rsRest], "closingRender"[rc]], "stateA"],
					"xorBool"[s, "parityBits"[Prepend[a][x]]]]]],
			"Rewrite"[hFalse],
			"Exact"["sys3ScanBlock0B"[x, L, s, a, Join["renderR"["true", rsRest], "closingRender"[rc]], hFalse]],
			"Introduce"[hTrue],
			"Change"["steps"["lookaheadStep"["system3"], Length[x] + 1,
				"lookaheadConfiguration"[L, "toCell"[a], Join["ofBits"[x], Prepend["color0"][Join["renderR"["true", rsRest], "closingRender"[rc]]]], "stB"[s]]] ==
				"some"[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, "LookaheadConfiguration"],
					"lookaheadConfiguration"["revAppend"["ofBits"["scanFrom"[s, Prepend[a][x]]], L], "color0", Join["renderR"["true", rsRest], "closingRender"[rc]], "stateB"],
					"lookaheadConfiguration"[Prepend["color0"]["revAppend"["ofBits"["dropLastBits"["scanFrom"[s, Prepend[a][x]]]], L]], "color0", Join["renderR"["true", rsRest], "closingRender"[rc]], "stateA"],
					"xorBool"[s, "parityBits"[Prepend[a][x]]]]]],
			"Rewrite"[hTrue],
			"Exact"["sys3ScanBlock0C"[x, L, s, a, Join["renderR"["true", rsRest], "closingRender"[rc]], hTrue]]
		}
	],
	machineTheorem["landingCons",
		ForAll[{Typed[L, {"Color"}], Typed[rs, {"TapeItem"}], Typed[rc, "Closing"], Typed[b, Booleans], Typed[z, {Booleans}], Typed[e, Booleans]},
			Implies[1 <= Length[z], "landing"[Prepend["toCell"[b]][L], rs, rc, z, e] == "landing"[L, rs, rc, Prepend[b][z], e]]],
		{
			"Introduce"[L, rs, rc, b, z, e], "Cases"[z],
			"Introduce"[h], "Have"[h0, 1 <= 0], "Exact"[h], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"["falseElimination"[f]],
			"Introduce"[z0, zRest, h],
			"Cases"[rs],
			"Cases"[rc], "Reflexivity", "Introduce"[cells], "Cases"[e], "Reflexivity", "Reflexivity",
			"Introduce"[it, rsRest], "Cases"[it],
			"Introduce"[y, U], "Reflexivity",
			"Cases"[e], "Reflexivity", "Reflexivity"
		}
	],
	(* afterScan *)
	TypeTheoryDefinition["isState4C", Typed[
		Function[{Typed[st, "System4State"]},
			InductiveRecursor["System4State"][Function[{Typed[q, "System4State"]}, Booleans], "false", "false", "true", st]],
		"System4State" -> Booleans
	]],
	TypeTheoryDefinition["afterScan", Typed[
		Function[{Typed[ls, {"TapeItem"}], Typed[rs, {"TapeItem"}], Typed[le, "LeftEnd"], Typed[rc, "Closing"],
				Typed[z, {Booleans}], Typed[s2, {NonNegativeIntegers}], Typed[st2, "System4State"]},
			"abstractConfig"[Prepend["itemSet"[z, s2]][ls], "tailList"[rs], le, rc, st2,
				InductiveRecursor[List][Function[{Typed[q, {"TapeItem"}]}, "Focus3"], "focusOff",
					Function[{Typed[it, "TapeItem"], Typed[rsRest, {"TapeItem"}], Typed[u, "Focus3"]},
						InductiveRecursor["TapeItem"][Function[{Typed[q, "TapeItem"]}, "Focus3"],
							Function[{Typed[y, {Booleans}], Typed[U, {NonNegativeIntegers}]}, "focusSetB"["headBool"[y], "tailList"[y], U]],
							"focusStar", it]], rs]]],
		{"TapeItem"} -> {"TapeItem"} -> "LeftEnd" -> "Closing" -> {Booleans} -> {NonNegativeIntegers} -> "System4State" -> "AbstractConfig"
	]],
	machineTheorem["afterScanTo3",
		ForAll[{Typed[ls, {"TapeItem"}], Typed[rs, {"TapeItem"}], Typed[le, "LeftEnd"], Typed[rc, "Closing"],
				Typed[z, {Booleans}], Typed[s2, {NonNegativeIntegers}], Typed[st2, "System4State"]},
			Implies[Not[st2 == "state4A"],
				Implies[ForAll[{Typed[y, {Booleans}], Typed[U, {NonNegativeIntegers}], Typed[rsRest, {"TapeItem"}]},
						Implies[rs == Prepend["itemSet"[y, U]][rsRest], 1 <= Length[y]]],
					"acToSystem3"["afterScan"[ls, rs, le, rc, z, s2, st2]] ==
						"landing"[Join["renderL"["false", ls], "leftEndRender"[le]], rs, rc, z, "isState4C"[st2]]]]],
		{
			"Introduce"[ls, rs, le, rc, z, s2, st2, hst],
			"Have"[hRev, Join[Join["ofBits"["reverseList"[z]], "renderL"["false", ls]], "leftEndRender"[le]] ==
				"revAppend"["ofBits"[z], Join["renderL"["false", ls], "leftEndRender"[le]]]],
			"Rewrite"["joinAssociativity"["ofBits"["reverseList"[z]], "renderL"["false", ls], "leftEndRender"[le]]],
			"Rewrite"["ofBitsReverseList"[z]], "Exact"["equalitySymmetry"["revAppendSplit"["ofBits"[z], Join["renderL"["false", ls], "leftEndRender"[le]]]]],
			"Have"[hRevDrop, Join[Join["tailList"["ofBits"["reverseList"[z]]], "renderL"["false", ls]], "leftEndRender"[le]] ==
				"revAppend"["ofBits"["dropLastBits"[z]], Join["renderL"["false", ls], "leftEndRender"[le]]]],
			"Rewrite"["joinAssociativity"["tailList"["ofBits"["reverseList"[z]]], "renderL"["false", ls], "leftEndRender"[le]]],
			"Rewrite"["ofBitsReverseList"[z]],
			"Rewrite"["tailOfBitsReverseDropLast"[z]],
			"Exact"["equalitySymmetry"["revAppendSplit"["ofBits"["dropLastBits"[z]], Join["renderL"["false", ls], "leftEndRender"[le]]]]],
			"Cases"[rs],
			"Introduce"[hrs], "Cases"[rc],
			"Cases"[st2],
			"Introduce"[hst], "Exact"["falseElimination"[hst["equalityReflexivity"["state4A"]]]],
			"Introduce"[hst], "Change"["lookaheadConfiguration"[Join[Join["ofBits"["reverseList"[z]], "renderL"["false", ls]], "leftEndRender"[le]], "color1", Typed[{}, {"Color"}], "stateB"] == "lookaheadConfiguration"["revAppend"["ofBits"[z], Join["renderL"["false", ls], "leftEndRender"[le]]], "color1", Typed[{}, {"Color"}], "stateB"]],
			"Rewrite"[hRev],
			"Introduce"[hst], "Change"["lookaheadConfiguration"[Join[Join["ofBits"["reverseList"[z]], "renderL"["false", ls]], "leftEndRender"[le]], "color1", Typed[{}, {"Color"}], "stateC"] == "lookaheadConfiguration"["revAppend"["ofBits"[z], Join["renderL"["false", ls], "leftEndRender"[le]]], "color1", Typed[{}, {"Color"}], "stateC"]],
			"Rewrite"[hRev],
			"Introduce"[cells], "Cases"[st2],
			"Introduce"[hst], "Exact"["falseElimination"[hst["equalityReflexivity"["state4A"]]]],
			"Introduce"[hst], "Change"["lookaheadConfiguration"[Join[Join["ofBits"["reverseList"[z]], "renderL"["false", ls]], "leftEndRender"[le]], "color0", cells, "stateB"] == "lookaheadConfiguration"["revAppend"["ofBits"[z], Join["renderL"["false", ls], "leftEndRender"[le]]], "color0", cells, "stateB"]],
			"Rewrite"[hRev],
			"Introduce"[hst], "Change"["lookaheadConfiguration"[Prepend["color0"][Join[Join["tailList"["ofBits"["reverseList"[z]]], "renderL"["false", ls]], "leftEndRender"[le]]], "color0", cells, "stateA"] == "lookaheadConfiguration"[Prepend["color0"]["revAppend"["ofBits"["dropLastBits"[z]], Join["renderL"["false", ls], "leftEndRender"[le]]]], "color0", cells, "stateA"]],
			"Rewrite"[hRevDrop],
			"Introduce"[it, rsRest, hrs], "Cases"[it],
			"Introduce"[y, U, hrs],
			"Have"[hyLen, 1 <= Length[y]], "Exact"[hrs[y, U, rsRest, "equalityReflexivity"[Prepend["itemSet"[y, U]][rsRest]]]],
			"Cases"[y],
			"Introduce"[hrs, hyLen], "Have"[h0, 1 <= 0], "Exact"[hyLen], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"["falseElimination"[f]],
			"Introduce"[y0, yRest, hrs, hyLen],
			"Cases"[st2],
			"Introduce"[hst], "Exact"["falseElimination"[hst["equalityReflexivity"["state4A"]]]],
			"Introduce"[hst], "Change"["lookaheadConfiguration"[Join[Join["ofBits"["reverseList"[z]], "renderL"["false", ls]], "leftEndRender"[le]], "toCell"[y0], Join["ofBits"[yRest], Join["renderR"["false", rsRest], "closingRender"[rc]]], "stateB"] == "lookaheadConfiguration"["revAppend"["ofBits"[z], Join["renderL"["false", ls], "leftEndRender"[le]]], "toCell"[y0], Join["ofBits"[yRest], Join["renderR"["false", rsRest], "closingRender"[rc]]], "stateB"]],
			"Rewrite"[hRev],
			"Introduce"[hst], "Change"["lookaheadConfiguration"[Join[Join["ofBits"["reverseList"[z]], "renderL"["false", ls]], "leftEndRender"[le]], "toCell"[y0], Join["ofBits"[yRest], Join["renderR"["false", rsRest], "closingRender"[rc]]], "stateC"] == "lookaheadConfiguration"["revAppend"["ofBits"[z], Join["renderL"["false", ls], "leftEndRender"[le]]], "toCell"[y0], Join["ofBits"[yRest], Join["renderR"["false", rsRest], "closingRender"[rc]]], "stateC"]],
			"Rewrite"[hRev],
			"Introduce"[hrs], "Cases"[st2],
			"Introduce"[hst], "Exact"["falseElimination"[hst["equalityReflexivity"["state4A"]]]],
			"Introduce"[hst], "Change"["lookaheadConfiguration"[Join[Join["ofBits"["reverseList"[z]], "renderL"["false", ls]], "leftEndRender"[le]], "color0", Join["renderR"["true", rsRest], "closingRender"[rc]], "stateB"] == "lookaheadConfiguration"["revAppend"["ofBits"[z], Join["renderL"["false", ls], "leftEndRender"[le]]], "color0", Join["renderR"["true", rsRest], "closingRender"[rc]], "stateB"]],
			"Rewrite"[hRev],
			"Introduce"[hst], "Change"["lookaheadConfiguration"[Prepend["color0"][Join[Join["tailList"["ofBits"["reverseList"[z]]], "renderL"["false", ls]], "leftEndRender"[le]]], "color0", Join["renderR"["true", rsRest], "closingRender"[rc]], "stateA"] == "lookaheadConfiguration"[Prepend["color0"]["revAppend"["ofBits"["dropLastBits"[z]], Join["renderL"["false", ls], "leftEndRender"[le]]]], "color0", Join["renderR"["true", rsRest], "closingRender"[rc]], "stateA"]],
			"Rewrite"[hRevDrop]
		}
	],
	machineTheorem["afterScanTo4",
		ForAll[{Typed[ls, {"TapeItem"}], Typed[rs, {"TapeItem"}], Typed[le, "LeftEnd"], Typed[rc, "Closing"],
				Typed[z, {Booleans}], Typed[s2, {NonNegativeIntegers}], Typed[st2, "System4State"]},
			"acToSystem4"["afterScan"[ls, rs, le, rc, z, s2, st2]] ==
				"system4Configuration"[Prepend["set4"[s2]][Map["itemToElem", ls]], Map["itemToElem", rs], st2]],
		{
			"Introduce"[ls, rs, le, rc, z, s2, st2], "Cases"[rs], "Reflexivity",
			"Introduce"[it, rsRest], "Cases"[it], "Introduce"[y, U], "Reflexivity", "Reflexivity"
		}
	],
	machineTheorem["afterScanOk",
		ForAll[{Typed[w, NonNegativeIntegers], Typed[h, NonNegativeIntegers],
				Typed[ls, {"TapeItem"}], Typed[rs, {"TapeItem"}], Typed[le, "LeftEnd"], Typed[rc, "Closing"],
				Typed[z, {Booleans}], Typed[s2, {NonNegativeIntegers}], Typed[st2, "System4State"]},
			Implies[Not[st2 == "state4A"],
				Implies[(h + 1) + 3 <= "pow2"[w],
					Implies["leftEndOk"[h, "acToSystem4"["afterScan"[ls, rs, le, rc, z, s2, st2]], le],
						Implies["allItemsOk"["pow2"[w], h + 2, ls],
							Implies["allItemsOk"["pow2"[w], h + 2, rs],
								Implies["leftItemsOk"["leftEndIsJunk"[le], ls],
									Implies["rightItemsOk"[rs],
										Implies["itemOk"["pow2"[w], h + 1, "itemSet"[z, s2]],
											Implies["lastBit"[z] == "isState4C"[st2],
												"acOk"[w, h, "afterScan"[ls, rs, le, rc, z, s2, st2]]]]]]]]]]]],
		{
			"Introduce"[w, h, ls, rs, le, rc, z, s2, st2, hst, hN, hle, hls, hrs, hL, hR, hz, hLast],
			"Have"[hN2, h + 3 <= "pow2"[w]], "LinearArithmetic",
			"Have"[leStep, h + 1 <= h + 2], "LinearArithmetic",
			"Have"[hls2, "allItemsOk"["pow2"[w], h + 1, Prepend["itemSet"[z, s2]][ls]]],
			"Exact"["andIntroduction"[hz, "allItemsOkMono"["pow2"[w], h + 1, h + 2, ls, hls, leStep]]],
			"Have"[hLenZ, 1 <= Length[z]],
			"Cases"[hz], "Introduce"[hLz, h2],
			"Have"[hp, 1 <= "pow2"[w]], "Exact"["pow2Pos"[w]],
			"Rewrite"[hLz], "Exact"[hp],
			"Cases"[rs],
			"Introduce"[hle, hrs, hR],
			"Exact"["andIntroduction"[hN2, "andIntroduction"[hle, "andIntroduction"[hls2,
				"andIntroduction"["trueIntroduction", "andIntroduction"[hL, "andIntroduction"["trueIntroduction", "equalityReflexivity"[Typed[{}, {"TapeItem"}]]]]]]]]],
			"Introduce"[it, rsRest, hle, hrs, hR],
			"Cases"[hrs], "Introduce"[hit, hrsRest],
			"Have"[hrs2, "allItemsOk"["pow2"[w], h + 1, rsRest]], "Exact"["allItemsOkMono"["pow2"[w], h + 1, h + 2, rsRest, hrsRest, leStep]],
			"Cases"[it],
			"Introduce"[y, U, hle, hR, hit],
			"Cases"[hit], "Introduce"[hyLen, hy2],
			"Have"[hyPos, 1 <= Length[y]], "Rewrite"[hyLen], "Exact"["pow2Pos"[w]],
			"Cases"[y],
			"Introduce"[hle, hR, hyLen, hy2, hyPos], "Have"[h0, 1 <= 0], "Exact"[hyPos], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"["falseElimination"[f]],
			"Introduce"[y0, yRest, hle, hR, hyLen, hy2, hyPos],
			"Exact"["andIntroduction"[hN2, "andIntroduction"[hle, "andIntroduction"[hls2,
				"andIntroduction"[hrs2, "andIntroduction"[hL, "andIntroduction"[hR,
					"andIntroduction"[hst, "itemOkMono"["pow2"[w], h + 1, h + 2, "itemSet"[Prepend[y0][yRest], U], "andIntroduction"[hyLen, hy2], leStep]]]]]]]]],
			"Introduce"[hle, hR, hit],
			"Cases"[hR], "Introduce"[hFirst, hRRest],
			"Cases"[st2],
			"Introduce"[hst, hLast, hle], "Exact"["falseElimination"[hst["equalityReflexivity"["state4A"]]]],
			"Introduce"[hst, hLast, hle],
			"Exact"["andIntroduction"[hN2, "andIntroduction"[hle, "andIntroduction"[hls2,
				"andIntroduction"[hrs2, "andIntroduction"[hL, "andIntroduction"[hRRest, "andIntroduction"["trueIntroduction", hFirst]]]]]]]],
			"Introduce"[hst, hLast, hle],
			"Exact"["andIntroduction"[hN2, "andIntroduction"[hle, "andIntroduction"[hls2,
				"andIntroduction"[hrs2, "andIntroduction"[hL, "andIntroduction"[hRRest,
					"andIntroduction"["orIntroductionLeft"["lastTrueFromLastBit"[z, hLenZ, hLast]], hFirst]]]]]]]]
		}
	],

	machineTheorem["someInjectiveI",
		ForAll[{TypedImplicit[S, TypeUniverse[1]], TypedImplicit[x, S], TypedImplicit[y, S]}, Implies["some"[x] == "some"[y], x == y]],
		{"Introduce"[S, x, y, eq], "Exact"["someInjective"[S, x, y, eq]]}
	],
	machineTheorem["noneNotSomeI",
		ForAll[{TypedImplicit[S, TypeUniverse[1]], TypedImplicit[x, S]}, Implies[Typed["none", Option[S]] == "some"[x], False]],
		{"Introduce"[S, x, eq], "Exact"["noneNotSome"[S, x, eq]]}
	],
	TypeTheoryDefinition["matchesStep", Typed[
		Function[{Typed[w, NonNegativeIntegers], Typed[h, NonNegativeIntegers], Typed[rc, "Closing"],
				Typed[c3, "LookaheadConfiguration"], Typed[c4p, "System4Configuration"]},
			Exists[{Typed[k, NonNegativeIntegers]}, And[1 <= k,
				Exists[{Typed[a2, "AbstractConfig"]},
					And[a2[["rc"]] == rc,
						And["steps"["lookaheadStep"["system3"], k, c3] == "some"["acToSystem3"[a2]],
							And[c4p == "acToSystem4"[a2], "acOk"[w, h, a2]]]]]]]],
		NonNegativeIntegers -> NonNegativeIntegers -> "Closing" -> "LookaheadConfiguration" -> "System4Configuration" -> TypeUniverse[0]
	]],
	(* Shared helpers for all 7 cases *)
	machineTheorem["itemsHeadNonEmpty",
		ForAll[{Typed[w, NonNegativeIntegers], Typed[k, NonNegativeIntegers], Typed[rs, {"TapeItem"}]},
			Implies["allItemsOk"["pow2"[w], k, rs],
				ForAll[{Typed[y, {Booleans}], Typed[U, {NonNegativeIntegers}], Typed[rsRest, {"TapeItem"}]},
					Implies[rs == Prepend["itemSet"[y, U]][rsRest], 1 <= Length[y]]]]],
		{
			"Introduce"[w, k, rs, hrs, y, U, rsRest, eq],
			"Have"[hrs2, "allItemsOk"["pow2"[w], k, Prepend["itemSet"[y, U]][rsRest]]],
			"Rewrite"["equalitySymmetry"[eq]], "Exact"[hrs],
			"Cases"[hrs2], "Introduce"[hit, hrest],
			"Cases"[hit], "Introduce"[hlen, h2],
			"Rewrite"[hlen], "Exact"["pow2Pos"[w]]
		}
	],
	machineTheorem["flipState4BNotA",
		ForAll[{Typed[b, Booleans]}, Not["flipState4"[b, "state4B"] == "state4A"]],
		{
			"Introduce"[b], "Cases"[b],
			"Introduce"[eq], "Exact"[Construct["equalitySubstitution", "System4State",
				Function[{Typed[st, "System4State"]}, InductiveRecursor["System4State"][Function[{Typed[q, "System4State"]}, TypeUniverse[0]], False, True, False, st]],
				"state4B", "state4A", eq, "trueIntroduction"]],
			"Introduce"[eq], "Exact"[Construct["equalitySubstitution", "System4State",
				Function[{Typed[st, "System4State"]}, InductiveRecursor["System4State"][Function[{Typed[q, "System4State"]}, TypeUniverse[0]], False, False, True, st]],
				"state4C", "state4A", eq, "trueIntroduction"]]
		}
	],
	machineTheorem["flipState4CNotA",
		ForAll[{Typed[b, Booleans]}, Not["flipState4"[b, "state4C"] == "state4A"]],
		{
			"Introduce"[b], "Cases"[b],
			"Introduce"[eq], "Exact"[Construct["equalitySubstitution", "System4State",
				Function[{Typed[st, "System4State"]}, InductiveRecursor["System4State"][Function[{Typed[q, "System4State"]}, TypeUniverse[0]], False, False, True, st]],
				"state4C", "state4A", eq, "trueIntroduction"]],
			"Introduce"[eq], "Exact"[Construct["equalitySubstitution", "System4State",
				Function[{Typed[st, "System4State"]}, InductiveRecursor["System4State"][Function[{Typed[q, "System4State"]}, TypeUniverse[0]], False, True, False, st]],
				"state4B", "state4A", eq, "trueIntroduction"]]
		}
	],
	machineTheorem["isState4CFlipB",
		ForAll[{Typed[b, Booleans]}, "isState4C"["flipState4"[b, "state4B"]] == b],
		{"Introduce"[b], "Cases"[b], "Reflexivity", "Reflexivity"}
	],
	machineTheorem["isState4CFlipC",
		ForAll[{Typed[b, Booleans]}, "isState4C"["flipState4"[b, "state4C"]] == "xorBool"["true", b]],
		{"Introduce"[b], "Cases"[b], "Reflexivity", "Reflexivity"}
	],
	(* Case 1: focusSetB in state4B *)
	machineTheorem["caseScanB",
		ForAll[{Typed[w, NonNegativeIntegers], Typed[h, NonNegativeIntegers],
				Typed[ls, {"TapeItem"}], Typed[rs, {"TapeItem"}], Typed[le, "LeftEnd"], Typed[rc, "Closing"],
				Typed[x0, Booleans], Typed[xRest, {Booleans}], Typed[s, {NonNegativeIntegers}], Typed[c4p, "System4Configuration"]},
			Implies[(h + 1) + 3 <= "pow2"[w],
				Implies["allItemsOk"["pow2"[w], h + 2, ls],
					Implies["allItemsOk"["pow2"[w], h + 2, rs],
						Implies["leftItemsOk"["leftEndIsJunk"[le], ls],
							Implies["rightItemsOk"[rs],
								Implies["itemOk"["pow2"[w], h + 2, "itemSet"[Prepend[x0][xRest], s]],
									Implies["leftEndOk"[h + 1, "acToSystem4"["abstractConfig"[ls, rs, le, rc, "state4B", "focusSetB"[x0, xRest, s]]], le],
										Implies["system4Step"["acToSystem4"["abstractConfig"[ls, rs, le, rc, "state4B", "focusSetB"[x0, xRest, s]]]] == "some"[c4p],
											"matchesStep"[w, h, rc, "acToSystem3"["abstractConfig"[ls, rs, le, rc, "state4B", "focusSetB"[x0, xRest, s]]], c4p]]]]]]]]]],
		{
			"Introduce"[w, h, ls, rs, le, rc, x0, xRest, s, c4p, hN, hls, hrs, hL, hR, hit, hle, hs],
			"Have"[hle2, "leftEndOk"[h, c4p, le]],
			"Exact"["leftEndOkStep"[le, h, "acToSystem4"["abstractConfig"[ls, rs, le, rc, "state4B", "focusSetB"[x0, xRest, s]]], c4p, hs, hle]],
			"Have"[eqC4, c4p == "system4Configuration"[Prepend["set4"["decr4"[s]]][Map["itemToElem", ls]], Map["itemToElem", rs], "flipState4"["hasZero4"[s], "state4B"]]],
			"Exact"["equalitySymmetry"["someInjectiveI"[hs]]],
			"Cases"[hit], "Introduce"[hxLen, h2], "Cases"[h2], "Introduce"[hsInc, hsDec],
			"Have"[hPar, "parityBits"[Prepend[x0][xRest]] == "hasZero4"[s]],
			"Exact"["decodesParity"[Prepend[x0][xRest], s, h + 1, hsInc, hsDec]],
			"Have"[hNonEmpty, ForAll[{Typed[y, {Booleans}], Typed[U, {NonNegativeIntegers}], Typed[rsRest, {"TapeItem"}]},
				Implies[rs == Prepend["itemSet"[y, U]][rsRest], 1 <= Length[y]]]],
			"Exact"["itemsHeadNonEmpty"[w, h + 2, rs, hrs]],
			"Have"[hRun, "steps"["lookaheadStep"["system3"], Length[xRest] + 1,
				"acToSystem3"["abstractConfig"[ls, rs, le, rc, "state4B", "focusSetB"[x0, xRest, s]]]] ==
				"some"["acToSystem3"["afterScan"[ls, rs, le, rc, "scanB"[Prepend[x0][xRest]], "decr4"[s], "flipState4"["hasZero4"[s], "state4B"]]]]],
			"Rewrite"["afterScanTo3"[ls, rs, le, rc, "scanB"[Prepend[x0][xRest]], "decr4"[s], "flipState4"["hasZero4"[s], "state4B"], "flipState4BNotA"["hasZero4"[s]], hNonEmpty]],
			"Rewrite"["isState4CFlipB"["hasZero4"[s]]],
			"Rewrite"["equalitySymmetry"[hPar]],
			"Exact"["scanRun"[Join["renderL"["false", ls], "leftEndRender"[le]], "false", x0, xRest, rs, rc, hNonEmpty]],
			"Have"[hTo4, c4p == "acToSystem4"["afterScan"[ls, rs, le, rc, "scanB"[Prepend[x0][xRest]], "decr4"[s], "flipState4"["hasZero4"[s], "state4B"]]]],
			"Rewrite"["afterScanTo4"[ls, rs, le, rc, "scanB"[Prepend[x0][xRest]], "decr4"[s], "flipState4"["hasZero4"[s], "state4B"]]],
			"Exact"[eqC4],
			"Have"[hleAfter, "leftEndOk"[h, "acToSystem4"["afterScan"[ls, rs, le, rc, "scanB"[Prepend[x0][xRest]], "decr4"[s], "flipState4"["hasZero4"[s], "state4B"]]], le]],
			"Rewrite"["equalitySymmetry"[hTo4]], "Exact"[hle2],
			"Have"[hzLen, Length["scanB"[Prepend[x0][xRest]]] == "pow2"[w]],
			"Change"[Length["scanFrom"["false", Prepend[x0][xRest]]] == "pow2"[w]],
			"Rewrite"["lengthScanFrom"[Prepend[x0][xRest], "false"]], "Exact"[hxLen],
			"Have"[hzOk, "itemOk"["pow2"[w], h + 1, "itemSet"["scanB"[Prepend[x0][xRest]], "decr4"[s]]]],
			"Exact"["andIntroduction"[hzLen, "andIntroduction"["decr4StrictlyIncreasing"[s, hsInc], "decodesScanB"[Prepend[x0][xRest], s, h + 1, hsInc, hsDec]]]],
			"Have"[hLast, "lastBit"["scanB"[Prepend[x0][xRest]]] == "isState4C"["flipState4"["hasZero4"[s], "state4B"]]],
			"Rewrite"["isState4CFlipB"["hasZero4"[s]]],
			"Change"["lastBit"["scanFrom"["false", Prepend[x0][xRest]]] == "hasZero4"[s]],
			"Rewrite"["lastBitScanFrom"[xRest, x0, "false"]],
			"Exact"[hPar],
			"Have"[hPos, 1 <= Length[xRest] + 1], "LinearArithmetic",
			"Exact"["existsIntroduction"[Length[xRest] + 1, "andIntroduction"[hPos,
				"existsIntroduction"["afterScan"[ls, rs, le, rc, "scanB"[Prepend[x0][xRest]], "decr4"[s], "flipState4"["hasZero4"[s], "state4B"]],
					"andIntroduction"["equalityReflexivity"[rc], "andIntroduction"[hRun, "andIntroduction"[hTo4,
						"afterScanOk"[w, h, ls, rs, le, rc, "scanB"[Prepend[x0][xRest]], "decr4"[s], "flipState4"["hasZero4"[s], "state4B"],
							"flipState4BNotA"["hasZero4"[s]], hN, hleAfter, hls, hrs, hL, hR, hzOk, hLast]]]]]]]]
		}
	],
	(* Case 2: focusSetB in state4C *)
	machineTheorem["caseScanC",
		ForAll[{Typed[w, NonNegativeIntegers], Typed[h, NonNegativeIntegers],
				Typed[ls, {"TapeItem"}], Typed[rs, {"TapeItem"}], Typed[le, "LeftEnd"], Typed[rc, "Closing"],
				Typed[x0, Booleans], Typed[xRest, {Booleans}], Typed[s, {NonNegativeIntegers}], Typed[c4p, "System4Configuration"]},
			Implies[(h + 1) + 3 <= "pow2"[w],
				Implies["allItemsOk"["pow2"[w], h + 2, ls],
					Implies["allItemsOk"["pow2"[w], h + 2, rs],
						Implies["leftItemsOk"["leftEndIsJunk"[le], ls],
							Implies["rightItemsOk"[rs],
								Implies["itemOk"["pow2"[w], h + 2, "itemSet"[Prepend[x0][xRest], s]],
									Implies["leftEndOk"[h + 1, "acToSystem4"["abstractConfig"[ls, rs, le, rc, "state4C", "focusSetB"[x0, xRest, s]]], le],
										Implies["system4Step"["acToSystem4"["abstractConfig"[ls, rs, le, rc, "state4C", "focusSetB"[x0, xRest, s]]]] == "some"[c4p],
											"matchesStep"[w, h, rc, "acToSystem3"["abstractConfig"[ls, rs, le, rc, "state4C", "focusSetB"[x0, xRest, s]]], c4p]]]]]]]]]],
		{
			"Introduce"[w, h, ls, rs, le, rc, x0, xRest, s, c4p, hN, hls, hrs, hL, hR, hit, hle, hs],
			"Have"[hle2, "leftEndOk"[h, c4p, le]],
			"Exact"["leftEndOkStep"[le, h, "acToSystem4"["abstractConfig"[ls, rs, le, rc, "state4C", "focusSetB"[x0, xRest, s]]], c4p, hs, hle]],
			"Have"[eqC4, c4p == "system4Configuration"[Prepend["set4"["decr4"[s]]][Map["itemToElem", ls]], Map["itemToElem", rs], "flipState4"["hasZero4"[s], "state4C"]]],
			"Exact"["equalitySymmetry"["someInjectiveI"[hs]]],
			"Cases"[hit], "Introduce"[hxLen, h2], "Cases"[h2], "Introduce"[hsInc, hsDec],
			"Have"[hPar, "parityBits"[Prepend[x0][xRest]] == "hasZero4"[s]],
			"Exact"["decodesParity"[Prepend[x0][xRest], s, h + 1, hsInc, hsDec]],
			"Have"[hNonEmpty, ForAll[{Typed[y, {Booleans}], Typed[U, {NonNegativeIntegers}], Typed[rsRest, {"TapeItem"}]},
				Implies[rs == Prepend["itemSet"[y, U]][rsRest], 1 <= Length[y]]]],
			"Exact"["itemsHeadNonEmpty"[w, h + 2, rs, hrs]],
			"Have"[hRun, "steps"["lookaheadStep"["system3"], Length[xRest] + 1,
				"acToSystem3"["abstractConfig"[ls, rs, le, rc, "state4C", "focusSetB"[x0, xRest, s]]]] ==
				"some"["acToSystem3"["afterScan"[ls, rs, le, rc, "scanFrom"["true", Prepend[x0][xRest]], "decr4"[s], "flipState4"["hasZero4"[s], "state4C"]]]]],
			"Rewrite"["afterScanTo3"[ls, rs, le, rc, "scanFrom"["true", Prepend[x0][xRest]], "decr4"[s], "flipState4"["hasZero4"[s], "state4C"], "flipState4CNotA"["hasZero4"[s]], hNonEmpty]],
			"Rewrite"["isState4CFlipC"["hasZero4"[s]]],
			"Rewrite"["equalitySymmetry"[hPar]],
			"Exact"["scanRun"[Join["renderL"["false", ls], "leftEndRender"[le]], "true", x0, xRest, rs, rc, hNonEmpty]],
			"Have"[hTo4, c4p == "acToSystem4"["afterScan"[ls, rs, le, rc, "scanFrom"["true", Prepend[x0][xRest]], "decr4"[s], "flipState4"["hasZero4"[s], "state4C"]]]],
			"Rewrite"["afterScanTo4"[ls, rs, le, rc, "scanFrom"["true", Prepend[x0][xRest]], "decr4"[s], "flipState4"["hasZero4"[s], "state4C"]]],
			"Exact"[eqC4],
			"Have"[hleAfter, "leftEndOk"[h, "acToSystem4"["afterScan"[ls, rs, le, rc, "scanFrom"["true", Prepend[x0][xRest]], "decr4"[s], "flipState4"["hasZero4"[s], "state4C"]]], le]],
			"Rewrite"["equalitySymmetry"[hTo4]], "Exact"[hle2],
			"Have"[hzLen, Length["scanFrom"["true", Prepend[x0][xRest]]] == "pow2"[w]],
			"Rewrite"["lengthScanFrom"[Prepend[x0][xRest], "true"]], "Exact"[hxLen],
			"Have"[hkBound, ((h + 1) + 1) + 1 <= "pow2"[w]], "LinearArithmetic",
			"Have"[hzOk, "itemOk"["pow2"[w], h + 1, "itemSet"["scanFrom"["true", Prepend[x0][xRest]], "decr4"[s]]]],
			"Exact"["andIntroduction"[hzLen, "andIntroduction"["decr4StrictlyIncreasing"[s, hsInc], "decodesScanC"[w, x0, xRest, s, h + 1, hxLen, hsInc, hkBound, hsDec]]]],
			"Have"[hLast, "lastBit"["scanFrom"["true", Prepend[x0][xRest]]] == "isState4C"["flipState4"["hasZero4"[s], "state4C"]]],
			"Rewrite"["isState4CFlipC"["hasZero4"[s]]],
			"Rewrite"["lastBitScanFrom"[xRest, x0, "true"]],
			"Rewrite"[hPar],
			"Have"[hPos, 1 <= Length[xRest] + 1], "LinearArithmetic",
			"Exact"["existsIntroduction"[Length[xRest] + 1, "andIntroduction"[hPos,
				"existsIntroduction"["afterScan"[ls, rs, le, rc, "scanFrom"["true", Prepend[x0][xRest]], "decr4"[s], "flipState4"["hasZero4"[s], "state4C"]],
					"andIntroduction"["equalityReflexivity"[rc], "andIntroduction"[hRun, "andIntroduction"[hTo4,
						"afterScanOk"[w, h, ls, rs, le, rc, "scanFrom"["true", Prepend[x0][xRest]], "decr4"[s], "flipState4"["hasZero4"[s], "state4C"],
							"flipState4CNotA"["hasZero4"[s]], hN, hleAfter, hls, hrs, hL, hR, hzOk, hLast]]]]]]]]
		}
	],
	(* Case 3: focusSetT in state4C (transient skipped-first-cell scan after rule 5) *)
	machineTheorem["caseScanT",
		ForAll[{Typed[w, NonNegativeIntegers], Typed[h, NonNegativeIntegers],
				Typed[ls, {"TapeItem"}], Typed[rs, {"TapeItem"}], Typed[le, "LeftEnd"], Typed[rc, "Closing"],
				Typed[x1, Booleans], Typed[xRest, {Booleans}], Typed[s, {NonNegativeIntegers}], Typed[c4p, "System4Configuration"]},
			Implies[(h + 1) + 3 <= "pow2"[w],
				Implies["allItemsOk"["pow2"[w], h + 2, ls],
					Implies["allItemsOk"["pow2"[w], h + 2, rs],
						Implies["leftItemsOk"["leftEndIsJunk"[le], ls],
							Implies["rightItemsOk"[rs],
								Implies["strictlyIncreasing"[s],
									Implies[Length[Prepend["true"][Prepend[x1][xRest]]] == "pow2"[w],
										Implies["decodesBits"[Prepend["true"][Prepend[x1][xRest]], "xorMerge"[{1}, s], h + 2],
											Implies["leftEndOk"[h + 1, "acToSystem4"["abstractConfig"[ls, rs, le, rc, "state4C", "focusSetT"[x1, xRest, s]]], le],
												Implies["system4Step"["acToSystem4"["abstractConfig"[ls, rs, le, rc, "state4C", "focusSetT"[x1, xRest, s]]]] == "some"[c4p],
													"matchesStep"[w, h, rc, "acToSystem3"["abstractConfig"[ls, rs, le, rc, "state4C", "focusSetT"[x1, xRest, s]]], c4p]]]]]]]]]]]],
		{
			"Introduce"[w, h, ls, rs, le, rc, x1, xRest, s, c4p, hN, hls, hrs, hL, hR, hsInc, hxLen, hsDec, hle, hs],
			"Have"[hle2, "leftEndOk"[h, c4p, le]],
			"Exact"["leftEndOkStep"[le, h, "acToSystem4"["abstractConfig"[ls, rs, le, rc, "state4C", "focusSetT"[x1, xRest, s]]], c4p, hs, hle]],
			"Have"[eqC4, c4p == "system4Configuration"[Prepend["set4"["decr4"[s]]][Map["itemToElem", ls]], Map["itemToElem", rs], "flipState4"["hasZero4"[s], "state4C"]]],
			"Exact"["equalitySymmetry"["someInjectiveI"[hs]]],
			"Have"[hPar, "parityBits"[Prepend[x1][xRest]] == "xorBool"["true", "hasZero4"[s]]],
			"Exact"["decodesTransientParity"[Prepend[x1][xRest], s, h + 1, hsInc, hsDec]],
			"Have"[hNonEmpty, ForAll[{Typed[y, {Booleans}], Typed[U, {NonNegativeIntegers}], Typed[rsRest, {"TapeItem"}]},
				Implies[rs == Prepend["itemSet"[y, U]][rsRest], 1 <= Length[y]]]],
			"Exact"["itemsHeadNonEmpty"[w, h + 2, rs, hrs]],
			"Have"[hRun, "steps"["lookaheadStep"["system3"], Length[xRest] + 1,
				"acToSystem3"["abstractConfig"[ls, rs, le, rc, "state4C", "focusSetT"[x1, xRest, s]]]] ==
				"some"["acToSystem3"["afterScan"[ls, rs, le, rc, Prepend["true"]["scanFrom"["false", Prepend[x1][xRest]]], "decr4"[s], "flipState4"["hasZero4"[s], "state4C"]]]]],
			"Rewrite"["afterScanTo3"[ls, rs, le, rc, Prepend["true"]["scanFrom"["false", Prepend[x1][xRest]]], "decr4"[s], "flipState4"["hasZero4"[s], "state4C"], "flipState4CNotA"["hasZero4"[s]], hNonEmpty]],
			"Rewrite"["isState4CFlipC"["hasZero4"[s]]],
			"Rewrite"["equalitySymmetry"[hPar]],
			"Have"[hLenScan, 1 <= Length["scanFrom"["false", Prepend[x1][xRest]]]],
			"Rewrite"["lengthScanFrom"[Prepend[x1][xRest], "false"]], "Change"[1 <= Length[xRest] + 1], "LinearArithmetic",
			"Rewrite"["equalitySymmetry"["landingCons"[Join["renderL"["false", ls], "leftEndRender"[le]], rs, rc, "true", "scanFrom"["false", Prepend[x1][xRest]], "parityBits"[Prepend[x1][xRest]], hLenScan]]],
			"Exact"["scanRun"[Prepend["color2"][Join["renderL"["false", ls], "leftEndRender"[le]]], "false", x1, xRest, rs, rc, hNonEmpty]],
			"Have"[hTo4, c4p == "acToSystem4"["afterScan"[ls, rs, le, rc, Prepend["true"]["scanFrom"["false", Prepend[x1][xRest]]], "decr4"[s], "flipState4"["hasZero4"[s], "state4C"]]]],
			"Rewrite"["afterScanTo4"[ls, rs, le, rc, Prepend["true"]["scanFrom"["false", Prepend[x1][xRest]]], "decr4"[s], "flipState4"["hasZero4"[s], "state4C"]]],
			"Exact"[eqC4],
			"Have"[hleAfter, "leftEndOk"[h, "acToSystem4"["afterScan"[ls, rs, le, rc, Prepend["true"]["scanFrom"["false", Prepend[x1][xRest]]], "decr4"[s], "flipState4"["hasZero4"[s], "state4C"]]], le]],
			"Rewrite"["equalitySymmetry"[hTo4]], "Exact"[hle2],
			"Have"[hzLen, Length[Prepend["true"]["scanFrom"["false", Prepend[x1][xRest]]]] == "pow2"[w]],
			"Change"[Length["scanFrom"["false", Prepend[x1][xRest]]] + 1 == "pow2"[w]],
			"Rewrite"["lengthScanFrom"[Prepend[x1][xRest], "false"]], "Exact"[hxLen],
			"Have"[hkBound, ((h + 1) + 1) + 1 <= "pow2"[w]], "LinearArithmetic",
			"Have"[hzOk, "itemOk"["pow2"[w], h + 1, "itemSet"[Prepend["true"]["scanFrom"["false", Prepend[x1][xRest]]], "decr4"[s]]]],
			"Exact"["andIntroduction"[hzLen, "andIntroduction"["decr4StrictlyIncreasing"[s, hsInc], "decodesTransient"[w, Prepend[x1][xRest], s, h + 1, hxLen, hsInc, hkBound, hsDec]]]],
			"Have"[hLast, "lastBit"[Prepend["true"]["scanFrom"["false", Prepend[x1][xRest]]]] == "isState4C"["flipState4"["hasZero4"[s], "state4C"]]],
			"Rewrite"["isState4CFlipC"["hasZero4"[s]]],
			"Change"["lastBit"["scanFrom"["false", Prepend[x1][xRest]]] == "xorBool"["true", "hasZero4"[s]]],
			"Rewrite"["lastBitScanFrom"[xRest, x1, "false"]],
			"Exact"[hPar],
			"Have"[hPos, 1 <= Length[xRest] + 1], "LinearArithmetic",
			"Exact"["existsIntroduction"[Length[xRest] + 1, "andIntroduction"[hPos,
				"existsIntroduction"["afterScan"[ls, rs, le, rc, Prepend["true"]["scanFrom"["false", Prepend[x1][xRest]]], "decr4"[s], "flipState4"["hasZero4"[s], "state4C"]],
					"andIntroduction"["equalityReflexivity"[rc], "andIntroduction"[hRun, "andIntroduction"[hTo4,
						"afterScanOk"[w, h, ls, rs, le, rc, Prepend["true"]["scanFrom"["false", Prepend[x1][xRest]]], "decr4"[s], "flipState4"["hasZero4"[s], "state4C"],
							"flipState4CNotA"["hasZero4"[s]], hN, hleAfter, hls, hrs, hL, hR, hzOk, hLast]]]]]]]]
		}
	],
	(* Helpers for turnRun and caseSetA *)
	machineTheorem["lengthOfBits",
		ForAll[{Typed[xs, {Booleans}]}, Length["ofBits"[xs]] == Length[xs]],
		{"Introduce"[xs], "Exact"["lengthMap"["toCell", xs]]}
	],
	machineTheorem["ofBitsZipper",
		ForAll[{Typed[xl, {Booleans}], Typed[b, Booleans], Typed[xr, {Booleans}], Typed[R0, {"Color"}]},
			"revAppend"["ofBits"[xl], Prepend["toCell"[b]][Join["ofBits"[xr], R0]]] == Join["ofBits"[Join["reverseList"[xl], Prepend[b][xr]]], R0]],
		{
			"Introduce"[xl, b, xr, R0],
			"Rewrite"["revAppendSplit"["ofBits"[xl], Prepend["toCell"[b]][Join["ofBits"[xr], R0]]]],
			"Change"[Join["reverseList"["ofBits"[xl]], Prepend["toCell"[b]][Join["ofBits"[xr], R0]]] == Join["ofBits"[Join["reverseList"[xl], Prepend[b][xr]]], R0]],
			"Rewrite"["equalitySymmetry"["ofBitsReverseList"[xl]]],
			"Rewrite"["ofBitsJoin"["reverseList"[xl], Prepend[b][xr]]],
			"Exact"["equalitySymmetry"["joinAssociativity"["ofBits"["reverseList"[xl]], Prepend["toCell"[b]]["ofBits"[xr]], R0]]]
		}
	],
	machineTheorem["allNonZeroColorsJoin",
		ForAll[{Typed[P, {"Color"}], Typed[Q, {"Color"}]},
			Implies["allNonZeroColors"[P], Implies["allNonZeroColors"[Q], "allNonZeroColors"[Join[P, Q]]]]],
		{
			"Introduce"[P, Q], "Induction"[P],
			"Introduce"[hP, hQ], "Exact"[hQ],
			"Introduce"[c, rest, ih, hP, hQ], "Cases"[hP], "Introduce"[hc, hRest],
			"Exact"["andIntroduction"[hc, ih[hRest, hQ]]]
		}
	],
	machineTheorem["ofBitsZeros",
		ForAll[{Typed[t, NonNegativeIntegers]}, "ofBits"["zerosBits"[t]] == "replicateColor"[t, "color1"]],
		{
			"Introduce"[t], "Induction"[t], "Reflexivity",
			"Introduce"[k, ih], "Change"[Prepend["color1"]["ofBits"["zerosBits"[k]]] == Prepend["color1"]["replicateColor"[k, "color1"]]],
			"Rewrite"[ih]
		}
	],
	machineTheorem["reverseListReplicateColor",
		ForAll[{Typed[t, NonNegativeIntegers], Typed[c, "Color"]}, "reverseList"["replicateColor"[t, c]] == "replicateColor"[t, c]],
		{
			"Introduce"[t, c], "Induction"[t], "Reflexivity",
			"Introduce"[k, ih],
			"Change"["reverseList"[Prepend[c]["replicateColor"[k, c]]] == Prepend[c]["replicateColor"[k, c]]],
			"Rewrite"["reverseListPrepend"[c, "replicateColor"[k, c]]],
			"Rewrite"[ih],
			"Have"[repApp, ForAll[{Typed[n, NonNegativeIntegers]}, Join["replicateColor"[n, c], {c}] == Prepend[c]["replicateColor"[n, c]]]],
			"Introduce"[n], "Induction"[n], "Reflexivity",
			"Introduce"[j, ih2], "Change"[Prepend[c][Join["replicateColor"[j, c], {c}]] == Prepend[c][Prepend[c]["replicateColor"[j, c]]]], "Rewrite"[ih2],
			"Exact"[repApp[k]]
		}
	],
	machineTheorem["lengthReplicateColor",
		ForAll[{Typed[t, NonNegativeIntegers], Typed[c, "Color"]}, Length["replicateColor"[t, c]] == t],
		{
			"Introduce"[t, c], "Induction"[t], "Reflexivity",
			"Introduce"[k, ih], "Change"[Length["replicateColor"[k, c]] + 1 == k + 1], "Rewrite"[ih]
		}
	],
	machineTheorem["allNonZeroReplicateColor1",
		ForAll[{Typed[t, NonNegativeIntegers]}, "allNonZeroColors"["replicateColor"[t, "color1"]]],
		{
			"Introduce"[t], "Induction"[t], "Exact"["trueIntroduction"],
			"Introduce"[k, ih], "Exact"["andIntroduction"["toCellNotZero"["false"], ih]]
		}
	],
	machineTheorem["turnRun",
		ForAll[{Typed[xl, {Booleans}], Typed[b, Booleans], Typed[xr, {Booleans}],
				Typed[m1, NonNegativeIntegers], Typed[t, NonNegativeIntegers], Typed[R0, {"Color"}],
				Typed[x0, Booleans], Typed[xRest, {Booleans}]},
			Implies[Join["reverseList"[xl], Prepend[b][xr]] == Prepend[x0][xRest],
				"steps"["lookaheadStep"["system3"], (Length[xl] + t) + (t + 6),
					"lookaheadConfiguration"[Join["ofBits"[xl], "leftEndRev"[m1 + 1, t]], "toCell"[b], Join["ofBits"[xr], R0], "stateA"]] ==
				"some"["lookaheadConfiguration"["leftEndRev"[m1, t + 1], "toCell"[x0], Join["ofBits"[xRest], R0], "stateB"]]]],
		{
			"Introduce"[xl, b, xr, m1, t, R0, x0, xRest, hx],
			"Have"[hP, "allNonZeroColors"[Join["ofBits"[xl], Join["replicateColor"[t, "color1"], {"color2", "color2"}]]]],
			"Exact"["allNonZeroColorsJoin"["ofBits"[xl], Join["replicateColor"[t, "color1"], {"color2", "color2"}],
				"ofBitsNonZero"[xl],
				"allNonZeroColorsJoin"["replicateColor"[t, "color1"], {"color2", "color2"},
					"allNonZeroReplicateColor1"[t],
					"andIntroduction"["toCellNotZero"["true"], "andIntroduction"["toCellNotZero"["true"], "trueIntroduction"]]]]],
			"Have"[lenP, Length[Join["ofBits"[xl], Join["replicateColor"[t, "color1"], {"color2", "color2"}]]] == (Length[xl] + t) + 2],
			"Rewrite"["lengthJoin"["ofBits"[xl], Join["replicateColor"[t, "color1"], {"color2", "color2"}]]],
			"Rewrite"["lengthJoin"["replicateColor"[t, "color1"], {"color2", "color2"}]],
			"Rewrite"["lengthOfBits"[xl]],
			"Rewrite"["lengthReplicateColor"[t, "color1"]],
			"Change"[Length[xl] + (t + 2) == (Length[xl] + t) + 2], "LinearArithmetic",
			"Have"[lenScan, Length[Prepend["true"]["zerosBits"[t]]] == t + 1],
			"Change"[Length["zerosBits"[t]] + 1 == t + 1], "Rewrite"["lengthZerosBits"[t]],
			"Have"[stepSplit, (Length[xl] + t) + (t + 6) ==
				((Length[Join["ofBits"[xl], Join["replicateColor"[t, "color1"], {"color2", "color2"}]]] + 1) + 1) + (Length[Prepend["true"]["zerosBits"[t]]] + 1)],
			"Rewrite"[lenP], "Rewrite"[lenScan], "LinearArithmetic",
			"Have"[eLeft, Join["ofBits"[xl], "leftEndRev"[m1 + 1, t]] ==
				Join[Join["ofBits"[xl], Join["replicateColor"[t, "color1"], {"color2", "color2"}]], Prepend["color0"]["replicateColor"[m1, "color0"]]]],
			"Change"[Join["ofBits"[xl], Join["replicateColor"[t, "color1"], Join[{"color2", "color2"}, Prepend["color0"]["replicateColor"[m1, "color0"]]]]] ==
				Join[Join["ofBits"[xl], Join["replicateColor"[t, "color1"], {"color2", "color2"}]], Prepend["color0"]["replicateColor"[m1, "color0"]]]],
			"Rewrite"["equalitySymmetry"["joinAssociativity"["replicateColor"[t, "color1"], {"color2", "color2"}, Prepend["color0"]["replicateColor"[m1, "color0"]]]]],
			"Exact"["equalitySymmetry"["joinAssociativity"["ofBits"[xl], Join["replicateColor"[t, "color1"], {"color2", "color2"}], Prepend["color0"]["replicateColor"[m1, "color0"]]]]],
			"Rewrite"[stepSplit], "Rewrite"[eLeft],
			"Rewrite"["stepsAdd"["LookaheadConfiguration", "lookaheadStep"["system3"],
				(Length[Join["ofBits"[xl], Join["replicateColor"[t, "color1"], {"color2", "color2"}]]] + 1) + 1,
				Length[Prepend["true"]["zerosBits"[t]]] + 1,
				"lookaheadConfiguration"[Join[Join["ofBits"[xl], Join["replicateColor"[t, "color1"], {"color2", "color2"}]], Prepend["color0"]["replicateColor"[m1, "color0"]]],
					"toCell"[b], Join["ofBits"[xr], R0], "stateA"]]],
			"Rewrite"["stepsAdd"["LookaheadConfiguration", "lookaheadStep"["system3"],
				Length[Join["ofBits"[xl], Join["replicateColor"[t, "color1"], {"color2", "color2"}]]] + 1, 1,
				"lookaheadConfiguration"[Join[Join["ofBits"[xl], Join["replicateColor"[t, "color1"], {"color2", "color2"}]], Prepend["color0"]["replicateColor"[m1, "color0"]]],
					"toCell"[b], Join["ofBits"[xr], R0], "stateA"]]],
			"Rewrite"["sys3WalkLeft"[Join["ofBits"[xl], Join["replicateColor"[t, "color1"], {"color2", "color2"}]],
				"color0", "replicateColor"[m1, "color0"], "toCell"[b], Join["ofBits"[xr], R0], hP, "toCellNotZero"[b]]],
			"Have"[eRev, "revAppend"[Join["ofBits"[xl], Join["replicateColor"[t, "color1"], {"color2", "color2"}]], Prepend["toCell"[b]][Join["ofBits"[xr], R0]]] ==
				Prepend["color2"][Prepend["color2"][Join["replicateColor"[t, "color1"], Prepend["toCell"[x0]][Join["ofBits"[xRest], R0]]]]]],
			"Rewrite"["revAppendJoin"["ofBits"[xl], Join["replicateColor"[t, "color1"], {"color2", "color2"}], Prepend["toCell"[b]][Join["ofBits"[xr], R0]]]],
			"Rewrite"["ofBitsZipper"[xl, b, xr, R0]],
			"Rewrite"[hx],
			"Rewrite"["revAppendJoin"["replicateColor"[t, "color1"], {"color2", "color2"}, Join["ofBits"[Prepend[x0][xRest]], R0]]],
			"Rewrite"["revAppendSplit"["replicateColor"[t, "color1"], Join["ofBits"[Prepend[x0][xRest]], R0]]],
			"Change"[Prepend["color2"][Prepend["color2"][Join["reverseList"["replicateColor"[t, "color1"]], Prepend["toCell"[x0]][Join["ofBits"[xRest], R0]]]]] ==
				Prepend["color2"][Prepend["color2"][Join["replicateColor"[t, "color1"], Prepend["toCell"[x0]][Join["ofBits"[xRest], R0]]]]]],
			"Rewrite"["reverseListReplicateColor"[t, "color1"]],
			"Change"["optionBind"["optionBind"["some"["lookaheadConfiguration"["replicateColor"[m1, "color0"], "color0",
				"revAppend"[Join["ofBits"[xl], Join["replicateColor"[t, "color1"], {"color2", "color2"}]], Prepend["toCell"[b]][Join["ofBits"[xr], R0]]], "stateA"]],
				Function[{Typed[y, "LookaheadConfiguration"]}, "lookaheadStep"["system3", y]]],
				Function[{Typed[y, "LookaheadConfiguration"]}, "steps"["lookaheadStep"["system3"], Length[Prepend["true"]["zerosBits"[t]]] + 1, y]]] ==
				"some"["lookaheadConfiguration"["leftEndRev"[m1, t + 1], "toCell"[x0], Join["ofBits"[xRest], R0], "stateB"]]],
			"Rewrite"[eRev],
			"Change"["optionBind"["lookaheadStep"["system3", "lookaheadConfiguration"["replicateColor"[m1, "color0"], "color0",
				Prepend["color2"][Prepend["color2"][Join["replicateColor"[t, "color1"], Prepend["toCell"[x0]][Join["ofBits"[xRest], R0]]]]], "stateA"]],
				Function[{Typed[y, "LookaheadConfiguration"]}, "steps"["lookaheadStep"["system3"], Length[Prepend["true"]["zerosBits"[t]]] + 1, y]]] ==
				"some"["lookaheadConfiguration"["leftEndRev"[m1, t + 1], "toCell"[x0], Join["ofBits"[xRest], R0], "stateB"]]],
			"Rewrite"["sys3TurnA"["replicateColor"[m1, "color0"], "color2",
				Prepend["color2"][Join["replicateColor"[t, "color1"], Prepend["toCell"[x0]][Join["ofBits"[xRest], R0]]]]]],
			"Have"[eScanIn, Prepend["color2"][Join["replicateColor"[t, "color1"], Prepend["toCell"[x0]][Join["ofBits"[xRest], R0]]]] ==
				Join["ofBits"[Prepend["true"]["zerosBits"[t]]], Prepend["toCell"[x0]][Join["ofBits"[xRest], R0]]]],
			"Rewrite"["equalitySymmetry"["ofBitsZeros"[t]]], "Reflexivity",
			"Change"["steps"["lookaheadStep"["system3"], Length[Prepend["true"]["zerosBits"[t]]] + 1,
				"lookaheadConfiguration"[Prepend["color2"]["replicateColor"[m1, "color0"]], "toCell"["true"],
					Prepend["color2"][Join["replicateColor"[t, "color1"], Prepend["toCell"[x0]][Join["ofBits"[xRest], R0]]]], "stB"["false"]]] ==
				"some"["lookaheadConfiguration"["leftEndRev"[m1, t + 1], "toCell"[x0], Join["ofBits"[xRest], R0], "stateB"]]],
			"Rewrite"[eScanIn],
			"Rewrite"["sys3ScanBlock"[Prepend["true"]["zerosBits"[t]], Prepend["color2"]["replicateColor"[m1, "color0"]],
				"false", "true", "toCell"[x0], Join["ofBits"[xRest], R0], "toCellNotZero"[x0]]],
			"Have"[eScanOut, "scanFrom"["false", Prepend["true"][Prepend["true"]["zerosBits"[t]]]] ==
				Prepend["true"][Prepend["false"]["zerosBits"[t]]]],
			"Change"[Prepend["true"][Prepend["false"]["scanFrom"["false", "zerosBits"[t]]]] == Prepend["true"][Prepend["false"]["zerosBits"[t]]]],
			"Rewrite"["scanFromZeros"[t, "false"]], "Reflexivity",
			"Have"[eParOut, "xorBool"["false", "parityBits"[Prepend["true"][Prepend["true"]["zerosBits"[t]]]]] == "false"],
			"Change"["xorBool"["true", "xorBool"["true", "parityBits"["zerosBits"[t]]]] == "false"],
			"Rewrite"["parityBitsZeros"[t]], "Reflexivity",
			"Rewrite"[eScanOut], "Rewrite"[eParOut],
			"Have"[eEnd, "revAppend"["ofBits"[Prepend["true"][Prepend["false"]["zerosBits"[t]]]], Prepend["color2"]["replicateColor"[m1, "color0"]]] ==
				"leftEndRev"[m1, t + 1]],
			"Change"["revAppend"["ofBits"["zerosBits"[t]], Prepend["color1"][Prepend["color2"][Prepend["color2"]["replicateColor"[m1, "color0"]]]]] ==
				Join["replicateColor"[t + 1, "color1"], Prepend["color2"][Prepend["color2"]["replicateColor"[m1, "color0"]]]]],
			"Rewrite"["ofBitsZeros"[t]],
			"Rewrite"["revAppendSplit"["replicateColor"[t, "color1"], Prepend["color1"][Prepend["color2"][Prepend["color2"]["replicateColor"[m1, "color0"]]]]]],
			"Change"[Join["reverseList"["replicateColor"[t, "color1"]], Join[{"color1"}, Prepend["color2"][Prepend["color2"]["replicateColor"[m1, "color0"]]]]] ==
				Join[Prepend["color1"]["replicateColor"[t, "color1"]], Prepend["color2"][Prepend["color2"]["replicateColor"[m1, "color0"]]]]],
			"Rewrite"["reverseListReplicateColor"[t, "color1"]],
			"Rewrite"["equalitySymmetry"["joinAssociativity"["replicateColor"[t, "color1"], {"color1"}, Prepend["color2"][Prepend["color2"]["replicateColor"[m1, "color0"]]]]]],
			"Have"[repApp, ForAll[{Typed[n, NonNegativeIntegers]}, Join["replicateColor"[n, "color1"], {"color1"}] == Prepend["color1"]["replicateColor"[n, "color1"]]]],
			"Introduce"[n], "Induction"[n], "Reflexivity",
			"Introduce"[j, ih2], "Change"[Prepend["color1"][Join["replicateColor"[j, "color1"], {"color1"}]] == Prepend["color1"][Prepend["color1"]["replicateColor"[j, "color1"]]]], "Rewrite"[ih2],
			"Rewrite"[repApp[t]],
			"Rewrite"[eEnd], "Reflexivity"
		}
	],
	machineTheorem["itemOkReverseSplit",
		ForAll[{Typed[N, NonNegativeIntegers], Typed[k, NonNegativeIntegers], Typed[y, {Booleans}], Typed[T, {NonNegativeIntegers}],
				Typed[b, Booleans], Typed[yl, {Booleans}]},
			Implies["reverseList"[y] == Prepend[b][yl],
				Implies["itemOk"[N, k, "itemSet"[y, T]],
					"itemOk"[N, k, "itemSet"[Join["reverseList"[yl], {b}], T]]]]],
		{
			"Introduce"[N, k, y, T, b, yl, hy, hOk],
			"Have"[eqY, Join["reverseList"[yl], {b}] == y],
			"Rewrite"["equalitySymmetry"["reverseListPrepend"[b, yl]]],
			"Rewrite"["equalitySymmetry"[hy]],
			"Exact"["reverseListInvolution"[y]],
			"Rewrite"[eqY], "Exact"[hOk]
		}
	],
	machineTheorem["listSplitFirst",
		ForAll[{TypedImplicit[A, TypeUniverse[1]], Typed[xs, {A}]},
			Implies[1 <= Length[xs], Exists[{Typed[h, A], Typed[t, {A}]}, xs == Prepend[h][t]]]],
		{
			"Introduce"[A, xs], "Cases"[xs],
			"Introduce"[h], "Have"[h0, 1 <= 0], "Exact"[h], "Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"["falseElimination"[f]],
			"Introduce"[h, t, hl], "Exact"["existsIntroduction"[h, "existsIntroduction"[t, "equalityReflexivity"[Prepend[h][t]]]]]
		}
	],
	(* Case 4: focusSetA in state4A *)
	machineTheorem["caseSetA",
		ForAll[{Typed[w, NonNegativeIntegers], Typed[h, NonNegativeIntegers],
				Typed[ls, {"TapeItem"}], Typed[rs, {"TapeItem"}], Typed[le, "LeftEnd"], Typed[rc, "Closing"],
				Typed[xl, {Booleans}], Typed[b, Booleans], Typed[xr, {Booleans}], Typed[s, {NonNegativeIntegers}], Typed[c4p, "System4Configuration"]},
			Implies[(h + 1) + 3 <= "pow2"[w],
				Implies["allItemsOk"["pow2"[w], h + 2, ls],
					Implies["allItemsOk"["pow2"[w], h + 2, rs],
						Implies["leftItemsOk"["leftEndIsJunk"[le], ls],
							Implies["rightItemsOk"[rs],
								Implies["itemOk"["pow2"[w], h + 2, "itemSet"[Join["reverseList"[xl], Prepend[b][xr]], s]],
									Implies["leftEndOk"[h + 1, "acToSystem4"["abstractConfig"[ls, rs, le, rc, "state4A", "focusSetA"[xl, b, xr, s]]], le],
										Implies["system4Step"["acToSystem4"["abstractConfig"[ls, rs, le, rc, "state4A", "focusSetA"[xl, b, xr, s]]]] == "some"[c4p],
											"matchesStep"[w, h, rc, "acToSystem3"["abstractConfig"[ls, rs, le, rc, "state4A", "focusSetA"[xl, b, xr, s]]], c4p]]]]]]]]]],
		{
			"Introduce"[w, h, ls, rs, le, rc, xl, b, xr, s, c4p, hN, hls, hrs, hL, hR, hit, hle, hs],
			"Have"[hle2, "leftEndOk"[h, c4p, le]],
			"Exact"["leftEndOkStep"[le, h, "acToSystem4"["abstractConfig"[ls, rs, le, rc, "state4A", "focusSetA"[xl, b, xr, s]]], c4p, hs, hle]],
			"Have"[hN2, h + 3 <= "pow2"[w]], "LinearArithmetic",
			"Have"[leStep, h + 1 <= h + 2], "LinearArithmetic",
			"Have"[hit2, "itemOk"["pow2"[w], h + 1, "itemSet"[Join["reverseList"[xl], Prepend[b][xr]], s]]],
			"Exact"["itemOkMono"["pow2"[w], h + 1, h + 2, "itemSet"[Join["reverseList"[xl], Prepend[b][xr]], s], hit, leStep]],
			"Have"[hrs2, "allItemsOk"["pow2"[w], h + 1, rs]],
			"Exact"["allItemsOkMono"["pow2"[w], h + 1, h + 2, rs, hrs, leStep]],
			"Cases"[ls],
			(* ls = {}: turn at left end *)
			"Introduce"[hls, hL, hle, hs],
			"Have"[eqC4, c4p == "system4Configuration"[Typed[{}, {"System4Element"}], Prepend["set4"[s]][Map["itemToElem", rs]], "state4B"]],
			"Exact"["equalitySymmetry"["someInjectiveI"[hs]]],
			"Cases"[le],
			(* le = leftEndZeros[m, t] *)
			"Introduce"[m, t, hle2, hL, hle, hs],
			"Cases"[hle], "Introduce"[hm, ht],
			"Cases"["lessEqualExists"[h + 1, m, hm]], "Introduce"[dm, eqM],
			"Have"[eqM2, m == (dm + h) + 1], "LinearArithmetic",
			"Have"[hLenX, 1 <= Length[Join["reverseList"[xl], Prepend[b][xr]]]],
			"Cases"[hit], "Introduce"[hLx, h2], "Rewrite"[hLx], "Exact"["pow2Pos"[w]],
			"Cases"["listSplitFirst"[Join["reverseList"[xl], Prepend[b][xr]], hLenX]],
			"Introduce"[x0, ex1], "Cases"[ex1], "Introduce"[xRest, eqX],
			"Have"[hRun, "steps"["lookaheadStep"["system3"], (Length[xl] + t) + (t + 6),
				"acToSystem3"["abstractConfig"[Typed[{}, {"TapeItem"}], rs, "leftEndZeros"[m, t], rc, "state4A", "focusSetA"[xl, b, xr, s]]]] ==
				"some"["acToSystem3"["abstractConfig"[Typed[{}, {"TapeItem"}], rs, "leftEndZeros"[dm + h, t + 1], rc, "state4B", "focusSetB"[x0, xRest, s]]]]],
			"Change"["steps"["lookaheadStep"["system3"], (Length[xl] + t) + (t + 6),
				"lookaheadConfiguration"[Join["ofBits"[xl], "leftEndRev"[m, t]], "toCell"[b], Join["ofBits"[xr], Join["renderR"["false", rs], "closingRender"[rc]]], "stateA"]] ==
				"some"["lookaheadConfiguration"["leftEndRev"[dm + h, t + 1], "toCell"[x0], Join["ofBits"[xRest], Join["renderR"["false", rs], "closingRender"[rc]]], "stateB"]]],
			"Rewrite"[eqM2],
			"Exact"["turnRun"[xl, b, xr, dm + h, t, Join["renderR"["false", rs], "closingRender"[rc]], x0, xRest, eqX]],
			"Have"[hPos, 1 <= (Length[xl] + t) + (t + 6)], "LinearArithmetic",
			"Have"[hLeNew, And[h <= dm + h, 1 <= t + 1]],
			"Have"[a1, h <= dm + h], "LinearArithmetic", "Have"[a2, 1 <= t + 1], "LinearArithmetic", "Exact"["andIntroduction"[a1, a2]],
			"Have"[hitNew, "itemOk"["pow2"[w], h + 1, "itemSet"[Prepend[x0][xRest], s]]],
			"Rewrite"["equalitySymmetry"[eqX]], "Exact"[hit2],
			"Have"[hNotA, Not["state4B" == "state4A"]],
			"Introduce"[eq], "Exact"[Construct["equalitySubstitution", "System4State",
				Function[{Typed[st, "System4State"]}, InductiveRecursor["System4State"][Function[{Typed[q, "System4State"]}, TypeUniverse[0]], False, True, False, st]],
				"state4B", "state4A", eq, "trueIntroduction"]],
			"Exact"["existsIntroduction"[(Length[xl] + t) + (t + 6), "andIntroduction"[hPos,
				"existsIntroduction"["abstractConfig"[Typed[{}, {"TapeItem"}], rs, "leftEndZeros"[dm + h, t + 1], rc, "state4B", "focusSetB"[x0, xRest, s]],
					"andIntroduction"["equalityReflexivity"[rc], "andIntroduction"[hRun, "andIntroduction"[eqC4,
						"andIntroduction"[hN2, "andIntroduction"[hLeNew, "andIntroduction"["trueIntroduction",
							"andIntroduction"[hrs2, "andIntroduction"["trueIntroduction", "andIntroduction"[hR,
								"andIntroduction"[hNotA, hitNew]]]]]]]]]]]]]],
			(* le = leftEndJunk[cells]: impossible by safeCNow! *)
			"Introduce"[cells, hle2, hL, hle, hs],
			"Cases"["safeCNow"[h + 1, "acToSystem4"["abstractConfig"[Typed[{}, {"TapeItem"}], rs, "leftEndJunk"[cells], rc, "state4A", "focusSetA"[xl, b, xr, s]]], hle]],
			"Introduce"[ne], "Exact"["falseElimination"[ne["equalityReflexivity"[Typed[{}, {"System4Element"}]]]]],
			"Introduce"[eqAC], "Exact"["falseElimination"[Construct["equalitySubstitution", "System4State",
				Function[{Typed[st, "System4State"]}, InductiveRecursor["System4State"][Function[{Typed[q, "System4State"]}, TypeUniverse[0]], True, False, False, st]],
				"state4A", "state4C", eqAC, "trueIntroduction"]]],
			(* ls = it :: lsRest: walk left onto it *)
			"Introduce"[it, lsRest, hls, hL, hle, hs],
			"Cases"[hls], "Introduce"[hitL, hlsRest],
			"Have"[hls2, "allItemsOk"["pow2"[w], h + 1, lsRest]],
			"Exact"["allItemsOkMono"["pow2"[w], h + 1, h + 2, lsRest, hlsRest, leStep]],
			"Have"[eqC4, c4p == "system4Configuration"[Map["itemToElem", lsRest],
				Prepend["itemToElem"[it]][Prepend["set4"[s]][Map["itemToElem", rs]]], "state4A"]],
			"Exact"["equalitySymmetry"["someInjectiveI"[hs]]],
			"Have"[hPos, 1 <= Length[xl] + 1], "LinearArithmetic",
			"Cases"[it],
			(* it = itemSet[y, T] *)
			"Introduce"[y, T, hL, hle, hs, hitL, eqC4],
			"Have"[hLenRevY, 1 <= Length["reverseList"[y]]],
			"Rewrite"["lengthReverseList"[y]], "Cases"[hitL], "Introduce"[hLy, h2], "Rewrite"[hLy], "Exact"["pow2Pos"[w]],
			"Cases"["listSplitFirst"["reverseList"[y], hLenRevY]],
			"Introduce"[b2, ex1], "Cases"[ex1], "Introduce"[yl, eqRevY],
			"Have"[hRun, "steps"["lookaheadStep"["system3"], Length[xl] + 1,
				"acToSystem3"["abstractConfig"[Prepend["itemSet"[y, T]][lsRest], rs, le, rc, "state4A", "focusSetA"[xl, b, xr, s]]]] ==
				"some"["acToSystem3"["abstractConfig"[lsRest, Prepend["itemSet"[Join["reverseList"[xl], Prepend[b][xr]], s]][rs], le, rc, "state4A", "focusSetA"[yl, b2, Typed[{}, {Booleans}], T]]]]],
			"Change"["steps"["lookaheadStep"["system3"], Length[xl] + 1,
				"lookaheadConfiguration"[Join["ofBits"[xl], Join[Join["ofBits"["reverseList"[y]], "renderL"["false", lsRest]], "leftEndRender"[le]]],
					"toCell"[b], Join["ofBits"[xr], Join["renderR"["false", rs], "closingRender"[rc]]], "stateA"]] ==
				"some"["lookaheadConfiguration"[Join["ofBits"[yl], Join["renderL"["false", lsRest], "leftEndRender"[le]]],
					"toCell"[b2], Join[Join["ofBits"[Join["reverseList"[xl], Prepend[b][xr]]], "renderR"["false", rs]], "closingRender"[rc]], "stateA"]]],
			"Rewrite"[eqRevY],
			"Rewrite"["joinAssociativity"["ofBits"[Prepend[b2][yl]], "renderL"["false", lsRest], "leftEndRender"[le]]],
			"Rewrite"["joinAssociativity"["ofBits"[Join["reverseList"[xl], Prepend[b][xr]]], "renderR"["false", rs], "closingRender"[rc]]],
			"Have"[hWalk, "steps"["lookaheadStep"["system3"], Length["ofBits"[xl]] + 1,
				"lookaheadConfiguration"[Join["ofBits"[xl], Prepend["toCell"[b2]][Join["ofBits"[yl], Join["renderL"["false", lsRest], "leftEndRender"[le]]]]],
					"toCell"[b], Join["ofBits"[xr], Join["renderR"["false", rs], "closingRender"[rc]]], "stateA"]] ==
				"some"["lookaheadConfiguration"[Join["ofBits"[yl], Join["renderL"["false", lsRest], "leftEndRender"[le]]],
					"toCell"[b2], "revAppend"["ofBits"[xl], Prepend["toCell"[b]][Join["ofBits"[xr], Join["renderR"["false", rs], "closingRender"[rc]]]]], "stateA"]]],
			"Exact"["sys3WalkLeft"["ofBits"[xl], "toCell"[b2], Join["ofBits"[yl], Join["renderL"["false", lsRest], "leftEndRender"[le]]],
				"toCell"[b], Join["ofBits"[xr], Join["renderR"["false", rs], "closingRender"[rc]]], "ofBitsNonZero"[xl], "toCellNotZero"[b]]],
			"Rewrite"["equalitySymmetry"["lengthOfBits"[xl]]],
			"Rewrite"["equalitySymmetry"["ofBitsZipper"[xl, b, xr, Join["renderR"["false", rs], "closingRender"[rc]]]]],
			"Exact"[hWalk],
			"Have"[hleNew, "leftEndOk"[h, "acToSystem4"["abstractConfig"[lsRest, Prepend["itemSet"[Join["reverseList"[xl], Prepend[b][xr]], s]][rs], le, rc, "state4A", "focusSetA"[yl, b2, Typed[{}, {Booleans}], T]]], le]],
			"Change"["leftEndOk"[h, "system4Configuration"[Map["itemToElem", lsRest], Prepend["itemToElem"["itemSet"[y, T]]][Prepend["set4"[s]][Map["itemToElem", rs]]], "state4A"], le]],
			"Rewrite"["equalitySymmetry"[eqC4]], "Exact"[hle2],
			"Have"[hitNew, "itemOk"["pow2"[w], h + 1, "itemSet"[Join["reverseList"[yl], {b2}], T]]],
			"Exact"["itemOkReverseSplit"["pow2"[w], h + 1, y, T, b2, yl, eqRevY, "itemOkMono"["pow2"[w], h + 1, h + 2, "itemSet"[y, T], hitL, leStep]]],
			"Exact"["existsIntroduction"[Length[xl] + 1, "andIntroduction"[hPos,
				"existsIntroduction"["abstractConfig"[lsRest, Prepend["itemSet"[Join["reverseList"[xl], Prepend[b][xr]], s]][rs], le, rc, "state4A", "focusSetA"[yl, b2, Typed[{}, {Booleans}], T]],
					"andIntroduction"["equalityReflexivity"[rc], "andIntroduction"[hRun, "andIntroduction"[eqC4,
						"andIntroduction"[hN2, "andIntroduction"[hleNew, "andIntroduction"[hls2,
							"andIntroduction"["andIntroduction"[hit2, hrs2], "andIntroduction"[hL, "andIntroduction"[hR,
								"andIntroduction"["equalityReflexivity"["state4A"], hitNew]]]]]]]]]]]]]],
			(* it = itemStar *)
			"Introduce"[hL, hle, hs, hitL, eqC4],
			"Cases"[hL], "Introduce"[hLeftLast, hLRest],
			"Cases"[hLeftLast],
			(* headLastTrue[lsRest]: walk left onto star *)
			"Introduce"[hLastTrue],
			"Have"[hRun, "steps"["lookaheadStep"["system3"], Length[xl] + 1,
				"acToSystem3"["abstractConfig"[Prepend["itemStar"][lsRest], rs, le, rc, "state4A", "focusSetA"[xl, b, xr, s]]]] ==
				"some"["acToSystem3"["abstractConfig"[lsRest, Prepend["itemSet"[Join["reverseList"[xl], Prepend[b][xr]], s]][rs], le, rc, "state4A", "focusStar"]]]],
			"Change"["steps"["lookaheadStep"["system3"], Length[xl] + 1,
				"lookaheadConfiguration"[Join["ofBits"[xl], Prepend["color0"][Join["renderL"["true", lsRest], "leftEndRender"[le]]]],
					"toCell"[b], Join["ofBits"[xr], Join["renderR"["false", rs], "closingRender"[rc]]], "stateA"]] ==
				"some"["lookaheadConfiguration"[Join["renderL"["true", lsRest], "leftEndRender"[le]],
					"color0", Join[Join["ofBits"[Join["reverseList"[xl], Prepend[b][xr]]], "renderR"["false", rs]], "closingRender"[rc]], "stateA"]]],
			"Rewrite"["joinAssociativity"["ofBits"[Join["reverseList"[xl], Prepend[b][xr]]], "renderR"["false", rs], "closingRender"[rc]]],
			"Have"[hWalk, "steps"["lookaheadStep"["system3"], Length["ofBits"[xl]] + 1,
				"lookaheadConfiguration"[Join["ofBits"[xl], Prepend["color0"][Join["renderL"["true", lsRest], "leftEndRender"[le]]]],
					"toCell"[b], Join["ofBits"[xr], Join["renderR"["false", rs], "closingRender"[rc]]], "stateA"]] ==
				"some"["lookaheadConfiguration"[Join["renderL"["true", lsRest], "leftEndRender"[le]],
					"color0", "revAppend"["ofBits"[xl], Prepend["toCell"[b]][Join["ofBits"[xr], Join["renderR"["false", rs], "closingRender"[rc]]]]], "stateA"]]],
			"Exact"["sys3WalkLeft"["ofBits"[xl], "color0", Join["renderL"["true", lsRest], "leftEndRender"[le]],
				"toCell"[b], Join["ofBits"[xr], Join["renderR"["false", rs], "closingRender"[rc]]], "ofBitsNonZero"[xl], "toCellNotZero"[b]]],
			"Rewrite"["equalitySymmetry"["lengthOfBits"[xl]]],
			"Rewrite"["equalitySymmetry"["ofBitsZipper"[xl, b, xr, Join["renderR"["false", rs], "closingRender"[rc]]]]],
			"Exact"[hWalk],
			"Have"[hleNew, "leftEndOk"[h, "acToSystem4"["abstractConfig"[lsRest, Prepend["itemSet"[Join["reverseList"[xl], Prepend[b][xr]], s]][rs], le, rc, "state4A", "focusStar"]], le]],
			"Change"["leftEndOk"[h, "system4Configuration"[Map["itemToElem", lsRest], Prepend["itemToElem"["itemStar"]][Prepend["set4"[s]][Map["itemToElem", rs]]], "state4A"], le]],
			"Rewrite"["equalitySymmetry"[eqC4]], "Exact"[hle2],
			"Exact"["existsIntroduction"[Length[xl] + 1, "andIntroduction"[hPos,
				"existsIntroduction"["abstractConfig"[lsRest, Prepend["itemSet"[Join["reverseList"[xl], Prepend[b][xr]], s]][rs], le, rc, "state4A", "focusStar"],
					"andIntroduction"["equalityReflexivity"[rc], "andIntroduction"[hRun, "andIntroduction"[eqC4,
						"andIntroduction"[hN2, "andIntroduction"[hleNew, "andIntroduction"[hls2,
							"andIntroduction"["andIntroduction"[hit2, hrs2], "andIntroduction"[hLRest, "andIntroduction"[hR,
								"andIntroduction"[hLastTrue, "trueIntroduction"]]]]]]]]]]]]]],
			(* lsRest == {} && isJunk == true: impossible by safeCNow on c4p! *)
			"Introduce"[hJunkPair], "Cases"[hJunkPair], "Introduce"[eqEmpty, eqJunk],
			"Cases"[le],
			"Introduce"[m, t, hle2, hle, hs, hLRest, eqJunk],
			"Exact"["falseElimination"[Construct["equalitySubstitution", Booleans,
				Function[{Typed[q, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[u, Booleans]}, TypeUniverse[0]], True, False, q]],
				"false", "true", eqJunk, "trueIntroduction"]]],
			"Introduce"[cells, hle2, hle, hs, hLRest, eqJunk],
			"Have"[hSafe, "safeC"[h, "system4Configuration"[Typed[{}, {"System4Element"}], Prepend["star4"][Prepend["set4"[s]][Map["itemToElem", rs]]], "state4A"]]],
			"Change"["safeC"[h, "system4Configuration"[Map["itemToElem", Typed[{}, {"TapeItem"}]], Prepend["itemToElem"["itemStar"]][Prepend["set4"[s]][Map["itemToElem", rs]]], "state4A"]]],
			"Rewrite"["equalitySymmetry"[eqEmpty]], "Rewrite"["equalitySymmetry"[eqC4]], "Exact"[hle2],
			"Cases"["safeCNow"[h, "system4Configuration"[Typed[{}, {"System4Element"}], Prepend["star4"][Prepend["set4"[s]][Map["itemToElem", rs]]], "state4A"], hSafe]],
			"Introduce"[ne], "Exact"["falseElimination"[ne["equalityReflexivity"[Typed[{}, {"System4Element"}]]]]],
			"Introduce"[eqAC], "Exact"["falseElimination"[Construct["equalitySubstitution", "System4State",
				Function[{Typed[st, "System4State"]}, InductiveRecursor["System4State"][Function[{Typed[q, "System4State"]}, TypeUniverse[0]], True, False, False, st]],
				"state4A", "state4C", eqAC, "trueIntroduction"]]]
		}
	],
	(* Case 5: focusStar in state4A (Rule 2) *)
	machineTheorem["caseStarA",
		ForAll[{Typed[w, NonNegativeIntegers], Typed[h, NonNegativeIntegers],
				Typed[ls, {"TapeItem"}], Typed[rs, {"TapeItem"}], Typed[le, "LeftEnd"], Typed[rc, "Closing"], Typed[c4p, "System4Configuration"]},
			Implies[(h + 1) + 3 <= "pow2"[w],
				Implies["allItemsOk"["pow2"[w], h + 2, ls],
					Implies["allItemsOk"["pow2"[w], h + 2, rs],
						Implies["leftItemsOk"["leftEndIsJunk"[le], ls],
							Implies["rightItemsOk"[rs],
								Implies["headLastTrue"[ls],
									Implies["headSet"[rs],
										Implies["leftEndOk"[h + 1, "acToSystem4"["abstractConfig"[ls, rs, le, rc, "state4A", "focusStar"]], le],
											Implies["system4Step"["acToSystem4"["abstractConfig"[ls, rs, le, rc, "state4A", "focusStar"]]] == "some"[c4p],
												"matchesStep"[w, h, rc, "acToSystem3"["abstractConfig"[ls, rs, le, rc, "state4A", "focusStar"]], c4p]]]]]]]]]]],
		{
			"Introduce"[w, h, ls, rs, le, rc, c4p, hN, hls, hrs, hL, hR, hLast, hSet, hle, hs],
			"Have"[hle2, "leftEndOk"[h, c4p, le]],
			"Exact"["leftEndOkStep"[le, h, "acToSystem4"["abstractConfig"[ls, rs, le, rc, "state4A", "focusStar"]], c4p, hs, hle]],
			"Have"[hN2, h + 3 <= "pow2"[w]], "LinearArithmetic",
			"Have"[leStep, h + 1 <= h + 2], "LinearArithmetic",
			"Cases"[rs],
			"Introduce"[hrs, hR, hSet, hle, hs], "Exact"["falseElimination"[hSet]],
			"Introduce"[it, rsRest, hrs, hR, hSet, hle, hs],
			"Cases"[it],
			"Introduce"[y, U, hrs, hR, hSet, hle, hs],
			"Cases"[hrs], "Introduce"[hyOk, hrsRest],
			"Have"[hyPos, 1 <= Length[y]], "Cases"[hyOk], "Introduce"[hLy, h2], "Rewrite"[hLy], "Exact"["pow2Pos"[w]],
			"Cases"["listSplitFirst"[y, hyPos]], "Introduce"[y0, ex1], "Cases"[ex1], "Introduce"[yRest, eqY],
			"Have"[eqC4, c4p == "system4Configuration"[Map["itemToElem", ls], Prepend["set4"[U]][Map["itemToElem", rsRest]], "state4B"]],
			"Exact"["equalitySymmetry"["someInjectiveI"[hs]]],
			"Have"[hRun, "steps"["lookaheadStep"["system3"], 1,
				"acToSystem3"["abstractConfig"[ls, Prepend["itemSet"[y, U]][rsRest], le, rc, "state4A", "focusStar"]]] ==
				"some"["acToSystem3"["abstractConfig"[ls, rsRest, le, rc, "state4B", "focusSetB"[y0, yRest, U]]]]],
			"Change"["lookaheadStep"["system3", "lookaheadConfiguration"[Join["renderL"["true", ls], "leftEndRender"[le]], "color0",
				Join[Join["ofBits"[y], "renderR"["false", rsRest]], "closingRender"[rc]], "stateA"]] ==
				"some"["lookaheadConfiguration"[Join["renderL"["false", ls], "leftEndRender"[le]], "toCell"[y0],
					Join["ofBits"[yRest], Join["renderR"["false", rsRest], "closingRender"[rc]]], "stateB"]]],
			"Rewrite"[eqY],
			"Rewrite"["joinAssociativity"["ofBits"[Prepend[y0][yRest]], "renderR"["false", rsRest], "closingRender"[rc]]],
			"Change"["lookaheadStep"["system3", "lookaheadConfiguration"[Join["renderL"["true", ls], "leftEndRender"[le]], "color0",
				Prepend["toCell"[y0]][Join["ofBits"[yRest], Join["renderR"["false", rsRest], "closingRender"[rc]]]], "stateA"]] ==
				"some"["lookaheadConfiguration"[Join["renderL"["false", ls], "leftEndRender"[le]], "toCell"[y0],
					Join["ofBits"[yRest], Join["renderR"["false", rsRest], "closingRender"[rc]]], "stateB"]]],
			"Rewrite"["sys3TurnA"[Join["renderL"["true", ls], "leftEndRender"[le]], "toCell"[y0], Join["ofBits"[yRest], Join["renderR"["false", rsRest], "closingRender"[rc]]]]],
			"Rewrite"["equalitySymmetry"["renderLOfHeadLastTrue"[ls, hLast]]], "Reflexivity",
			"Have"[hleNew, "leftEndOk"[h, "acToSystem4"["abstractConfig"[ls, rsRest, le, rc, "state4B", "focusSetB"[y0, yRest, U]]], le]],
			"Change"["leftEndOk"[h, "system4Configuration"[Map["itemToElem", ls], Prepend["set4"[U]][Map["itemToElem", rsRest]], "state4B"], le]],
			"Rewrite"["equalitySymmetry"[eqC4]], "Exact"[hle2],
			"Have"[hNotA, Not["state4B" == "state4A"]],
			"Introduce"[eq], "Exact"[Construct["equalitySubstitution", "System4State",
				Function[{Typed[st, "System4State"]}, InductiveRecursor["System4State"][Function[{Typed[q, "System4State"]}, TypeUniverse[0]], False, True, False, st]],
				"state4B", "state4A", eq, "trueIntroduction"]],
			"Have"[hyNew, "itemOk"["pow2"[w], h + 1, "itemSet"[Prepend[y0][yRest], U]]],
			"Rewrite"["equalitySymmetry"[eqY]], "Exact"["itemOkMono"["pow2"[w], h + 1, h + 2, "itemSet"[y, U], hyOk, leStep]],
			"Exact"["existsIntroduction"[1, "andIntroduction"["lessEqualReflexivity",
				"existsIntroduction"["abstractConfig"[ls, rsRest, le, rc, "state4B", "focusSetB"[y0, yRest, U]],
					"andIntroduction"["equalityReflexivity"[rc], "andIntroduction"[hRun, "andIntroduction"[eqC4,
						"andIntroduction"[hN2, "andIntroduction"[hleNew, "andIntroduction"["allItemsOkMono"["pow2"[w], h + 1, h + 2, ls, hls, leStep],
							"andIntroduction"["allItemsOkMono"["pow2"[w], h + 1, h + 2, rsRest, hrsRest, leStep],
								"andIntroduction"[hL, "andIntroduction"[hR, "andIntroduction"[hNotA, hyNew]]]]]]]]]]]]]],
			"Introduce"[hrs, hR, hSet, hle, hs], "Exact"["falseElimination"[hSet]]
		}
	],
	(* Case 6: focusStar in state4B (Rule 4) *)
	machineTheorem["caseStarB",
		ForAll[{Typed[w, NonNegativeIntegers], Typed[h, NonNegativeIntegers],
				Typed[ls, {"TapeItem"}], Typed[rs, {"TapeItem"}], Typed[le, "LeftEnd"], Typed[rc, "Closing"], Typed[c4p, "System4Configuration"]},
			Implies[(h + 1) + 3 <= "pow2"[w],
				Implies["allItemsOk"["pow2"[w], h + 2, ls],
					Implies["allItemsOk"["pow2"[w], h + 2, rs],
						Implies["leftItemsOk"["leftEndIsJunk"[le], ls],
							Implies["rightItemsOk"[rs],
								Implies["headSet"[ls],
									Implies["headFirstTrue"[rs],
										Implies["leftEndOk"[h + 1, "acToSystem4"["abstractConfig"[ls, rs, le, rc, "state4B", "focusStar"]], le],
											Implies["system4Step"["acToSystem4"["abstractConfig"[ls, rs, le, rc, "state4B", "focusStar"]]] == "some"[c4p],
												"matchesStep"[w, h, rc, "acToSystem3"["abstractConfig"[ls, rs, le, rc, "state4B", "focusStar"]], c4p]]]]]]]]]]],
		{
			"Introduce"[w, h, ls, rs, le, rc, c4p, hN, hls, hrs, hL, hR, hSet, hFirst, hle, hs],
			"Have"[hle2, "leftEndOk"[h, c4p, le]],
			"Exact"["leftEndOkStep"[le, h, "acToSystem4"["abstractConfig"[ls, rs, le, rc, "state4B", "focusStar"]], c4p, hs, hle]],
			"Have"[hN2, h + 3 <= "pow2"[w]], "LinearArithmetic",
			"Have"[leStep, h + 1 <= h + 2], "LinearArithmetic",
			"Cases"[ls],
			"Introduce"[hls, hL, hSet, hle, hs], "Exact"["falseElimination"[hSet]],
			"Introduce"[it, lsRest, hls, hL, hSet, hle, hs],
			"Cases"[it],
			"Introduce"[y, T, hls, hL, hSet, hle, hs],
			"Cases"[hls], "Introduce"[hyOk, hlsRest],
			"Have"[hLenRevY, 1 <= Length["reverseList"[y]]],
			"Rewrite"["lengthReverseList"[y]], "Cases"[hyOk], "Introduce"[hLy, h2], "Rewrite"[hLy], "Exact"["pow2Pos"[w]],
			"Cases"["listSplitFirst"["reverseList"[y], hLenRevY]], "Introduce"[b2, ex1], "Cases"[ex1], "Introduce"[yl, eqRevY],
			"Have"[eqC4, c4p == "system4Configuration"[Map["itemToElem", lsRest], Prepend["set4"[T]][Map["itemToElem", rs]], "state4A"]],
			"Exact"["equalitySymmetry"["someInjectiveI"[hs]]],
			"Have"[hRun, "steps"["lookaheadStep"["system3"], 1,
				"acToSystem3"["abstractConfig"[Prepend["itemSet"[y, T]][lsRest], rs, le, rc, "state4B", "focusStar"]]] ==
				"some"["acToSystem3"["abstractConfig"[lsRest, rs, le, rc, "state4A", "focusSetA"[yl, b2, Typed[{}, {Booleans}], T]]]]],
			"Change"["lookaheadStep"["system3", "lookaheadConfiguration"[Join[Join["ofBits"["reverseList"[y]], "renderL"["false", lsRest]], "leftEndRender"[le]], "color0",
				Join["renderR"["true", rs], "closingRender"[rc]], "stateB"]] ==
				"some"["lookaheadConfiguration"[Join["ofBits"[yl], Join["renderL"["false", lsRest], "leftEndRender"[le]]], "toCell"[b2],
					Join["renderR"["false", rs], "closingRender"[rc]], "stateA"]]],
			"Rewrite"[eqRevY],
			"Rewrite"["joinAssociativity"["ofBits"[Prepend[b2][yl]], "renderL"["false", lsRest], "leftEndRender"[le]]],
			"Change"["lookaheadStep"["system3", "lookaheadConfiguration"[Prepend["toCell"[b2]][Join["ofBits"[yl], Join["renderL"["false", lsRest], "leftEndRender"[le]]]], "color0",
				Join["renderR"["true", rs], "closingRender"[rc]], "stateB"]] ==
				"some"["lookaheadConfiguration"[Join["ofBits"[yl], Join["renderL"["false", lsRest], "leftEndRender"[le]]], "toCell"[b2],
					Join["renderR"["false", rs], "closingRender"[rc]], "stateA"]]],
			"Rewrite"["sys3StarB"["toCell"[b2], Join["ofBits"[yl], Join["renderL"["false", lsRest], "leftEndRender"[le]]], Join["renderR"["true", rs], "closingRender"[rc]]]],
			"Rewrite"["equalitySymmetry"["renderROfHeadFirstTrue"[rs, hFirst]]], "Reflexivity",
			"Have"[hleNew, "leftEndOk"[h, "acToSystem4"["abstractConfig"[lsRest, rs, le, rc, "state4A", "focusSetA"[yl, b2, Typed[{}, {Booleans}], T]]], le]],
			"Change"["leftEndOk"[h, "system4Configuration"[Map["itemToElem", lsRest], Prepend["set4"[T]][Map["itemToElem", rs]], "state4A"], le]],
			"Rewrite"["equalitySymmetry"[eqC4]], "Exact"[hle2],
			"Have"[hyNew, "itemOk"["pow2"[w], h + 1, "itemSet"[Join["reverseList"[yl], {b2}], T]]],
			"Exact"["itemOkReverseSplit"["pow2"[w], h + 1, y, T, b2, yl, eqRevY, "itemOkMono"["pow2"[w], h + 1, h + 2, "itemSet"[y, T], hyOk, leStep]]],
			"Exact"["existsIntroduction"[1, "andIntroduction"["lessEqualReflexivity",
				"existsIntroduction"["abstractConfig"[lsRest, rs, le, rc, "state4A", "focusSetA"[yl, b2, Typed[{}, {Booleans}], T]],
					"andIntroduction"["equalityReflexivity"[rc], "andIntroduction"[hRun, "andIntroduction"[eqC4,
						"andIntroduction"[hN2, "andIntroduction"[hleNew, "andIntroduction"["allItemsOkMono"["pow2"[w], h + 1, h + 2, lsRest, hlsRest, leStep],
							"andIntroduction"["allItemsOkMono"["pow2"[w], h + 1, h + 2, rs, hrs, leStep],
								"andIntroduction"[hL, "andIntroduction"[hR, "andIntroduction"["equalityReflexivity"["state4A"], hyNew]]]]]]]]]]]]]],
			"Introduce"[hls, hL, hSet, hle, hs], "Exact"["falseElimination"[hSet]]
		}
	],
	(* Case 7: focusStar in state4C (Rule 5) *)
	machineTheorem["caseStarC",
		ForAll[{Typed[w, NonNegativeIntegers], Typed[h, NonNegativeIntegers],
				Typed[ls, {"TapeItem"}], Typed[rs, {"TapeItem"}], Typed[le, "LeftEnd"], Typed[rc, "Closing"], Typed[c4p, "System4Configuration"]},
			Implies[(h + 1) + 3 <= "pow2"[w],
				Implies["allItemsOk"["pow2"[w], h + 2, ls],
					Implies["allItemsOk"["pow2"[w], h + 2, rs],
						Implies["leftItemsOk"["leftEndIsJunk"[le], ls],
							Implies["rightItemsOk"[rs],
								Implies["leftLast"["leftEndIsJunk"[le], ls],
									Implies["headFirstTrue"[rs],
										Implies["leftEndOk"[h + 1, "acToSystem4"["abstractConfig"[ls, rs, le, rc, "state4C", "focusStar"]], le],
											Implies["system4Step"["acToSystem4"["abstractConfig"[ls, rs, le, rc, "state4C", "focusStar"]]] == "some"[c4p],
												"matchesStep"[w, h, rc, "acToSystem3"["abstractConfig"[ls, rs, le, rc, "state4C", "focusStar"]], c4p]]]]]]]]]]],
		{
			"Introduce"[w, h, ls, rs, le, rc, c4p, hN, hls, hrs, hL, hR, hLeftLast, hFirst, hle, hs],
			"Have"[hle2, "leftEndOk"[h, c4p, le]],
			"Exact"["leftEndOkStep"[le, h, "acToSystem4"["abstractConfig"[ls, rs, le, rc, "state4C", "focusStar"]], c4p, hs, hle]],
			"Have"[hN2, h + 3 <= "pow2"[w]], "LinearArithmetic",
			"Have"[leStep, h + 1 <= h + 2], "LinearArithmetic",
			"Cases"[rs],
			"Introduce"[hrs, hR, hFirst, hle, hs], "Exact"["falseElimination"[hFirst]],
			"Introduce"[it, rsRest, hrs, hR, hFirst, hle, hs],
			"Cases"[it],
			"Introduce"[y, U, hrs, hR, hFirst, hle, hs],
			"Cases"[hrs], "Introduce"[hyOk, hrsRest],
			"Cases"["firstTrueCons"[y, hFirst]], "Introduce"[yTail, eqY],
			"Cases"[hyOk], "Introduce"[hyLen, hy2], "Cases"[hy2], "Introduce"[hUInc, hUDec],
			"Have"[hyTailPos, 1 <= Length[yTail]],
			"Have"[hLenT, Length[yTail] + 1 == "pow2"[w]],
			"Change"[Length[Prepend["true"][yTail]] == "pow2"[w]], "Rewrite"["equalitySymmetry"[eqY]], "Exact"[hyLen],
			"LinearArithmetic",
			"Cases"["listSplitFirst"[yTail, hyTailPos]], "Introduce"[y1, ex1], "Cases"[ex1], "Introduce"[yRest, eqYT],
			"Have"[eqYFull, y == Prepend["true"][Prepend[y1][yRest]]],
			"Rewrite"[eqY], "Rewrite"[eqYT],
			"Have"[eqC4, c4p == "system4Configuration"[Prepend["star4"][Map["itemToElem", ls]], Prepend["set4"["xorMerge"[{1}, U]]][Map["itemToElem", rsRest]], "state4C"]],
			"Exact"["equalitySymmetry"["someInjectiveI"[hs]]],
			"Have"[hRun, "steps"["lookaheadStep"["system3"], 1,
				"acToSystem3"["abstractConfig"[ls, Prepend["itemSet"[y, U]][rsRest], le, rc, "state4C", "focusStar"]]] ==
				"some"["acToSystem3"["abstractConfig"[Prepend["itemStar"][ls], rsRest, le, rc, "state4C", "focusSetT"[y1, yRest, "xorMerge"[{1}, U]]]]]],
			"Change"["lookaheadStep"["system3", "lookaheadConfiguration"[Prepend["color0"][Join["renderL"["true", ls], "leftEndRender"[le]]], "color0",
				Join[Join["tailList"["ofBits"[y]], "renderR"["false", rsRest]], "closingRender"[rc]], "stateA"]] ==
				"some"["lookaheadConfiguration"[Prepend["color2"][Prepend["color0"][Join["renderL"["true", ls], "leftEndRender"[le]]]], "toCell"[y1],
					Join["ofBits"[yRest], Join["renderR"["false", rsRest], "closingRender"[rc]]], "stateB"]]],
			"Rewrite"[eqYFull],
			"Change"["lookaheadStep"["system3", "lookaheadConfiguration"[Prepend["color0"][Join["renderL"["true", ls], "leftEndRender"[le]]], "color0",
				Join[Join[Prepend["toCell"[y1]]["ofBits"[yRest]], "renderR"["false", rsRest]], "closingRender"[rc]], "stateA"]] ==
				"some"["lookaheadConfiguration"[Prepend["color2"][Prepend["color0"][Join["renderL"["true", ls], "leftEndRender"[le]]]], "toCell"[y1],
					Join["ofBits"[yRest], Join["renderR"["false", rsRest], "closingRender"[rc]]], "stateB"]]],
			"Rewrite"["joinAssociativity"[Prepend["toCell"[y1]]["ofBits"[yRest]], "renderR"["false", rsRest], "closingRender"[rc]]],
			"Exact"["sys3TurnA"[Prepend["color0"][Join["renderL"["true", ls], "leftEndRender"[le]]], "toCell"[y1],
				Join["ofBits"[yRest], Join["renderR"["false", rsRest], "closingRender"[rc]]]]],
			"Have"[hleNew, "leftEndOk"[h, "acToSystem4"["abstractConfig"[Prepend["itemStar"][ls], rsRest, le, rc, "state4C", "focusSetT"[y1, yRest, "xorMerge"[{1}, U]]]], le]],
			"Change"["leftEndOk"[h, "system4Configuration"[Prepend["star4"][Map["itemToElem", ls]], Prepend["set4"["xorMerge"[{1}, U]]][Map["itemToElem", rsRest]], "state4C"], le]],
			"Rewrite"["equalitySymmetry"[eqC4]], "Exact"[hle2],
			"Have"[hLenFull, Length[Prepend["true"][Prepend[y1][yRest]]] == "pow2"[w]],
			"Rewrite"["equalitySymmetry"[eqYFull]], "Exact"[hyLen],
			"Have"[hDecFull, "decodesBits"[Prepend["true"][Prepend[y1][yRest]], "xorMerge"[{1}, "xorMerge"[{1}, U]], h + 1]],
			"Have"[hDecU, "decodesBits"[Prepend["true"][Prepend[y1][yRest]], U, h + 1]],
			"Rewrite"["equalitySymmetry"[eqYFull]], "Exact"["decodesMono"[y, U, h + 1, h + 2, hUDec, leStep]],
			"Exact"["decodesXorOneTwice"[Prepend["true"][Prepend[y1][yRest]], U, h + 1, hUInc, hDecU]],
			"Exact"["existsIntroduction"[1, "andIntroduction"["lessEqualReflexivity",
				"existsIntroduction"["abstractConfig"[Prepend["itemStar"][ls], rsRest, le, rc, "state4C", "focusSetT"[y1, yRest, "xorMerge"[{1}, U]]],
					"andIntroduction"["equalityReflexivity"[rc], "andIntroduction"[hRun, "andIntroduction"[eqC4,
						"andIntroduction"[hN2, "andIntroduction"[hleNew,
							"andIntroduction"["andIntroduction"["trueIntroduction", "allItemsOkMono"["pow2"[w], h + 1, h + 2, ls, hls, leStep]],
								"andIntroduction"["allItemsOkMono"["pow2"[w], h + 1, h + 2, rsRest, hrsRest, leStep],
									"andIntroduction"["andIntroduction"[hLeftLast, hL], "andIntroduction"[hR,
										"andIntroduction"["equalityReflexivity"["state4C"],
											"andIntroduction"["xorMergeStrictlyIncreasing"[{1}, U, "trueIntroduction", hUInc],
												"andIntroduction"[hLenFull, hDecFull]]]]]]]]]]]]]]]],
			"Introduce"[hrs, hR, hFirst, hle, hs], "Exact"["falseElimination"[hFirst]]
		}
	],
	(* Combine all 7 cases into acStep, system3Simulation, and system0SimulatesSystem4 *)
	machineTheorem["acStep",
		ForAll[{Typed[w, NonNegativeIntegers], Typed[h, NonNegativeIntegers], Typed[a, "AbstractConfig"], Typed[c4p, "System4Configuration"]},
			Implies["acOk"[w, h + 1, a], Implies["system4Step"["acToSystem4"[a]] == "some"[c4p], "matchesStep"[w, h, a[["rc"]], "acToSystem3"[a], c4p]]]],
		{
			"Introduce"[w, h, a, c4p], "Cases"[a], "Introduce"[ls, rs, le, rc, st, foc, hOk, hs],
			"Cases"[hOk], "Introduce"[hN, h1], "Cases"[h1], "Introduce"[hle, h2],
			"Cases"[h2], "Introduce"[hls, h3], "Cases"[h3], "Introduce"[hrs, h4],
			"Cases"[h4], "Introduce"[hL, h5], "Cases"[h5], "Introduce"[hR, hfoc],
			"Cases"[foc],
			(* focusSetA *)
			"Introduce"[xl, b, xr, s, hs, hle, hfoc],
			"Cases"[hfoc], "Introduce"[eqSt, hit],
			"Rewrite"[eqSt],
			"Have"[hleA, "leftEndOk"[h + 1, "acToSystem4"["abstractConfig"[ls, rs, le, rc, "state4A", "focusSetA"[xl, b, xr, s]]], le]],
			"Rewrite"["equalitySymmetry"[eqSt]], "Exact"[hle],
			"Have"[hsA, "system4Step"["acToSystem4"["abstractConfig"[ls, rs, le, rc, "state4A", "focusSetA"[xl, b, xr, s]]]] == "some"[c4p]],
			"Rewrite"["equalitySymmetry"[eqSt]], "Exact"[hs],
			"Exact"["caseSetA"[w, h, ls, rs, le, rc, xl, b, xr, s, c4p, hN, hls, hrs, hL, hR, hit, hleA, hsA]],
			(* focusSetB *)
			"Introduce"[x0, xRest, s, hs, hle, hfoc],
			"Cases"[hfoc], "Introduce"[hst, hit],
			"Cases"[st],
			"Introduce"[hs, hle, hst], "Exact"["falseElimination"[hst["equalityReflexivity"["state4A"]]]],
			"Introduce"[hs, hle, hst], "Exact"["caseScanB"[w, h, ls, rs, le, rc, x0, xRest, s, c4p, hN, hls, hrs, hL, hR, hit, hle, hs]],
			"Introduce"[hs, hle, hst], "Exact"["caseScanC"[w, h, ls, rs, le, rc, x0, xRest, s, c4p, hN, hls, hrs, hL, hR, hit, hle, hs]],
			(* focusSetT *)
			"Introduce"[x1, xRest, s, hs, hle, hfoc],
			"Cases"[hfoc], "Introduce"[eqSt, hf2], "Cases"[hf2], "Introduce"[hsInc, hf3], "Cases"[hf3], "Introduce"[hxLen, hsDec],
			"Have"[hleC, "leftEndOk"[h + 1, "acToSystem4"["abstractConfig"[ls, rs, le, rc, "state4C", "focusSetT"[x1, xRest, s]]], le]],
			"Rewrite"["equalitySymmetry"[eqSt]], "Exact"[hle],
			"Have"[hsC, "system4Step"["acToSystem4"["abstractConfig"[ls, rs, le, rc, "state4C", "focusSetT"[x1, xRest, s]]]] == "some"[c4p]],
			"Rewrite"["equalitySymmetry"[eqSt]], "Exact"[hs],
			"Exact"["caseScanT"[w, h, ls, rs, le, rc, x1, xRest, s, c4p, hN, hls, hrs, hL, hR, hsInc, hxLen, hsDec, hleC, hsC]],
			(* focusStar *)
			"Introduce"[hs, hle, hfoc],
			"Cases"[st],
			"Introduce"[hs, hle, hfoc], "Cases"[hfoc], "Introduce"[hLast, hSet],
			"Exact"["caseStarA"[w, h, ls, rs, le, rc, c4p, hN, hls, hrs, hL, hR, hLast, hSet, hle, hs]],
			"Introduce"[hs, hle, hfoc], "Cases"[hfoc], "Introduce"[hSet, hFirst],
			"Exact"["caseStarB"[w, h, ls, rs, le, rc, c4p, hN, hls, hrs, hL, hR, hSet, hFirst, hle, hs]],
			"Introduce"[hs, hle, hfoc], "Cases"[hfoc], "Introduce"[hLeftLast, hFirst],
			"Exact"["caseStarC"[w, h, ls, rs, le, rc, c4p, hN, hls, hrs, hL, hR, hLeftLast, hFirst, hle, hs]],
			(* focusOff: rs == {} => system4Step == none, contradiction! *)
			"Introduce"[hs, hle, hfoc],
			"Have"[hsNone, Typed["none", Option["System4Configuration"]] == "some"[c4p]],
			"Change"["system4Step"["system4Configuration"[Map["itemToElem", ls], Map["itemToElem", Typed[{}, {"TapeItem"}]], st]] == "some"[c4p]],
			"Rewrite"["equalitySymmetry"[hfoc]], "Exact"[hs],
			"Exact"["falseElimination"["noneNotSomeI"[hsNone]]]
		}
	],
	(* Main Rung 5 Forward Simulation: System 4 -> System 3 *)
	machineTheorem["system3Simulation",
		ForAll[{Typed[w, NonNegativeIntegers], Typed[rc, "Closing"]},
			"forwardSimulation"["fueledSystem4Step", "lookaheadStep"["system3"], "system3Represents"[w, rc]]],
		{
			"Introduce"[w, rc, fs, c3, fs2, hRep, hStep],
			"Cases"[hRep], "Introduce"[a, hr1], "Cases"[hr1], "Introduce"[hRc, hr2],
			"Cases"[hr2], "Introduce"[hOk, hr3], "Cases"[hr3], "Introduce"[eqC3, eqC4],
			"Cases"[fs], "Introduce"[c4, h, hStep, hOk, eqC4],
			"Cases"[h],
			"Introduce"[hStep, hOk, eqC4], "Exact"["falseElimination"["noneNotSomeI"[hStep]]],
			"Introduce"[h1, hStep, hOk, eqC4],
			"Have"[stepEx, Exists[{Typed[c4p, "System4Configuration"]}, And["system4Step"[c4] == "some"[c4p], fs2 == "fueledSystem4"[c4p, h1]]]],
			"Have"[gen, ForAll[{Typed[o, Option["System4Configuration"]]},
				Implies["optionMap"[Function[{Typed[c2, "System4Configuration"]}, "fueledSystem4"[c2, h1]], o] == "some"[fs2],
					Exists[{Typed[c4p, "System4Configuration"]}, And[o == "some"[c4p], fs2 == "fueledSystem4"[c4p, h1]]]]]],
			"Introduce"[o], "Cases"[o],
			"Introduce"[he], "Exact"["falseElimination"["noneNotSomeI"[he]]],
			"Introduce"[c4p, he],
			"Exact"["existsIntroduction"[c4p, "andIntroduction"["equalityReflexivity"["some"[c4p]], "equalitySymmetry"["someInjectiveI"[he]]]]],
			"Exact"[gen["system4Step"[c4], hStep]],
			"Cases"[stepEx], "Introduce"[c4p, he1], "Cases"[he1], "Introduce"[hs4, eqFs2],
			"Have"[hs4a, "system4Step"["acToSystem4"[a]] == "some"[c4p]], "Rewrite"["equalitySymmetry"[eqC4]], "Exact"[hs4],
			"Cases"["acStep"[w, h1, a, c4p, hOk, hs4a]],
			"Introduce"[k, hm1], "Cases"[hm1], "Introduce"[kPos, hm2],
			"Cases"[hm2], "Introduce"[a2, hm3], "Cases"[hm3], "Introduce"[hRc2, hm4],
			"Cases"[hm4], "Introduce"[hRun, hm5], "Cases"[hm5], "Introduce"[eqC4p, hOk2],
			"Have"[hRunC3, "steps"["lookaheadStep"["system3"], k, c3] == "some"["acToSystem3"[a2]]], "Rewrite"[eqC3], "Exact"[hRun],
			"Have"[hRc2Fixed, a2[["rc"]] == rc], "Rewrite"["equalitySymmetry"[hRc]], "Exact"[hRc2],
			"Rewrite"[eqFs2],
			"Exact"["existsIntroduction"[k, "andIntroduction"[kPos,
				"existsIntroduction"["acToSystem3"[a2], "andIntroduction"[hRunC3,
					"existsIntroduction"[a2, "andIntroduction"[hRc2Fixed, "andIntroduction"[hOk2,
						"andIntroduction"["equalityReflexivity"["acToSystem3"[a2]], eqC4p]]]]]]]]]
		}
	],
	(* Composition with Rung 6 (on lookaheadStep["system0"] for Rung 7 confinement!) *)
	machineTheorem["system0SimulatesSystem4",
		ForAll[{Typed[w, NonNegativeIntegers], Typed[rc, "Closing"]},
			"forwardSimulation"["fueledSystem4Step", "lookaheadStep"["system0"],
				Function[{Typed[fs, "FueledSystem4"], Typed[c0, "LookaheadConfiguration"]},
					Exists[{Typed[c3, "LookaheadConfiguration"]}, And["system3Represents"[w, rc, fs, c3], c0 == "phi2"["phi3"[c3]]]]]]],
		{
			"Introduce"[w, rc, fs, c0, fs2, hRel, hStep],
			"Cases"[hRel], "Introduce"[c3, hc], "Cases"[hc], "Introduce"[hRep, eqC0],
			"Cases"["system3Simulation"[w, rc, fs, c3, fs2, hRep, hStep]],
			"Introduce"[k, hk1], "Cases"[hk1], "Introduce"[kPos, hk2],
			"Cases"[hk2], "Introduce"[c3p, hk3], "Cases"[hk3], "Introduce"[hRun3, hRep2],
			"Have"[hRel30, Exists[{Typed[d1, "LookaheadConfiguration"]},
				And[Exists[{Typed[d2, "LookaheadConfiguration"]}, And[d2 == "phi3"[c3], d1 == "phi2"[d2]]], c0 == d1]]],
			"Exact"["existsIntroduction"["phi2"["phi3"[c3]],
				"andIntroduction"["existsIntroduction"["phi3"[c3],
					"andIntroduction"["equalityReflexivity"["phi3"[c3]], "equalityReflexivity"["phi2"["phi3"[c3]]]]], eqC0]]],
			"Cases"["forwardSimulationSteps"["LookaheadConfiguration", "LookaheadConfiguration", "lookaheadStep"["system3"], "lookaheadStep"["system0"],
				Function[{Typed[c, "LookaheadConfiguration"], Typed[e, "LookaheadConfiguration"]},
					Exists[{Typed[d1, "LookaheadConfiguration"]}, And[Exists[{Typed[d2, "LookaheadConfiguration"]}, And[d2 == "phi3"[c], d1 == "phi2"[d2]]], e == d1]]],
				"system0Simulates3", k, c3, c0, c3p, hRel30, hRun3]],
			"Introduce"[m, hm1], "Cases"[hm1], "Introduce"[kLeM, hm2],
			"Have"[mPos, 1 <= m], "LinearArithmetic",
			"Cases"[hm2], "Introduce"[c0p, hm3], "Cases"[hm3], "Introduce"[hRun0, hRel2],
			"Cases"[hRel2], "Introduce"[d1, hd1], "Cases"[hd1], "Introduce"[exD2, eqC0p],
			"Cases"[exD2], "Introduce"[d2, hd2], "Cases"[hd2], "Introduce"[eqD2, eqD1],
			"Have"[eqFinal, c0p == "phi2"["phi3"[c3p]]],
			"Rewrite"[eqC0p], "Rewrite"[eqD1], "Rewrite"[eqD2],
			"Exact"["existsIntroduction"[m, "andIntroduction"[mPos,
				"existsIntroduction"[c0p, "andIntroduction"[hRun0,
					"existsIntroduction"[c3p, "andIntroduction"[hRep2, eqFinal]]]]]]]
		}
	],

	(* =================================================================== *)
	(* Part 1: Initial Tape Encoder (baseSet, encSet, initAC, rep3Init)    *)
	(* =================================================================== *)
	TypeTheoryDefinition["baseSet", Typed[
		Function[{Typed[n, NonNegativeIntegers], Typed[s, {NonNegativeIntegers}]},
			InductiveRecursor[List][Function[{Typed[q, {NonNegativeIntegers}]}, {Booleans}], "zerosBits"[n],
				Function[{Typed[e, NonNegativeIntegers], Typed[rest, {NonNegativeIntegers}], Typed[prev, {Booleans}]},
					"xorBits"["rowBits"[n, e], prev]], s]],
		NonNegativeIntegers -> {NonNegativeIntegers} -> {Booleans}
	]],
	machineTheorem["lengthBaseSet",
		ForAll[{Typed[n, NonNegativeIntegers], Typed[s, {NonNegativeIntegers}]},
			Implies[1 <= n, Length["baseSet"[n, s]] == n]],
		{
			"Introduce"[n, s, hn], "Induction"[s],
			"Exact"["lengthZerosBits"[n]],
			"Introduce"[e, rest, ih],
			"Change"[Length["xorBits"["rowBits"[n, e], "baseSet"[n, rest]]] == n],
			"Have"[hEq, Length["rowBits"[n, e]] == Length["baseSet"[n, rest]]],
			"Rewrite"["lengthRowBits"[n, e, hn]], "Rewrite"[ih],
			"Rewrite"["lengthXorBits"["rowBits"[n, e], "baseSet"[n, rest], hEq]],
			"Exact"["lengthRowBits"[n, e, hn]]
		}
	],
	machineTheorem["parAtBaseSet",
		ForAll[{Typed[w, NonNegativeIntegers], Typed[s, {NonNegativeIntegers}], Typed[i, NonNegativeIntegers]},
			Implies["strictlyIncreasing"[s],
				Implies["allBelowEqual"[Subtract["pow2"[w], 1], s],
					Implies[i + 1 <= "pow2"[w], "parAt"["baseSet"["pow2"[w], s], i] == "memNat"[i, s]]]]],
		{
			"Introduce"[w, s], "Induction"[s],
			"Introduce"[i, hInc, hBd, hi], "Exact"["parAtZeros"["pow2"[w], i]],
			"Introduce"[e, rest, ih, i, hInc, hBd, hi],
			"Cases"[hBd], "Introduce"[heBd, hRestBd],
			"Have"[hPos, 1 <= "pow2"[w]], "Exact"["pow2Pos"[w]],
			"Have"[heLt, e + 1 <= "pow2"[w]],
			"Cases"["lessEqualExists"[1, "pow2"[w], hPos]], "Introduce"[m, eqP],
			"Have"[hSub, Subtract["pow2"[w], 1] == m], "Rewrite"[eqP], "Exact"["additionSubtractionCancellation"[m, 1]],
			"Have"[heM, e <= m], "Rewrite"["equalitySymmetry"[hSub]], "Exact"[heBd],
			"Rewrite"[eqP], "LinearArithmetic",
			"Have"[hRestInc, "strictlyIncreasing"[rest]],
			"Cases"[rest], "Introduce"[ih, hInc, hRestBd], "Exact"["trueIntroduction"],
			"Introduce"[e2, r2, ih, hInc, hRestBd], "Cases"[hInc], "Introduce"[he2, hR2Above], "Exact"[hR2Above],
			"Have"[hLenEq, Length["rowBits"["pow2"[w], e]] == Length["baseSet"["pow2"[w], rest]]],
			"Rewrite"["lengthRowBits"["pow2"[w], e, hPos]],
			"Rewrite"["lengthBaseSet"["pow2"[w], rest, hPos]],
			"Change"["parAt"["xorBits"["rowBits"["pow2"[w], e], "baseSet"["pow2"[w], rest]], i] == "memNat"[i, Prepend[e][rest]]],
			"Rewrite"["parAtXor"["rowBits"["pow2"[w], e], "baseSet"["pow2"[w], rest], i, hLenEq]],
			"Rewrite"["parAtRowBits"[w, e, i, heLt, hi]],
			"Rewrite"[ih[i, hRestInc, hRestBd, hi]],
			"Have"[dec, Decidable[i == e]], "Exact"["naturalNumberEqualityDecidable"[i, e]], "Cases"[dec],
			"Introduce"[neq],
			"Change"["xorBool"[Decide[i == e], "memNat"[i, rest]] ==
				InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Booleans], "memNat"[i, rest], "true", Decide[i == e]]],
			"Rewrite"["decideEqualFalse"[i, e, neq]], "Reflexivity",
			"Introduce"[eq],
			"Change"["xorBool"[Decide[i == e], "memNat"[i, rest]] ==
				InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Booleans], "memNat"[i, rest], "true", Decide[i == e]]],
			"Rewrite"["decideEqualTrue"[i, e, eq]],
			"Have"[notIn, "memNat"[i, rest] == "false"],
			"Rewrite"[eq], "Exact"["memNatStrictlyAboveFalse"[e, e, rest, "lessEqualReflexivity", hInc]],
			"Rewrite"[notIn], "Reflexivity"
		}
	],
	TypeTheoryDefinition["encSet", Typed[
		Function[{Typed[n, NonNegativeIntegers], Typed[s, {NonNegativeIntegers}]},
			InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, {Booleans}],
				"xorBits"["baseSet"[n, s], "rowBits"[n, Subtract[n, 2]]],
				"baseSet"[n, s],
				"headBool"["baseSet"[n, s]]]],
		NonNegativeIntegers -> {NonNegativeIntegers} -> {Booleans}
	]],
	machineTheorem["lengthEncSet",
		ForAll[{Typed[n, NonNegativeIntegers], Typed[s, {NonNegativeIntegers}]},
			Implies[1 <= n, Length["encSet"[n, s]] == n]],
		{
			"Introduce"[n, s, hn],
			"Have"[gen, ForAll[{Typed[b, Booleans]},
				Length[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, {Booleans}],
					"xorBits"["baseSet"[n, s], "rowBits"[n, Subtract[n, 2]]],
					"baseSet"[n, s], b]] == n]],
			"Introduce"[b], "Cases"[b],
			"Change"[Length["xorBits"["baseSet"[n, s], "rowBits"[n, Subtract[n, 2]]]] == n],
			"Have"[hEq, Length["baseSet"[n, s]] == Length["rowBits"[n, Subtract[n, 2]]]],
			"Rewrite"["lengthBaseSet"[n, s, hn]], "Rewrite"["lengthRowBits"[n, Subtract[n, 2], hn]],
			"Rewrite"["lengthXorBits"["baseSet"[n, s], "rowBits"[n, Subtract[n, 2]], hEq]],
			"Exact"["lengthBaseSet"[n, s, hn]],
			"Exact"["lengthBaseSet"[n, s, hn]],
			"Exact"[gen["headBool"["baseSet"[n, s]]]]
		}
	],
	machineTheorem["stepRFirstTrue",
		ForAll[{Typed[xs, {Booleans}]}, Implies["firstTrue"[xs], "firstTrue"["stepR"[xs]]]],
		{
			"Introduce"[xs, h],
			"Cases"["firstTrueCons"[xs, h]], "Introduce"[rest, eq],
			"Rewrite"[eq], "Exact"["equalityReflexivity"["true"]]
		}
	],
	machineTheorem["rowBitsFirstTrue",
		ForAll[{Typed[n, NonNegativeIntegers], Typed[i, NonNegativeIntegers]},
			Implies[1 <= n, "firstTrue"["rowBits"[n, i]]]],
		{
			"Introduce"[n, i, hn], "Induction"[i],
			"Cases"["lessEqualExists"[1, n, hn]], "Introduce"[m, eqN],
			"Rewrite"[eqN], "Exact"["equalityReflexivity"["true"]],
			"Introduce"[k, ih],
			"Change"["firstTrue"["stepR"["rowBits"[n, k]]]],
			"Exact"["stepRFirstTrue"["rowBits"[n, k], ih]]
		}
	],
	machineTheorem["firstTrueEncSet",
		ForAll[{Typed[w, NonNegativeIntegers], Typed[s, {NonNegativeIntegers}]},
			"firstTrue"["encSet"["pow2"[w], s]]],
		{
			"Introduce"[w, s],
			"Have"[hPos, 1 <= "pow2"[w]], "Exact"["pow2Pos"[w]],
			"Have"[hLen, Length["baseSet"["pow2"[w], s]] == "pow2"[w]], "Exact"["lengthBaseSet"["pow2"[w], s, hPos]],
			"Have"[hPosB, 1 <= Length["baseSet"["pow2"[w], s]]], "Rewrite"[hLen], "Exact"[hPos],
			"Cases"["listSplitFirst"["baseSet"["pow2"[w], s], hPosB]],
			"Introduce"[b, ex], "Cases"[ex], "Introduce"[rest, eqB],
			"Change"["firstTrue"[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, {Booleans}],
				"xorBits"["baseSet"["pow2"[w], s], "rowBits"["pow2"[w], Subtract["pow2"[w], 2]]],
				"baseSet"["pow2"[w], s], "headBool"["baseSet"["pow2"[w], s]]]]],
			"Rewrite"[eqB],
			"Cases"[b],
			(* b = false *)
			"Introduce"[eqB],
			"Cases"["firstTrueCons"["rowBits"["pow2"[w], Subtract["pow2"[w], 2]], "rowBitsFirstTrue"["pow2"[w], Subtract["pow2"[w], 2], hPos]]],
			"Introduce"[rTail, eqR],
			"Change"["firstTrue"["xorBits"[Prepend["false"][rest], "rowBits"["pow2"[w], Subtract["pow2"[w], 2]]]]],
			"Rewrite"[eqR], "Exact"["equalityReflexivity"["true"]],
			(* b = true *)
			"Introduce"[eqB],
			"Exact"["equalityReflexivity"["true"]]
		}
	],
	machineTheorem["decodesEncSet",
		ForAll[{Typed[w, NonNegativeIntegers], Typed[k, NonNegativeIntegers], Typed[s, {NonNegativeIntegers}]},
			Implies["strictlyIncreasing"[s],
				Implies["allBelowEqual"[Subtract["pow2"[w], 1], s],
					Implies[k + 2 <= "pow2"[w], "decodesBits"["encSet"["pow2"[w], s], s, k]]]]],
		{
			"Introduce"[w, k, s, hInc, hBd, hk, i, hi],
			"Have"[hPos, 1 <= "pow2"[w]], "Exact"["pow2Pos"[w]],
			"Have"[hiP, i + 1 <= "pow2"[w]], "LinearArithmetic",
			"Have"[hBase, "parAt"["baseSet"["pow2"[w], s], i] == "memNat"[i, s]],
			"Exact"["parAtBaseSet"[w, s, i, hInc, hBd, hiP]],
			"Have"[hSub2Lt, Subtract["pow2"[w], 2] + 1 <= "pow2"[w]],
			"Have"[le2, 2 <= "pow2"[w]], "LinearArithmetic",
			"Cases"["lessEqualExists"[2, "pow2"[w], le2]], "Introduce"[m, eqP],
			"Have"[hSub, Subtract["pow2"[w], 2] == m], "Rewrite"[eqP], "Exact"["additionSubtractionCancellation"[m, 2]],
			"Rewrite"[hSub], "Rewrite"[eqP], "LinearArithmetic",
			"Have"[neqSub2, Not[i == Subtract["pow2"[w], 2]]],
			"Introduce"[eq],
			"Have"[le2, 2 <= "pow2"[w]], "LinearArithmetic",
			"Cases"["lessEqualExists"[2, "pow2"[w], le2]], "Introduce"[m, eqP],
			"Have"[hSub, Subtract["pow2"[w], 2] == m], "Rewrite"[eqP], "Exact"["additionSubtractionCancellation"[m, 2]],
			"Have"[eqM, i == m], "Rewrite"[eq], "Exact"[hSub],
			"Have"[f, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"[f],
			"Have"[gen, ForAll[{Typed[b, Booleans]},
				"parAt"[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, {Booleans}],
					"xorBits"["baseSet"["pow2"[w], s], "rowBits"["pow2"[w], Subtract["pow2"[w], 2]]],
					"baseSet"["pow2"[w], s], b], i] == "memNat"[i, s]]],
			"Introduce"[b], "Cases"[b],
			"Change"["parAt"["xorBits"["baseSet"["pow2"[w], s], "rowBits"["pow2"[w], Subtract["pow2"[w], 2]]], i] == "memNat"[i, s]],
			"Have"[hLenEq, Length["baseSet"["pow2"[w], s]] == Length["rowBits"["pow2"[w], Subtract["pow2"[w], 2]]]],
			"Rewrite"["lengthBaseSet"["pow2"[w], s, hPos]],
			"Rewrite"["lengthRowBits"["pow2"[w], Subtract["pow2"[w], 2], hPos]],
			"Rewrite"["parAtXor"["baseSet"["pow2"[w], s], "rowBits"["pow2"[w], Subtract["pow2"[w], 2]], i, hLenEq]],
			"Rewrite"[hBase],
			"Rewrite"["parAtRowBits"[w, Subtract["pow2"[w], 2], i, hSub2Lt, hiP]],
			"Rewrite"["decideEqualFalse"[i, Subtract["pow2"[w], 2], neqSub2]],
			"Exact"["xorBoolFalseRight"["memNat"[i, s]]],
			"Exact"[hBase],
			"Exact"[gen["headBool"["baseSet"["pow2"[w], s]]]]
		}
	],
	machineTheorem["itemOkEncSet",
		ForAll[{Typed[w, NonNegativeIntegers], Typed[k, NonNegativeIntegers], Typed[s, {NonNegativeIntegers}]},
			Implies["strictlyIncreasing"[s],
				Implies["allBelowEqual"[Subtract["pow2"[w], 1], s],
					Implies[k + 2 <= "pow2"[w], "itemOk"["pow2"[w], k, "itemSet"["encSet"["pow2"[w], s], s]]]]]],
		{
			"Introduce"[w, k, s, hInc, hBd, hk],
			"Exact"["andIntroduction"["lengthEncSet"["pow2"[w], s, "pow2Pos"[w]],
				"andIntroduction"[hInc, "decodesEncSet"[w, k, s, hInc, hBd, hk]]]]
		}
	],
	TypeTheoryDefinition["toItem", Typed[
		Function[{Typed[n, NonNegativeIntegers], Typed[e, "System4Element"]},
			InductiveRecursor["System4Element"][Function[{Typed[q, "System4Element"]}, "TapeItem"],
				"itemStar",
				Function[{Typed[s, {NonNegativeIntegers}]}, "itemSet"["encSet"[n, s], s]], e]],
		NonNegativeIntegers -> "System4Element" -> "TapeItem"
	]],
	machineTheorem["mapItemToElemToItem",
		ForAll[{Typed[n, NonNegativeIntegers], Typed[xs, {"System4Element"}]},
			Map["itemToElem", Map["toItem"[n], xs]] == xs],
		{
			"Introduce"[n, xs], "Induction"[xs], "Reflexivity",
			"Introduce"[e, rest, ih], "Cases"[e],
			"Change"[Prepend["star4"][Map["itemToElem", Map["toItem"[n], rest]]] == Prepend["star4"][rest]], "Rewrite"[ih],
			"Introduce"[s],
			"Change"[Prepend["set4"[s]][Map["itemToElem", Map["toItem"[n], rest]]] == Prepend["set4"[s]][rest]], "Rewrite"[ih]
		}
	],
	machineTheorem["allItemsOkMapToItem",
		ForAll[{Typed[w, NonNegativeIntegers], Typed[k, NonNegativeIntegers], Typed[xs, {"System4Element"}]},
			Implies[k + 2 <= "pow2"[w],
				Implies["allTapeSetsOk"[Subtract["pow2"[w], 1], xs],
					"allItemsOk"["pow2"[w], k, Map["toItem"["pow2"[w]], xs]]]]],
		{
			"Introduce"[w, k, xs], "Induction"[xs],
			"Introduce"[hk, hOk], "Exact"["trueIntroduction"],
			"Introduce"[e, rest, ih, hk, hOk],
			"Cases"[hOk], "Introduce"[he, hRest],
			"Cases"[e],
			"Introduce"[he], "Exact"["andIntroduction"["trueIntroduction", ih[hk, hRest]]],
			"Introduce"[s, he], "Cases"[he], "Introduce"[hsInc, hsBd],
			"Exact"["andIntroduction"["itemOkEncSet"[w, k, s, hsInc, hsBd, hk], ih[hk, hRest]]]
		}
	],
	machineTheorem["rightItemsOkMapToItem",
		ForAll[{Typed[w, NonNegativeIntegers], Typed[xs, {"System4Element"}]},
			Implies["noAdjacentStarsFrom"["false", xs],
				Implies[Implies[Not[xs == Typed[{}, {"System4Element"}]], "endsWithSet4"[xs]],
					"rightItemsOk"[Map["toItem"["pow2"[w]], xs]]]]],
		{
			"Introduce"[w, xs], "Induction"[xs],
			"Introduce"[hAdj, hEnd], "Exact"["trueIntroduction"],
			"Introduce"[e, rest, ih, hAdj, hEnd],
			"Have"[hRestEnd, Implies[Not[rest == Typed[{}, {"System4Element"}]], "endsWithSet4"[rest]]],
			"Introduce"[hNe],
			"Have"[hAllEnd, "endsWithSet4"[Prepend[e][rest]]],
			"Have"[hNeAll, Not[Prepend[e][rest] == Typed[{}, {"System4Element"}]]],
			"Introduce"[eq],
			"Exact"[Construct["equalitySubstitution", {"System4Element"},
				Function[{Typed[l, {"System4Element"}]}, InductiveRecursor[List][Function[{Typed[q, {"System4Element"}]}, TypeUniverse[0]], False, Function[{Typed[h, "System4Element"], Typed[t, {"System4Element"}], Typed[u, TypeUniverse[0]]}, True], l]],
				Prepend[e][rest], Typed[{}, {"System4Element"}], eq, "trueIntroduction"]],
			"Exact"[hEnd[hNeAll]],
			"Have"[genTail, ForAll[{Typed[l, {"System4Element"}], Typed[b, Booleans]},
				Implies[Not[l == Typed[{}, {"System4Element"}]],
					Implies[InductiveRecursor[List][Function[{Typed[q, {"System4Element"}]}, Booleans -> TypeUniverse[0]],
						Function[{Typed[lw, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, TypeUniverse[0]], False, True, lw]],
						Function[{Typed[x, "System4Element"], Typed[t, {"System4Element"}], Typed[p, Booleans -> TypeUniverse[0]]},
							Function[{Typed[lw, Booleans]}, InductiveRecursor["System4Element"][Function[{Typed[q, "System4Element"]}, TypeUniverse[0]], p["false"], Function[{Typed[s, {NonNegativeIntegers}]}, p["true"]], x]]], l][b],
						"endsWithSet4"[l]]]]],
			"Introduce"[l], "Cases"[l],
			"Introduce"[b, hne, h], "Exact"["falseElimination"[hne["equalityReflexivity"[Typed[{}, {"System4Element"}]]]]],
			"Introduce"[x, t, b, hne, h], "Cases"[x], "Introduce"[hne, h], "Exact"[h], "Introduce"[s, hne, h], "Exact"[h],
			"Cases"[e],
			(* e = star4 *)
			"Introduce"[hAdj, hEnd, hAllEnd], "Exact"[genTail[rest, "false", hNe, hAllEnd]],
			(* e = set4[s] *)
			"Introduce"[s, hAdj, hEnd, hAllEnd], "Exact"[genTail[rest, "true", hNe, hAllEnd]],
			"Cases"[e],
			(* e = star4 *)
			"Introduce"[hAdj, hEnd],
			"Cases"[rest],
			"Introduce"[ih, hRestEnd, hAdj, hEnd],
			"Have"[hNeAll, Not[Prepend["star4"][Typed[{}, {"System4Element"}]] == Typed[{}, {"System4Element"}]]],
			"Introduce"[eq],
			"Exact"[Construct["equalitySubstitution", {"System4Element"},
				Function[{Typed[l, {"System4Element"}]}, InductiveRecursor[List][Function[{Typed[q, {"System4Element"}]}, TypeUniverse[0]], False, Function[{Typed[h, "System4Element"], Typed[t, {"System4Element"}], Typed[u, TypeUniverse[0]]}, True], l]],
				Prepend["star4"][Typed[{}, {"System4Element"}]], Typed[{}, {"System4Element"}], eq, "trueIntroduction"]],
			"Exact"["falseElimination"[hEnd[hNeAll]]],
			"Introduce"[e2, r2, ih, hRestEnd, hAdj, hEnd],
			"Cases"[e2],
			"Introduce"[ih, hRestEnd, hAdj, hEnd], "Exact"["falseElimination"[hAdj]],
			"Introduce"[s2, ih, hRestEnd, hAdj, hEnd],
			"Exact"["andIntroduction"["firstTrueEncSet"[w, s2], ih[hAdj, hRestEnd]]],
			(* e = set4[s] *)
			"Introduce"[s, hAdj, hEnd],
			"Exact"[ih[hAdj, hRestEnd]]
		}
	],
	machineTheorem["encSetCons",
		ForAll[{Typed[w, NonNegativeIntegers], Typed[s, {NonNegativeIntegers}]},
			Prepend["headBool"["encSet"["pow2"[w], s]]]["tailList"["encSet"["pow2"[w], s]]] == "encSet"["pow2"[w], s]],
		{
			"Introduce"[w, s],
			"Have"[hPos, 1 <= Length["encSet"["pow2"[w], s]]],
			"Rewrite"["lengthEncSet"["pow2"[w], s, "pow2Pos"[w]]], "Exact"["pow2Pos"[w]],
			"Cases"["listSplitFirst"["encSet"["pow2"[w], s], hPos]],
			"Introduce"[b, ex], "Cases"[ex], "Introduce"[rest, eq],
			"Rewrite"[eq], "Reflexivity"
		}
	],
	TypeTheoryDefinition["initAC", Typed[
		Function[{Typed[w, NonNegativeIntegers], Typed[h, NonNegativeIntegers], Typed[s0, {NonNegativeIntegers}], Typed[rest, {"System4Element"}]},
			"abstractConfig"[Typed[{}, {"TapeItem"}], Map["toItem"["pow2"[w]], rest], "leftEndZeros"[h, 1], "closingOne", "state4A",
				"focusSetA"[Typed[{}, {Booleans}], "headBool"["encSet"["pow2"[w], s0]], "tailList"["encSet"["pow2"[w], s0]], s0]]],
		NonNegativeIntegers -> NonNegativeIntegers -> {NonNegativeIntegers} -> {"System4Element"} -> "AbstractConfig"
	]],
	machineTheorem["initACTo4",
		ForAll[{Typed[w, NonNegativeIntegers], Typed[h, NonNegativeIntegers], Typed[s0, {NonNegativeIntegers}], Typed[rest, {"System4Element"}]},
			"acToSystem4"["initAC"[w, h, s0, rest]] == "system4Configuration"[Typed[{}, {"System4Element"}], Prepend["set4"[s0]][rest], "state4A"]],
		{
			"Introduce"[w, h, s0, rest],
			"Change"["system4Configuration"[Typed[{}, {"System4Element"}], Prepend["set4"[s0]][Map["itemToElem", Map["toItem"["pow2"[w]], rest]]], "state4A"] ==
				"system4Configuration"[Typed[{}, {"System4Element"}], Prepend["set4"[s0]][rest], "state4A"]],
			"Rewrite"["mapItemToElemToItem"["pow2"[w], rest]]
		}
	],
	machineTheorem["rep3Init",
		ForAll[{Typed[w, NonNegativeIntegers], Typed[h, NonNegativeIntegers], Typed[s0, {NonNegativeIntegers}], Typed[rest, {"System4Element"}]},
			Implies[h + 3 <= "pow2"[w],
				Implies["noAdjacentStarsFrom"["false", rest],
					Implies["endsWithSet4"[Prepend["set4"[s0]][rest]],
						Implies["allTapeSetsOk"[Subtract["pow2"[w], 1], Prepend["set4"[s0]][rest]],
							"system3Represents"[w, "closingOne",
								"fueledSystem4"["system4Configuration"[Typed[{}, {"System4Element"}], Prepend["set4"[s0]][rest], "state4A"], h],
								"acToSystem3"["initAC"[w, h, s0, rest]]]]]]]],
		{
			"Introduce"[w, h, s0, rest, hN, hAdj, hEnd, hAllOk],
			"Cases"[hAllOk], "Introduce"[hs0Ok, hRestOk],
			"Cases"[hs0Ok], "Introduce"[hs0Inc, hs0Bd],
			"Have"[hK2, (h + 1) + 2 <= "pow2"[w]], "LinearArithmetic",
			"Have"[hRestEnd, Implies[Not[rest == Typed[{}, {"System4Element"}]], "endsWithSet4"[rest]]],
			"Introduce"[hNe],
			"Cases"[rest],
			"Introduce"[hAdj, hEnd, hRestOk, hNe], "Exact"["falseElimination"[hNe["equalityReflexivity"[Typed[{}, {"System4Element"}]]]]],
			"Introduce"[e, r, hAdj, hEnd, hRestOk, hNe], "Cases"[e], "Introduce"[hAdj, hEnd, hRestOk, hNe], "Exact"[hEnd], "Introduce"[s, hAdj, hEnd, hRestOk, hNe], "Exact"[hEnd],
			"Have"[hFocItem, "itemOk"["pow2"[w], h + 1, "itemSet"[Join["reverseList"[Typed[{}, {Booleans}]],
				Prepend["headBool"["encSet"["pow2"[w], s0]]]["tailList"["encSet"["pow2"[w], s0]]]], s0]]],
			"Change"["itemOk"["pow2"[w], h + 1, "itemSet"[Prepend["headBool"["encSet"["pow2"[w], s0]]]["tailList"["encSet"["pow2"[w], s0]]], s0]]],
			"Rewrite"["encSetCons"[w, s0]],
			"Exact"["itemOkEncSet"[w, h + 1, s0, hs0Inc, hs0Bd, hK2]],
			"Exact"["existsIntroduction"["initAC"[w, h, s0, rest],
				"andIntroduction"["equalityReflexivity"["closingOne"],
					"andIntroduction"["andIntroduction"[hN,
						"andIntroduction"["andIntroduction"["lessEqualReflexivity", "lessEqualReflexivity"],
							"andIntroduction"["trueIntroduction",
								"andIntroduction"["allItemsOkMapToItem"[w, h + 1, rest, hK2, hRestOk],
									"andIntroduction"["trueIntroduction",
										"andIntroduction"["rightItemsOkMapToItem"[w, rest, hAdj, hRestEnd],
											"andIntroduction"["equalityReflexivity"["state4A"], hFocItem]]]]]]],
						"andIntroduction"["equalityReflexivity"["acToSystem3"["initAC"[w, h, s0, rest]]],
							"equalitySymmetry"["initACTo4"[w, h, s0, rest]]]]]]]
		}
	],

	(* =================================================================== *)
	(* Part 2: Exit Lemmas (rep3Exit, phiExit, phi2StateNotC, exit step)   *)
	(* =================================================================== *)
	machineTheorem["rep3Exit",
		ForAll[{Typed[w, NonNegativeIntegers], Typed[h, NonNegativeIntegers], Typed[c4, "System4Configuration"], Typed[c3, "LookaheadConfiguration"]},
			Implies["system3Represents"[w, "closingOne", "fueledSystem4"[c4, h], c3],
				Implies[c4[["right"]] == Typed[{}, {"System4Element"}],
					Implies[c4[["state"]] == "state4C",
						Exists[{Typed[L, {"Color"}]}, c3 == "lookaheadConfiguration"[L, "color1", Typed[{}, {"Color"}], "stateC"]]]]]],
		{
			"Introduce"[w, h, c4, c3, hRep, hRight, hSt],
			"Cases"[hRep], "Introduce"[a, hr1], "Cases"[hr1], "Introduce"[hRc, hr2],
			"Cases"[hr2], "Introduce"[hOk, hr3], "Cases"[hr3], "Introduce"[eqC3, eqC4],
			"Cases"[a], "Introduce"[ls, rs, le, rc, st, foc, hRc, hOk, eqC3, eqC4],
			"Have"[hR2, "acToSystem4"["abstractConfig"[ls, rs, le, rc, st, foc]][["right"]] == Typed[{}, {"System4Element"}]],
			"Rewrite"["equalitySymmetry"[eqC4]], "Exact"[hRight],
			"Have"[hS2, "acToSystem4"["abstractConfig"[ls, rs, le, rc, st, foc]][["state"]] == "state4C"],
			"Rewrite"["equalitySymmetry"[eqC4]], "Exact"[hSt],
			"Have"[consNotNil, ForAll[{Typed[x, "System4Element"], Typed[xs, {"System4Element"}]},
				Implies[Prepend[x][xs] == Typed[{}, {"System4Element"}], False]]],
			"Introduce"[x, xs, eq],
			"Exact"[Construct["equalitySubstitution", {"System4Element"},
				Function[{Typed[l, {"System4Element"}]}, InductiveRecursor[List][Function[{Typed[q, {"System4Element"}]}, TypeUniverse[0]], False, Function[{Typed[h0, "System4Element"], Typed[t0, {"System4Element"}], Typed[u0, TypeUniverse[0]]}, True], l]],
				Prepend[x][xs], Typed[{}, {"System4Element"}], eq, "trueIntroduction"]],
			"Cases"[foc],
			"Introduce"[xl, b, xr, s, hRc, hOk, eqC3, eqC4, hR2, hS2], "Exact"["falseElimination"[consNotNil["set4"[s], Map["itemToElem", rs], hR2]]],
			"Introduce"[x0, xr, s, hRc, hOk, eqC3, eqC4, hR2, hS2], "Exact"["falseElimination"[consNotNil["set4"[s], Map["itemToElem", rs], hR2]]],
			"Introduce"[x1, xr, s, hRc, hOk, eqC3, eqC4, hR2, hS2], "Exact"["falseElimination"[consNotNil["set4"[s], Map["itemToElem", rs], hR2]]],
			"Introduce"[hRc, hOk, eqC3, eqC4, hR2, hS2], "Exact"["falseElimination"[consNotNil["star4", Map["itemToElem", rs], hR2]]],
			(* focusOff *)
			"Introduce"[hRc, hOk, eqC3, eqC4, hR2, hS2],
			"Have"[eqRc, rc == "closingOne"], "Exact"[hRc],
			"Have"[eqSt, st == "state4C"], "Exact"[hS2],
			"Have"[eqFinal, c3 == "lookaheadConfiguration"[Join["renderL"["false", ls], "leftEndRender"[le]], "color1", Typed[{}, {"Color"}], "stateC"]],
			"Rewrite"[eqC3], "Rewrite"[eqRc], "Rewrite"[eqSt], "Reflexivity",
			"Exact"["existsIntroduction"[Join["renderL"["false", ls], "leftEndRender"[le]], eqFinal]]
		}
	],
	machineTheorem["phiExit",
		ForAll[{Typed[L, {"Color"}]},
			"phi2"["phi3"["lookaheadConfiguration"[L, "color1", Typed[{}, {"Color"}], "stateC"]]] ==
				"lookaheadConfiguration"[Map["swapColor", L], "color2", Typed[{}, {"Color"}], "stateB"]],
		{"Introduce"[L], "Reflexivity"}
	],
	machineTheorem["phi2StateNotC",
		ForAll[{Typed[c, "LookaheadConfiguration"]}, Not["phi2"[c][["state"]] == "stateC"]],
		{
			"Introduce"[c, eq], "Cases"[c], "Introduce"[L, a, R, st, eq], "Cases"[st],
			"Introduce"[eq], "Exact"[Construct["equalitySubstitution", "LookaheadState",
				Function[{Typed[q, "LookaheadState"]}, InductiveRecursor["LookaheadState"][Function[{Typed[u, "LookaheadState"]}, TypeUniverse[0]], True, True, False, q]],
				"stateA", "stateC", eq, "trueIntroduction"]],
			"Introduce"[eq], "Exact"[Construct["equalitySubstitution", "LookaheadState",
				Function[{Typed[q, "LookaheadState"]}, InductiveRecursor["LookaheadState"][Function[{Typed[u, "LookaheadState"]}, TypeUniverse[0]], True, True, False, q]],
				"stateB", "stateC", eq, "trueIntroduction"]],
			"Introduce"[eq], "Exact"[Construct["equalitySubstitution", "LookaheadState",
				Function[{Typed[q, "LookaheadState"]}, InductiveRecursor["LookaheadState"][Function[{Typed[u, "LookaheadState"]}, TypeUniverse[0]], True, True, False, q]],
				"stateB", "stateC", eq, "trueIntroduction"]]
		}
	],
	machineTheorem["wolfram23ExitStep",
		ForAll[{Typed[L, {"Color"}]},
			"turingMachineStep"["system0", "lookaheadConfiguration"[L, "color2", Typed[{}, {"Color"}], "stateB"]] ==
				"some"["lookaheadConfiguration"[Prepend["color0"][L], "color0", Typed[{}, {"Color"}], "stateA"]]],
		{"Introduce"[L], "Reflexivity"}
	],

	(* =================================================================== *)
	(* Part 3: Wolfram (2,3) Tape Decoder (decodeBlocks, decodeW23, rep3Decode) *)
	(* =================================================================== *)
	TypeTheoryDefinition["colorNonZeroBool", Typed[
		Function[{Typed[c, "Color"]},
			InductiveRecursor["Color"][Function[{Typed[q, "Color"]}, Booleans], "false", "true", "true", c]],
		"Color" -> Booleans
	]],
	TypeTheoryDefinition["allNonZeroColorsBool", Typed[
		Function[{Typed[xs, {"Color"}]},
			InductiveRecursor[List][Function[{Typed[q, {"Color"}]}, Booleans], "true",
				Function[{Typed[c, "Color"], Typed[rest, {"Color"}], Typed[prev, Booleans]},
					InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Booleans], "false", prev, "colorNonZeroBool"[c]]], xs]],
		{"Color"} -> Booleans
	]],
	TypeTheoryDefinition["takeWhileNonZeroColor", Typed[
		Function[{Typed[xs, {"Color"}]},
			InductiveRecursor[List][Function[{Typed[q, {"Color"}]}, {"Color"}], Typed[{}, {"Color"}],
				Function[{Typed[c, "Color"], Typed[rest, {"Color"}], Typed[prev, {"Color"}]},
					InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, {"Color"}],
						Typed[{}, {"Color"}], Prepend[c][prev], "colorNonZeroBool"[c]]], xs]],
		{"Color"} -> {"Color"}
	]],
	TypeTheoryDefinition["colorToBit", Typed[
		Function[{Typed[c, "Color"]},
			InductiveRecursor["Color"][Function[{Typed[q, "Color"]}, Booleans], "false", "false", "true", c]],
		"Color" -> Booleans
	]],
	TypeTheoryDefinition["takeColor", Typed[
		Function[{Typed[n, NonNegativeIntegers], Typed[xs, {"Color"}]},
			InductiveRecursor[NonNegativeIntegers][Function[{Typed[q, NonNegativeIntegers]}, {"Color"} -> {"Color"}],
				Function[{Typed[l, {"Color"}]}, Typed[{}, {"Color"}]],
				Function[{Typed[k, NonNegativeIntegers], Typed[prev, {"Color"} -> {"Color"}]},
					Function[{Typed[l, {"Color"}]},
						InductiveRecursor[List][Function[{Typed[q, {"Color"}]}, {"Color"}], Typed[{}, {"Color"}],
							Function[{Typed[c, "Color"], Typed[r, {"Color"}], Typed[u, {"Color"}]}, Prepend[c][prev[r]]], l]]], n][xs]],
		NonNegativeIntegers -> {"Color"} -> {"Color"}
	]],
	TypeTheoryDefinition["dropColor", Typed[
		Function[{Typed[n, NonNegativeIntegers], Typed[xs, {"Color"}]},
			InductiveRecursor[NonNegativeIntegers][Function[{Typed[q, NonNegativeIntegers]}, {"Color"} -> {"Color"}],
				Function[{Typed[l, {"Color"}]}, l],
				Function[{Typed[k, NonNegativeIntegers], Typed[prev, {"Color"} -> {"Color"}]},
					Function[{Typed[l, {"Color"}]},
						InductiveRecursor[List][Function[{Typed[q, {"Color"}]}, {"Color"}], Typed[{}, {"Color"}],
							Function[{Typed[c, "Color"], Typed[r, {"Color"}], Typed[u, {"Color"}]}, prev[r]], l]]], n][xs]],
		NonNegativeIntegers -> {"Color"} -> {"Color"}
	]],
	TypeTheoryDefinition["xorChunkLoop", Typed[
		Function[{Typed[fuel, NonNegativeIntegers], Typed[n, NonNegativeIntegers], Typed[cells, {"Color"}]},
			InductiveRecursor[NonNegativeIntegers][Function[{Typed[q, NonNegativeIntegers]}, {"Color"} -> Option[{Booleans}]],
				Function[{Typed[l, {"Color"}]},
					InductiveRecursor[List][Function[{Typed[q, {"Color"}]}, Option[{Booleans}]],
						"some"["zerosBits"[n]],
						Function[{Typed[c, "Color"], Typed[r, {"Color"}], Typed[u, Option[{Booleans}]]}, Typed["none", Option[{Booleans}]]], l]],
				Function[{Typed[k, NonNegativeIntegers], Typed[prev, {"Color"} -> Option[{Booleans}]]},
					Function[{Typed[l, {"Color"}]},
						InductiveRecursor[List][Function[{Typed[q, {"Color"}]}, Option[{Booleans}]],
							"some"["zerosBits"[n]],
							Function[{Typed[c, "Color"], Typed[r, {"Color"}], Typed[u, Option[{Booleans}]]},
								InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Option[{Booleans}]],
									Typed["none", Option[{Booleans}]],
									"optionMap"[Function[{Typed[acc, {Booleans}]}, "xorBits"[Map["colorToBit", "takeColor"[n, Prepend[c][r]]], acc]],
										prev["dropColor"[n, Prepend[c][r]]]],
									Decide[n <= Length[Prepend[c][r]]]]], l]]], fuel][cells]],
		NonNegativeIntegers -> NonNegativeIntegers -> {"Color"} -> Option[{Booleans}]
	]],
	TypeTheoryDefinition["decodeParityLoop", Typed[
		Function[{Typed[x, {Booleans}], Typed[count, NonNegativeIntegers], Typed[idx, NonNegativeIntegers], Typed[isEven, Booleans], Typed[q, NonNegativeIntegers]},
			InductiveRecursor[NonNegativeIntegers][Function[{Typed[u, NonNegativeIntegers]}, NonNegativeIntegers -> Booleans -> NonNegativeIntegers -> Option[{NonNegativeIntegers}]],
				Function[{Typed[i, NonNegativeIntegers], Typed[ev, Booleans], Typed[qv, NonNegativeIntegers]}, "some"[Typed[{}, {NonNegativeIntegers}]]],
				Function[{Typed[k, NonNegativeIntegers], Typed[prev, NonNegativeIntegers -> Booleans -> NonNegativeIntegers -> Option[{NonNegativeIntegers}]]},
					Function[{Typed[i, NonNegativeIntegers], Typed[ev, Booleans], Typed[qv, NonNegativeIntegers]},
						InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Option[{NonNegativeIntegers}]],
							(* odd: reject if parAt[x, i] == true *)
							InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Option[{NonNegativeIntegers}]],
								prev[i + 1, "true", qv + 1],
								Typed["none", Option[{NonNegativeIntegers}]],
								"parAt"[x, i]],
							(* even: i = 2*qv, if parAt[x, i] == true, prepend qv + 1 *)
							InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Option[{NonNegativeIntegers}]],
								prev[i + 1, "false", qv],
								"optionMap"[Function[{Typed[rest, {NonNegativeIntegers}]}, Prepend[qv + 1][rest]], prev[i + 1, "false", qv]],
								"parAt"[x, i]],
							ev]]], count][idx, isEven, q]],
		{Booleans} -> NonNegativeIntegers -> NonNegativeIntegers -> Booleans -> NonNegativeIntegers -> Option[{NonNegativeIntegers}]
	]],
	TypeTheoryDefinition["decodeBlocks", Typed[
		Function[{Typed[n, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[cells, {"Color"}]},
			InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Option[{NonNegativeIntegers}]],
				Typed["none", Option[{NonNegativeIntegers}]],
				InductiveRecursor[List][Function[{Typed[q, {"Color"}]}, Option[{NonNegativeIntegers}]],
					Typed["none", Option[{NonNegativeIntegers}]],
					Function[{Typed[c, "Color"], Typed[r, {"Color"}], Typed[u, Option[{NonNegativeIntegers}]]},
						InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Option[{NonNegativeIntegers}]],
							Typed["none", Option[{NonNegativeIntegers}]],
							"optionBind"["xorChunkLoop"[Length[Prepend[c][r]], n, Prepend[c][r]],
								Function[{Typed[x, {Booleans}]}, "decodeParityLoop"[x, b, 0, "true", 0]]],
							"allNonZeroColorsBool"[Prepend[c][r]]]], cells],
				Decide[1 <= n]]],
		NonNegativeIntegers -> NonNegativeIntegers -> {"Color"} -> Option[{NonNegativeIntegers}]
	]],
	TypeTheoryDefinition["decodeW23", Typed[
		Function[{Typed[n, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[cfg, "LookaheadConfiguration"]},
			"optionBind"["decodeBlocks"[n, b, Prepend[cfg[["head"]]]["takeWhileNonZeroColor"[cfg[["right"]]]]], "decodeBag"]],
		NonNegativeIntegers -> NonNegativeIntegers -> "LookaheadConfiguration" -> Option[{Booleans}]
	]],
	TypeTheoryDefinition["colorOccurs", Typed[
		Function[{Typed[c, "Color"], Typed[xs, {"Color"}]},
			InductiveRecursor[List][Function[{Typed[q, {"Color"}]}, TypeUniverse[0]], False,
				Function[{Typed[a, "Color"], Typed[rest, {"Color"}], Typed[prev, TypeUniverse[0]]}, Or[a == c, prev]], xs]],
		"Color" -> {"Color"} -> TypeUniverse[0]
	]],
	machineTheorem["colorOccursJoinRight",
		ForAll[{Typed[c, "Color"], Typed[xs, {"Color"}], Typed[ys, {"Color"}]},
			Implies["colorOccurs"[c, ys], "colorOccurs"[c, Join[xs, ys]]]],
		{
			"Introduce"[c, xs], "Induction"[xs],
			"Introduce"[ys, hy], "Exact"[hy],
			"Introduce"[a, rest, ih, ys, hy],
			"Exact"["orIntroductionRight"[ih[ys, hy]]]
		}
	],
	machineTheorem["takeWhileNonZeroColorJoin",
		ForAll[{Typed[p, {"Color"}], Typed[q, {"Color"}]},
			Implies["allNonZeroColorsBool"[p] == "true",
				"takeWhileNonZeroColor"[Join[p, Prepend["color0"][q]]] == p]],
		{
			"Introduce"[p], "Induction"[p],
			"Introduce"[q, hp], "Reflexivity",
			"Introduce"[c, rest, ih, q, hp],
			"Cases"[c],
			"Introduce"[hp], "Exact"["falseElimination"[Construct["equalitySubstitution", Booleans,
				Function[{Typed[b, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, TypeUniverse[0]], True, False, b]],
				"false", "true", hp, "trueIntroduction"]]],
			"Introduce"[hp], "Change"[Prepend["color1"]["takeWhileNonZeroColor"[Join[rest, Prepend["color0"][q]]]] == Prepend["color1"][rest]], "Rewrite"[ih[q, hp]],
			"Introduce"[hp], "Change"[Prepend["color2"]["takeWhileNonZeroColor"[Join[rest, Prepend["color0"][q]]]] == Prepend["color2"][rest]], "Rewrite"[ih[q, hp]]
		}
	],
	machineTheorem["allNonZeroColorsBoolJoin",
		ForAll[{Typed[p, {"Color"}], Typed[q, {"Color"}]},
			Implies["allNonZeroColorsBool"[p] == "true",
				Implies["allNonZeroColorsBool"[q] == "true", "allNonZeroColorsBool"[Join[p, q]] == "true"]]],
		{
			"Introduce"[p], "Induction"[p],
			"Introduce"[q, hp, hq], "Exact"[hq],
			"Introduce"[c, rest, ih, q, hp, hq],
			"Cases"[c],
			"Introduce"[hp], "Exact"["falseElimination"[Construct["equalitySubstitution", Booleans,
				Function[{Typed[b, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, TypeUniverse[0]], True, False, b]],
				"false", "true", hp, "trueIntroduction"]]],
			"Introduce"[hp], "Exact"[ih[q, hp, hq]],
			"Introduce"[hp], "Exact"[ih[q, hp, hq]]
		}
	],
	machineTheorem["allNonZeroColorsBoolOfBits",
		ForAll[{Typed[x, {Booleans}]}, "allNonZeroColorsBool"["ofBits"[x]] == "true"],
		{
			"Introduce"[x], "Induction"[x], "Reflexivity",
			"Introduce"[b, rest, ih], "Cases"[b], "Exact"[ih], "Exact"[ih]
		}
	],
	machineTheorem["mapColorToBitOfBits",
		ForAll[{Typed[x, {Booleans}]}, Map["colorToBit", "ofBits"[x]] == x],
		{
			"Introduce"[x], "Induction"[x], "Reflexivity",
			"Introduce"[b, rest, ih], "Cases"[b],
			"Change"[Prepend["false"][Map["colorToBit", "ofBits"[rest]]] == Prepend["false"][rest]], "Rewrite"[ih],
			"Change"[Prepend["true"][Map["colorToBit", "ofBits"[rest]]] == Prepend["true"][rest]], "Rewrite"[ih]
		}
	],
	machineTheorem["takeColorJoin",
		ForAll[{Typed[p, {"Color"}], Typed[q, {"Color"}]}, "takeColor"[Length[p], Join[p, q]] == p],
		{
			"Introduce"[p], "Induction"[p], "Introduce"[q], "Reflexivity",
			"Introduce"[c, rest, ih, q],
			"Change"[Prepend[c]["takeColor"[Length[rest], Join[rest, q]]] == Prepend[c][rest]], "Rewrite"[ih[q]]
		}
	],
	machineTheorem["dropColorJoin",
		ForAll[{Typed[p, {"Color"}], Typed[q, {"Color"}]}, "dropColor"[Length[p], Join[p, q]] == q],
		{
			"Introduce"[p], "Induction"[p], "Introduce"[q], "Reflexivity",
			"Introduce"[c, rest, ih, q],
			"Change"["dropColor"[Length[rest], Join[rest, q]] == q], "Exact"[ih[q]]
		}
	],
	(* Helpers for lists of (Bits, Set) blocks used in rep3Decode *)
	TypeTheoryInductiveType["BlockPair", TypeUniverse[1], {
		"blockPair" -> ForAll[{Typed[bits, {Booleans}], Typed[elems, {NonNegativeIntegers}]}, "BlockPair"]
	}],
	TypeTheoryDefinition["flatMapOfBits", Typed[
		Function[{Typed[bs, {"BlockPair"}]},
			InductiveRecursor[List][Function[{Typed[q, {"BlockPair"}]}, {"Color"}], Typed[{}, {"Color"}],
				Function[{Typed[p, "BlockPair"], Typed[rest, {"BlockPair"}], Typed[prev, {"Color"}]},
					Join["ofBits"[p[["bits"]]], prev]], bs]],
		{"BlockPair"} -> {"Color"}
	]],
	TypeTheoryDefinition["foldrXorBlocks", Typed[
		Function[{Typed[n, NonNegativeIntegers], Typed[bs, {"BlockPair"}]},
			InductiveRecursor[List][Function[{Typed[q, {"BlockPair"}]}, {Booleans}], "zerosBits"[n],
				Function[{Typed[p, "BlockPair"], Typed[rest, {"BlockPair"}], Typed[prev, {Booleans}]},
					"xorBits"[p[["bits"]], prev]], bs]],
		NonNegativeIntegers -> {"BlockPair"} -> {Booleans}
	]],
	TypeTheoryDefinition["allBlocksOk", Typed[
		Function[{Typed[n, NonNegativeIntegers], Typed[k, NonNegativeIntegers], Typed[bs, {"BlockPair"}]},
			InductiveRecursor[List][Function[{Typed[q, {"BlockPair"}]}, TypeUniverse[0]], True,
				Function[{Typed[p, "BlockPair"], Typed[rest, {"BlockPair"}], Typed[prev, TypeUniverse[0]]},
					And[And[Length[p[["bits"]]] == n, "decodesBits"[p[["bits"]], p[["elems"]], k]], prev]], bs]],
		NonNegativeIntegers -> NonNegativeIntegers -> {"BlockPair"} -> TypeUniverse[0]
	]],
	machineTheorem["allNonZeroColorsBoolFlatMap",
		ForAll[{Typed[bs, {"BlockPair"}]}, "allNonZeroColorsBool"["flatMapOfBits"[bs]] == "true"],
		{
			"Introduce"[bs], "Induction"[bs], "Reflexivity",
			"Introduce"[p, rest, ih],
			"Exact"["allNonZeroColorsBoolJoin"["ofBits"[p[["bits"]]], "flatMapOfBits"[rest],
				"allNonZeroColorsBoolOfBits"[p[["bits"]]], ih]]
		}
	],
	machineTheorem["lengthFoldrXorBlocks",
		ForAll[{Typed[n, NonNegativeIntegers], Typed[k, NonNegativeIntegers], Typed[bs, {"BlockPair"}]},
			Implies["allBlocksOk"[n, k, bs], Length["foldrXorBlocks"[n, bs]] == n]],
		{
			"Introduce"[n, k, bs], "Induction"[bs],
			"Introduce"[h], "Exact"["lengthZerosBits"[n]],
			"Introduce"[p, rest, ih, h],
			"Cases"[h], "Introduce"[hp, hrest], "Cases"[hp], "Introduce"[hLen, hDec],
			"Have"[hEq, Length[p[["bits"]]] == Length["foldrXorBlocks"[n, rest]]],
			"Rewrite"[hLen], "Rewrite"[ih[hrest]],
			"Change"[Length["xorBits"[p[["bits"]], "foldrXorBlocks"[n, rest]]] == n],
			"Rewrite"["lengthXorBits"[p[["bits"]], "foldrXorBlocks"[n, rest], hEq]], "Exact"[hLen]
		}
	],
	machineTheorem["parAtBlocks",
		ForAll[{Typed[n, NonNegativeIntegers], Typed[k, NonNegativeIntegers], Typed[bs, {"BlockPair"}], Typed[i, NonNegativeIntegers]},
			Implies["allBlocksOk"[n, k, bs],
				Implies[i + 1 <= k, "parAt"["foldrXorBlocks"[n, bs], i] == "parMem"[i, Map[Function[{Typed[p, "BlockPair"]}, p[["elems"]]], bs]]]]],
		{
			"Introduce"[n, k, bs], "Induction"[bs],
			"Introduce"[i, h, hi], "Exact"["parAtZeros"[n, i]],
			"Introduce"[p, rest, ih, i, h, hi],
			"Cases"[h], "Introduce"[hp, hrest], "Cases"[hp], "Introduce"[hLen, hDec],
			"Have"[hEq, Length[p[["bits"]]] == Length["foldrXorBlocks"[n, rest]]],
			"Rewrite"[hLen], "Rewrite"["lengthFoldrXorBlocks"[n, k, rest, hrest]],
			"Change"["parAt"["xorBits"[p[["bits"]], "foldrXorBlocks"[n, rest]], i] ==
				"xorBool"["memNat"[i, p[["elems"]]], "parMem"[i, Map[Function[{Typed[q, "BlockPair"]}, q[["elems"]]], rest]]]],
			"Rewrite"["parAtXor"[p[["bits"]], "foldrXorBlocks"[n, rest], i, hEq]],
			"Rewrite"[hDec[i, hi]], "Rewrite"[ih[i, hrest, hi]], "Reflexivity"
		}
	],
	machineTheorem["lengthFlatMapGeCount",
		ForAll[{Typed[n, NonNegativeIntegers], Typed[k, NonNegativeIntegers], Typed[bs, {"BlockPair"}]},
			Implies[1 <= n, Implies["allBlocksOk"[n, k, bs], Length[bs] <= Length["flatMapOfBits"[bs]]]]],
		{
			"Introduce"[n, k, bs], "Induction"[bs],
			"Introduce"[hn, h], "Exact"["lessEqualReflexivity"],
			"Introduce"[p, rest, ih, hn, h],
			"Cases"[h], "Introduce"[hp, hrest], "Cases"[hp], "Introduce"[hLen, hDec],
			"Have"[h1, Length["flatMapOfBits"[Prepend[p][rest]]] == Length["ofBits"[p[["bits"]]]] + Length["flatMapOfBits"[rest]]],
			"Exact"["lengthJoin"["ofBits"[p[["bits"]]], "flatMapOfBits"[rest]]],
			"Have"[h2, Length["ofBits"[p[["bits"]]]] == n], "Rewrite"["lengthOfBits"[p[["bits"]]]], "Exact"[hLen],
			"Have"[h3, Length[rest] <= Length["flatMapOfBits"[rest]]], "Exact"[ih[hn, hrest]],
			"Rewrite"[h1], "Rewrite"[h2], "Change"[Length[rest] + 1 <= n + Length["flatMapOfBits"[rest]]], "LinearArithmetic"
		}
	],
	machineTheorem["xorChunkLoopBlocks",
		ForAll[{Typed[bs, {"BlockPair"}], Typed[fuel, NonNegativeIntegers], Typed[n, NonNegativeIntegers], Typed[k, NonNegativeIntegers]},
			Implies[1 <= n, Implies["allBlocksOk"[n, k, bs], Implies[Length[bs] <= fuel,
				"xorChunkLoop"[fuel, n, "flatMapOfBits"[bs]] == "some"["foldrXorBlocks"[n, bs]]]]]],
		{
			"Introduce"[bs], "Induction"[bs],
			"Introduce"[fuel, n, k, hn, hOk, hFuel],
			"Cases"[fuel], "Introduce"[hFuel], "Reflexivity", "Introduce"[f1, hFuel], "Reflexivity",
			"Introduce"[p, rest, ih, fuel, n, k, hn, hOk, hFuel],
			"Cases"[hOk], "Introduce"[hp, hrest], "Cases"[hp], "Introduce"[hLen, hDec],
			"Cases"[fuel],
			"Introduce"[hFuel], "Have"[hFuel2, Length[rest] + 1 <= 0], "Exact"[hFuel],
			"Have"[f0, Typed[False, TypeUniverse[0]]], "LinearArithmetic", "Exact"["falseElimination"[f0]],
			"Introduce"[f1, hFuel],
			"Have"[hFuel2, Length[rest] + 1 <= f1 + 1], "Exact"[hFuel],
			"Have"[hfRest, Length[rest] <= f1], "LinearArithmetic",
			"Have"[hLenOf, Length["ofBits"[p[["bits"]]]] == n], "Rewrite"["lengthOfBits"[p[["bits"]]]], "Exact"[hLen],
			"Have"[hOfPos, 1 <= Length["ofBits"[p[["bits"]]]]], "Rewrite"[hLenOf], "Exact"[hn],
			"Cases"["listSplitFirst"["ofBits"[p[["bits"]]], hOfPos]],
			"Introduce"[c0, ex0], "Cases"[ex0], "Introduce"[cRest, eqOf],
			"Have"[hFullEq, "flatMapOfBits"[Prepend[p][rest]] == Prepend[c0][Join[cRest, "flatMapOfBits"[rest]]]],
			"Change"[Join["ofBits"[p[["bits"]]], "flatMapOfBits"[rest]] == Prepend[c0][Join[cRest, "flatMapOfBits"[rest]]]],
			"Rewrite"[eqOf], "Reflexivity",
			"Have"[hLenFull, n <= Length[Prepend[c0][Join[cRest, "flatMapOfBits"[rest]]]]],
			"Rewrite"["equalitySymmetry"[hFullEq]],
			"Change"[n <= Length[Join["ofBits"[p[["bits"]]], "flatMapOfBits"[rest]]]],
			"Rewrite"["lengthJoin"["ofBits"[p[["bits"]]], "flatMapOfBits"[rest]]],
			"Rewrite"[hLenOf], "LinearArithmetic",
			"Have"[hTake, "takeColor"[n, Prepend[c0][Join[cRest, "flatMapOfBits"[rest]]]] == "ofBits"[p[["bits"]]]],
			"Rewrite"["equalitySymmetry"[hFullEq]], "Rewrite"["equalitySymmetry"[hLenOf]],
			"Exact"["takeColorJoin"["ofBits"[p[["bits"]]], "flatMapOfBits"[rest]]],
			"Have"[hDrop, "dropColor"[n, Prepend[c0][Join[cRest, "flatMapOfBits"[rest]]]] == "flatMapOfBits"[rest]],
			"Rewrite"["equalitySymmetry"[hFullEq]], "Rewrite"["equalitySymmetry"[hLenOf]],
			"Exact"["dropColorJoin"["ofBits"[p[["bits"]]], "flatMapOfBits"[rest]]],
			"Rewrite"[hFullEq],
			"Change"[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Option[{Booleans}]],
				Typed["none", Option[{Booleans}]],
				"optionMap"[Function[{Typed[acc, {Booleans}]}, "xorBits"[Map["colorToBit", "takeColor"[n, Prepend[c0][Join[cRest, "flatMapOfBits"[rest]]]]], acc]],
					"xorChunkLoop"[f1, n, "dropColor"[n, Prepend[c0][Join[cRest, "flatMapOfBits"[rest]]]]]],
				Decide[n <= Length[Prepend[c0][Join[cRest, "flatMapOfBits"[rest]]]]]] == "some"["xorBits"[p[["bits"]], "foldrXorBlocks"[n, rest]]]],
			"Rewrite"["decideLessEqualTrue"[n, Length[Prepend[c0][Join[cRest, "flatMapOfBits"[rest]]]], hLenFull]],
			"Rewrite"[hTake], "Rewrite"[hDrop],
			"Rewrite"["mapColorToBitOfBits"[p[["bits"]]]],
			"Rewrite"[ih[f1, n, k, hn, hrest, hfRest]], "Reflexivity"
		}
	],
	machineTheorem["decodeParityLoopEqS4Loop",
		ForAll[{Typed[count, NonNegativeIntegers], Typed[x, {Booleans}], Typed[K, {{NonNegativeIntegers}}],
				Typed[idx, NonNegativeIntegers], Typed[isEven, Booleans], Typed[q, NonNegativeIntegers]},
			Implies[ForAll[{Typed[y, NonNegativeIntegers]}, Implies[idx <= y, Implies[y + 1 <= idx + count, "parAt"[x, y] == "parMem"[y, K]]]],
				"decodeParityLoop"[x, count, idx, isEven, q] == "decodeS4Loop"[K, count, idx, isEven, q]]],
		{
			"Introduce"[count], "Induction"[count],
			"Introduce"[x, K, idx, isEven, q, hEq], "Reflexivity",
			"Introduce"[k, ih, x, K, idx, isEven, q, hEq],
			"Have"[hHere, "parAt"[x, idx] == "parMem"[idx, K]],
			"Have"[l1, idx <= idx], "LinearArithmetic",
			"Have"[l2, idx + 1 <= idx + (k + 1)], "LinearArithmetic",
			"Exact"[hEq[idx, l1, l2]],
			"Have"[hRest, ForAll[{Typed[y, NonNegativeIntegers]}, Implies[idx + 1 <= y, Implies[y + 1 <= (idx + 1) + k, "parAt"[x, y] == "parMem"[y, K]]]]],
			"Introduce"[y, hy1, hy2],
			"Have"[ya, idx <= y], "LinearArithmetic",
			"Have"[yb, y + 1 <= idx + (k + 1)], "LinearArithmetic",
			"Exact"[hEq[y, ya, yb]],
			"Cases"[isEven],
			(* isEven = false *)
			"Change"[InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Option[{NonNegativeIntegers}]],
				"decodeParityLoop"[x, k, idx + 1, "true", q + 1], Typed["none", Option[{NonNegativeIntegers}]], "parAt"[x, idx]] ==
				InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Option[{NonNegativeIntegers}]],
				"decodeS4Loop"[K, k, idx + 1, "true", q + 1], Typed["none", Option[{NonNegativeIntegers}]], "parMem"[idx, K]]],
			"Rewrite"[hHere], "Rewrite"[ih[x, K, idx + 1, "true", q + 1, hRest]],
			(* isEven = true *)
			"Change"[InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Option[{NonNegativeIntegers}]],
				"decodeParityLoop"[x, k, idx + 1, "false", q],
				"optionMap"[Function[{Typed[rest, {NonNegativeIntegers}]}, Prepend[q + 1][rest]], "decodeParityLoop"[x, k, idx + 1, "false", q]],
				"parAt"[x, idx]] ==
				InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Option[{NonNegativeIntegers}]],
				"decodeS4Loop"[K, k, idx + 1, "false", q],
				"optionMap"[Function[{Typed[rest, {NonNegativeIntegers}]}, Prepend[q + 1][rest]], "decodeS4Loop"[K, k, idx + 1, "false", q]],
				"parMem"[idx, K]]],
			"Rewrite"[hHere], "Rewrite"[ih[x, K, idx + 1, "false", q, hRest]]
		}
	],
	machineTheorem["prependInjectiveHead",
		ForAll[{TypedImplicit[A, TypeUniverse[1]], Typed[a1, A], Typed[a2, A], Typed[l1, {A}], Typed[l2, {A}]},
			Implies[Prepend[a1][l1] == Prepend[a2][l2], a1 == a2]],
		{
			"Introduce"[A, a1, a2, l1, l2, eq],
			"Exact"["equalityCongruence"[
				Function[{Typed[l, {A}]}, InductiveRecursor[List][Function[{Typed[q, {A}]}, A], a1,
					Function[{Typed[h, A], Typed[t, {A}], Typed[u, A]}, h], l]],
				eq]]
		}
	],
	machineTheorem["prependInjectiveTail",
		ForAll[{TypedImplicit[A, TypeUniverse[1]], Typed[a1, A], Typed[a2, A], Typed[l1, {A}], Typed[l2, {A}]},
			Implies[Prepend[a1][l1] == Prepend[a2][l2], l1 == l2]],
		{
			"Introduce"[A, a1, a2, l1, l2, eq],
			"Exact"["equalityCongruence"[Function[{Typed[l, {A}]}, "tailList"[l]], eq]]
		}
	],
	machineTheorem["mapToElemEqSetsStar",
		ForAll[{Typed[K, {{NonNegativeIntegers}}], Typed[rs, {"TapeItem"}], Typed[R, {"System4Element"}]},
			Implies[Map["itemToElem", rs] == Join["sets4"[K], Prepend["star4"][R]],
				Exists[{Typed[ps, {"BlockPair"}], Typed[rs2, {"TapeItem"}]},
					And[rs == Join[Map[Function[{Typed[p, "BlockPair"]}, "itemSet"[p[["bits"]], p[["elems"]]]], ps], Prepend["itemStar"][rs2]],
						And[Map[Function[{Typed[p, "BlockPair"]}, p[["elems"]]], ps] == K, Map["itemToElem", rs2] == R]]]]],
		{
			"Introduce"[K], "Induction"[K],
			(* K = {} *)
			"Introduce"[rs, R, h],
			"Cases"[rs],
			"Introduce"[h],
			"Exact"["falseElimination"[Construct["equalitySubstitution", {"System4Element"},
				Function[{Typed[l, {"System4Element"}]}, InductiveRecursor[List][Function[{Typed[q, {"System4Element"}]}, TypeUniverse[0]], True, Function[{Typed[h0, "System4Element"], Typed[t0, {"System4Element"}], Typed[u0, TypeUniverse[0]]}, False], l]],
				Typed[{}, {"System4Element"}], Prepend["star4"][R], h, "trueIntroduction"]]],
			"Introduce"[it, rs2, h],
			"Cases"[it],
			"Introduce"[x, s, h],
			"Have"[hHead, "set4"[s] == "star4"], "Exact"["prependInjectiveHead"["set4"[s], "star4", Map["itemToElem", rs2], R, h]],
			"Exact"["falseElimination"[Construct["equalitySubstitution", "System4Element",
				Function[{Typed[e, "System4Element"]}, InductiveRecursor["System4Element"][Function[{Typed[q, "System4Element"]}, TypeUniverse[0]], False, Function[{Typed[u, {NonNegativeIntegers}]}, True], e]],
				"set4"[s], "star4", hHead, "trueIntroduction"]]],
			"Introduce"[h],
			"Have"[hTail, Map["itemToElem", rs2] == R], "Exact"["prependInjectiveTail"["star4", "star4", Map["itemToElem", rs2], R, h]],
			"Exact"["existsIntroduction"[Typed[{}, {"BlockPair"}], "existsIntroduction"[rs2,
				"andIntroduction"["equalityReflexivity"[Prepend["itemStar"][rs2]],
					"andIntroduction"["equalityReflexivity"[Typed[{}, {{NonNegativeIntegers}}]], hTail]]]]],
			(* K = S :: Krest *)
			"Introduce"[S, Krest, ih, rs, R, h],
			"Cases"[rs],
			"Introduce"[h],
			"Exact"["falseElimination"[Construct["equalitySubstitution", {"System4Element"},
				Function[{Typed[l, {"System4Element"}]}, InductiveRecursor[List][Function[{Typed[q, {"System4Element"}]}, TypeUniverse[0]], True, Function[{Typed[h0, "System4Element"], Typed[t0, {"System4Element"}], Typed[u0, TypeUniverse[0]]}, False], l]],
				Typed[{}, {"System4Element"}], Prepend["set4"[S]][Join["sets4"[Krest], Prepend["star4"][R]]], h, "trueIntroduction"]]],
			"Introduce"[it, rsRest, h],
			"Cases"[it],
			"Introduce"[x, s2, h],
			"Have"[hHead, "set4"[s2] == "set4"[S]], "Exact"["prependInjectiveHead"["set4"[s2], "set4"[S], Map["itemToElem", rsRest], Join["sets4"[Krest], Prepend["star4"][R]], h]],
			"Have"[eqS, s2 == S],
			"Exact"["equalityCongruence"[
				Function[{Typed[e, "System4Element"]}, InductiveRecursor["System4Element"][Function[{Typed[q, "System4Element"]}, {NonNegativeIntegers}], s2, Function[{Typed[u, {NonNegativeIntegers}]}, u], e]],
				hHead]],
			"Have"[hTail, Map["itemToElem", rsRest] == Join["sets4"[Krest], Prepend["star4"][R]]],
			"Exact"["prependInjectiveTail"["set4"[s2], "set4"[S], Map["itemToElem", rsRest], Join["sets4"[Krest], Prepend["star4"][R]], h]],
			"Cases"[ih[rsRest, R, hTail]],
			"Introduce"[ps, ex1], "Cases"[ex1], "Introduce"[rs2, ex2], "Cases"[ex2], "Introduce"[eqRs, ex3], "Cases"[ex3], "Introduce"[eqK, eqR],
			"Exact"["existsIntroduction"[Prepend["blockPair"[x, s2]][ps], "existsIntroduction"[rs2,
				"andIntroduction"["equalityCongruence"[Function[{Typed[l, {"TapeItem"}]}, Prepend["itemSet"[x, s2]][l]], eqRs],
					"andIntroduction"["equalityTransitivity"["equalityCongruence"[Function[{Typed[l, {{NonNegativeIntegers}}]}, Prepend[s2][l]], eqK],
						"equalityCongruence"[Function[{Typed[u, {NonNegativeIntegers}]}, Prepend[u][Krest]], eqS]], eqR]]]]],
			"Introduce"[h],
			"Have"[hHead, "star4" == "set4"[S]], "Exact"["prependInjectiveHead"["star4", "set4"[S], Map["itemToElem", rsRest], Join["sets4"[Krest], Prepend["star4"][R]], h]],
			"Exact"["falseElimination"[Construct["equalitySubstitution", "System4Element",
				Function[{Typed[e, "System4Element"]}, InductiveRecursor["System4Element"][Function[{Typed[q, "System4Element"]}, TypeUniverse[0]], True, Function[{Typed[u, {NonNegativeIntegers}]}, False], e]],
				"star4", "set4"[S], hHead, "trueIntroduction"]]]
		}
	],
	machineTheorem["renderRBlocks",
		ForAll[{Typed[ps, {"BlockPair"}], Typed[rest, {"TapeItem"}]},
			"renderR"["false", Join[Map[Function[{Typed[p, "BlockPair"]}, "itemSet"[p[["bits"]], p[["elems"]]]], ps], rest]] ==
				Join["flatMapOfBits"[ps], "renderR"["false", rest]]],
		{
			"Introduce"[ps], "Induction"[ps],
			"Introduce"[rest], "Reflexivity",
			"Introduce"[p, tail, ih, rest],
			"Exact"["equalityTransitivity"[
				"equalityCongruence"[Function[{Typed[l, {"Color"}]}, Join["ofBits"[p[["bits"]]], l]], ih[rest]],
				"equalitySymmetry"["joinAssociativity"["ofBits"[p[["bits"]]], "flatMapOfBits"[tail], "renderR"["false", rest]]]]]
		}
	],
	machineTheorem["allBlocksOkFromAllItemsOk",
		ForAll[{Typed[n, NonNegativeIntegers], Typed[k, NonNegativeIntegers], Typed[ps, {"BlockPair"}], Typed[rest, {"TapeItem"}]},
			Implies["allItemsOk"[n, k, Join[Map[Function[{Typed[p, "BlockPair"]}, "itemSet"[p[["bits"]], p[["elems"]]]], ps], rest]],
				"allBlocksOk"[n, k, ps]]],
		{
			"Introduce"[n, k, ps], "Induction"[ps],
			"Introduce"[rest, h], "Exact"["trueIntroduction"],
			"Introduce"[p, tail, ih, rest, h],
			"Cases"[h], "Introduce"[hp, hrest],
			"Cases"[hp], "Introduce"[hLen, hp2], "Cases"[hp2], "Introduce"[hInc, hDec],
			"Exact"["andIntroduction"["andIntroduction"[hLen, hDec], ih[rest, hrest]]]
		}
	],
	(* Main Rung 5 Decoding Theorem: rep3Decode! *)
	machineTheorem["rep3Decode",
		ForAll[{Typed[w, NonNegativeIntegers], Typed[h, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[rc, "Closing"],
				Typed[Lp, {"System4Element"}], Typed[K0, {NonNegativeIntegers}], Typed[Krest, {{NonNegativeIntegers}}], Typed[R, {"System4Element"}],
				Typed[c3, "LookaheadConfiguration"]},
			Implies[b <= h + 1,
				Implies["system3Represents"[w, rc,
					"fueledSystem4"["system4Configuration"[Lp, Join["sets4"[Prepend[K0][Krest]], Prepend["star4"][R]], "state4B"], h], c3],
					And["decodeW23"["pow2"[w], b, "phi2"["phi3"[c3]]] ==
						"optionBind"["decodeS4"["system4Configuration"[Lp, Join["sets4"[Prepend[K0][Krest]], Prepend["star4"][R]], "state4B"], b], "decodeBag"],
						"colorOccurs"["color0", "phi2"["phi3"[c3]][["right"]]]]]]],
		{
			"Introduce"[w, h, b, rc, Lp, K0, Krest, R, c3, hb, hRep],
			"Cases"[hRep], "Introduce"[a, hr1], "Cases"[hr1], "Introduce"[hRc, hr2],
			"Cases"[hr2], "Introduce"[hOk, hr3], "Cases"[hr3], "Introduce"[eqC3, eqC4],
			"Cases"[a], "Introduce"[ls, rs, le, rc2, st, foc, hRc, hOk, eqC3, eqC4],
			"Cases"[hOk], "Introduce"[hN, ho1], "Cases"[ho1], "Introduce"[hle, ho2],
			"Cases"[ho2], "Introduce"[hls, ho3], "Cases"[ho3], "Introduce"[hrs, ho4],
			"Cases"[ho4], "Introduce"[hL, ho5], "Cases"[ho5], "Introduce"[hR, hfoc],
			"Have"[hStEq, "acToSystem4"["abstractConfig"[ls, rs, le, rc2, st, foc]][["state"]] == "state4B"],
			"Rewrite"["equalitySymmetry"[eqC4]], "Reflexivity",
			"Have"[hRtEq, "acToSystem4"["abstractConfig"[ls, rs, le, rc2, st, foc]][["right"]] == Join["sets4"[Prepend[K0][Krest]], Prepend["star4"][R]]],
			"Rewrite"["equalitySymmetry"[eqC4]], "Reflexivity",
			"Cases"[foc],
			(* focusSetA: st == state4A != state4B *)
			"Introduce"[xl, bb, xr, S, hRc, eqC3, eqC4, hle, hfoc, hStEq, hRtEq],
			"Cases"[hfoc], "Introduce"[eqStA, hIt],
			"Have"[eqAB, "state4A" == "state4B"], "Rewrite"["equalitySymmetry"[eqStA]], "Exact"[hStEq],
			"Exact"["falseElimination"[Construct["equalitySubstitution", "System4State",
				Function[{Typed[q, "System4State"]}, InductiveRecursor["System4State"][Function[{Typed[u, "System4State"]}, TypeUniverse[0]], True, False, False, q]],
				"state4A", "state4B", eqAB, "trueIntroduction"]]],
			(* focusSetB: THE MATCHING CASE! *)
			"Introduce"[x0, xRest, S, hRc, eqC3, eqC4, hle, hfoc, hStEq, hRtEq],
			"Cases"[hfoc], "Introduce"[hstNotA, hIt0],
			"Cases"[hIt0], "Introduce"[hLen0, hi1], "Cases"[hi1], "Introduce"[hInc0, hDec0],
			"Have"[eqStB, st == "state4B"], "Exact"[hStEq],
			"Have"[hHeadSet, "set4"[S] == "set4"[K0]],
			"Exact"["prependInjectiveHead"["set4"[S], "set4"[K0], Map["itemToElem", rs], Join["sets4"[Krest], Prepend["star4"][R]], hRtEq]],
			"Have"[eqS, S == K0],
			"Exact"["equalityCongruence"[
				Function[{Typed[e, "System4Element"]}, InductiveRecursor["System4Element"][Function[{Typed[q, "System4Element"]}, {NonNegativeIntegers}], S, Function[{Typed[u, {NonNegativeIntegers}]}, u], e]],
				hHeadSet]],
			"Have"[hTailRs, Map["itemToElem", rs] == Join["sets4"[Krest], Prepend["star4"][R]]],
			"Exact"["prependInjectiveTail"["set4"[S], "set4"[K0], Map["itemToElem", rs], Join["sets4"[Krest], Prepend["star4"][R]], hRtEq]],
			"Cases"["mapToElemEqSetsStar"[Krest, rs, R, hTailRs]],
			"Introduce"[ps, ex1], "Cases"[ex1], "Introduce"[rs2, ex2], "Cases"[ex2], "Introduce"[eqRs, ex3], "Cases"[ex3], "Introduce"[eqK, eqR],
			(* Rewrite c3 to explicit stateB lookaheadConfiguration *)
			"Have"[eqC3Exp, c3 == "lookaheadConfiguration"[Join["renderL"["false", ls], "leftEndRender"[le]], "toCell"[x0],
				Join[Join["ofBits"[xRest], "flatMapOfBits"[ps]], Prepend["color0"][Join["renderR"["true", rs2], "closingRender"[rc2]]]], "stateB"]],
			"Rewrite"[eqC3], "Rewrite"[eqStB], "Rewrite"[eqRs],
			"Change"["lookaheadConfiguration"[Join["renderL"["false", ls], "leftEndRender"[le]], "toCell"[x0],
				Join["ofBits"[xRest], Join["renderR"["false", Join[Map[Function[{Typed[p, "BlockPair"]}, "itemSet"[p[["bits"]], p[["elems"]]]], ps], Prepend["itemStar"][rs2]]], "closingRender"[rc2]]], "stateB"] ==
				"lookaheadConfiguration"[Join["renderL"["false", ls], "leftEndRender"[le]], "toCell"[x0],
				Join[Join["ofBits"[xRest], "flatMapOfBits"[ps]], Prepend["color0"][Join["renderR"["true", rs2], "closingRender"[rc2]]]], "stateB"]],
			"Rewrite"["renderRBlocks"[ps, Prepend["itemStar"][rs2]]],
			"Change"["lookaheadConfiguration"[Join["renderL"["false", ls], "leftEndRender"[le]], "toCell"[x0],
				Join["ofBits"[xRest], Join[Join["flatMapOfBits"[ps], Prepend["color0"]["renderR"["true", rs2]]], "closingRender"[rc2]]], "stateB"] ==
				"lookaheadConfiguration"[Join["renderL"["false", ls], "leftEndRender"[le]], "toCell"[x0],
				Join[Join["ofBits"[xRest], "flatMapOfBits"[ps]], Prepend["color0"][Join["renderR"["true", rs2], "closingRender"[rc2]]]], "stateB"]],
			"Rewrite"["joinAssociativity"["flatMapOfBits"[ps], Prepend["color0"]["renderR"["true", rs2]], "closingRender"[rc2]]],
			"Rewrite"["equalitySymmetry"["joinAssociativity"["ofBits"[xRest], "flatMapOfBits"[ps], Join[Prepend["color0"]["renderR"["true", rs2]], "closingRender"[rc2]]]]],
			"Reflexivity",
			"Have"[eqPhi, "phi2"["phi3"[c3]] == "lookaheadConfiguration"[Map["swapColor", Join["renderL"["false", ls], "leftEndRender"[le]]], "toCell"[x0],
				Join[Join["ofBits"[xRest], "flatMapOfBits"[ps]], Prepend["color0"][Join["renderR"["true", rs2], "closingRender"[rc2]]]], "stateB"]],
			"Rewrite"[eqC3Exp], "Reflexivity",
			(* Part B: color0 occurs in right *)
			"Have"[hOcc, "colorOccurs"["color0", "phi2"["phi3"[c3]][["right"]]]],
			"Rewrite"[eqPhi],
			"Exact"["colorOccursJoinRight"["color0", Join["ofBits"[xRest], "flatMapOfBits"[ps]],
				Prepend["color0"][Join["renderR"["true", rs2], "closingRender"[rc2]]],
				"orIntroductionLeft"["equalityReflexivity"["color0"]]]],
			(* Part A: decodeBlocks matches decodeS4 *)
			"Have"[hNzP, "allNonZeroColorsBool"[Join["ofBits"[xRest], "flatMapOfBits"[ps]]] == "true"],
			"Exact"["allNonZeroColorsBoolJoin"["ofBits"[xRest], "flatMapOfBits"[ps],
				"allNonZeroColorsBoolOfBits"[xRest], "allNonZeroColorsBoolFlatMap"[ps]]],
			"Have"[hTakeW, "takeWhileNonZeroColor"[Join[Join["ofBits"[xRest], "flatMapOfBits"[ps]], Prepend["color0"][Join["renderR"["true", rs2], "closingRender"[rc2]]]]] ==
				Join["ofBits"[xRest], "flatMapOfBits"[ps]]],
			"Exact"["takeWhileNonZeroColorJoin"[Join["ofBits"[xRest], "flatMapOfBits"[ps]],
				Join["renderR"["true", rs2], "closingRender"[rc2]], hNzP]],
			"Have"[hAllBlocks, "allBlocksOk"["pow2"[w], h + 1, Prepend["blockPair"[Prepend[x0][xRest], S]][ps]]],
			"Have"[hPsOk, "allBlocksOk"["pow2"[w], h + 1, ps]],
			"Have"[hrs2, "allItemsOk"["pow2"[w], h + 1, Join[Map[Function[{Typed[p, "BlockPair"]}, "itemSet"[p[["bits"]], p[["elems"]]]], ps], Prepend["itemStar"][rs2]]]],
			"Rewrite"["equalitySymmetry"[eqRs]], "Exact"[hrs],
			"Exact"["allBlocksOkFromAllItemsOk"["pow2"[w], h + 1, ps, Prepend["itemStar"][rs2], hrs2]],
			"Exact"["andIntroduction"["andIntroduction"[hLen0, hDec0], hPsOk]],
			"Have"[hCellsEq, Prepend["toCell"[x0]][Join["ofBits"[xRest], "flatMapOfBits"[ps]]] ==
				"flatMapOfBits"[Prepend["blockPair"[Prepend[x0][xRest], S]][ps]]],
			"Reflexivity",
			"Have"[hPosN, 1 <= "pow2"[w]], "Exact"["pow2Pos"[w]],
			"Have"[hFuelOk, Length[Prepend["blockPair"[Prepend[x0][xRest], S]][ps]] <= Length[Prepend["toCell"[x0]][Join["ofBits"[xRest], "flatMapOfBits"[ps]]]]],
			"Rewrite"[hCellsEq],
			"Exact"["lengthFlatMapGeCount"["pow2"[w], h + 1, Prepend["blockPair"[Prepend[x0][xRest], S]][ps], hPosN, hAllBlocks]],
			"Have"[hChunkEq, "xorChunkLoop"[Length[Prepend["toCell"[x0]][Join["ofBits"[xRest], "flatMapOfBits"[ps]]]], "pow2"[w],
				Prepend["toCell"[x0]][Join["ofBits"[xRest], "flatMapOfBits"[ps]]]] ==
				"some"["foldrXorBlocks"["pow2"[w], Prepend["blockPair"[Prepend[x0][xRest], S]][ps]]]],
			"Rewrite"[hCellsEq],
			"Exact"["xorChunkLoopBlocks"[Prepend["blockPair"[Prepend[x0][xRest], S]][ps],
				Length["flatMapOfBits"[Prepend["blockPair"[Prepend[x0][xRest], S]][ps]]], "pow2"[w], h + 1, hPosN, hAllBlocks,
				"lengthFlatMapGeCount"["pow2"[w], h + 1, Prepend["blockPair"[Prepend[x0][xRest], S]][ps], hPosN, hAllBlocks]]],
			"Have"[hAllNzFull, "allNonZeroColorsBool"[Prepend["toCell"[x0]][Join["ofBits"[xRest], "flatMapOfBits"[ps]]]] == "true"],
			"Rewrite"[hCellsEq], "Exact"["allNonZeroColorsBoolFlatMap"[Prepend["blockPair"[Prepend[x0][xRest], S]][ps]]],
			"Have"[hParAgree, ForAll[{Typed[y, NonNegativeIntegers]},
				Implies[0 <= y, Implies[y + 1 <= 0 + b,
					"parAt"["foldrXorBlocks"["pow2"[w], Prepend["blockPair"[Prepend[x0][xRest], S]][ps]], y] ==
						"parMem"[y, Prepend[K0][Krest]]]]]],
			"Introduce"[y, hy0, hyb],
			"Have"[hyH, y + 1 <= h + 1], "LinearArithmetic",
			"Rewrite"["parAtBlocks"["pow2"[w], h + 1, Prepend["blockPair"[Prepend[x0][xRest], S]][ps], y, hAllBlocks, hyH]],
			"Change"["parMem"[y, Prepend[S][Map[Function[{Typed[p, "BlockPair"]}, p[["elems"]]], ps]]] == "parMem"[y, Prepend[K0][Krest]]],
			"Rewrite"[eqS], "Rewrite"[eqK],
			"Have"[hDecEq, "decodeBlocks"["pow2"[w], b, Prepend["toCell"[x0]][Join["ofBits"[xRest], "flatMapOfBits"[ps]]]] ==
				"decodeS4"["system4Configuration"[Lp, Join["sets4"[Prepend[K0][Krest]], Prepend["star4"][R]], "state4B"], b]],
			"Change"[InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Option[{NonNegativeIntegers}]],
				Typed["none", Option[{NonNegativeIntegers}]],
				InductiveRecursor[Booleans][Function[{Typed[q, Booleans]}, Option[{NonNegativeIntegers}]],
					Typed["none", Option[{NonNegativeIntegers}]],
					"optionBind"["xorChunkLoop"[Length[Prepend["toCell"[x0]][Join["ofBits"[xRest], "flatMapOfBits"[ps]]]], "pow2"[w],
						Prepend["toCell"[x0]][Join["ofBits"[xRest], "flatMapOfBits"[ps]]]],
						Function[{Typed[x, {Booleans}]}, "decodeParityLoop"[x, b, 0, "true", 0]]],
					"allNonZeroColorsBool"[Prepend["toCell"[x0]][Join["ofBits"[xRest], "flatMapOfBits"[ps]]]]],
				Decide[1 <= "pow2"[w]]] ==
				"decodeS4Loop"["leadSets4"[Join["sets4"[Prepend[K0][Krest]], Prepend["star4"][R]]], b, 0, "true", 0]],
			"Rewrite"["decideLessEqualTrue"[1, "pow2"[w], hPosN]],
			"Rewrite"[hAllNzFull],
			"Rewrite"[hChunkEq],
			"Rewrite"["leadSets4SetsStar"[Prepend[K0][Krest], R]],
			"Exact"["decodeParityLoopEqS4Loop"[b, "foldrXorBlocks"["pow2"[w], Prepend["blockPair"[Prepend[x0][xRest], S]][ps]],
				Prepend[K0][Krest], 0, "true", 0, hParAgree]],
			"Have"[hW23, "decodeW23"["pow2"[w], b, "phi2"["phi3"[c3]]] ==
				"optionBind"["decodeS4"["system4Configuration"[Lp, Join["sets4"[Prepend[K0][Krest]], Prepend["star4"][R]], "state4B"], b], "decodeBag"]],
			"Rewrite"[eqPhi],
			"Change"["optionBind"["decodeBlocks"["pow2"[w], b, Prepend["toCell"[x0]]["takeWhileNonZeroColor"[
				Join[Join["ofBits"[xRest], "flatMapOfBits"[ps]], Prepend["color0"][Join["renderR"["true", rs2], "closingRender"[rc2]]]]]]], "decodeBag"] ==
				"optionBind"["decodeS4"["system4Configuration"[Lp, Join["sets4"[Prepend[K0][Krest]], Prepend["star4"][R]], "state4B"], b], "decodeBag"]],
			"Rewrite"[hTakeW], "Rewrite"[hDecEq],
			"Exact"["andIntroduction"[hW23, hOcc]],
			(* focusSetT: st == state4C != state4B *)
			"Introduce"[x1, xr, S, hRc, eqC3, eqC4, hle, hfoc, hStEq, hRtEq],
			"Cases"[hfoc], "Introduce"[eqStC, hRest],
			"Have"[eqCB, "state4C" == "state4B"], "Rewrite"["equalitySymmetry"[eqStC]], "Exact"[hStEq],
			"Exact"["falseElimination"[Construct["equalitySubstitution", "System4State",
				Function[{Typed[q, "System4State"]}, InductiveRecursor["System4State"][Function[{Typed[u, "System4State"]}, TypeUniverse[0]], False, False, True, q]],
				"state4C", "state4B", eqCB, "trueIntroduction"]]],
			(* focusStar: star4 == set4[K0] impossible *)
			"Introduce"[hRc, eqC3, eqC4, hle, hfoc, hStEq, hRtEq],
			"Have"[hHead, "star4" == "set4"[K0]],
			"Exact"["prependInjectiveHead"["star4", "set4"[K0], Map["itemToElem", rs], Join["sets4"[Krest], Prepend["star4"][R]], hRtEq]],
			"Exact"["falseElimination"[Construct["equalitySubstitution", "System4Element",
				Function[{Typed[e, "System4Element"]}, InductiveRecursor["System4Element"][Function[{Typed[q, "System4Element"]}, TypeUniverse[0]], True, Function[{Typed[u, {NonNegativeIntegers}]}, False], e]],
				"star4", "set4"[K0], hHead, "trueIntroduction"]]],
			(* focusOff: {} == set4[K0] :: ... impossible *)
			"Introduce"[hRc, eqC3, eqC4, hle, hfoc, hStEq, hRtEq],
			"Have"[hEmpty, Typed[{}, {"System4Element"}] == Prepend["set4"[K0]][Join["sets4"[Krest], Prepend["star4"][R]]]],
			"Change"[Map["itemToElem", Typed[{}, {"TapeItem"}]] == Prepend["set4"[K0]][Join["sets4"[Krest], Prepend["star4"][R]]]],
			"Rewrite"["equalitySymmetry"[hfoc]], "Exact"[hRtEq],
			"Exact"["falseElimination"[Construct["equalitySubstitution", {"System4Element"},
				Function[{Typed[l, {"System4Element"}]}, InductiveRecursor[List][Function[{Typed[q, {"System4Element"}]}, TypeUniverse[0]], True, Function[{Typed[h0, "System4Element"], Typed[t0, {"System4Element"}], Typed[u0, TypeUniverse[0]]}, False], l]],
				Typed[{}, {"System4Element"}], Prepend["set4"[K0]][Join["sets4"[Krest], Prepend["star4"][R]]], hEmpty, "trueIntroduction"]]]
		}
	]
}
