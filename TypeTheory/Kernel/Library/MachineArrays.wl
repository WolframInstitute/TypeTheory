(* ::Package:: *)

(*
The vectors of typed code: the packed arrays of rank 1 that the compiler's typed entries take, make and return, with
their operations as typed code computes them, in TypeTheoryEnvironment["Machine"] and, with the reals' vectors,
TypeTheoryEnvironment["MachineReals"].

An array is a list that a machine can hold, a subtype of the prelude's lists: its length is below 2^63, so Length of
an array is a machine integer and never leaves, as in typed code. a["list"] is the list of an array a, as n["integer"]
is the integer of a machine integer, and a["proof"] the proof that the length is in range. Parts are counted from 1, or
below 0 from the end, and a part that is not there is the compiler's leave Failure["PartRange", <||>].

	"PackedArray"[A, rank]           the compiler's "PackedArray"::[A, rank]: A at rank 0, and at a rank above, the
	                                 lists a machine holds of the arrays of the rank below; the model has rank 1, of
	                                 "Integer64" or "Real64"
	"arrayLength"[a]                 Length[a], an "Integer64"
	"arrayPart"[a, i]                a[[i]], A | Failure
	"arraySetPart"[a, i, v]          the array of a[[i]] = v, by the same rule on i
	"arrayTake"[a, n]                Take[a, n]: the first n, or below 0 the last -n
	"arrayConstant"[c, n]            ConstantArray[c, n], leaving with Failure["Range", <||>] for a length below 0
	"arrayTotal"[a]                  Total of machine integers: the machine's sums from 0, left to right, leaving with
	                                 Failure["IntegerOverflow", <||>] where one does; typed code has no Total of reals
	"listPart", "listSetPart", "listTake", "listDrop", "listConstant"
	                                 the same on lists, a place counted from 0 by an integer
	"arrayOfList"[l]                 the array of a list, and the leave of an allocation that fails, Failure["Memory",
	                                 <||>], for a list too long to hold: no operation here reaches it
	"integerListSum", "partialSumsInRange"
	                                 the sum of the integers of a list, and that every sum on the way to it is a machine
	                                 integer: what a total is stated against

Whether an allocation fails depends on the machine and not on the values, as the checks of the recursion level do,
which the model leaves out: the meaning of typed code is its value where it does not leave for want of memory. The
theorems say so of each operation: a part set keeps the length, "arraySetPartLength"; Take gives the length asked for,
"arrayTakeLength", and never more than the array has, "arrayTakeLengthBound"; each leaves by a part that is not there
alone, "arraySetPartLeave" and "arrayTakeLeave"; a constant array of a length a machine integer counts is there,
"arrayConstantOfNatural". A proof about a loop over an array takes its rounds with "arrayPartOfJoin" and
"arraySetPartOfJoin", the array split at the place the loop is at, and its invariant with "confirmBindThen".
*)


(* ::Section:: *)
(*PackageExported*)




(* ::Section:: *)
(*PackageScoped*)


PackageScoped[$machineArrayDeclarations]


(* ::Section:: *)
(*Usage Messages*)


$machineArrayDeclarations::usage = "$machineArrayDeclarations is the list of the declarations of the vectors of typed code, in order, which need the declarations of the machine integers before them."


(* ::Section:: *)
(*Function Definitions*)


(* the declarations in order, each theorem proved by its tactics in the environment so far; the bound written as a
   literal *)
$machineArrayDeclarations = With[{upper = 9223372036854775808}, {
	(* the two cases of a sum are apart, and each is one to one: what a proof needs of a result that is known to be a
	   value, or known to be a leave *)
	TypeTheoryTheorem["rightNotLeft",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]], Typed[x, A], Typed[f, B]}, Implies[Typed["right"[f], A | B] == Typed["left"[x], A | B], False]],
		Function[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]], Typed[x, A], Typed[f, B], Typed[e, Typed["right"[f], A | B] == Typed["left"[x], A | B]]},
			"equalitySubstitution"[e, "trueIntroduction",
				P -> Function[{Typed[s, A | B]}, InductiveRecursor[DisjointUnionType][Function[{Typed[t, A | B]}, TypeUniverse[0]], Function[{Typed[a, A]}, False], Function[{Typed[b, B]}, True], s]]]]
	],
	TypeTheoryTheorem["leftNotRight",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]], Typed[x, A], Typed[f, B]}, Implies[Typed["left"[x], A | B] == Typed["right"[f], A | B], False]],
		Function[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]], Typed[x, A], Typed[f, B], Typed[e, Typed["left"[x], A | B] == Typed["right"[f], A | B]]},
			"rightNotLeft"[A, B, x, f, "equalitySymmetry"[e]]]
	],
	TypeTheoryTheorem["leftInjective",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]], Typed[x, A], Typed[y, A]}, Implies[Typed["left"[x], A | B] == Typed["left"[y], A | B], x == y]],
		Function[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[e, Typed["left"[x], A | B] == Typed["left"[y], A | B]]},
			"equalityCongruence"[Function[{Typed[s, A | B]}, InductiveRecursor[DisjointUnionType][Function[{Typed[t, A | B]}, A], Function[{Typed[a, A]}, a], Function[{Typed[b, B]}, x], s]], e]]
	],
	TypeTheoryTheorem["rightInjective",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]], Typed[f, B], Typed[g, B]}, Implies[Typed["right"[f], A | B] == Typed["right"[g], A | B], f == g]],
		Function[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]], Typed[f, B], Typed[g, B], Typed[e, Typed["right"[f], A | B] == Typed["right"[g], A | B]]},
			"equalityCongruence"[Function[{Typed[s, A | B]}, InductiveRecursor[DisjointUnionType][Function[{Typed[t, A | B]}, B], Function[{Typed[a, A]}, f], Function[{Typed[b, B]}, b], s]], e]]
	],
	(* a failure passes through two continuations as through one: where each value's continuation, bound again, is g's.
	   The invariant of a loop is stated of the loop bound to what the function does with its state, and this takes a
	   round of the loop, a result bound to the rest of the loop, to the hypothesis of the induction *)
	machineTheorem["confirmBindThen",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[B, TypeUniverse[1]], Typed[C, TypeUniverse[1]], Typed[m, A | Failure], Typed[f, A -> B | Failure], Typed[k, B -> C | Failure], Typed[g, A -> C | Failure]},
			Implies[ForAll[{Typed[t, A]}, "confirmBind"[f[t], k] == g[t]], "confirmBind"["confirmBind"[m, f], k] == "confirmBind"[m, g]]],
		{"Introduce"[A, B, C, m, f, k, g, h], "Cases"[m], "Introduce"[a], "Exact"[h[a]], "Introduce"[e], "Reflexivity"}
	],

	(* the lists a machine holds: the variable of the range names the list of an array, a["list"] *)
	TypeTheoryDefinition["arrayLengthRange", Typed[
		Function[{Typed[A, TypeUniverse[1]]}, Typed[list, {A}] |-> Length[list] < upper],
		ForAll[{Typed[A, TypeUniverse[1]]}, {A} -> TypeUniverse[0]]
	]],
	(* by its rank, as the compiler's type "PackedArray"::[t, 1]: an array of rank 0 is an element, and one of a rank
	   above an array of the rank below of the lists of elements a machine holds. The recursion carries the type of
	   the elements, so that the array of rank 1 computes to the lists of A itself, and not of a recursion at rank 0
	   that is yet to compute: a hypothesis on a["list"] and a term written with {A} are then the same term, which a
	   rewrite needs *)
	TypeTheoryDefinition["PackedArray", Typed[
		Function[{Typed[A, TypeUniverse[1]], Typed[rank, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
			Function[{Typed[k, NonNegativeIntegers]}, TypeUniverse[1] -> TypeUniverse[1]],
			Function[{Typed[T, TypeUniverse[1]]}, T],
			Function[{Typed[k, NonNegativeIntegers], Typed[r, TypeUniverse[1] -> TypeUniverse[1]]}, Function[{Typed[T, TypeUniverse[1]]}, r[Subtype["arrayLengthRange"[T]]]]],
			rank
		][A]],
		TypeUniverse[1] -> NonNegativeIntegers -> TypeUniverse[1]
	]],
	(* the element of a list at a place counted from 0 by an integer: the list is walked with the place counted
	   down, so a place below 0 or past the end is never met, and is not there *)
	TypeTheoryDefinition["listPart", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[l, {A}]}, InductiveRecursor[List][
			Function[{Typed[t, {A}]}, Integers -> (A | Failure)],
			Function[{Typed[j, Integers]}, Typed["right"[Failure["PartRange", <||>]], A | Failure]],
			Function[{Typed[x, A], Typed[rest, {A}], Typed[r, Integers -> (A | Failure)]}, Function[{Typed[j, Integers]},
				"machineIf"["integerEqual"[j, 0], Typed["left"[x], A | Failure], r[j - 1]]
			]],
			l
		]],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, {A} -> Integers -> (A | Failure)]
	]],
	(* the list with the element at such a place set *)
	TypeTheoryDefinition["listSetPart", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[l, {A}], Typed[v, A]}, InductiveRecursor[List][
			Function[{Typed[t, {A}]}, Integers -> ({A} | Failure)],
			Function[{Typed[j, Integers]}, Typed["right"[Failure["PartRange", <||>]], {A} | Failure]],
			Function[{Typed[x, A], Typed[rest, {A}], Typed[r, Integers -> ({A} | Failure)]}, Function[{Typed[j, Integers]},
				"machineIf"["integerEqual"[j, 0],
					Typed["left"[Prepend[v][rest]], {A} | Failure],
					"confirmBind"[r[j - 1], Function[{Typed[t, {A}]}, Typed["left"[Prepend[x][t]], {A} | Failure]]]
				]
			]],
			l
		]],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, {A} -> A -> Integers -> ({A} | Failure)]
	]],
	(* the first elements of a list, as many as an integer counts, and the list without them; more than it has are
	   not there *)
	TypeTheoryDefinition["listTake", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[l, {A}]}, InductiveRecursor[List][
			Function[{Typed[t, {A}]}, Integers -> ({A} | Failure)],
			Function[{Typed[c, Integers]}, "machineIf"["integerEqual"[c, 0], Typed["left"[Typed[{}, {A}]], {A} | Failure], Typed["right"[Failure["PartRange", <||>]], {A} | Failure]]],
			Function[{Typed[x, A], Typed[rest, {A}], Typed[r, Integers -> ({A} | Failure)]}, Function[{Typed[c, Integers]},
				"machineIf"["integerEqual"[c, 0],
					Typed["left"[Typed[{}, {A}]], {A} | Failure],
					"confirmBind"[r[c - 1], Function[{Typed[t, {A}]}, Typed["left"[Prepend[x][t]], {A} | Failure]]]
				]
			]],
			l
		]],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, {A} -> Integers -> ({A} | Failure)]
	]],
	TypeTheoryDefinition["listDrop", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[l, {A}]}, InductiveRecursor[List][
			Function[{Typed[t, {A}]}, Integers -> ({A} | Failure)],
			Function[{Typed[c, Integers]}, "machineIf"["integerEqual"[c, 0], Typed["left"[Typed[{}, {A}]], {A} | Failure], Typed["right"[Failure["PartRange", <||>]], {A} | Failure]]],
			Function[{Typed[x, A], Typed[rest, {A}], Typed[r, Integers -> ({A} | Failure)]}, Function[{Typed[c, Integers]},
				"machineIf"["integerEqual"[c, 0], Typed["left"[Prepend[x][rest]], {A} | Failure], r[c - 1]]
			]],
			l
		]],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, {A} -> Integers -> ({A} | Failure)]
	]],
	(* the list of a number of copies of an element *)
	TypeTheoryDefinition["listConstant", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[c, A], Typed[n, NonNegativeIntegers]}, InductiveRecursor[NonNegativeIntegers][
			Function[{Typed[k, NonNegativeIntegers]}, {A}],
			Typed[{}, {A}],
			Function[{Typed[k, NonNegativeIntegers], Typed[r, {A}]}, Prepend[c][r]],
			n
		]],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, A -> NonNegativeIntegers -> {A}]
	]],
	(* the array of a list a machine can hold, and for a longer one the leave of an allocation that fails. Setting a
	   part and Take never give such a list, "arraySetPartLeave" and "arrayTakeLeave", nor does a constant array of a
	   length a machine integer counts, "arrayConstantOfNatural": the leave is not part of the meaning of typed code *)
	TypeTheoryDefinition["arrayOfList", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[l, {A}]}, InductiveRecursor[Decidable][
			Typed[d, Decidable["arrayLengthRange"[A][l]]] |-> "PackedArray"[A, 1] | Failure,
			Typed[h, Not["arrayLengthRange"[A][l]]] |-> Typed["right"[Failure["Memory", <||>]], "PackedArray"[A, 1] | Failure],
			Typed[h, "arrayLengthRange"[A][l]] |-> Typed["left"["subtype"[l, h]], "PackedArray"[A, 1] | Failure],
			"machineDecision"["arrayLengthRange"[A][l]]
		]],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, {A} -> ("PackedArray"[A, 1] | Failure)]
	]],
	(* Length never leaves: the length of an array's list is a machine integer by the array's own proof *)
	TypeTheoryDefinition["arrayLength", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]]},
			Typed["subtype"["integerOfNatural"[Length[a[["list"]]]], "naturalInteger64Range"[Length[a[["list"]]], a[["proof"]]]], "Integer64"]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, "PackedArray"[A, 1] -> "Integer64"]
	]],
	(* a[[i]]: from 1, or below 0 from the end *)
	TypeTheoryDefinition["arrayPart", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[i, Integers]},
			"machineIf"["integerLessEqualQ"[1, i],
				"listPart"[a[["list"]]][i - 1],
				"listPart"[a[["list"]]]["integerOfNatural"[Length[a[["list"]]]] + i]
			]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, "PackedArray"[A, 1] -> Integers -> (A | Failure)]
	]],
	(* a[[i]] = v: the array with the part set, by the same rule *)
	TypeTheoryDefinition["arraySetPart", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[i, Integers], Typed[v, A]},
			"confirmBind"[
				"machineIf"["integerLessEqualQ"[1, i],
					"listSetPart"[a[["list"]], v][i - 1],
					"listSetPart"[a[["list"]], v]["integerOfNatural"[Length[a[["list"]]]] + i]
				],
				Function[{Typed[l, {A}]}, "arrayOfList"[l]]
			]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, "PackedArray"[A, 1] -> Integers -> A -> ("PackedArray"[A, 1] | Failure)]
	]],
	(* Take[a, n]: the first n, or below 0 the last -n *)
	TypeTheoryDefinition["arrayTake", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[n, Integers]},
			"confirmBind"[
				"machineIf"["integerLessEqualQ"[0, n],
					"listTake"[a[["list"]]][n],
					"listDrop"[a[["list"]]]["integerOfNatural"[Length[a[["list"]]]] + n]
				],
				Function[{Typed[l, {A}]}, "arrayOfList"[l]]
			]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, "PackedArray"[A, 1] -> Integers -> ("PackedArray"[A, 1] | Failure)]
	]],
	(* ConstantArray[c, n]: the natural number of an integer that is not below 0 is the first of its normal pair; a
	   length below 0 is the compiler's leave Failure["Range", <||>] *)
	TypeTheoryDefinition["arrayConstant", Typed[
		Function[{TypedImplicit[A, TypeUniverse[1]], Typed[c, A], Typed[n, Integers]},
			"machineIf"["integerLessEqualQ"[0, n],
				"arrayOfList"["listConstant"[c, "integerNormalPair"[n][[1]]]],
				Typed["right"[Failure["Range", <||>]], "PackedArray"[A, 1] | Failure]
			]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[1]]}, A -> Integers -> ("PackedArray"[A, 1] | Failure)]
	]],
	(* Total of machine integers: the machine's sums from 0, left to right, leaving where one does *)
	TypeTheoryDefinition["integerListTotal", Typed[
		Function[{Typed[l, {"Integer64"}]}, InductiveRecursor[List][
			Function[{Typed[t, {"Integer64"}]}, "Integer64" -> ("Integer64" | Failure)],
			Function[{Typed[s, "Integer64"]}, Typed["left"[s], "Integer64" | Failure]],
			Function[{Typed[x, "Integer64"], Typed[rest, {"Integer64"}], Typed[r, "Integer64" -> ("Integer64" | Failure)]}, Function[{Typed[s, "Integer64"]},
				"confirmBind"["machinePlus"[s[["integer"]], x[["integer"]]], r]
			]],
			l
		]],
		{"Integer64"} -> "Integer64" -> ("Integer64" | Failure)
	]],
	TypeTheoryDefinition["arrayTotal", Typed[
		Function[{Typed[a, "PackedArray"["Integer64", 1]]}, "confirmBind"["machineResult"[0], Function[{Typed[zero, "Integer64"]}, "integerListTotal"[a[["list"]]][zero]]]],
		"PackedArray"["Integer64", 1] -> ("Integer64" | Failure)
	]],
	(* the mathematics the total is stated against: the sum of the integers of a list of machine integers, and that
	   every sum on the way to it from s, left to right, is one a machine holds *)
	TypeTheoryDefinition["integerListSum", Typed[
		Function[{Typed[l, {"Integer64"}]}, InductiveRecursor[List][
			Function[{Typed[t, {"Integer64"}]}, Integers],
			Typed[0, Integers],
			Function[{Typed[x, "Integer64"], Typed[rest, {"Integer64"}], Typed[r, Integers]}, x[["integer"]] + r],
			l
		]],
		{"Integer64"} -> Integers
	]],
	TypeTheoryDefinition["partialSumsInRange", Typed[
		Function[{Typed[l, {"Integer64"}]}, InductiveRecursor[List][
			Function[{Typed[t, {"Integer64"}]}, Integers -> TypeUniverse[0]],
			Function[{Typed[s, Integers]}, True],
			Function[{Typed[x, "Integer64"], Typed[rest, {"Integer64"}], Typed[r, Integers -> TypeUniverse[0]]}, Function[{Typed[s, Integers]},
				"integer64Range"[s + x[["integer"]]] && r[s + x[["integer"]]]
			]],
			l
		]],
		{"Integer64"} -> Integers -> TypeUniverse[0]
	]],

	(* a list a machine can hold is its array, with no leave: the decision of the range, whatever the instance, takes its
	   true case, and any two proofs of the range are one. And the array of a list, where there is one, has that list *)
	TypeTheoryTheorem["arrayOfListInRange",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[l, {A}], Typed[h, "arrayLengthRange"[A][l]]}, "arrayOfList"[l] == Typed["left"["subtype"[l, h]], "PackedArray"[A, 1] | Failure]],
		Function[{Typed[A, TypeUniverse[1]], Typed[l, {A}], Typed[h, "arrayLengthRange"[A][l]]}, InductiveRecursor[Decidable][
			Typed[d, Decidable["arrayLengthRange"[A][l]]] |-> InductiveRecursor[Decidable][
				Typed[e, Decidable["arrayLengthRange"[A][l]]] |-> "PackedArray"[A, 1] | Failure,
				Typed[k, Not["arrayLengthRange"[A][l]]] |-> Typed["right"[Failure["Memory", <||>]], "PackedArray"[A, 1] | Failure],
				Typed[k, "arrayLengthRange"[A][l]] |-> Typed["left"["subtype"[l, k]], "PackedArray"[A, 1] | Failure],
				d
			] == Typed["left"["subtype"[l, h]], "PackedArray"[A, 1] | Failure],
			Typed[k, Not["arrayLengthRange"[A][l]]] |-> "falseElimination"[k[h]],
			Typed[k, "arrayLengthRange"[A][l]] |-> "equalityReflexivity"[Typed["left"["subtype"[l, h]], "PackedArray"[A, 1] | Failure]],
			"machineDecision"["arrayLengthRange"[A][l]]
		]]
	],
	machineTheorem["arrayOfListValue",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[m, {A}], Typed[b, "PackedArray"[A, 1]]}, Implies["arrayOfList"[m] == Typed["left"[b], "PackedArray"[A, 1] | Failure], b[["list"]] == m]],
		{"Introduce"[A, m, b],
			"Change"[Implies[InductiveRecursor[Decidable][
				Typed[d, Decidable["arrayLengthRange"[A][m]]] |-> "PackedArray"[A, 1] | Failure,
				Typed[k, Not["arrayLengthRange"[A][m]]] |-> Typed["right"[Failure["Memory", <||>]], "PackedArray"[A, 1] | Failure],
				Typed[k, "arrayLengthRange"[A][m]] |-> Typed["left"["subtype"[m, k]], "PackedArray"[A, 1] | Failure],
				"machineDecision"["arrayLengthRange"[A][m]]
			] == Typed["left"[b], "PackedArray"[A, 1] | Failure], b[["list"]] == m]],
			"Cases"["machineDecision"["arrayLengthRange"[A][m]]],
			"Introduce"[k, h], "Exact"["falseElimination"["rightNotLeft"["PackedArray"[A, 1], Failure, b, Failure["Memory", <||>], h]]],
			"Introduce"[k, h], "Rewrite"["leftInjective"["PackedArray"[A, 1], Failure, "subtype"[m, k], b, h], "RightToLeft"], "Reflexivity"}
	],
	(* the integer of an array's length is the integer of its list's *)
	machineTheorem["arrayLengthInteger",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[v, "PackedArray"[A, 1]]}, "arrayLength"[v][["integer"]] == "integerOfNatural"[Length[v[["list"]]]]],
		{"Introduce"[A, v], "Reflexivity"}
	],
	(* a constant list has the length given *)
	machineTheorem["listConstantLength",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[c, A], Typed[n, NonNegativeIntegers]}, Length["listConstant"[c, n]] == n],
		{"Introduce"[A, c, n], "Induction"[n], "Reflexivity", "Introduce"[k, ih], "Exact"["equalityCongruence"["successor", ih]]}
	],
	(* the part of a list at the length of what comes before it, and the list with that part set *)
	machineTheorem["listPartOfJoin",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[x, A], Typed[rest, {A}], Typed[pre, {A}]},
			"listPart"[Join[pre, Prepend[x][rest]]]["integerOfNatural"[Length[pre]]] == Typed["left"[x], A | Failure]],
		{"Introduce"[A, x, rest, pre], "Induction"[pre],
			"Reflexivity",
			"Introduce"[y, tail, ih],
			"Change"["machineIf"["integerEqual"["integerOfNatural"[Length[tail] + 1], 0], Typed["left"[y], A | Failure],
				"listPart"[Join[tail, Prepend[x][rest]]]["integerOfNatural"[Length[tail] + 1] - 1]] == Typed["left"[x], A | Failure]],
			"Rewrite"["integerOfSuccessorNotZero"[Length[tail]]], "Rewrite"["integerOfNaturalPredecessor"[Length[tail]]], "Exact"[ih]}
	],
	machineTheorem["listSetPartOfJoin",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[v, A], Typed[y, A], Typed[rest, {A}], Typed[pre, {A}]},
			"listSetPart"[Join[pre, Prepend[y][rest]], v]["integerOfNatural"[Length[pre]]] == Typed["left"[Join[pre, Prepend[v][rest]]], {A} | Failure]],
		{"Introduce"[A, v, y, rest, pre], "Induction"[pre],
			"Reflexivity",
			"Introduce"[z, tail, ih],
			"Change"["machineIf"["integerEqual"["integerOfNatural"[Length[tail] + 1], 0],
				Typed["left"[Prepend[v][Join[tail, Prepend[y][rest]]]], {A} | Failure],
				"confirmBind"["listSetPart"[Join[tail, Prepend[y][rest]], v]["integerOfNatural"[Length[tail] + 1] - 1], Function[{Typed[t, {A}]}, Typed["left"[Prepend[z][t]], {A} | Failure]]]
			] == Typed["left"[Join[Prepend[z][tail], Prepend[v][rest]]], {A} | Failure]],
			"Rewrite"["integerOfSuccessorNotZero"[Length[tail]]], "Rewrite"["integerOfNaturalPredecessor"[Length[tail]]], "Rewrite"[ih], "Reflexivity"}
	],
	(* a list with a part set is as long as it was, and the setting leaves by a part that is not there alone *)
	machineTheorem["listSetPartLength",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[v, A], Typed[l, {A}], Typed[j, Integers], Typed[m, {A}]},
			Implies["listSetPart"[l, v][j] == Typed["left"[m], {A} | Failure], Length[m] == Length[l]]],
		{"Introduce"[A, v, l], "Induction"[l],
			"Introduce"[j, m, h], "Exact"["falseElimination"["rightNotLeft"[{A}, Failure, m, Failure["PartRange", <||>], h]]],
			"Introduce"[x, rest, ih, j, m],
			"Change"[Implies["machineIf"["integerEqual"[j, 0], Typed["left"[Prepend[v][rest]], {A} | Failure],
				"confirmBind"["listSetPart"[rest, v][j - 1], Function[{Typed[t, {A}]}, Typed["left"[Prepend[x][t]], {A} | Failure]]]] == Typed["left"[m], {A} | Failure], Length[m] == Length[rest] + 1]],
			"Cases"["integerEqual"[j, 0]],
			"Have"[ih2, ForAll[{Typed[t, {A}]}, Implies["listSetPart"[rest, v][j - 1] == Typed["left"[t], {A} | Failure], Length[t] == Length[rest]]]], "Exact"[ih[j - 1]],
			"Generalize"[ih2], "Cases"["listSetPart"[rest, v][j - 1]],
			"Introduce"[t, ih2, h],
			"Have"[hl, Length[t] == Length[rest]], "Exact"[ih2[t, "equalityReflexivity"[Typed["left"[t], {A} | Failure]]]],
			"Rewrite"["leftInjective"[{A}, Failure, Prepend[x][t], m, h], "RightToLeft"], "Exact"["equalityCongruence"["successor", hl]],
			"Introduce"[f, ih2, h], "Exact"["falseElimination"["rightNotLeft"[{A}, Failure, m, f, h]]],
			"Introduce"[h], "Rewrite"["leftInjective"[{A}, Failure, Prepend[v][rest], m, h], "RightToLeft"], "Reflexivity"}
	],
	machineTheorem["listSetPartLeave",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[v, A], Typed[l, {A}], Typed[j, Integers], Typed[f, Failure]},
			Implies["listSetPart"[l, v][j] == Typed["right"[f], {A} | Failure], f == Failure["PartRange", <||>]]],
		{"Introduce"[A, v, l], "Induction"[l],
			"Introduce"[j, f, h], "Exact"["equalitySymmetry"["rightInjective"[{A}, Failure, Failure["PartRange", <||>], f, h]]],
			"Introduce"[x, rest, ih, j, f],
			"Change"[Implies["machineIf"["integerEqual"[j, 0], Typed["left"[Prepend[v][rest]], {A} | Failure],
				"confirmBind"["listSetPart"[rest, v][j - 1], Function[{Typed[t, {A}]}, Typed["left"[Prepend[x][t]], {A} | Failure]]]] == Typed["right"[f], {A} | Failure], f == Failure["PartRange", <||>]]],
			"Cases"["integerEqual"[j, 0]],
			"Have"[ih2, ForAll[{Typed[g, Failure]}, Implies["listSetPart"[rest, v][j - 1] == Typed["right"[g], {A} | Failure], g == Failure["PartRange", <||>]]]], "Exact"[ih[j - 1]],
			"Generalize"[ih2], "Cases"["listSetPart"[rest, v][j - 1]],
			"Introduce"[t, ih2, h], "Exact"["falseElimination"["leftNotRight"[{A}, Failure, Prepend[x][t], f, h]]],
			"Introduce"[g, ih2, h], "Rewrite"["rightInjective"[{A}, Failure, g, f, h], "RightToLeft"], "Exact"[ih2[g, "equalityReflexivity"[Typed["right"[g], {A} | Failure]]]],
			"Introduce"[h], "Exact"["falseElimination"["leftNotRight"[{A}, Failure, Prepend[v][rest], f, h]]]}
	],
	(* Take gives the length asked for, of a list no longer than the one it takes from, and leaves by a part that is
	   not there alone *)
	machineTheorem["listTakeLength",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[l, {A}], Typed[c, Integers], Typed[m, {A}]},
			Implies["listTake"[l][c] == Typed["left"[m], {A} | Failure], "integerOfNatural"[Length[m]] == c && Length[m] <= Length[l]]],
		{"Introduce"[A, l], "Induction"[l],
			"Introduce"[c, m],
			"Change"[Implies["machineIf"["integerEqual"[c, 0], Typed["left"[Typed[{}, {A}]], {A} | Failure], Typed["right"[Failure["PartRange", <||>]], {A} | Failure]] == Typed["left"[m], {A} | Failure],
				"integerOfNatural"[Length[m]] == c && Length[m] <= 0]],
			"Have"[hc, Implies["integerEqual"[c, 0] == "true", c == 0]], "Exact"["integerEqualTrue"[c, 0]],
			"Generalize"[hc], "Cases"["integerEqual"[c, 0]],
			"Introduce"[hc, h], "Exact"["falseElimination"["rightNotLeft"[{A}, Failure, m, Failure["PartRange", <||>], h]]],
			"Introduce"[hc, h], "Rewrite"["leftInjective"[{A}, Failure, Typed[{}, {A}], m, h], "RightToLeft"],
			"Exact"["andIntroduction"["equalitySymmetry"[hc["equalityReflexivity"["true"]]], "lessEqualZero"[0]]],
			"Introduce"[x, rest, ih, c, m],
			"Change"[Implies["machineIf"["integerEqual"[c, 0], Typed["left"[Typed[{}, {A}]], {A} | Failure],
				"confirmBind"["listTake"[rest][c - 1], Function[{Typed[t, {A}]}, Typed["left"[Prepend[x][t]], {A} | Failure]]]] == Typed["left"[m], {A} | Failure],
				"integerOfNatural"[Length[m]] == c && Length[m] <= Length[rest] + 1]],
			"Have"[hc, Implies["integerEqual"[c, 0] == "true", c == 0]], "Exact"["integerEqualTrue"[c, 0]],
			"Generalize"[hc], "Cases"["integerEqual"[c, 0]],
			"Introduce"[hc],
			"Have"[ih2, ForAll[{Typed[t, {A}]}, Implies["listTake"[rest][c - 1] == Typed["left"[t], {A} | Failure], "integerOfNatural"[Length[t]] == c - 1 && Length[t] <= Length[rest]]]], "Exact"[ih[c - 1]],
			"Generalize"[ih2], "Cases"["listTake"[rest][c - 1]],
			"Introduce"[t, ih2, h],
			"Have"[hl, "integerOfNatural"[Length[t]] == c - 1 && Length[t] <= Length[rest]], "Exact"[ih2[t, "equalityReflexivity"[Typed["left"[t], {A} | Failure]]]],
			"Rewrite"["leftInjective"[{A}, Failure, Prepend[x][t], m, h], "RightToLeft"],
			"Change"["integerOfNatural"[Length[t] + 1] == c && Length[t] + 1 <= Length[rest] + 1],
			"Apply"["andIntroduction"],
			"Rewrite"["integerOfNaturalAddition"[Length[t], 1]], "Rewrite"[hl[["left"]]], "Ring",
			"Exact"["lessEqualSuccessor"[hl[["right"]]]],
			"Introduce"[f, ih2, h], "Exact"["falseElimination"["rightNotLeft"[{A}, Failure, m, f, h]]],
			"Introduce"[hc, h], "Rewrite"["leftInjective"[{A}, Failure, Typed[{}, {A}], m, h], "RightToLeft"],
			"Exact"["andIntroduction"["equalitySymmetry"[hc["equalityReflexivity"["true"]]], "lessEqualZero"[Length[rest] + 1]]]}
	],
	machineTheorem["listTakeLeave",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[l, {A}], Typed[c, Integers], Typed[f, Failure]},
			Implies["listTake"[l][c] == Typed["right"[f], {A} | Failure], f == Failure["PartRange", <||>]]],
		{"Introduce"[A, l], "Induction"[l],
			"Introduce"[c, f],
			"Change"[Implies["machineIf"["integerEqual"[c, 0], Typed["left"[Typed[{}, {A}]], {A} | Failure], Typed["right"[Failure["PartRange", <||>]], {A} | Failure]] == Typed["right"[f], {A} | Failure],
				f == Failure["PartRange", <||>]]],
			"Cases"["integerEqual"[c, 0]],
			"Introduce"[h], "Exact"["equalitySymmetry"["rightInjective"[{A}, Failure, Failure["PartRange", <||>], f, h]]],
			"Introduce"[h], "Exact"["falseElimination"["leftNotRight"[{A}, Failure, Typed[{}, {A}], f, h]]],
			"Introduce"[x, rest, ih, c, f],
			"Change"[Implies["machineIf"["integerEqual"[c, 0], Typed["left"[Typed[{}, {A}]], {A} | Failure],
				"confirmBind"["listTake"[rest][c - 1], Function[{Typed[t, {A}]}, Typed["left"[Prepend[x][t]], {A} | Failure]]]] == Typed["right"[f], {A} | Failure], f == Failure["PartRange", <||>]]],
			"Cases"["integerEqual"[c, 0]],
			"Have"[ih2, ForAll[{Typed[g, Failure]}, Implies["listTake"[rest][c - 1] == Typed["right"[g], {A} | Failure], g == Failure["PartRange", <||>]]]], "Exact"[ih[c - 1]],
			"Generalize"[ih2], "Cases"["listTake"[rest][c - 1]],
			"Introduce"[t, ih2, h], "Exact"["falseElimination"["leftNotRight"[{A}, Failure, Prepend[x][t], f, h]]],
			"Introduce"[g, ih2, h], "Rewrite"["rightInjective"[{A}, Failure, g, f, h], "RightToLeft"], "Exact"[ih2[g, "equalityReflexivity"[Typed["right"[g], {A} | Failure]]]],
			"Introduce"[h], "Exact"["falseElimination"["leftNotRight"[{A}, Failure, Typed[{}, {A}], f, h]]]}
	],
	(* a list without its first elements is no longer than it, and it too leaves by a part that is not there alone *)
	machineTheorem["listDropLength",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[l, {A}], Typed[c, Integers], Typed[m, {A}]},
			Implies["listDrop"[l][c] == Typed["left"[m], {A} | Failure], Length[m] <= Length[l]]],
		{"Introduce"[A, l], "Induction"[l],
			"Introduce"[c, m],
			"Change"[Implies["machineIf"["integerEqual"[c, 0], Typed["left"[Typed[{}, {A}]], {A} | Failure], Typed["right"[Failure["PartRange", <||>]], {A} | Failure]] == Typed["left"[m], {A} | Failure],
				Length[m] <= 0]],
			"Cases"["integerEqual"[c, 0]],
			"Introduce"[h], "Exact"["falseElimination"["rightNotLeft"[{A}, Failure, m, Failure["PartRange", <||>], h]]],
			"Introduce"[h], "Rewrite"["leftInjective"[{A}, Failure, Typed[{}, {A}], m, h], "RightToLeft"], "Exact"["lessEqualZero"[0]],
			"Introduce"[x, rest, ih, c, m],
			"Change"[Implies["machineIf"["integerEqual"[c, 0], Typed["left"[Prepend[x][rest]], {A} | Failure], "listDrop"[rest][c - 1]] == Typed["left"[m], {A} | Failure], Length[m] <= Length[rest] + 1]],
			"Cases"["integerEqual"[c, 0]],
			"Introduce"[h], "Exact"["lessEqualStep"[ih[c - 1, m, h]]],
			"Introduce"[h], "Rewrite"["leftInjective"[{A}, Failure, Prepend[x][rest], m, h], "RightToLeft"], "Change"[Length[rest] + 1 <= Length[rest] + 1], "Exact"["lessEqualReflexivity"]}
	],
	machineTheorem["listDropLeave",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[l, {A}], Typed[c, Integers], Typed[f, Failure]},
			Implies["listDrop"[l][c] == Typed["right"[f], {A} | Failure], f == Failure["PartRange", <||>]]],
		{"Introduce"[A, l], "Induction"[l],
			"Introduce"[c, f],
			"Change"[Implies["machineIf"["integerEqual"[c, 0], Typed["left"[Typed[{}, {A}]], {A} | Failure], Typed["right"[Failure["PartRange", <||>]], {A} | Failure]] == Typed["right"[f], {A} | Failure],
				f == Failure["PartRange", <||>]]],
			"Cases"["integerEqual"[c, 0]],
			"Introduce"[h], "Exact"["equalitySymmetry"["rightInjective"[{A}, Failure, Failure["PartRange", <||>], f, h]]],
			"Introduce"[h], "Exact"["falseElimination"["leftNotRight"[{A}, Failure, Typed[{}, {A}], f, h]]],
			"Introduce"[x, rest, ih, c, f],
			"Change"[Implies["machineIf"["integerEqual"[c, 0], Typed["left"[Prepend[x][rest]], {A} | Failure], "listDrop"[rest][c - 1]] == Typed["right"[f], {A} | Failure], f == Failure["PartRange", <||>]]],
			"Cases"["integerEqual"[c, 0]],
			"Introduce"[h], "Exact"[ih[c - 1, f, h]],
			"Introduce"[h], "Exact"["falseElimination"["leftNotRight"[{A}, Failure, Prepend[x][rest], f, h]]]}
	],
	(* an operation on the list of an array, made an array again: where the array is there, the operation gave its list;
	   and where the operation gives lists no longer than the array's, the leave is the operation's own, the same
	   failure in the sum of the lists and in the sum of the arrays *)
	machineTheorem["arrayOfResultValue",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[r, {A} | Failure], Typed[b, "PackedArray"[A, 1]]},
			Implies["confirmBind"[r, Function[{Typed[l, {A}]}, "arrayOfList"[l]]] == Typed["left"[b], "PackedArray"[A, 1] | Failure], r == Typed["left"[b[["list"]]], {A} | Failure]]],
		{"Introduce"[A, r], "Cases"[r],
			"Introduce"[m, b, h], "Rewrite"["arrayOfListValue"[A, m, b, h]],
			"Introduce"[f, b, h], "Exact"["falseElimination"["rightNotLeft"["PackedArray"[A, 1], Failure, b, f, h]]]}
	],
	machineTheorem["arrayOfResultLeave",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[r, {A} | Failure], Typed[e, Failure]},
			Implies[ForAll[{Typed[m, {A}]}, Implies[r == Typed["left"[m], {A} | Failure], Length[m] <= Length[a[["list"]]]]],
				Implies["confirmBind"[r, Function[{Typed[l, {A}]}, "arrayOfList"[l]]] == Typed["right"[e], "PackedArray"[A, 1] | Failure], r == Typed["right"[e], {A} | Failure]]]],
		{"Introduce"[A, a, r], "Cases"[r],
			"Introduce"[m, e, hb, h],
			"Have"[shorter, Length[m] <= Length[a[["list"]]]], "Exact"[hb[m, "equalityReflexivity"[Typed["left"[m], {A} | Failure]]]],
			"Have"[held, Length[a[["list"]]] < upper], "Exact"[a[["proof"]]],
			"Have"[hr, "arrayLengthRange"[A][m]], "Exact"["lessEqualTransitivity"["lessEqualSuccessor"[shorter], held]],
			"Have"[h2, "arrayOfList"[m] == Typed["right"[e], "PackedArray"[A, 1] | Failure]], "Exact"[h],
			"Rewrite"["arrayOfListInRange"[A, m, hr], "At" -> h2],
			"Exact"["falseElimination"["leftNotRight"["PackedArray"[A, 1], Failure, "subtype"[m, hr], e, h2]]],
			"Introduce"[f, e, hb, h],
			"Have"[h3, Typed["right"[f], "PackedArray"[A, 1] | Failure] == Typed["right"[e], "PackedArray"[A, 1] | Failure]], "Exact"[h],
			"Rewrite"["rightInjective"["PackedArray"[A, 1], Failure, f, e, h3]]}
	],
	(* the part of an array at the place after what comes before it *)
	machineTheorem["arrayPartOfJoin",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[v, "PackedArray"[A, 1]], Typed[pre, {A}], Typed[x, A], Typed[rest, {A}]},
			Implies[v[["list"]] == Join[pre, Prepend[x][rest]], "arrayPart"[v, "integerOfNatural"[Length[pre] + 1]] == Typed["left"[x], A | Failure]]],
		{"Introduce"[A, v, pre, x, rest, e],
			"Have"[positive, 1 <= Length[pre] + 1], "LinearArithmetic",
			"Change"["machineIf"["integerLessEqualQ"[1, "integerOfNatural"[Length[pre] + 1]],
				"listPart"[v[["list"]]]["integerOfNatural"[Length[pre] + 1] - 1],
				"listPart"[v[["list"]]]["integerOfNatural"[Length[v[["list"]]]] + "integerOfNatural"[Length[pre] + 1]]] == Typed["left"[x], A | Failure]],
			"Rewrite"["integerLessEqualQOfNatural"[1, Length[pre] + 1, positive]],
			"Rewrite"["integerOfNaturalPredecessor"[Length[pre]]],
			"Rewrite"[e],
			"Exact"["listPartOfJoin"[A, x, rest, pre]]}
	],
	(* an array with a part set is an array, the list as long as it was; the part of an array set at the place after
	   what comes before it, with the proof of the range named, and then as an array there is, whose list is known *)
	machineTheorem["arraySetPartRange",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[pre, {A}], Typed[y, A], Typed[v, A], Typed[rest, {A}]},
			Implies[a[["list"]] == Join[pre, Prepend[y][rest]], "arrayLengthRange"[A][Join[pre, Prepend[v][rest]]]]],
		{"Introduce"[A, a, pre, y, v, rest, e],
			"Change"[Length[Join[pre, Prepend[v][rest]]] < upper], "Rewrite"["lengthJoin"[pre, Prepend[v][rest]]],
			"Change"[Length[pre] + Length[Prepend[y][rest]] < upper], "Rewrite"["lengthJoin"[pre, Prepend[y][rest]], "RightToLeft"],
			"Rewrite"[e, "RightToLeft"], "Exact"[a[["proof"]]]}
	],
	machineTheorem["arraySetPartOfJoinInRange",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[pre, {A}], Typed[y, A], Typed[v, A], Typed[rest, {A}], Typed[h, "arrayLengthRange"[A][Join[pre, Prepend[v][rest]]]]},
			Implies[a[["list"]] == Join[pre, Prepend[y][rest]],
				"arraySetPart"[a, "integerOfNatural"[Length[pre] + 1], v] == Typed["left"["subtype"[Join[pre, Prepend[v][rest]], h]], "PackedArray"[A, 1] | Failure]]],
		{"Introduce"[A, a, pre, y, v, rest, h, e],
			"Have"[positive, 1 <= Length[pre] + 1], "LinearArithmetic",
			"Change"["confirmBind"[
				"machineIf"["integerLessEqualQ"[1, "integerOfNatural"[Length[pre] + 1]],
					"listSetPart"[a[["list"]], v]["integerOfNatural"[Length[pre] + 1] - 1],
					"listSetPart"[a[["list"]], v]["integerOfNatural"[Length[a[["list"]]]] + "integerOfNatural"[Length[pre] + 1]]],
				Function[{Typed[l, {A}]}, "arrayOfList"[l]]] == Typed["left"["subtype"[Join[pre, Prepend[v][rest]], h]], "PackedArray"[A, 1] | Failure]],
			"Rewrite"["integerLessEqualQOfNatural"[1, Length[pre] + 1, positive]],
			"Rewrite"["integerOfNaturalPredecessor"[Length[pre]]],
			"Rewrite"[e],
			"Rewrite"["listSetPartOfJoin"[A, v, y, rest, pre]],
			"Exact"["arrayOfListInRange"[A, Join[pre, Prepend[v][rest]], h]]}
	],
	machineTheorem["arraySetPartOfJoin",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[pre, {A}], Typed[y, A], Typed[v, A], Typed[rest, {A}]},
			Implies[a[["list"]] == Join[pre, Prepend[y][rest]],
				Exists[{Typed[b, "PackedArray"[A, 1]]}, "arraySetPart"[a, "integerOfNatural"[Length[pre] + 1], v] == Typed["left"[b], "PackedArray"[A, 1] | Failure] && b[["list"]] == Join[pre, Prepend[v][rest]]]]],
		{"Introduce"[A, a, pre, y, v, rest, e],
			"Have"[h, "arrayLengthRange"[A][Join[pre, Prepend[v][rest]]]], "Exact"["arraySetPartRange"[A, a, pre, y, v, rest, e]],
			"Exact"["existsIntroduction"["subtype"[Join[pre, Prepend[v][rest]], h],
				"andIntroduction"["arraySetPartOfJoinInRange"[A, a, pre, y, v, rest, h, e], "equalityReflexivity"[Join[pre, Prepend[v][rest]]]]]]}
	],
	(* a[[i]] = v keeps the length, and leaves by a part that is not there alone *)
	machineTheorem["arraySetPartLength",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[i, Integers], Typed[v, A], Typed[b, "PackedArray"[A, 1]]},
			Implies["arraySetPart"[a, i, v] == Typed["left"[b], "PackedArray"[A, 1] | Failure], Length[b[["list"]]] == Length[a[["list"]]]]],
		{"Introduce"[A, a, i, v, b],
			"Change"[Implies["confirmBind"[
				"machineIf"["integerLessEqualQ"[1, i], "listSetPart"[a[["list"]], v][i - 1], "listSetPart"[a[["list"]], v]["integerOfNatural"[Length[a[["list"]]]] + i]],
				Function[{Typed[l, {A}]}, "arrayOfList"[l]]] == Typed["left"[b], "PackedArray"[A, 1] | Failure], Length[b[["list"]]] == Length[a[["list"]]]]],
			"Cases"["integerLessEqualQ"[1, i]],
			"Introduce"[h], "Exact"["listSetPartLength"[A, v, a[["list"]], "integerOfNatural"[Length[a[["list"]]]] + i, b[["list"]],
				"arrayOfResultValue"[A, "listSetPart"[a[["list"]], v]["integerOfNatural"[Length[a[["list"]]]] + i], b, h]]],
			"Introduce"[h], "Exact"["listSetPartLength"[A, v, a[["list"]], i - 1, b[["list"]], "arrayOfResultValue"[A, "listSetPart"[a[["list"]], v][i - 1], b, h]]]}
	],
	machineTheorem["arraySetPartLeave",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[i, Integers], Typed[v, A], Typed[e, Failure]},
			Implies["arraySetPart"[a, i, v] == Typed["right"[e], "PackedArray"[A, 1] | Failure], e == Failure["PartRange", <||>]]],
		{"Introduce"[A, a, i, v, e],
			"Change"[Implies["confirmBind"[
				"machineIf"["integerLessEqualQ"[1, i], "listSetPart"[a[["list"]], v][i - 1], "listSetPart"[a[["list"]], v]["integerOfNatural"[Length[a[["list"]]]] + i]],
				Function[{Typed[l, {A}]}, "arrayOfList"[l]]] == Typed["right"[e], "PackedArray"[A, 1] | Failure], e == Failure["PartRange", <||>]]],
			"Cases"["integerLessEqualQ"[1, i]],
			"Introduce"[h], "Exact"["listSetPartLeave"[A, v, a[["list"]], "integerOfNatural"[Length[a[["list"]]]] + i, e,
				"arrayOfResultLeave"[A, a, "listSetPart"[a[["list"]], v]["integerOfNatural"[Length[a[["list"]]]] + i], e,
					Function[{Typed[m, {A}], Typed[hm, "listSetPart"[a[["list"]], v]["integerOfNatural"[Length[a[["list"]]]] + i] == Typed["left"[m], {A} | Failure]]},
						"equalitySubstitution"["equalitySymmetry"["listSetPartLength"[A, v, a[["list"]], "integerOfNatural"[Length[a[["list"]]]] + i, m, hm]], "lessEqualReflexivity",
							P -> Function[{Typed[k, NonNegativeIntegers]}, k <= Length[a[["list"]]]]]],
					h]]],
			"Introduce"[h], "Exact"["listSetPartLeave"[A, v, a[["list"]], i - 1, e,
				"arrayOfResultLeave"[A, a, "listSetPart"[a[["list"]], v][i - 1], e,
					Function[{Typed[m, {A}], Typed[hm, "listSetPart"[a[["list"]], v][i - 1] == Typed["left"[m], {A} | Failure]]},
						"equalitySubstitution"["equalitySymmetry"["listSetPartLength"[A, v, a[["list"]], i - 1, m, hm]], "lessEqualReflexivity",
							P -> Function[{Typed[k, NonNegativeIntegers]}, k <= Length[a[["list"]]]]]],
					h]]]}
	],
	(* Take[a, n] of a count that is not below 0 has the length n; of any count, a length no more than the array's; and it
	   leaves by a part that is not there alone *)
	machineTheorem["arrayTakeLength",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[n, Integers], Typed[b, "PackedArray"[A, 1]]},
			Implies["integerLessEqualQ"[0, n] == "true", Implies["arrayTake"[a, n] == Typed["left"[b], "PackedArray"[A, 1] | Failure], "integerOfNatural"[Length[b[["list"]]]] == n]]],
		{"Introduce"[A, a, n, b, hn],
			"Change"[Implies["confirmBind"[
				"machineIf"["integerLessEqualQ"[0, n], "listTake"[a[["list"]]][n], "listDrop"[a[["list"]]]["integerOfNatural"[Length[a[["list"]]]] + n]],
				Function[{Typed[l, {A}]}, "arrayOfList"[l]]] == Typed["left"[b], "PackedArray"[A, 1] | Failure], "integerOfNatural"[Length[b[["list"]]]] == n]],
			"Rewrite"[hn], "Introduce"[h],
			"Exact"["andEliminationLeft"["listTakeLength"[A, a[["list"]], n, b[["list"]], "arrayOfResultValue"[A, "listTake"[a[["list"]]][n], b, h]]]]}
	],
	machineTheorem["arrayTakeLengthBound",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[n, Integers], Typed[b, "PackedArray"[A, 1]]},
			Implies["arrayTake"[a, n] == Typed["left"[b], "PackedArray"[A, 1] | Failure], Length[b[["list"]]] <= Length[a[["list"]]]]],
		{"Introduce"[A, a, n, b],
			"Change"[Implies["confirmBind"[
				"machineIf"["integerLessEqualQ"[0, n], "listTake"[a[["list"]]][n], "listDrop"[a[["list"]]]["integerOfNatural"[Length[a[["list"]]]] + n]],
				Function[{Typed[l, {A}]}, "arrayOfList"[l]]] == Typed["left"[b], "PackedArray"[A, 1] | Failure], Length[b[["list"]]] <= Length[a[["list"]]]]],
			"Cases"["integerLessEqualQ"[0, n]],
			"Introduce"[h], "Exact"["listDropLength"[A, a[["list"]], "integerOfNatural"[Length[a[["list"]]]] + n, b[["list"]],
				"arrayOfResultValue"[A, "listDrop"[a[["list"]]]["integerOfNatural"[Length[a[["list"]]]] + n], b, h]]],
			"Introduce"[h], "Exact"["andEliminationRight"["listTakeLength"[A, a[["list"]], n, b[["list"]], "arrayOfResultValue"[A, "listTake"[a[["list"]]][n], b, h]]]]}
	],
	machineTheorem["arrayTakeLeave",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[a, "PackedArray"[A, 1]], Typed[n, Integers], Typed[e, Failure]},
			Implies["arrayTake"[a, n] == Typed["right"[e], "PackedArray"[A, 1] | Failure], e == Failure["PartRange", <||>]]],
		{"Introduce"[A, a, n, e],
			"Change"[Implies["confirmBind"[
				"machineIf"["integerLessEqualQ"[0, n], "listTake"[a[["list"]]][n], "listDrop"[a[["list"]]]["integerOfNatural"[Length[a[["list"]]]] + n]],
				Function[{Typed[l, {A}]}, "arrayOfList"[l]]] == Typed["right"[e], "PackedArray"[A, 1] | Failure], e == Failure["PartRange", <||>]]],
			"Cases"["integerLessEqualQ"[0, n]],
			"Introduce"[h], "Exact"["listDropLeave"[A, a[["list"]], "integerOfNatural"[Length[a[["list"]]]] + n, e,
				"arrayOfResultLeave"[A, a, "listDrop"[a[["list"]]]["integerOfNatural"[Length[a[["list"]]]] + n], e,
					Function[{Typed[m, {A}], Typed[hm, "listDrop"[a[["list"]]]["integerOfNatural"[Length[a[["list"]]]] + n] == Typed["left"[m], {A} | Failure]]},
						"listDropLength"[A, a[["list"]], "integerOfNatural"[Length[a[["list"]]]] + n, m, hm]],
					h]]],
			"Introduce"[h], "Exact"["listTakeLeave"[A, a[["list"]], n, e,
				"arrayOfResultLeave"[A, a, "listTake"[a[["list"]]][n], e,
					Function[{Typed[m, {A}], Typed[hm, "listTake"[a[["list"]]][n] == Typed["left"[m], {A} | Failure]]},
						"andEliminationRight"["listTakeLength"[A, a[["list"]], n, m, hm]]],
					h]]]}
	],
	(* a constant array of a length a machine integer counts: there is the array, and its list is known *)
	machineTheorem["arrayConstantOfNatural",
		ForAll[{Typed[A, TypeUniverse[1]], Typed[c, A], Typed[k, NonNegativeIntegers]}, Implies[k < upper,
			Exists[{Typed[a, "PackedArray"[A, 1]]}, "arrayConstant"[c, "integerOfNatural"[k]] == Typed["left"[a], "PackedArray"[A, 1] | Failure] && a[["list"]] == "listConstant"[c, k]]]],
		{"Introduce"[A, c, k, hk],
			"Have"[h, "arrayLengthRange"[A]["listConstant"[c, k]]],
			"Change"[Length["listConstant"[c, k]] < upper], "Rewrite"["listConstantLength"[A, c, k]], "Exact"[hk],
			"Have"[hc, "arrayConstant"[c, "integerOfNatural"[k]] == Typed["left"["subtype"["listConstant"[c, k], h]], "PackedArray"[A, 1] | Failure]],
			"Change"["machineIf"["integerLessEqualQ"[0, "integerOfNatural"[k]],
				"arrayOfList"["listConstant"[c, "integerNormalPair"["integerOfNatural"[k]][[1]]]],
				Typed["right"[Failure["Range", <||>]], "PackedArray"[A, 1] | Failure]] == Typed["left"["subtype"["listConstant"[c, k], h]], "PackedArray"[A, 1] | Failure]],
			"Rewrite"["integerLessEqualQOfNatural"[0, k, "lessEqualZero"[k]]], "Rewrite"["integerNormalPairOfNatural"[k]],
			"Exact"["arrayOfListInRange"[A, "listConstant"[c, k], h]],
			"Exact"["existsIntroduction"["subtype"["listConstant"[c, k], h], "andIntroduction"[hc, "equalityReflexivity"["listConstant"[c, k]]]]]}
	],
	(* where the sums on the way are in range the total does not leave, and is the sum *)
	machineTheorem["integerListTotalOfSums",
		ForAll[{Typed[l, {"Integer64"}], Typed[s, "Integer64"]}, Implies["partialSumsInRange"[l][s[["integer"]]],
			Exists[{Typed[r, "Integer64"]}, "integerListTotal"[l][s] == Typed["left"[r], "Integer64" | Failure] && r[["integer"]] == s[["integer"]] + "integerListSum"[l]]]],
		{"Introduce"[l], "Induction"[l],
			"Introduce"[s, h],
			"Exact"["existsIntroduction"[s, "andIntroduction"["equalityReflexivity"[Typed["left"[s], "Integer64" | Failure]], "equalitySymmetry"["integerAdditionZero"[s[["integer"]]]]]]],
			"Introduce"[x, tail, ih, s],
			"Change"[Implies["integer64Range"[s[["integer"]] + x[["integer"]]] && "partialSumsInRange"[tail][s[["integer"]] + x[["integer"]]],
				Exists[{Typed[r, "Integer64"]}, "confirmBind"["machineResult"[s[["integer"]] + x[["integer"]]], "integerListTotal"[tail]] == Typed["left"[r], "Integer64" | Failure] &&
					r[["integer"]] == s[["integer"]] + (x[["integer"]] + "integerListSum"[tail])]]],
			"Introduce"[h],
			"Rewrite"["machineResultInRange"[s[["integer"]] + x[["integer"]], h[["left"]]]],
			"Cases"[ih["subtype"[s[["integer"]] + x[["integer"]], h[["left"]]], h[["right"]]]],
			"Introduce"[r, hr],
			"Exact"["existsIntroduction"[r, "andIntroduction"[hr[["left"]],
				"equalityTransitivity"[hr[["right"]], "integerAdditionAssociativity"[s[["integer"]], x[["integer"]], "integerListSum"[tail]]]]]]}
	]
}]
