(* The kernel's nearness check against the machine, on any kernel that runs TypeTheory:

       wolframscript -f scripts/real64_nearest_grid.wl
       wl -f scripts/real64_nearest_grid.wl < /dev/null

   "real64NearestQ"[q, m, a, b] is the Boolean the kernel computes for a rational q and a machine real m 2^a / 2^b: that
   the real is the one the rounding of q gives. This script holds it to the machine on a grid. For each q the value is
   computed by integers (nearestReal64), and three things are asked: that the value is the one expected, by hand or by
   the machine's own arithmetic; that the kernel's check accepts it; and that the check refuses the machine reals next
   to it on each side. For a q from 2^1024 - 2^970 on there is no value, and the check must refuse the largest real.

   The rows: the ties and bounds worked by hand in docs/notes/MachineReals.md and their negatives; products, sums and
   reciprocals of machine reals, whose exact results IEEE 754 has the machine round to the nearest, the value expected
   being the machine's; sums of two neighbours m 2^e and (m + 1) 2^e, exact ties (2 m + 1) 2^e built from integers;
   ties among the subnormal reals, (2 k + 1) 2^-1075; and rationals whose numerator and denominator are past 2^64.
   The numbers come from a generator written out here, so that every kernel runs the same rows.

   N of a rational is not asked to agree: the last count of each line says how often it gives the value, for the
   record. On Wolfram 15.0 it is a last place off for a third of the rationals past 2^64. *)

PacletDirectoryLoad[FileNameJoin[{ParentDirectory[DirectoryName[$InputFileName]], "TypeTheory"}]];
Needs["WolframInstitute`TypeTheory`"];

nearestReal64 = WolframInstitute`TypeTheory`PackageScope`nearestReal64;
canonicalForm = WolframInstitute`TypeTheory`PackageScope`real64CanonicalForm;
neighbours = WolframInstitute`TypeTheory`PackageScope`real64Neighbours;
reals = TypeTheoryEnvironment["MachineReals"];
If[Head[reals] =!= TypeTheoryEnvironment, Print["the environment of the machine reals did not build: ", reals]; Exit[1]];

(* the kernel's verdict on q and the machine real r *)
nearestQ[q_, r_] := Replace[canonicalForm[r], {m_, a_, b_} :> Replace[
	WeakHeadNormalForm[TypeTheoryTerm["real64NearestQ"[Typed[q, Rationals], Typed[m, Integers], a, b], reals]],
	{TypeTheoryTerm["true", ___] -> True, TypeTheoryTerm["false", ___] -> False}
]];

(* the exact rational of a machine real *)
exactOf[x_] := SetPrecision[x, Infinity];
state = 20261111;
next[] := (state = Mod[state 6364136223846793005 + 1442695040888963407, 2^64]; state);
below[n_] := Mod[Quotient[next[], 2^11], n];
big[bits_] := Mod[next[] 2^192 + next[] 2^128 + next[] 2^64 + next[], 2^bits] + 2^bits;
significand[] := 2^52 + below[2^52];
(* a machine real m 2^e, made by the machine: the integer is exact and so is the power of 2 *)
machineReal[m_, e_] := N[m] 2.^e;
largest = (2^53 - 1) 2^971;
bound = 2^1024 - 2^970;

(* a row: {kind, label, q, the value expected, by hand or by the machine, or None} *)
handRows = {
	{"hand", "2^-1075, between 0 and 2^-1074", 2^-1075, 0},
	{"hand", "3 2^-1075", 3 2^-1075, 2 2^-1074},
	{"hand", "2^-1074", 2^-1074, 2^-1074},
	{"hand", "2^53 - 1/2, below a power of two", 2^53 - 1/2, 2^53},
	{"hand", "(2^53 - 1/2) 2^900", (2^53 - 1/2) 2^900, 2^953},
	{"hand", "(2^53 - 1/2) 2^-1074", (2^53 - 1/2) 2^-1074, 2^-1021},
	{"hand", "2^53 + 1, above a power of two", 2^53 + 1, 2^53},
	{"hand", "2^53 + 3", 2^53 + 3, 2^53 + 4},
	{"hand", "(2^53 + 1) 2^-1074", (2^53 + 1) 2^-1074, 2^-1021},
	{"hand", "2^1024 - 2^970, the bound", bound, "leave"},
	{"hand", "the bound and 2^971 more", bound + 2^971, "leave"},
	{"hand", "the bound less 2^971, a tie below the largest real", bound - 2^971, (2^53 - 2) 2^971},
	{"hand", "the bound less 1", bound - 1, largest},
	{"hand", "the largest real", largest, largest},
	{"hand", "2^1024", 2^1024, "leave"},
	{"hand", "0", 0, 0},
	{"hand", "1/10", 1/10, 3602879701896397/36028797018963968}
};
rows = Join[
	handRows,
	Map[Function[row, {"hand", "minus " <> row[[2]], -row[[3]], If[row[[4]] === "leave", "leave", -row[[4]]]}], Select[handRows, Function[row, row[[3]] =!= 0]]],
	Table[With[{x = machineReal[significand[], below[600] - 352], y = machineReal[significand[], below[600] - 352]}, {"product", "x y", exactOf[x] exactOf[y], exactOf[x y]}], 60],
	Table[With[{e = below[1800] - 950}, With[{x = machineReal[significand[], e], y = machineReal[significand[], e - below[60]]}, {"sum", "x + y", exactOf[x] + exactOf[y], exactOf[x + y]}]], 60],
	Table[With[{y = machineReal[significand[], below[1800] - 950]}, {"reciprocal", "1 / y", 1 / exactOf[y], exactOf[1 / y]}], 40],
	Table[With[{m = 2^52 + below[2^52 - 1], e = below[1900] - 1000}, {"tie", "(2 m + 1) 2^e", (2 m + 1) 2^e, exactOf[machineReal[m, e] + machineReal[m + 1, e]]}], 40],
	Table[With[{k = below[2^52]}, {"subnormal tie", "(2 k + 1) 2^-1075", (2 k + 1) 2^-1075, (k + Mod[k, 2]) 2^-1074}], 20],
	Table[With[{q = big[64 + below[130]] / big[64 + below[130]] 2^(below[1900] - 950)}, {"rational", "p / d past 2^64", If[below[2] == 0, q, -q], None}], 200]
];

(* {kind, the value is the one expected, the check accepts it, the check refuses its neighbours, N gives it or None} *)
judge[{kind_, label_, q_, expected_}] := With[{value = If[Abs[q] >= bound, "leave", nearestReal64[q]]},
	{
		kind,
		expected === None || expected === value,
		If[value === "leave", nearestQ[q, Sign[q] largest] === False, nearestQ[q, value]],
		If[value === "leave", True, AllTrue[Select[neighbours[value], Function[r, Abs[r] < 2^1024]], Function[r, nearestQ[q, r] === False]]],
		With[{n = Quiet[N[q]]}, If[value =!= "leave" && MachineNumberQ[n], exactOf[n] === value, None]]
	}
];
verdicts = Map[judge, rows];
Scan[
	Function[kind, With[{of = Select[verdicts, Function[verdict, First[verdict] === kind]]},
		Print[kind, ": ", Length[of], " rows; the value is the one expected: ", Count[of, {_, True, __}], "; the check accepts it: ", Count[of, {_, _, True, __}],
			"; refuses its neighbours: ", Count[of, {_, _, _, True, _}], "; N gives it: ", Count[of, {__, True}], " of ", Count[of, {__, True | False}]]
	]],
	DeleteDuplicates[First /@ verdicts]
];
failing = Pick[rows, Map[Function[verdict, ! (verdict[[2]] && verdict[[3]] === True && verdict[[4]])], verdicts]];
Print["rows that fail: ", Length[failing], If[failing === {}, "", "  first: " <> ToString[Take[First[failing], 2]] <> " " <> ToString[InputForm[First[failing][[3]]]]]];
Print[$Version];

Exit[If[failing === {}, 0, 1]]
