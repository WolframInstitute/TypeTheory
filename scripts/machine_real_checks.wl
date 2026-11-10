(* Compiled real arithmetic against the evaluator, on the kernel that compiles definitions:

       wl -f scripts/machine_real_checks.wl

   The machine model of TypeTheoryFormalize[f, "Machine"] reads a machine real as the rational it is and each
   operation as the compiler's table of typed operations says. This script runs the edges that reading rests on:
   compiled code and the evaluator must give the same text, InputForm, never SameQ, which takes two reals a last bit
   apart as the same, and the column of declines says where the typed entry leaves. It prints a row for each case,
   and the system it ran on: the fused multiply-add of x y + z depends on the platform's C compiler. *)
addR[x_Real, y_Real] := x + y;
subR[x_Real, y_Real] := x - y;
mulR[x_Real, y_Real] := x y;
divR[x_Real, y_Real] := x / y;
fmaR[x_Real, y_Real, z_Real] := x y + z;
fmaLeftR[x_Real, y_Real, z_Real] := z + x y;
fmaMinusR[x_Real, y_Real, z_Real] := x y - z;
ltIR[n_Integer, x_Real] := n < x;
roundR[x_Real] := Round[x];
floorR[x_Real] := Floor[x];
signR[x_Real] := Sign[x];
zeroQR[x_Real] := x == 0.;
minusR[x_Real] := Minus[x];
timesNegR[x_Real] := -1. * x;
sqrtR[x_Real] := Sqrt[x];
absR[x_Real] := Abs[x];
nOfI[n_Integer] := N[n];
eqR[x_Real, y_Real] := x == y;
atanR[x_Real, y_Real] := ArcTan[x, y];
text[x_] := ToString[x, InputForm];
quotients = Select[
	Flatten[Table[{N[p], N[q], text[N[p]/N[q]], text[N[p] (1/N[q])], text[N[p/q]]}, {p, 1, 60}, {q, 1, 60}], 1],
	Function[t, t[[3]] =!= t[[5]]]
];
Print["the evaluator's zeros: ", {text[-0.], text[Minus[0.]], text[-1. * 0.], ToString[-0.], text[Sqrt[-0.]], text[ArcTan[-0.]]}];
Print["pairs p, q <= 60 where the evaluator's x/y is not the nearest real to the exact quotient: ", Length[quotients]];
Print["  of them with x/y the same text as x (1/y): ", Count[quotients, t_ /; t[[3]] === t[[4]]]];
Print["  first: ", Take[quotients, UpTo[3]]];
cases = Join[
	{
		{"sum overflows", Hold[addR[1.7*^308, 1.7*^308]]},
		{"sum in range", Hold[addR[0.1, 0.2]]},
		{"product below $MinMachineNumber", Hold[mulR[1.*^-160, 1.*^-160]]},
		{"product underflows to 0", Hold[mulR[1.*^-200, 1.*^-200]]},
		{"difference subnormal", Hold[subR[3.*^-308, 2.5*^-308]]},
		{"x y + z, fused or not", Hold[fmaR[1. + 2.^-27, 1. + 2.^-27, -(1. + 2.^-26)]]},
		{"z + x y, fused or not", Hold[fmaLeftR[1. + 2.^-27, 1. + 2.^-27, -(1. + 2.^-26)]]},
		{"x y - z, fused or not", Hold[fmaMinusR[1. + 2.^-27, 1. + 2.^-27, 1. + 2.^-26]]},
		{"5. / 3.", Hold[divR[5., 3.]]},
		{"1. / 0.", Hold[divR[1., 0.]]},
		{"1. / -0.", Hold[divR[1., -0.]]},
		{"2^53 < 1.*^16", Hold[ltIR[9007199254740992, 1.*^16]]},
		{"2^53 + 1 < 1.*^16", Hold[ltIR[9007199254740993, 1.*^16]]},
		{"Round[8.9*^18]", Hold[roundR[8.9*^18]]},
		{"Round[9.1*^18]", Hold[roundR[9.1*^18]]},
		{"Round[9.3*^18]", Hold[roundR[9.3*^18]]},
		{"Round[2.5]", Hold[roundR[2.5]]},
		{"Round[3.5]", Hold[roundR[3.5]]},
		{"Floor[-2.5]", Hold[floorR[-2.5]]},
		{"Floor[9.1*^18]", Hold[floorR[9.1*^18]]},
		{"Sign[-0.]", Hold[signR[-0.]]},
		{"-0. == 0.", Hold[zeroQR[-0.]]},
		{"Minus[0.]", Hold[minusR[0.]]},
		{"-1. * 0.", Hold[timesNegR[0.]]},
		{"Sqrt[2.]", Hold[sqrtR[2.]]},
		{"Sqrt[-0.]", Hold[sqrtR[-0.]]},
		{"Sqrt[-1.]", Hold[sqrtR[-1.]]},
		{"Abs[-2.5]", Hold[absR[-2.5]]},
		{"N[2^53 + 1]", Hold[nOfI[9007199254740993]]},
		{"N[2^53 + 3]", Hold[nOfI[9007199254740995]]},
		{"1. == 1. + 2^-47", Hold[eqR[1., 1.0000000000000071]]},
		{"1. == 1. + 2^-45", Hold[eqR[1., 1.0000000000000284]]},
		{"ArcTan[-1., Minus[0.]]", Hold[atanR[-1., minusR[0.]]]},
		{"ArcTan[-1., 0.]", Hold[atanR[-1., 0.]]}
	},
	Map[Function[t, {"x / y not the nearest: " <> text[t[[1]]] <> " / " <> text[t[[2]]] <> " (nearest " <> t[[5]] <> ")", Hold[divR[#1, #2]] & @@ Take[t, 2]}], Take[quotients, UpTo[4]]]
];
expected = Map[Function[c, text[Quiet[ReleaseHold[c[[2]]]]]], cases];
Print["compile: ", Head[Kernel`CompileDefinitions[addR, subR, mulR, divR, fmaR, fmaLeftR, fmaMinusR, ltIR, roundR, floorR, signR, zeroQR, minusR, timesNegR, sqrtR, absR, nOfI, eqR, atanR]]];
declines[] := Total[{Kernel`CompiledInformation[addR]["Declines"], Kernel`CompiledInformation[subR]["Declines"], Kernel`CompiledInformation[mulR]["Declines"], Kernel`CompiledInformation[divR]["Declines"], Kernel`CompiledInformation[fmaR]["Declines"], Kernel`CompiledInformation[fmaLeftR]["Declines"], Kernel`CompiledInformation[fmaMinusR]["Declines"], Kernel`CompiledInformation[ltIR]["Declines"], Kernel`CompiledInformation[roundR]["Declines"], Kernel`CompiledInformation[floorR]["Declines"], Kernel`CompiledInformation[signR]["Declines"], Kernel`CompiledInformation[zeroQR]["Declines"], Kernel`CompiledInformation[minusR]["Declines"], Kernel`CompiledInformation[timesNegR]["Declines"], Kernel`CompiledInformation[sqrtR]["Declines"], Kernel`CompiledInformation[absR]["Declines"], Kernel`CompiledInformation[nOfI]["Declines"], Kernel`CompiledInformation[eqR]["Declines"], Kernel`CompiledInformation[atanR]["Declines"]}];
compiledQ = Map[Function[info, {info["Compiled"], info["Parameters"], info["Result"]}], {Kernel`CompiledInformation[minusR], Kernel`CompiledInformation[sqrtR], Kernel`CompiledInformation[nOfI], Kernel`CompiledInformation[eqR], Kernel`CompiledInformation[absR]}];
Print["typed entries (Minus, Sqrt, N, Equal, Abs): ", compiledQ];
MapThread[
	Function[{c, e}, Module[{before = declines[], value}, value = text[Quiet[ReleaseHold[c[[2]]]]]; Print[c[[1]], " | compiled: ", value, " | evaluator: ", e, " | same text: ", value === e, " | declines: ", declines[] - before]]],
	{cases, expected}
];
Print["system: ", $System, "  ", $ProcessorType];
