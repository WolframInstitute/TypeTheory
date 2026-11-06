#!/usr/bin/env wolframscript
(* ::Package:: *)

(* Compare the kernel's offset rule for natural numbers with unfolding alone, and its literal values read by offsets with
   those read by peeling successors, as docs/notes/KernelLiterals.md asks.

   Usage:
     wolframscript -f scripts/offset_agreement.wls        (* offsets 0 to 12 *)
     wolframscript -f scripts/offset_agreement.wls 6      (* offsets 0 to 6 *)

   Every pair of terms from the bases zero, x, y, successor[x] and x + y, with each offset, written as successors, as the
   base plus a literal and as the base plus zero plus a literal, is compared by definitional equality with
   $naturalOffsetRule on and off. Unfolding terminates in this range, so the two must agree. The literal value of each
   term and of the sum of each pair, which the kernel reads by offsets, must be the one peeling successors after weak head
   normal forms gives, the kernel's way before the offsets: the same integer, or None for both. Past the range, where
   peeling cannot finish, the literal values of 120 terms with random offsets up to 2^64 must be the offsets' sums: the
   offset over zero, None over a variable. A term read as stuck, which no literal can be, must have no literal value by
   peeling either. It prints the counts and the times, and the cases that disagree, and exits
   with status 1 on a disagreement. The run is held under a memory cap. *)

repositoryRoot = ParentDirectory[DirectoryName[$InputFileName]]

PacletDirectoryLoad[FileNameJoin[{repositoryRoot, "TypeTheory"}]]

Needs["WolframInstitute`TypeTheory`"]

largestOffset = Replace[Rest[$ScriptCommandLine], {{n_String} :> ToExpression[n], _ -> 12}]

scope[name_String] := Symbol["WolframInstitute`TypeTheory`PackageScope`" <> name]

prelude = TypeTheoryEnvironment["Prelude"]

reference[name_] := scope["constantReference"][HoldComplete[name], {}]

applied[head_, arguments__] := Fold[scope["application"], head, {arguments}]

variables = {scope["freshFreeVariable"][], scope["freshFreeVariable"][]}

context = Fold[Function[{partial, id}, scope["extendContext"][partial, id, HoldComplete["v"], reference[NonNegativeIntegers], "Explicit"]], <||>, variables]

{x, y} = scope["freeVariable"] /@ variables

plus[a_, b_] := applied[reference[Plus], a, b]

successor[a_] := applied[reference["successor"], a]

literal[n_] := scope["naturalLiteral"][n]

forms[base_, k_] := {Nest[successor, base, k], plus[base, literal[k]], plus[base, plus[literal[0], literal[k]]]}

terms = Flatten[Outer[forms, {reference["zero"], x, y, successor[x], plus[x, y]}, Range[0, largestOffset]], 2]

pairs = Tuples[terms, 2]

compared[] := Function[pair, scope["definitionallyEqualQ"][prelude, context, First[pair], Last[pair]]] /@ pairs

settings = scope["naturalNumberSettings"][prelude]

offsetLiteralValue[term_] := WolframInstitute`TypeTheory`Checking`NaturalNumbers`Private`literalValue[prelude, context, settings, term]

(* the literal value as the kernel read it before the offsets: the weak head normal form, then its successors peeled
   one by one, each argument reduced again, down to a literal or zero *)
(* the composite heads hold their parts, so the references are put in the pattern computed *)
peeledLiteralValue[term_] := With[
	{successorPattern = scope["application"] @@ {reference["successor"], Blank[]}, zero = reference["zero"]},
	Module[{current = scope["weakHeadNormalForm"][prelude, context, term], successors = 0},
		While[MatchQ[current, successorPattern],
			successors++;
			current = scope["weakHeadNormalForm"][prelude, context, Last[current]]
		];
		Replace[current, {
			scope["naturalLiteral"][n_Integer] :> n + successors,
			zero :> successors,
			_ :> None
		}]
	]
]

valueTerms = Join[terms, Function[pair, plus[First[pair], Last[pair]]] /@ pairs]

stuckQ[term_] := WolframInstitute`TypeTheory`Checking`NaturalNumbers`Private`stuckQ[context, settings, term]

(* random offsets up to 2^64, over zero and over x, written as base plus a literal and as base plus zero plus a literal *)
largeCases = BlockRandom[SeedRandom[2026]; Flatten[Function[k, {
	{plus[reference["zero"], literal[k]], k},
	{plus[plus[literal[0], literal[k]], literal[1]], k + 1},
	{plus[x, plus[literal[0], literal[k]]], None}
}] /@ RandomInteger[{10^6, 2^64}, 40], 1]]

result = MemoryConstrained[
	{
		AbsoluteTiming[compared[]],
		Block[{WolframInstitute`TypeTheory`PackageScope`$naturalOffsetRule = False}, AbsoluteTiming[compared[]]]
	},
	4*^9,
	"MemoryLimit"
]

values = MemoryConstrained[
	{
		AbsoluteTiming[offsetLiteralValue /@ valueTerms],
		AbsoluteTiming[peeledLiteralValue /@ valueTerms],
		AbsoluteTiming[Function[case, offsetLiteralValue[First[case]]] /@ largeCases]
	},
	4*^9,
	"MemoryLimit"
]

If[ result === "MemoryLimit" || values === "MemoryLimit",
	Print["The comparison went past 4 GB."];
	Exit[1]
]

{{ruleTime, withRule}, {unfoldingTime, withoutRule}} = result

{{offsetTime, byOffsets}, {peelingTime, byPeeling}, {largeTime, largeValues}} = values

disagreements = Pick[pairs, MapThread[UnsameQ, {withRule, withoutRule}]]

valueDisagreements = Pick[valueTerms, MapThread[UnsameQ, {byOffsets, byPeeling}]]

largeDisagreements = Pick[largeCases, MapThread[UnsameQ, {largeValues, Last /@ largeCases}]]

(* a term read as stuck has no literal value *)
stuckDisagreements = Pick[valueTerms, MapThread[Function[{term, value}, stuckQ[term] && value =!= None], {valueTerms, byPeeling}]]

Print[Length[pairs], " pairs of offsets 0 to ", largestOffset, ", ", Count[withRule, True], " equal; ", Length[disagreements], " disagree"]

Print["offset rule ", Round[ruleTime, 0.01], " s, unfolding alone ", Round[unfoldingTime, 0.01], " s"]

Print[Length[valueTerms], " literal values, ", Count[byOffsets, _Integer], " integers and ", Count[byOffsets, None], " None; ", Length[valueDisagreements], " disagree"]

Print["by offsets ", Round[offsetTime, 0.01], " s, by peeling ", Round[peelingTime, 0.01], " s"]

Print[Length[largeCases], " literal values of offsets up to 2^64, ", Length[largeDisagreements], " disagree with the offsets' sums, in ", Round[largeTime, 0.01], " s"]

Print[Count[valueTerms, _?stuckQ], " terms read as stuck, ", Length[stuckDisagreements], " of them with a literal value by peeling"]

Scan[Function[pair, Print["disagree: ", InputForm[pair]]], Take[Join[disagreements, valueDisagreements, largeDisagreements, stuckDisagreements], UpTo[10]]]

Exit[If[disagreements === {} && valueDisagreements === {} && largeDisagreements === {} && stuckDisagreements === {}, 0, 1]]
