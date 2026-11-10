#!/usr/bin/env wolframscript
(* ::Package:: *)

(* Times the kernel on products nested k deep, where each added product about doubles the work, beside sums, which
   stay polynomial. Run from the repository root, on any kernel that runs TypeTheory:

       wolframscript -f scripts/product_chain_timing.wls

   1. The integers alone: the kernel's check that ((1 2) 3) ... k is the literal k!, a product of integer literals.
   2. The machine: a chain of k steps p_j = "machineTimes"[p_(j-1)[["integer"]], j], as compiled code is read, and
      the same chain of "machinePlus".

   An integer is a class of pairs of natural numbers, and (a, b) (c, d) is (a c + b d, a d + b c): each factor is
   used twice. The terms are written as text and parsed, so building them asks nothing of With or of patterns. *)

PacletDirectoryLoad[Directory[]]
Needs["WolframInstitute`TypeTheory`"]

integers = TypeTheoryEnvironment["Integers"]
machine = TypeTheoryEnvironment["Machine"]

seconds[evaluation_] := Round[First[AbsoluteTiming[TimeConstrained[evaluation, 120, "timeout"]]], 0.001]
SetAttributes[seconds, HoldFirst]

productText[k_Integer] := StringJoin[Table["(", {k - 1}], "Typed[1, Integers]", Table[" * " <> ToString[j] <> ")", {j, 2, k}]]

literalCheck[k_Integer] := Replace[
	ToExpression["{" <> productText[k] <> ", Typed[" <> ToString[k!] <> ", Integers]}", InputForm, HoldComplete],
	HoldComplete[{product_, literal_}] :> seconds[DefinitionallyEqualQ[TypeTheoryTerm[product, integers], TypeTheoryTerm[literal, integers]]]
]

chainText[operation_String, k_Integer] := StringJoin[
	"\"confirmBind\"[\"machineResult\"[1], Function[{Typed[p1, \"Integer64\"]}, ",
	Table["\"confirmBind\"[\"" <> operation <> "\"[p" <> ToString[j - 1] <> "[[\"integer\"]], " <> ToString[j] <> "], Function[{Typed[p" <> ToString[j] <> ", \"Integer64\"]}, ", {j, 2, k}],
	"Typed[\"left\"[p" <> ToString[k] <> "], \"Integer64\" | Failure]",
	Table["]]", {k - 1}],
	"]]"
]

chainNormalForm[operation_String, k_Integer] := Replace[
	ToExpression[chainText[operation, k], InputForm, HoldComplete],
	HoldComplete[term_] :> seconds[NormalForm[TypeTheoryTerm[term, machine]]]
]

Print["kernel: ", $Version]
Print["integer product nested k deep is its literal, {k, seconds}: ", Table[{k, literalCheck[k]}, {k, {8, 10, 12, 14, 16, 18}}]]
Print["machine chain of k products, {k, seconds}: ", Table[{k, chainNormalForm["machineTimes", k]}, {k, {8, 10, 12, 13, 14}}]]
Print["machine chain of k sums, {k, seconds}: ", Table[{k, chainNormalForm["machinePlus", k]}, {k, {8, 16, 32, 64}}]]
