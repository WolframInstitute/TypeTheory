(* ::Package:: *)

(* Tests for Elaboration/WolframDefinitions.wl: reading a symbol's definitions through the compiler, or a Failure that
   names how to install it. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

(* with the compiler a Core`Program with a definition for each of the symbol's; without it a Failure naming the
   paclet *)
VerificationTest[
	Block[{size},
		size[{}] = 0;
		size[{x_, rest___}] := 1 + size[{rest}];
		Replace[WolframInstitute`TypeTheory`PackageScope`lowerDefinitions[HoldComplete[size]], {
			Failure["KernelCompilerMissing", KeyValuePattern["MessageParameters" -> {_, install_String}]] :> StringContainsQ[install, "Wolfram/KernelCompiler"],
			program_ :> Length[Catenate[Values[First[program]]]] >= 2
		}]
	],
	True,
	TestID -> "Definitions-are-lowered-by-the-compiler-or-its-install-is-named"
]

(* with the compiler: a definition that translates is typed by elaboration, the symbols it calls formalized first and
   the built-ins it calls declared by their signatures; one that does not is an axiom Wolfram computes, of the type
   "Type" gives or over Expressions. Without it, an axiom of the type "Type" gives. *)
VerificationTest[
	Block[{$TypeTheoryEnvironment = TypeTheoryEnvironment["Rationals"], square, next, simplified, reversed},
		square[x_Integer] := x^2 + 1;
		next[x_Integer] := square[x] + 1;
		simplified[x_Integer] := Simplify[x + 1];
		reversed[s_] := StringReverse[s];
		If[ PacletFind["Wolfram/KernelCompiler"] === {},
			{TypeTheoryFormalize[reversed, "Type" -> Integers -> Integers]} === {{TypeTheoryAxiom[reversed, Integers -> Integers, "Implementation" -> reversed]}},
			{
				TypeTheoryFormalize[square] === {TypeTheoryDefinition[square, Function[{Typed[x, Integers]}, x^2 + 1]]},
				First[TypeOf[TypeTheoryTerm[next, TypeTheoryEnvironment[$TypeTheoryEnvironment, TypeTheoryFormalize[next]]]]] === (Integers -> Integers),
				TypeTheoryFormalize[simplified][[All, 1]] === {Simplify, simplified},
				Last[TypeTheoryFormalize[reversed]] === TypeTheoryAxiom[reversed, Expressions -> Expressions, "Implementation" -> reversed],
				TypeTheoryFormalize[reversed, "Type" -> Integers -> Integers] === {TypeTheoryAxiom[reversed, Integers -> Integers, "Implementation" -> reversed]}
			} === {True, True, True, True, True}
		]
	],
	True,
	TestID -> "A-symbol-is-formalized-as-a-definition-where-it-translates-and-as-an-axiom-Wolfram-computes-otherwise"
]

(* reading definitions leaves the context path as it was, so the compiler's names shadow none of TypeTheory's *)
VerificationTest[
	With[{path = $ContextPath},
		Block[{shadowed}, shadowed[x_] := x; WolframInstitute`TypeTheory`PackageScope`lowerDefinitions[HoldComplete[shadowed]]];
		{$ContextPath === path, Context[TypeTheoryCheck]}
	],
	{True, "WolframInstitute`TypeTheory`"},
	TestID -> "Reading-definitions-puts-nothing-on-the-context-path"
]

(* two definitions by structural recursion on a list, f[{}] and f[{x_, rest___}], are a definition by the recursor of
   lists, which computes: the type of its empty case gives its result, its elements of any type where they can be *)
VerificationTest[
	Block[{size, total, integers = TypeTheoryEnvironment["Integers"]},
		size[{}] = 0;
		size[{x_, rest___}] := 1 + size[{rest}];
		total[{}] = 0;
		total[{x_, rest___}] := x + total[{rest}];
		If[ PacletFind["Wolfram/KernelCompiler"] === {},
			True,
			With[{sized = TypeTheoryEnvironment[integers, TypeTheoryFormalize[size, integers]]},
				{
					MatchQ[TypeOf[TypeTheoryTerm[size, sized]], TypeTheoryTerm[HoldPattern[ForAll[{TypedImplicit[_, _]}, Lists[_] -> NonNegativeIntegers]], _]],
					WeakHeadNormalForm[TypeTheoryTerm[size[{4, 5, 6}], sized]] === TypeTheoryTerm[3, sized],
					MatchQ[TypeTheoryFormalize[total, integers, "Type" -> Lists[Integers] -> Integers], {TypeTheoryDefinition[total, Typed[_, Lists[Integers] -> Integers]]}]
				} === {True, True, True}
			]
		]
	],
	True,
	TestID -> "Structural-recursion-on-a-list-is-a-definition-by-the-recursor-of-lists"
]

(* conditions: definitions each but the last with one, and If in a body, are If by the decision of the condition,
   which elaboration finds as an instance of Decidable, and which computes; a type given decides the arguments, also
   where the patterns' heads say _Integer *)
VerificationTest[
	Block[{sign, clamp, prelude = TypeTheoryEnvironment["Prelude"]},
		sign[n_Integer /; n == 0] := 0;
		sign[n_Integer] := 1;
		clamp[x_Integer] := If[x <= 3, x, 3];
		If[ PacletFind["Wolfram/KernelCompiler"] === {},
			True,
			With[
				{
					signed = TypeTheoryEnvironment[prelude, TypeTheoryFormalize[sign, prelude, "Type" -> NonNegativeIntegers -> NonNegativeIntegers]],
					clamped = TypeTheoryEnvironment[prelude, TypeTheoryFormalize[clamp, prelude, "Type" -> NonNegativeIntegers -> NonNegativeIntegers]]
				},
				{
					MatchQ[signed[sign], TypeTheoryDefinition[sign, Typed[Function[{_}, HoldPattern[If[_, 0, 1]]], _]]],
					WeakHeadNormalForm[TypeTheoryTerm[sign[0], signed]] === TypeTheoryTerm[0, signed],
					WeakHeadNormalForm[TypeTheoryTerm[sign[7], signed]] === TypeTheoryTerm[1, signed],
					WeakHeadNormalForm[TypeTheoryTerm[clamp[5], clamped]] === TypeTheoryTerm[3, clamped],
					WeakHeadNormalForm[TypeTheoryTerm[clamp[2], clamped]] === TypeTheoryTerm[2, clamped]
				} === {True, True, True, True, True}
			]
		]
	],
	True,
	TestID -> "Conditions-and-If-are-If-by-the-decision-of-the-condition"
]

(* recursion on a natural number, f[0] and f[n_] calling f only on n - 1, perhaps with n an _Integer and n > 0 and with
   other arguments passed on as they are, is a definition by the recursor of the natural numbers, which computes *)
VerificationTest[
	Block[{fact, double, power, prelude = TypeTheoryEnvironment["Prelude"]},
		fact[0] = 1;
		fact[n_] := n fact[n - 1];
		double[0] = 0;
		double[n_Integer /; n > 0] := double[n - 1] + 2;
		power[x_, 0] = 1;
		power[x_, n_] := x power[x, n - 1];
		If[ PacletFind["Wolfram/KernelCompiler"] === {},
			True,
			With[
				{
					facts = TypeTheoryEnvironment[prelude, TypeTheoryFormalize[fact, prelude]],
					doubles = TypeTheoryEnvironment[prelude, TypeTheoryFormalize[double, prelude]]
				},
				{
					MatchQ[TypeOf[TypeTheoryTerm[fact, facts]], TypeTheoryTerm[HoldPattern[NonNegativeIntegers -> NonNegativeIntegers], _]],
					WeakHeadNormalForm[TypeTheoryTerm[fact[5], facts]] === TypeTheoryTerm[120, facts],
					WeakHeadNormalForm[TypeTheoryTerm[double[4], doubles]] === TypeTheoryTerm[8, doubles],
					With[{powers = TypeTheoryEnvironment[prelude, TypeTheoryFormalize[power, prelude]]}, WeakHeadNormalForm[TypeTheoryTerm[power[2, 10], powers]] === TypeTheoryTerm[1024, powers]]
				} === {True, True, True, True}
			]
		]
	],
	True,
	TestID -> "Recursion-on-a-natural-number-is-a-definition-by-the-recursor-of-the-natural-numbers"
]

(* a built-in that is total on lists has a signature over their elements, Range : NonNegativeIntegers -> Lists[...],
   and one that is partial, as First, a signature over Expressions *)
VerificationTest[
	Block[{upTo, firstOf, prelude = TypeTheoryEnvironment["Prelude"]},
		upTo[n_] := Range[n];
		firstOf[l_] := First[l];
		If[ PacletFind["Wolfram/KernelCompiler"] === {},
			True,
			{
				MatchQ[TypeOf[TypeTheoryTerm[upTo, TypeTheoryEnvironment[prelude, TypeTheoryFormalize[upTo, prelude]]]], TypeTheoryTerm[HoldPattern[NonNegativeIntegers -> Lists[NonNegativeIntegers]], _]],
				MatchQ[Last[TypeTheoryFormalize[firstOf, prelude]], TypeTheoryDefinition[firstOf, _Function]]
			} === {True, True}
		]
	],
	True,
	TestID -> "Built-ins-total-on-lists-have-signatures-over-their-elements"
]
