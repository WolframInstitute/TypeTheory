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
   "Type" gives or over "Expressions". Without it, an axiom of the type "Type" gives. *)
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
				Last[TypeTheoryFormalize[reversed]] === TypeTheoryAxiom[reversed, "Expressions" -> "Expressions", "Implementation" -> reversed],
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
