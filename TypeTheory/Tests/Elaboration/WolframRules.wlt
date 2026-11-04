(* ::Package:: *)

(* Tests for Elaboration/WolframRules.wl: the rules of a symbol as a definition of type Expressions -> Option[Expressions]
   in TypeTheoryEnvironment["WolframLanguage"], read from the compiler's match programs. Each test passes without the
   compiler, which reading rules needs. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

(* the rules of a symbol, with the atoms a call uses, and the expression f[a, ...] quoted *)
rulesEnvironment[rules_List, atoms_List] := TypeTheoryEnvironment[TypeTheoryEnvironment["WolframLanguage"], Join[rules, Function[atom, TypeTheoryAxiom[atom, Atoms]] /@ atoms]]

(* the rules compute: f[x_, y_, z___] rewrites f[a, b] to {a, b}, by the lengths, the parts and the sequence the
   kernel reduces, and leaves f[a] as it is *)
VerificationTest[
	Block[{listed},
		listed[x_, y_, z___] := {x, y, z};
		If[ PacletFind["Wolfram/KernelCompiler"] === {},
			True,
			With[{environment = rulesEnvironment[TypeTheoryFormalize[listed, TypeTheoryEnvironment["WolframLanguage"], "Meaning" -> "Rules"], {"Global`listed", "Global`a", "Global`b"}]},
				{
					First[TypeOf[TypeTheoryTerm["DownValues[listed]", environment]]],
					DefinitionallyEqualQ[
						TypeTheoryTerm["DownValues[listed]"[ExpressionNormal[ExpressionAtom["Global`listed"], {ExpressionAtom["Global`a"], ExpressionAtom["Global`b"]}]], environment],
						TypeTheoryTerm[OptionSome[ExpressionNormal[ExpressionAtom["System`List"], {ExpressionAtom["Global`a"], ExpressionAtom["Global`b"]}]], environment]
					],
					DefinitionallyEqualQ[
						TypeTheoryTerm["DownValues[listed]"[ExpressionNormal[ExpressionAtom["Global`listed"], {ExpressionAtom["Global`a"]}]], environment],
						TypeTheoryTerm[Typed[OptionNone, Option[Expressions]], environment]
					]
				} === {Expressions -> Option[Expressions], True, True}
			]
		]
	],
	True,
	TestID -> "The-rules-of-a-symbol-rewrite-an-expression-and-leave-one-no-rule-matches"
]

(* the first rule that matches is the one that applies, in the order the Wolfram Language tries them *)
VerificationTest[
	Block[{first, other},
		first[x_, y_] := x;
		first[x_, ___] := other;
		If[ PacletFind["Wolfram/KernelCompiler"] === {},
			True,
			With[{environment = rulesEnvironment[TypeTheoryFormalize[first, TypeTheoryEnvironment["WolframLanguage"], "Meaning" -> "Rules"], {"Global`first", "Global`a", "Global`b"}]},
				{
					DefinitionallyEqualQ[
						TypeTheoryTerm["DownValues[first]"[ExpressionNormal[ExpressionAtom["Global`first"], {ExpressionAtom["Global`a"], ExpressionAtom["Global`b"]}]], environment],
						TypeTheoryTerm[OptionSome[ExpressionAtom["Global`a"]], environment]
					],
					DefinitionallyEqualQ[
						TypeTheoryTerm["DownValues[first]"[ExpressionNormal[ExpressionAtom["Global`first"], {ExpressionAtom["Global`a"], ExpressionAtom["Global`b"], ExpressionAtom["Global`a"]}]], environment],
						TypeTheoryTerm[OptionSome[ExpressionAtom["Global`other"]], environment]
					]
				}
			]
		]
	],
	{True, True} | True,
	SameTest -> MatchQ,
	TestID -> "The-first-rule-that-matches-applies"
]

(* heads, literals, repeated names, alternatives, exceptions and conditions translate, to tests the Wolfram Language
   computes, and check *)
VerificationTest[
	Block[{headed, listHead, literal, repeated, either, except, tested, conditioned, last},
		headed[x_Integer, y_] := x + y;
		listHead[{a_, b___}] := g[a, b];
		literal[x_, 0] := x;
		literal[x_, "s"] := -1;
		repeated[h_[x_, x_]] := h;
		either[x : (_Integer | _Real)] := x;
		except[Except[0, x_]] := x;
		tested[x_?EvenQ] := x;
		conditioned[x_] := x^2 /; x < 3;
		last[x___, y_] := y;
		If[ PacletFind["Wolfram/KernelCompiler"] === {},
			True,
			Map[
				Function[held, Replace[held, HoldComplete[symbol_] :> With[{rules = TypeTheoryFormalize[symbol, TypeTheoryEnvironment["WolframLanguage"], "Meaning" -> "Rules"]},
					ListQ[rules] && Head[TypeTheoryEnvironment[TypeTheoryEnvironment["WolframLanguage"], rules]] === TypeTheoryEnvironment
				]]],
				HoldComplete /@ Unevaluated[{headed, listHead, literal, repeated, either, except, tested, conditioned, last}]
			] === ConstantArray[True, 9]
		]
	],
	True,
	TestID -> "Heads-literals-repeated-names-alternatives-and-conditions-translate"
]

(* a pattern that needs a search, which the compiler leaves to the evaluator, and an environment without expressions
   are Failures *)
VerificationTest[
	Block[{searched},
		searched[x__, y__] := {x};
		{
			If[ PacletFind["Wolfram/KernelCompiler"] === {},
				"Untranslatable",
				First[TypeTheoryFormalize[searched, TypeTheoryEnvironment["WolframLanguage"], "Meaning" -> "Rules"]]
			],
			First[TypeTheoryFormalize[searched, TypeTheoryEnvironment["Prelude"], "Meaning" -> "Rules"]],
			First[TypeTheoryFormalize[searched, TypeTheoryEnvironment["WolframLanguage"], "Meaning" -> "Everything"]]
		}
	],
	{"Untranslatable", "RulesEnvironment", "InvalidOption"},
	TestID -> "A-search-another-environment-and-another-meaning-are-Failures"
]
