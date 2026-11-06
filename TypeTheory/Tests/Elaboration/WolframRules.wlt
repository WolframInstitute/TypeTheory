(* ::Package:: *)

(* Tests for Elaboration/WolframRules.wl: the rules of a symbol as a definition of type Expressions -> Option[Expressions]
   in the prelude, translated from their patterns. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

(* the rules of a symbol, in the environment of expressions; atoms are data, so nothing else is declared *)
rulesEnvironment[rules_List] := TypeTheoryEnvironment[rules]

(* the rules compute in the kernel: f[x_, y_, z___] rewrites f[a, b] to {a, b}, by the lengths, the parts, the sequence
   and the heads it compares, and leaves f[a] as it is *)
VerificationTest[
	Block[{listed},
		listed[x_, y_, z___] := {x, y, z};
		With[{environment = rulesEnvironment[TypeTheoryFormalize[listed, "Meaning" -> "Rules"]]},
			{
				TypeTheoryType["DownValues[listed]", environment],
				DefinitionallyEqualQ[TypeTheoryTerm["DownValues[listed]"[Unevaluated[listed[a, b]]], environment], TypeTheoryTerm["some"[Unevaluated[{a, b}]], environment]],
				DefinitionallyEqualQ[TypeTheoryTerm["DownValues[listed]"[Unevaluated[listed[a]]], environment], TypeTheoryTerm[Typed["none", Option[Expressions]], environment]]
			}
		]
	],
	{TypeTheoryTerm[Expressions -> Option[Expressions], _], True, True},
	SameTest -> MatchQ,
	TestID -> "The-rules-of-a-symbol-rewrite-an-expression-and-leave-one-no-rule-matches"
]

(* the first rule that matches is the one that applies, in the order the Wolfram Language tries them *)
VerificationTest[
	Block[{first, other},
		first[x_, y_] := x;
		first[x_, ___] := other;
		With[{environment = rulesEnvironment[TypeTheoryFormalize[first, "Meaning" -> "Rules"]]},
			{
				DefinitionallyEqualQ[TypeTheoryTerm["DownValues[first]"[Unevaluated[first[a, b]]], environment], TypeTheoryTerm[Typed["some"[a], Option[Expressions]], environment]],
				DefinitionallyEqualQ[TypeTheoryTerm["DownValues[first]"[Unevaluated[first[a, b, a]]], environment], TypeTheoryTerm[Typed["some"[other], Option[Expressions]], environment]]
			}
		]
	],
	{True, True},
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
				Function[held, Replace[held, HoldComplete[symbol_] :> With[{rules = TypeTheoryFormalize[symbol, "Meaning" -> "Rules"]},
					ListQ[rules] && Head[TypeTheoryEnvironment[rules]] === TypeTheoryEnvironment
				]]],
				HoldComplete /@ Unevaluated[{headed, listHead, literal, repeated, either, except, tested, conditioned, last}]
			] === ConstantArray[True, 9]
		]
	],
	True,
	TestID -> "Heads-literals-repeated-names-alternatives-and-conditions-translate"
]

(* a pattern inside an association, an atom, an environment without matches, as the constructive one, and another meaning
   are Failures; a search translates *)
VerificationTest[
	Block[{searched, keyed},
		searched[x__, y__] := {x};
		keyed[KeyValuePattern["a" -> x_]] := x;
		{
			MatchQ[TypeTheoryFormalize[searched, "Meaning" -> "Rules"], {___, _TypeTheoryDefinition}],
			First[TypeTheoryFormalize[keyed, "Meaning" -> "Rules"]],
			First[TypeTheoryFormalize[searched, TypeTheoryEnvironment["Constructive"], "Meaning" -> "Rules"]],
			First[TypeTheoryFormalize[searched, "Meaning" -> "Everything"]]
		}
	],
	{True, "Untranslatable", "RulesEnvironment", "InvalidOption"},
	TestID -> "A-search-translates-and-an-association-another-environment-and-another-meaning-are-Failures"
]

(* the declarations TypeTheoryFormalize gives show in the environment they were made for: the constants of matches and
   Expressions are bold, with their types on mouseover *)
VerificationTest[
	Block[{listed, WolframInstitute`TypeTheory`PackageScope`$displayTooltips = True},
		listed[x_, y_] := {y, x};
		With[{boxes = ToBoxes[Last[TypeTheoryFormalize[listed, "Meaning" -> "Rules"]]]},
			{
				MemberQ[Cases[boxes, StyleBox[name_String, ___, Bold, ___] :> name, Infinity], "MatchFirst"],
				! FreeQ[boxes, TooltipBox[StyleBox["Expressions", ___], _]]
			}
		]
	],
	{True, True},
	TestID -> "Formalized-declarations-show-in-their-environment"
]
