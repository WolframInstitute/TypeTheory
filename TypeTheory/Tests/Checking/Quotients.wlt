(* ::Package:: *)

(* Tests for Checking/Quotients.wl: the quotient types of Lean's kernel, which the prelude declares with
   TypeTheoryQuotients[]; their lift and induction compute on a class, a lift needs its proof, the rules
   and the equality they need are checked, and a forged quotient record is caught. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

prelude = TypeTheoryEnvironment["Prelude"]

(* every two natural numbers related *)
related = TypeTheoryTerm[Typed[Function[{Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]}, True], TypeSpecifier[{NonNegativeIntegers, NonNegativeIntegers} -> TypeUniverse[0]]]]

(* a copy of the environment's store with one record changed by hand *)
forge[TypeTheoryEnvironment[store_Symbol], name_HoldComplete, change_] := Module[{copy},
	DownValues[copy] = DownValues[store] /. store -> copy;
	copy["Records"] = MapAt[change, copy["Records"], Key[name]];
	TypeTheoryEnvironment[copy]
]


VerificationTest[
	{
		Information[prelude, "Kinds"]["Quotient"],
		Count[Normal[prelude], TypeTheoryQuotients[]],
		Information[prelude, "Axioms"],
		MatchQ[prelude[FunctionExtensionality], TypeTheoryTheorem[__]]
	},
	{4, 1, {PropositionalExtensionality, QuotientSoundness, Choice}, True},
	TestID -> "The-prelude-has-Lean's-quotients-and-axioms"
]

VerificationTest[
	{
		WeakHeadNormalForm[TypeTheoryTerm[
			QuotientLift[Function[{Typed[k, NonNegativeIntegers]}, 7], Function[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[e, related[a, b]]}, EqualityReflexivity[7]], QuotientIntroduction[related, 5]]
		]],
		WeakHeadNormalForm[TypeTheoryTerm[Construct[
			QuotientInduction,
			NonNegativeIntegers,
			related,
			Function[{Typed[q, QuotientType[related]]}, True],
			Function[{Typed[a, NonNegativeIntegers]}, TrueIntroduction],
			QuotientIntroduction[related, 5]
		]]]
	},
	{TypeTheoryTerm[7, prelude], TypeTheoryTerm[TrueIntroduction, prelude]},
	TestID -> "A-lift-and-an-induction-compute-on-a-class"
]

VerificationTest[
	First @ TypeTheoryCheck[TypeTheoryTerm[
		QuotientLift[Function[{Typed[k, NonNegativeIntegers]}, k], Function[{Typed[a, NonNegativeIntegers], Typed[b, NonNegativeIntegers], Typed[e, related[a, b]]}, EqualityReflexivity[a]], QuotientIntroduction[related, 5]]
	]],
	"TypeMismatch",
	TestID -> "A-lift-needs-a-proof-that-its-function-respects-the-relation"
]

VerificationTest[
	First /@ {
		TypeTheoryEnvironment[TypeTheoryEnvironment[TypeTheoryRules["CalculusOfInductiveConstructions", "Quotients" -> False]], {TypeTheoryQuotients[]}],
		TypeTheoryEnvironment[TypeTheoryEnvironment[TypeTheoryRules["MartinLofTypeTheory", "Quotients" -> True]], {TypeTheoryQuotients[]}],
		TypeTheoryEnvironment[TypeTheoryEnvironment[], {TypeTheoryQuotients[]}],
		TypeTheoryEnvironment[prelude, {TypeTheoryQuotients[]}]
	},
	{"QuotientsNotAllowed", "QuotientsNotAllowed", "EqualityExpected", "AlreadyDeclared"},
	TestID -> "Quotients-need-rules-that-have-them-and-the-equality"
]

(* an Equal whose one constructor proves any equation would let a lift identify anything *)
VerificationTest[
	First @ TypeTheoryEnvironment[TypeTheoryEnvironment[], {
		TypeTheoryInductiveType[Equal, ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u]], Typed[x, \[Alpha]], Typed[y, \[Alpha]]}, TypeUniverse[0]], {
			AnyEquation -> ForAll[{TypedImplicit[\[Alpha], TypeUniverse[u]], Typed[x, \[Alpha]], Typed[y, \[Alpha]]}, Equal[x, y]]
		}],
		TypeTheoryQuotients[]
	}],
	"EqualityExpected",
	TestID -> "Quotients-refuse-an-equality-that-is-not-the-prelude's"
]

(* the lift forged without the hypothesis, and with the introduction it computes on changed *)
VerificationTest[
	{
		With[{introductionType = First[prelude]["Records"][HoldComplete[QuotientIntroduction]]["Type"]},
			First @ TypeTheoryCheck[forge[prelude, HoldComplete[QuotientLift], Function[record, Append[record, "Type" -> introductionType]]]]
		],
		First @ TypeTheoryCheck[forge[prelude, HoldComplete[QuotientLift], Function[record, Append[record, "Introduction" -> HoldComplete[NaturalNumberSuccessor]]]]]
	},
	{"DeclarationMismatch", "DeclarationMismatch"},
	TestID -> "A-forged-quotient-is-caught"
]

(* Lean's own names, with Lean's Eq, as LeanLink declares them *)
VerificationTest[
	With[
		{
			lean = TypeTheoryEnvironment[TypeTheoryEnvironment[], {
				TypeTheoryInductiveType["Eq", ForAll[{TypedImplicit["α", TypeUniverse["u"]], Typed["a", "α"], Typed["b", "α"]}, TypeUniverse[0]], {
					"Eq.refl" -> ForAll[{TypedImplicit["α", TypeUniverse["u"]], Typed["a", "α"]}, Construct["Eq", "α", "a", "a"]]
				}, "Parameters" -> 2],
				TypeTheoryQuotients["Eq", {"Quot", "Quot.mk", "Quot.lift", "Quot.ind"}]
			}]
		},
		{
			Keys[lean],
			Last[Normal[lean]],
			MatchQ[TypeTheoryCheck[lean], _Success]
		}
	],
	{{"Eq", "Eq.refl", InductiveRecursor["Eq"], "Quot", "Quot.mk", "Quot.lift", "Quot.ind"}, TypeTheoryQuotients["Eq", {"Quot", "Quot.mk", "Quot.lift", "Quot.ind"}], True},
	TestID -> "Quotients-under-other-names-with-another-equality"
]
