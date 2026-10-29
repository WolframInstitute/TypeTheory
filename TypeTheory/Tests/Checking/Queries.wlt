(* ::Package:: *)

(* Tests for Checking/Queries.wl: the questions about terms, environments as associations, and checking
   a whole environment again from scratch, which catches records changed by hand. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

prelude = TypeTheoryEnvironment["Prelude"]

constantReference = Symbol["WolframInstitute`TypeTheory`PackageScope`constantReference"]
boundVariable = Symbol["WolframInstitute`TypeTheory`PackageScope`boundVariable"]
naturalLiteral = Symbol["WolframInstitute`TypeTheory`PackageScope`naturalLiteral"]

(* the composite heads hold their parts, so a term written here is built from its parts computed first *)
application[parts___] := Construct[Symbol["WolframInstitute`TypeTheory`PackageScope`application"], parts]
lambdaAbstraction[parts___] := Construct[Symbol["WolframInstitute`TypeTheory`PackageScope`lambdaAbstraction"], parts]
dependentFunctionType[parts___] := Construct[Symbol["WolframInstitute`TypeTheory`PackageScope`dependentFunctionType"], parts]
localDefinition[parts___] := Construct[Symbol["WolframInstitute`TypeTheory`PackageScope`localDefinition"], parts]

natural = constantReference[HoldComplete[NonNegativeIntegers], {}]
firstProjection = lambdaAbstraction[HoldComplete[m], natural, lambdaAbstraction[HoldComplete[n], natural, boundVariable[1], "Explicit"], "Explicit"]

(* a copy of the environment's store with one record changed by hand *)
forge[TypeTheoryEnvironment[store_Symbol], name_HoldComplete, change_] := Module[{copy},
	DownValues[copy] = DownValues[store] /. store -> copy;
	copy["Records"] = MapAt[change, copy["Records"], Key[name]];
	TypeTheoryEnvironment[copy]
]


VerificationTest[
	TypeOf[TypeTheoryTerm[AndIntroduction, prelude]],
	With[{a = WolframInstitute`TypeTheory`Library`Prelude`Private`a, b = WolframInstitute`TypeTheory`Library`Prelude`Private`b},
		TypeTheoryTerm[
			ForAll[{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]]}, Implies[a, Implies[b, a && b]]],
			prelude
		]
	],
	TestID -> "A-constant-has-its-declared-type"
]

VerificationTest[
	TypeOf[TypeTheoryTerm[2 + 3], prelude],
	TypeTheoryTerm[NonNegativeIntegers, prelude],
	TestID -> "TypeOf-takes-an-environment"
]

VerificationTest[
	{
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[EqualityReflexivity[4], prelude], TypeTheoryTerm[2 + 2 == 4]], _Success],
		First @ TypeTheoryCheck[TypeTheoryTerm[EqualityReflexivity[4], prelude], TypeTheoryTerm[2 + 2 == 5]]
	},
	{True, "TypeMismatch"},
	TestID -> "TypeTheoryCheck-checks-a-term-against-a-type"
]

VerificationTest[
	First @ TypeTheoryCheck[TypeTheoryTerm[True, prelude], TypeTheoryTerm[TypeUniverse[0], Append[prelude, TypeTheoryAxiom[Extra, True]]]],
	"DifferentEnvironments",
	TestID -> "Two-terms-must-share-their-environment"
]

VerificationTest[
	DefinitionallyEqualQ[TypeTheoryTerm[True, prelude], TypeTheoryTerm[NotATerm, prelude]],
	False,
	TestID -> "DefinitionallyEqualQ-answers-False-for-a-term-that-does-not-check"
]

VerificationTest[
	Head /@ {TypeTheoryCheck[3], WeakHeadNormalForm[3], DefinitionallyEqualQ[1, 2]},
	{TypeTheoryCheck, WeakHeadNormalForm, DefinitionallyEqualQ},
	TestID -> "Arguments-that-are-not-terms-stay-unevaluated"
]


(* === environments as associations === *)

VerificationTest[
	{Length[prelude], Take[Keys[prelude], 3], KeyExistsQ[prelude, Plus], KeyExistsQ[prelude, Divide]},
	{169, {True, TrueIntroduction, InductiveRecursor[True]}, True, False},
	TestID -> "Keys-Length-and-KeyExistsQ"
]

VerificationTest[
	{prelude[NaturalNumberSuccessor] === prelude[NonNegativeIntegers], Head[prelude[Plus]], prelude[Divide]},
	{True, TypeTheoryDefinition, Missing["KeyAbsent", Divide]},
	TestID -> "Indexing-gives-the-declaration-of-a-constant"
]

VerificationTest[
	{Information[prelude, "Kinds"], Information[prelude, "Axioms"], Information[prelude, "NaturalNumbers"]},
	{
		<|"InductiveType" -> 17, "Constructor" -> 24, "Recursor" -> 17, "Definition" -> 32, "Quotient" -> 4, "Theorem" -> 72, "Axiom" -> 3|>,
		{PropositionalExtensionality, QuotientSoundness, Choice},
		<|"Type" -> NonNegativeIntegers, "Zero" -> NaturalNumberZero, "Successor" -> NaturalNumberSuccessor, "Operations" -> <|"Addition" -> Plus, "Subtraction" -> Subtract, "Multiplication" -> Times, "Power" -> Power, "Equal" -> "equal", "LessEqual" -> "lessEqual"|>|>
	},
	TestID -> "Information-about-an-environment"
]

VerificationTest[
	With[{rebuilt = TypeTheoryEnvironment[TypeTheoryEnvironment[], Normal[prelude]]}, {Keys[rebuilt] === Keys[prelude], MatchQ[TypeTheoryCheck[rebuilt], _Success]}],
	{True, True},
	TestID -> "Normal-gives-the-declarations-to-rebuild-an-environment-from"
]


(* === checking an environment === *)

VerificationTest[
	MatchQ[TypeTheoryCheck[prelude], _Success],
	True,
	TestID -> "The-prelude-checks-from-scratch"
]

VerificationTest[
	First @ TypeTheoryCheck[forge[prelude, HoldComplete[FalseElimination], Function[record, Append[record, "Type" -> constantReference[HoldComplete[False], {}]]]]],
	"TypeMismatch",
	TestID -> "A-forged-theorem-statement-is-caught"
]

VerificationTest[
	First @ TypeTheoryCheck[forge[prelude, HoldComplete[InductiveRecursor[Or]], Function[record, Append[record, "EliminationUniverse" -> True]]]],
	"DeclarationMismatch",
	TestID -> "A-forged-recursor-is-caught"
]

(* addition forged as the first projection, with the height of that value: well typed, and trusted on
   literals, so a theorem about it catches it *)
VerificationTest[
	First @ TypeTheoryCheck[forge[prelude, HoldComplete[Plus], Function[record, Append[record, {"Value" -> firstProjection, "Height" -> 1}]]]],
	"TypeMismatch",
	TestID -> "A-forged-addition-is-caught"
]

(* the abbreviation hint is the kernel's to give, to projection functions: one forged on addition, which projects
   nothing, does not come out of checking its declaration again *)
VerificationTest[
	First @ TypeTheoryCheck[forge[prelude, HoldComplete[Plus], Function[record, Append[record, "Hint" -> "Abbreviation"]]]],
	"DeclarationMismatch",
	TestID -> "A-forged-abbreviation-hint-is-caught"
]

(* An application's arguments are checked along its spine, each against its binder's domain with the arguments
   before it put in: EqualitySymmetry with x = 1 and y = 2 needs a proof of 1 == 2, and gets one of 1 == 1. A
   spine with more arguments than its function's type has binders, even after reducing it, applies a value that
   is no function. *)
VerificationTest[
	{
		First @ TypeTheoryCheck[forge[prelude, HoldComplete[AdditionZeroLeft], Function[record, Append[record, "Value" -> Fold[application, constantReference[HoldComplete[EqualitySymmetry], {1}], {
			natural,
			naturalLiteral[1],
			naturalLiteral[2],
			application[application[constantReference[HoldComplete[EqualityReflexivity], {1}], natural], naturalLiteral[1]]
		}]]]]],
		First @ TypeTheoryCheck[forge[prelude, HoldComplete[AdditionZeroLeft], Function[record, Append[record, "Value" -> Fold[application, constantReference[HoldComplete[NaturalNumberSuccessor], {}], {naturalLiteral[1], naturalLiteral[2]}]]]]]
	},
	{"TypeMismatch", "FunctionExpected"},
	TestID -> "A-forged-argument-is-caught-against-the-domain-its-earlier-arguments-give"
]

(* Inside a check, proof irrelevance compares two proofs by propositions inferred without checking the proofs, as
   in Lean's kernel. h of ForAll[{Typed[m, NonNegativeIntegers]}, True] applied to a proof is ill typed, yet
   inferred so it is a proof of True, which irrelevance finds equal to h[0]. Each forged proof of AdditionZeroLeft
   below is its own proof under a redex that binds such an h and reaches h[TrueIntroduction] only through that
   comparison: as an argument, as a function's domain, and as a local definition's value. The statement is kept,
   so no later declaration fails in its place, and the theorem's own check catches each one. *)
VerificationTest[
	With[
		{
			true = constantReference[HoldComplete[True], {}],
			trivial = constantReference[HoldComplete[TrueIntroduction], {}],
			equal = Function[{x, y}, Fold[application, constantReference[HoldComplete[Equal], {0}], {constantReference[HoldComplete[True], {}], x, y}]],
			reflexivity = Function[x, Fold[application, constantReference[HoldComplete[EqualityReflexivity], {0}], {constantReference[HoldComplete[True], {}], x}]],
			family = dependentFunctionType[HoldComplete[m], natural, constantReference[HoldComplete[True], {}], "Explicit"]
		},
		(* Function[{Typed[n, NonNegativeIntegers]}, Function[{Typed[h, family]}, inner][Function[{Typed[m, NonNegativeIntegers]}, TrueIntroduction]] *)
		With[
			{
				forgedProof = Function[inner, Function[record, Append[record, "Value" -> lambdaAbstraction[HoldComplete[n], natural, application[
					lambdaAbstraction[HoldComplete[h], family, inner[record["Value"]], "Explicit"],
					lambdaAbstraction[HoldComplete[m], natural, trivial, "Explicit"]
				], "Explicit"]]]]
			},
			First @ TypeTheoryCheck[forge[prelude, HoldComplete[AdditionZeroLeft], forgedProof[#]]]& /@ {
				Function[proof, application[
					lambdaAbstraction[HoldComplete[e], equal[application[boundVariable[0], naturalLiteral[0]], application[boundVariable[0], naturalLiteral[0]]], application[proof, boundVariable[2]], "Explicit"],
					reflexivity[application[boundVariable[0], trivial]]
				]],
				Function[proof, application[
					lambdaAbstraction[HoldComplete[e], equal[application[boundVariable[0], trivial], application[boundVariable[0], naturalLiteral[0]]], application[proof, boundVariable[2]], "Explicit"],
					reflexivity[application[boundVariable[0], naturalLiteral[0]]]
				]],
				Function[proof, localDefinition[HoldComplete[y], true, application[boundVariable[0], trivial], application[
					lambdaAbstraction[HoldComplete[e], equal[boundVariable[0], application[boundVariable[1], naturalLiteral[0]]], application[proof, boundVariable[3]], "Explicit"],
					reflexivity[application[boundVariable[1], naturalLiteral[0]]]
				]]]
			}
		]
	],
	{"TypeMismatch", "TypeMismatch", "TypeMismatch"},
	TestID -> "An-ill-typed-proof-reached-only-through-proof-irrelevance-is-caught-by-its-declaration"
]

(* an opaque definition never unfolds, but its value is checked as a definition's *)
VerificationTest[
	With[
		{
			secret = TypeTheoryEnvironment[TypeTheoryEnvironment[], {
				TypeTheoryInductiveType[Truth, TypeUniverse[1], {Yes -> Truth, No -> Truth}],
				TypeTheoryDefinition[Secret, Typed[Yes, Truth], "Opaque" -> True]
			}]
		},
		{
			Normal[secret][[-1]],
			MatchQ[TypeTheoryCheck[TypeTheoryEnvironment[TypeTheoryEnvironment[], Normal[secret]]], _Success],
			First @ TypeTheoryCheck[forge[secret, HoldComplete[Secret], Function[record, Append[record, "Value" -> constantReference[HoldComplete[Truth], {}]]]]]
		}
	],
	{TypeTheoryDefinition[Secret, Typed[Yes, Truth], "Opaque" -> True], True, "TypeMismatch"},
	TestID -> "An-opaque-definition-comes-back-from-Normal-and-a-forged-value-is-caught"
]

(* the height of a definition decides which of two unfolds first; checking the environment again gives it again *)
VerificationTest[
	With[
		{
			flips = TypeTheoryEnvironment[TypeTheoryEnvironment[], {
				TypeTheoryInductiveType[Truth, TypeUniverse[1], {Yes -> Truth, No -> Truth}],
				TypeTheoryDefinition[Flip, Function[{Typed[t, Truth]}, InductiveRecursor[Truth][Function[{Typed[s, Truth]}, Truth], No, Yes, t]]],
				TypeTheoryDefinition[FlipTwice, Function[{Typed[t, Truth]}, Flip[Flip[t]]]]
			}]
		},
		{
			First[flips]["Records"][HoldComplete[Flip]]["Height"],
			First[flips]["Records"][HoldComplete[FlipTwice]]["Height"],
			First @ TypeTheoryCheck[forge[flips, HoldComplete[FlipTwice], Function[record, Append[record, "Height" -> 1]]]]
		}
	],
	{1, 2, "DeclarationMismatch"},
	TestID -> "A-definition-is-higher-than-those-it-is-defined-by-and-a-forged-height-is-caught"
]

VerificationTest[
	{
		TypeTheoryAxiomClosure[TypeTheoryTerm[ExcludedMiddle]],
		TypeTheoryAxiomClosure[TypeTheoryTerm[EqualitySymmetry]],
		TypeTheoryAxiomClosure[TypeTheoryTerm[True]]
	},
	{<|Choice -> "Signature", QuotientSoundness -> "Proposition", PropositionalExtensionality -> "Proposition"|>, <||>, <||>},
	TestID -> "The-axiom-closure-of-excluded-middle-is-Lean's-three-axioms"
]

VerificationTest[
	With[{signed = TypeTheoryEnvironment[{TypeTheoryAxiom[Origin, Naturals], TypeTheoryAxiom[OriginPositive, 0 < Origin]}]},
		{
			TypeTheoryAxiomClosure[TypeTheoryTerm[Origin + 1, signed]],
			TypeTheoryAxiomClosure[TypeTheoryTerm[OriginPositive, signed]],
			Information[TypeTheoryTerm[OriginPositive, signed], "AxiomClosure"] === TypeTheoryAxiomClosure[TypeTheoryTerm[OriginPositive, signed]],
			Information[TypeTheoryTerm[2 + Origin, signed], "Constants"]
		}
	],
	{<|Origin -> "Signature"|>, <|OriginPositive -> "Proposition", Origin -> "Signature"|>, True, {Plus, Origin, NonNegativeIntegers}},
	TestID -> "An-axiom-of-a-type-is-a-signature-and-an-axiom-of-a-proposition-a-proposition"
]

VerificationTest[
	With[{closure = TypeTheoryAxiomClosure[TypeTheoryTerm[CircleInduction, TypeTheoryEnvironment["HomotopyTypeTheory"]]]},
		{closure[CircleInductionBase], closure[CircleInduction]}
	],
	{"RewriteRule", "Signature"},
	TestID -> "The-axiom-closure-lists-the-rewrite-rules-of-a-constant-reached"
]

VerificationTest[
	With[{rationals = TypeTheoryEnvironment["Rationals"]},
		Union @@ Map[Function[name, Keys[TypeTheoryAxiomClosure[TypeTheoryTerm[name, rationals]]]], Keys[rationals]]
	],
	{Choice, PropositionalExtensionality, QuotientSoundness},
	TestID -> "Every-constant-of-the-rationals-rests-on-Lean's-three-axioms-at-most"
]

VerificationTest[
	{
		Information[TypeTheoryTerm[TwoPlusTwo, TypeTheoryEnvironment[{TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, EqualityReflexivity[4]]}]], "Constants"],
		Information[TypeTheoryTerm[ForAll[{Typed[n, Naturals]}, n + 0 == n]], "Constants"]
	},
	{{Equal, NonNegativeIntegers, Plus, EqualityReflexivity}, {NonNegativeIntegers, Equal, Plus}},
	TestID -> "The-constants-of-a-constant-are-those-of-its-type-and-value"
]
