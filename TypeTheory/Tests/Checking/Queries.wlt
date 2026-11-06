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
	TypeTheoryType[TypeTheoryTerm["andIntroduction", prelude]],
	With[{a = WolframInstitute`TypeTheory`Library`Prelude`Private`a, b = WolframInstitute`TypeTheory`Library`Prelude`Private`b},
		TypeTheoryTerm[
			ForAll[{TypedImplicit[a, TypeUniverse[0]], TypedImplicit[b, TypeUniverse[0]]}, Implies[a, Implies[b, a && b]]],
			prelude
		]
	],
	TestID -> "A-constant-has-its-declared-type"
]

VerificationTest[
	TypeTheoryType[TypeTheoryTerm[2 + 3], prelude],
	TypeTheoryTerm[NonNegativeIntegers, prelude],
	TestID -> "TypeTheoryType-takes-an-environment"
]

VerificationTest[
	PacletSymbol["WolframInstitute/TypeTheory", "TypeTheoryType"][
		PacletSymbol["WolframInstitute/TypeTheory", "TypeTheoryTerm"][PacletSymbol["WolframInstitute/TypeTheory", "NaturalNumberPredecessor"][3], prelude]],
	TypeTheoryTerm[NonNegativeIntegers, prelude],
	TestID -> "TypeTheoryType-takes-a-term-written-with-PacletSymbol"
]

VerificationTest[
	With[{sum = TypeTheoryTerm[2 + 3, prelude]}, TypeTheoryType[sum]],
	TypeTheoryTerm[NonNegativeIntegers, prelude],
	TestID -> "TypeTheoryType-takes-a-term-in-a-variable"
]

VerificationTest[
	FailureQ[TypeTheoryType[TypeTheoryTerm[1 + True, prelude]]],
	True,
	TestID -> "TypeTheoryType-of-an-ill-typed-term-is-a-Failure"
]

(* TypeTheoryType holds its argument: an expression is a term without a TypeTheoryTerm around it *)
VerificationTest[
	Block[{$TypeTheoryEnvironment = prelude},
		{
			TypeTheoryType[2 + 3],
			TypeTheoryType[2 + 3, prelude],
			TypeTheoryType[ForAll[{Typed[n, NonNegativeIntegers]}, n + 0 == n]],
			Module[{sum = TypeTheoryTerm[2 + 3, prelude]}, TypeTheoryType[sum]],
			With[{terms = {TypeTheoryTerm[1 + 1 == 2, prelude]}}, TypeTheoryType[Evaluate[First[terms]]]],
			TypeTheoryCheck[TypeTheoryTerm[2 + 3, prelude]]
		}
	],
	{
		TypeTheoryTerm[NonNegativeIntegers, prelude], TypeTheoryTerm[NonNegativeIntegers, prelude], TypeTheoryTerm[TypeUniverse[0], prelude],
		TypeTheoryTerm[NonNegativeIntegers, prelude], TypeTheoryTerm[TypeUniverse[0], prelude], TypeTheoryTerm[NonNegativeIntegers, prelude]
	},
	TestID -> "TypeTheoryType-takes-an-expression-held-and-TypeTheoryCheck-of-a-term-calls-it"
]

VerificationTest[
	With[{wolfram = TypeTheoryEnvironment["Prelude"]}, TypeTheoryType[Sequence[1, Typed[2, Expressions]], wolfram] === TypeTheoryTerm[Sequence[NonNegativeIntegers, Expressions], wolfram]],
	True,
	TestID -> "TypeTheoryType-holds-a-sequence-whole"
]

VerificationTest[
	{
		MatchQ[TypeTheoryCheck[TypeTheoryTerm["equalityReflexivity"[4], prelude], TypeTheoryTerm[2 + 2 == 4]], _Success],
		First @ TypeTheoryCheck[TypeTheoryTerm["equalityReflexivity"[4], prelude], TypeTheoryTerm[2 + 2 == 5]]
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
	{257, {True, "trueIntroduction", InductiveRecursor[True]}, True, False},
	TestID -> "Keys-Length-and-KeyExistsQ"
]

VerificationTest[
	{prelude["successor"] === prelude[NonNegativeIntegers], Head[prelude[Plus]], prelude[Divide]},
	{True, TypeTheoryDefinition, Missing["KeyAbsent", Divide]},
	TestID -> "Indexing-gives-the-declaration-of-a-constant"
]

VerificationTest[
	{Information[prelude, "Kinds"], Information[prelude, "Axioms"], Information[prelude, "NaturalNumbers"]},
	{
		<|"InductiveType" -> 27, "Constructor" -> 41, "Recursor" -> 28, "Definition" -> 81, "Quotient" -> 4, "Theorem" -> 72, "Axiom" -> 4|>,
		{"propositionalExtensionality", "quotientSoundness", "choice", ExpressionEvaluate},
		<|"Type" -> NonNegativeIntegers, "Zero" -> "zero", "Successor" -> "successor", "Operations" -> <|"Addition" -> Plus, "Subtraction" -> Subtract, "Multiplication" -> Times, "Power" -> Power, "Equal" -> "equal", "LessEqual" -> "lessEqual"|>|>
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
	First @ TypeTheoryCheck[forge[prelude, HoldComplete["falseElimination"], Function[record, Append[record, "Type" -> constantReference[HoldComplete[False], {}]]]]],
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
	"InvalidNaturalNumberOperation",
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
   before it put in: "equalitySymmetry" with x = 1 and y = 2 needs a proof of 1 == 2, and gets one of 1 == 1. A
   spine with more arguments than its function's type has binders, even after reducing it, applies a value that
   is no function. *)
VerificationTest[
	{
		First @ TypeTheoryCheck[forge[prelude, HoldComplete["additionZeroLeft"], Function[record, Append[record, "Value" -> Fold[application, constantReference[HoldComplete["equalitySymmetry"], {1}], {
			natural,
			naturalLiteral[1],
			naturalLiteral[2],
			application[application[constantReference[HoldComplete["equalityReflexivity"], {1}], natural], naturalLiteral[1]]
		}]]]]],
		First @ TypeTheoryCheck[forge[prelude, HoldComplete["additionZeroLeft"], Function[record, Append[record, "Value" -> Fold[application, constantReference[HoldComplete["successor"], {}], {naturalLiteral[1], naturalLiteral[2]}]]]]]
	},
	{"TypeMismatch", "FunctionExpected"},
	TestID -> "A-forged-argument-is-caught-against-the-domain-its-earlier-arguments-give"
]

(* a binder whose domain is no type, as zero, which elaboration refuses before the kernel sees it, is refused by the
   kernel itself in a forged record: in the value, a function of an argument in zero, and in the type, a product over
   zero *)
VerificationTest[
	With[{zero = constantReference[HoldComplete["zero"], {}]},
		{
			First @ TypeTheoryCheck[forge[prelude, HoldComplete[Plus], Function[record, Append[record, {
				"Value" -> lambdaAbstraction[HoldComplete[m], natural, lambdaAbstraction[HoldComplete[n], natural, application[lambdaAbstraction[HoldComplete[x], zero, zero, "Explicit"], zero], "Explicit"], "Explicit"],
				"Height" -> 1
			}]]]],
			First @ TypeTheoryCheck[forge[prelude, HoldComplete[Plus], Function[record, Append[record, {
				"Type" -> dependentFunctionType[HoldComplete[m], zero, dependentFunctionType[HoldComplete[n], natural, natural, "Explicit"], "Explicit"]
			}]]]]
		}
	],
	{"TypeExpected", "TypeExpected"},
	TestID -> "A-forged-binder-whose-domain-is-no-type-is-caught"
]

(* Inside a check, proof irrelevance compares two proofs by propositions inferred without checking the proofs, as
   in Lean's kernel. h of ForAll[{Typed[m, NonNegativeIntegers]}, True] applied to a proof is ill typed, yet
   inferred so it is a proof of True, which irrelevance finds equal to h[0]. Each forged proof of "additionZeroLeft"
   below is its own proof under a redex that binds such an h and reaches h["trueIntroduction"] only through that
   comparison: as an argument, as a function's domain, and as a local definition's value. The statement is kept,
   so no later declaration fails in its place, and the theorem's own check catches each one. *)
VerificationTest[
	With[
		{
			true = constantReference[HoldComplete[True], {}],
			trivial = constantReference[HoldComplete["trueIntroduction"], {}],
			equal = Function[{x, y}, Fold[application, constantReference[HoldComplete[Equal], {0}], {constantReference[HoldComplete[True], {}], x, y}]],
			reflexivity = Function[x, Fold[application, constantReference[HoldComplete["equalityReflexivity"], {0}], {constantReference[HoldComplete[True], {}], x}]],
			family = dependentFunctionType[HoldComplete[m], natural, constantReference[HoldComplete[True], {}], "Explicit"]
		},
		(* Function[{Typed[n, NonNegativeIntegers]}, Function[{Typed[h, family]}, inner][Function[{Typed[m, NonNegativeIntegers]}, "trueIntroduction"]] *)
		With[
			{
				forgedProof = Function[inner, Function[record, Append[record, "Value" -> lambdaAbstraction[HoldComplete[n], natural, application[
					lambdaAbstraction[HoldComplete[h], family, inner[record["Value"]], "Explicit"],
					lambdaAbstraction[HoldComplete[m], natural, trivial, "Explicit"]
				], "Explicit"]]]]
			},
			First @ TypeTheoryCheck[forge[prelude, HoldComplete["additionZeroLeft"], forgedProof[#]]]& /@ {
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
		TypeTheoryAxiomClosure[TypeTheoryTerm["excludedMiddle"]],
		TypeTheoryAxiomClosure[TypeTheoryTerm["equalitySymmetry"]],
		TypeTheoryAxiomClosure[TypeTheoryTerm[True]]
	},
	{<|"choice" -> "Signature", "quotientSoundness" -> "Proposition", "propositionalExtensionality" -> "Proposition"|>, <||>, <||>},
	TestID -> "The-axiom-closure-of-excluded-middle-is-Lean's-three-axioms"
]

(* a proof's term reads back without the implicit arguments elaboration can find from its statement, and not without it:
   the closure of the proof itself is of its own core term *)
VerificationTest[
	With[{decided = TypeTheoryProof[2 + 2 == 4, {TypeTheoryTactic["Decide"]}]},
		{TypeTheoryAxiomClosure[decided], FailureQ[TypeTheoryAxiomClosure[decided["Term"]]], First @ TypeTheoryAxiomClosure[TypeTheoryProof[2 + 2 == 4]]}
	],
	{<||>, True, "ProofIncomplete"},
	TestID -> "The-axiom-closure-of-a-finished-proof-is-of-its-own-term"
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
	With[{closure = TypeTheoryAxiomClosure[TypeTheoryTerm["circleInduction", TypeTheoryEnvironment["HomotopyTypeTheory"]]]},
		{closure["circleInductionBase"], closure["circleInduction"]}
	],
	{"RewriteRule", "Signature"},
	TestID -> "The-axiom-closure-lists-the-rewrite-rules-of-a-constant-reached"
]

VerificationTest[
	With[{rationals = TypeTheoryEnvironment["Rationals"]},
		Union @@ Map[Function[name, Keys[TypeTheoryAxiomClosure[TypeTheoryTerm[name, rationals]]]], Keys[rationals]]
	],
	{"choice", "propositionalExtensionality", "quotientSoundness", ExpressionEvaluate},
	TestID -> "Every-constant-of-the-rationals-rests-on-Lean's-three-axioms-at-most"
]

VerificationTest[
	{
		Information[TypeTheoryTerm[TwoPlusTwo, TypeTheoryEnvironment[{TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, "equalityReflexivity"[4]]}]], "Constants"],
		Information[TypeTheoryTerm[ForAll[{Typed[n, Naturals]}, n + 0 == n]], "Constants"]
	},
	{{Equal, NonNegativeIntegers, Plus, "equalityReflexivity"}, {NonNegativeIntegers, Equal, Plus}},
	TestID -> "The-constants-of-a-constant-are-those-of-its-type-and-value"
]

(* the natural-deduction derivation of a proof of propositional logic: the functions of its propositions bind the atoms, a
   constant applied to them, as "excludedMiddle"[a], is an open assumption, and a proof of anything else is untranslatable *)
rules[tree_] := Cases[tree, TypeTheoryProofTree[rule_String, __] :> rule, {0, Infinity}]

VerificationTest[
	With[
		{
			k = TypeTheoryProofTree[TypeTheoryTerm[Function[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]], Typed[x, a], Typed[y, b]}, x], prelude]],
			swap = Information[TypeTheoryTerm[Function[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]], Typed[h, And[a, b]]}, "andIntroduction"["andEliminationRight"[h], "andEliminationLeft"[h]]], prelude], "ProofTree"]
		},
		{
			k[[1]], k[[2]] === TypeTheoryTerm[Implies[a, Implies[b, a]], prelude], rules[k],
			swap[[1]], swap[[2]] === TypeTheoryTerm[Implies[And[a, b], And[b, a]], prelude], rules[swap]
		}
	],
	{
		"ImpliesIntro", True, {"Assumption", "ImpliesIntro", "ImpliesIntro"},
		"ImpliesIntro", True, {"Assumption", "AndElim", "Assumption", "AndElim", "AndIntro", "ImpliesIntro"}
	},
	TestID -> "A-proof-of-propositional-logic-gives-its-natural-deduction-tree"
]

VerificationTest[
	With[
		{
			peirce = Information[
				TypeTheoryTerm[
					Function[{Typed[a, TypeUniverse[0]], Typed[b, TypeUniverse[0]], Typed[f, Implies[Implies[a, b], a]]},
						InductiveRecursor[Or][
							Function[{Typed[t, Or[a, Not[a]]]}, a],
							Function[{Typed[x, a]}, x],
							Function[{Typed[n, Not[a]]}, f[Function[{Typed[y, a]}, "falseElimination"[n[y]]]]],
							"excludedMiddle"[a]
						]
					],
					prelude
				],
				"ProofTree"
			]
		},
		{
			rules[peirce],
			MemberQ[Cases[peirce, TypeTheoryProofTree["Assumption", claim_, {}] :> claim, {0, Infinity}], TypeTheoryTerm[Or[a, Not[a]], prelude]],
			MatchQ[ToBoxes[peirce], InterpretationBox[_, _TypeTheoryProofTree]] && ! FreeQ[First[ToBoxes[peirce]], FractionBox] && ! FreeQ[First[ToBoxes[peirce]], StyleBox["\[Or]E", ___]]
		}
	],
	{
		{"Assumption", "Assumption", "Assumption", "Assumption", "Assumption", "ImpliesElim", "FalseElim", "ImpliesIntro", "ImpliesElim", "OrElim", "ImpliesIntro"},
		True,
		True
	},
	TestID -> "Peirce's-law-by-excluded-middle-has-an-open-assumption-and-shows-drawn"
]

VerificationTest[
	{
		Information[TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]}, n], prelude], "ProofTree"],
		Information[TypeTheoryTerm["equalityReflexivity"[2], prelude], "ProofTree"],
		MemberQ[Information[TypeTheoryTerm[2, prelude], "Properties"], "ProofTree"]
	},
	{Missing["Untranslatable"], Missing["Untranslatable"], True},
	TestID -> "A-proof-beyond-propositional-logic-has-no-proof-tree"
]

(* an environment's theorems by name, each with its statement: the prelude's are named by strings, and a library adds
   its own *)
VerificationTest[
	With[{theorems = Information[TypeTheoryEnvironment["Prelude"], "Theorems"], integers = Information[TypeTheoryEnvironment["Integers"], "Theorems"]},
		{
			AllTrue[Keys[theorems], StringQ],
			Head[theorems["additionCommutativity"]],
			MatchQ[theorems["additionCommutativity"], TypeTheoryTerm[_ForAll, _]],
			MemberQ[Keys[KeyDrop[integers, Keys[theorems]]], "integerDistributivity"],
			MemberQ[Information[TypeTheoryEnvironment["Prelude"], "Properties"], "Theorems"]
		}
	],
	{True, TypeTheoryTerm, True, True, True},
	TestID -> "An-environment-lists-its-theorems-with-their-statements"
]

(* NormalForm reduces every part of a term, under binders too, where WeakHeadNormalForm stops at the head *)
VerificationTest[
	{
		MatchQ[NormalForm[TypeTheoryTerm[{1 + 1, 2 * 3}, prelude]], HoldPattern[TypeTheoryTerm[{2, 6}, _]]],
		FreeQ[NormalForm[TypeTheoryTerm[Typed[n, NonNegativeIntegers] |-> n + 0, prelude]], Plus],
		FreeQ[WeakHeadNormalForm[TypeTheoryTerm[{1 + 1, 2 * 3}, prelude]], Plus]
	},
	{True, True, False},
	TestID -> "NormalForm-reduces-every-part-under-binders-too"
]

(* a name that names no library environment is a Failure, and so is a term or a type in it *)
VerificationTest[
	{
		First[TypeTheoryEnvironment["WolframLanguge"]],
		First[TypeTheoryTerm[1, TypeTheoryEnvironment["WolframLanguge"]]],
		First[TypeTheoryType[1, TypeTheoryEnvironment["WolframLanguge"]]],
		First[TypeTheoryProof[1 == 1, TypeTheoryEnvironment["WolframLanguge"]]]
	},
	ConstantArray["UnknownEnvironment", 4],
	TestID -> "A-misspelled-library-environment-is-a-Failure"
]

(* a library environment by its name, wherever an environment is given, and a name that names none is a Failure *)
VerificationTest[
	{
		WeakHeadNormalForm[TypeTheoryTerm[MatchFirst[MatchValue[3]]]] === TypeTheoryTerm["some"[3], TypeTheoryEnvironment["Prelude"]],
		TypeTheoryType[Arguments] === TypeTheoryTerm[Expressions -> Expressions..., TypeTheoryEnvironment["Prelude"]],
		TypeTheoryProof[2 + 2 == 4, "Integers", {"Reflexivity"}]["Goals"],
		Head[TypeTheoryEnvironment["Integers", {TypeTheoryAxiom[namedEnvironmentAxiom, Integers]}]],
		FailureQ[TypeTheoryTerm[1, "NoSuchEnvironment"]],
		FailureQ[TypeTheoryType[1, "NoSuchEnvironment"]]
	},
	{True, True, {}, TypeTheoryEnvironment, True, True},
	TestID -> "A-library-environment-is-given-by-its-name"
]

(* a term checked against a type is coerced to it, as an argument is; an unknown Method is a Failure; a finished proof
   has a tree; a term given with another environment than its own is a Failure; HoldForm alone is in the Wolfram Language
   environment *)
VerificationTest[
	Module[{proof, bits},
		proof = TypeTheoryProof[ForAll[{a, b}, Implies[And[a, b], And[b, a]]], {"Introduce"[a, b, h], "Classical"}];
		bits = TypeTheoryEnvironment[{TypeTheoryInductiveType[CheckedBit, TypeUniverse[1], {"checkedBitZero" -> CheckedBit, "checkedBitOne" -> CheckedBit}]}];
		{
			Head[TypeTheoryCheck[TypeTheoryTerm[3, "Integers"], TypeTheoryTerm[Integers]]],
			First[TypeTheoryCheck["Constructive", Method -> "Fast"]],
			Head[TypeTheoryProofTree[proof]],
			First[TypeTheoryType[TypeTheoryTerm["checkedBitOne", bits], TypeTheoryEnvironment["Prelude"]]],
			TypeTheoryType[Head[f[x]]] === TypeTheoryTerm[Expressions, TypeTheoryEnvironment["Prelude"]]
		}
	],
	{Success, "UnknownMethod", TypeTheoryProofTree, "DifferentEnvironments", True},
	TestID -> "Checks-coerce-methods-are-known-finished-proofs-have-trees-and-environments-agree"
]

(* an ascription has the type it is given, checked, not the kernel's own type of its term *)
VerificationTest[
	{
		MatchQ[TypeTheoryType[Typed["equalityReflexivity"[4], 2 + 2 == 4]], HoldPattern[TypeTheoryTerm[2 + 2 == 4, _]]],
		First[TypeTheoryType[Typed["equalityReflexivity"[4], 2 + 2 == 5]]]
	},
	{True, "TypeMismatch"},
	TestID -> "An-ascription-has-the-type-it-is-given"
]

(* the Wolfram Language reading of a term is the expression it is, as it is written, with the type theory's notation
   read as the Wolfram Language's: ascriptions and binder types dropped, constructors as data *)
VerificationTest[
	{
		TypeTheoryExpression[TypeTheoryTerm[Map[n |-> n^2, {1, 2, 3}]], HoldComplete],
		TypeTheoryExpression[TypeTheoryTerm[Typed[-3, Integers] + 1, "Integers"], HoldComplete],
		TypeTheoryExpression[TypeTheoryTerm[Decide[2 <= 3]], HoldComplete],
		TypeTheoryExpression[TypeTheoryTerm[{Arguments[readingHead[1, 2, 3]]}], HoldComplete],
		TypeTheoryExpression[TypeTheoryTerm[Typed["none", Option[NonNegativeIntegers]]], HoldComplete],
		TypeTheoryExpression[TypeTheoryTerm[Typed["none", Strings]], HoldComplete],
		TypeTheoryExpression[TypeTheoryTerm[FromString["Hi"]], HoldComplete],
		TypeTheoryExpression[TypeTheoryTerm[Unevaluated[1 + 2]], HoldComplete],
		TypeTheoryExpression[TypeTheoryTerm[Construct[readingHead, 1 + 2, Unevaluated[1 + 2]]], HoldComplete],
		TypeTheoryExpression[TypeTheoryTerm[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A]} |-> x], HoldComplete],
		TypeTheoryExpression[TypeTheoryTerm[Unevaluated[1, 2]], HoldComplete],
		Information[TypeTheoryTerm[Join[{1, 2}, {3}]], "Expression"],
		MemberQ[Information[TypeTheoryTerm[2], "Properties"], "Expression"]
	},
	{
		HoldComplete[Function[n, n^2] /@ {1, 2, 3}], HoldComplete[-3 + 1], HoldComplete[2 <= 3], HoldComplete[{Sequence @@ readingHead[1, 2, 3]}],
		HoldComplete[Missing["NotAvailable"]], HoldComplete["none"], HoldComplete["Hi"], HoldComplete[1 + 2],
		HoldComplete[Construct[readingHead, 1 + 2, Unevaluated[1 + 2]]], HoldComplete[Function[{x}, x]], HoldComplete[Sequence[1, 2]], {1, 2, 3}, True
	},
	TestID -> "The-reading-of-a-term-is-the-term-as-it-is-written"
]

(* the reading evaluated in the Wolfram Language is the reading of the value the kernel computes, where the term's
   constants are the Wolfram Language's or defined as it defines them, as a definition TypeTheoryFormalize reads is; a
   constant of your own reads as its symbol, which the Wolfram Language does not evaluate; a proof, or a recursor, has no
   reading *)
readingSquare[x_Integer] := x^2 + 1

VerificationTest[
	Module[{agreeQ, squares = TypeTheoryEnvironment[TypeTheoryFormalize[readingSquare]], doubling = TypeTheoryEnvironment[{TypeTheoryDefinition[ReadingDoubled, n |-> 2 n]}]},
		SetAttributes[agreeQ, HoldFirst];
		agreeQ[term_] := With[{written = term}, TypeTheoryExpression[written] === TypeTheoryExpression[NormalForm[written]]];
		{
			agreeQ[TypeTheoryTerm[Map[n |-> n^2, {1, 2, 3}]]],
			agreeQ[TypeTheoryTerm[Typed[-3, Integers] + 1, "Integers"]],
			agreeQ[TypeTheoryTerm[1/2 + 1/3, "Rationals"]],
			agreeQ[TypeTheoryTerm[Lookup[<|"a" -> 1, "b" -> 2|>, "c"]]],
			agreeQ[TypeTheoryTerm[ReplaceRepeated[log[a b c], log[x_ y_] :> log[x] + log[y]]]],
			agreeQ[TypeTheoryTerm[{Arguments[readingHead[1, 2, 3]]}]],
			agreeQ[TypeTheoryTerm[Typed["text", NonNegativeIntegers | Strings]]],
			agreeQ[TypeTheoryTerm[If[2 == 3, 1, 5]]],
			agreeQ[TypeTheoryTerm[Construct[readingHead, 1 + 2, Unevaluated[1 + 2]]]],
			agreeQ[TypeTheoryTerm[Failure["Tag", <|"x" -> 1|>]]],
			agreeQ[TypeTheoryTerm[readingSquare[5], squares]],
			agreeQ[TypeTheoryTerm[ReadingDoubled[21], doubling]],
			TypeTheoryExpression[TypeTheoryTerm[ReadingDoubled[21], doubling]],
			TypeTheoryExpression[TypeTheoryTerm[{a, b} |-> a + 2 b]][3, 4],
			First[TypeTheoryExpression[TypeTheoryTerm["equalityReflexivity"[2]]]],
			First[TypeTheoryExpression[TypeTheoryTerm[InductiveRecursor[Naturals][Naturals &, 1, #1 + #2 &, 3]]]]
		}
	],
	{True, True, True, True, True, True, True, True, True, True, True, False, ReadingDoubled[21], 11, "NoExpression", "NoExpression"},
	TestID -> "The-reading-evaluates-to-the-reading-of-the-value-where-the-definitions-are-the-Wolfram-Language-s"
]

(* the closure names every trusted assumption a proof rests on: here a projection registered as the greatest common
   divisor, which has no defining equations to check, makes the kernel compute FirstNumber[2, 3] as 1 and unfold it as 2,
   and the proof of False rests on no axiom but on the registration; a theorem of the prelude rests on the kernel alone *)
VerificationTest[
	Module[{lying},
		lying = TypeTheoryEnvironment[{
			TypeTheoryDefinition[FirstNumber, {Typed[m, NonNegativeIntegers], Typed[n, NonNegativeIntegers]} |-> m],
			TypeTheoryNaturalNumbers[NonNegativeIntegers, "zero", "successor", <|"GCD" -> FirstNumber|>],
			TypeTheoryTheorem[FirstIsIdentity, ForAll[{Typed[x, NonNegativeIntegers]}, FirstNumber[x, 3] == x], Typed[x, NonNegativeIntegers] |-> "equalityReflexivity"[x]],
			TypeTheoryTheorem[FirstIsOne, FirstNumber[2, 3] == 1, "equalityReflexivity"[1]],
			TypeTheoryTheorem[RegistrationParadox, False, "successorNotZero"[0]["equalitySymmetry"["successorInjectivity"["equalityTransitivity"["equalitySymmetry"[FirstIsOne], FirstIsIdentity[2]]]]]]
		}];
		{TypeTheoryAxiomClosure[TypeTheoryTerm[RegistrationParadox, lying]], TypeTheoryAxiomClosure[TypeTheoryTerm["additionCommutativity", prelude]]}
	],
	{<|FirstNumber -> "Registration"|>, <||>},
	TestID -> "The-axiom-closure-names-a-registration-the-kernel-trusts"
]
