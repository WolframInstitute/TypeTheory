(* ::Package:: *)

(* Calls of System` functions that TypeTheory makes, each with Wolfram 15's result: a conformance
   corpus for kernels that run TypeTheory. Written by scripts/kernel_conformance.wls; do not edit. *)

VerificationTest[
	AllTrue[{True}, BooleanQ],
	True,
	TestID -> "AllTrue-1"
]

VerificationTest[
	AllTrue[Values[{"RewriteRules" -> True}], BooleanQ],
	True,
	TestID -> "AllTrue-2"
]

VerificationTest[
	AllTrue[{}, Function[WolframInstitute`TypeTheory`Checking`Declarations`Private`parameter, MatchQ[Unevaluated[WolframInstitute`TypeTheory`Checking`Declarations`Private`parameter], _Symbol | _String], HoldAll]],
	True,
	TestID -> "AllTrue-3"
]

VerificationTest[
	AllTrue[Unevaluated[{}], Function[WolframInstitute`TypeTheory`Checking`Declarations`Private`parameter, MatchQ[Unevaluated[WolframInstitute`TypeTheory`Checking`Declarations`Private`parameter], _Symbol | _String], HoldAll]],
	True,
	TestID -> "AllTrue-4"
]

VerificationTest[
	AllTrue[{WolframInstitute`TypeTheory`Library`Prelude`Private`u}, Function[WolframInstitute`TypeTheory`Checking`Declarations`Private`parameter, MatchQ[Unevaluated[WolframInstitute`TypeTheory`Checking`Declarations`Private`parameter], _Symbol | _String], HoldAll]],
	True,
	TestID -> "AllTrue-5"
]

VerificationTest[
	True && True && True,
	True,
	TestID -> "And-1"
]

VerificationTest[
	ListQ[{}] && Length[{}] == Length[{}],
	True,
	TestID -> "And-2"
]

VerificationTest[
	MatchQ[1, WolframInstitute`TypeTheory`PackageScope`levelSuccessor[_WolframInstitute`TypeTheory`PackageScope`levelMetavariable, _]] && IntegerQ[0] && 0 >= Last[1],
	False,
	TestID -> "And-3"
]

VerificationTest[
	AnyTrue[{0}, Function[WolframInstitute`TypeTheory`Terms`CoreTerms`Private`component, MatchQ[WolframInstitute`TypeTheory`Terms`CoreTerms`Private`component, (WolframInstitute`TypeTheory`Terms`CoreTerms`Private`n_Integer /; WolframInstitute`TypeTheory`Terms`CoreTerms`Private`n > 0) | {_, WolframInstitute`TypeTheory`Terms`CoreTerms`Private`k_ /; WolframInstitute`TypeTheory`Terms`CoreTerms`Private`k > 0}]]],
	False,
	TestID -> "AnyTrue-1"
]

VerificationTest[
	Append[{}, 3544],
	{3544},
	TestID -> "Append-1"
]

VerificationTest[
	Append[{3564}, 3565],
	{3564, 3565},
	TestID -> "Append-2"
]

VerificationTest[
	Append[{}, WolframInstitute`TypeTheory`PackageScope`boundVariable[1]],
	{WolframInstitute`TypeTheory`PackageScope`boundVariable[1]},
	TestID -> "Append-3"
]

VerificationTest[
	Append[{"/Users/swish/src/wolfram/TypeTheory/TypeTheory"}, "/Users/swish/src/wolfram/TypeTheory"],
	{"/Users/swish/src/wolfram/TypeTheory/TypeTheory", "/Users/swish/src/wolfram/TypeTheory"},
	TestID -> "Append-4"
]

VerificationTest[
	Append[{WolframInstitute`TypeTheory`PackageScope`freeVariable[4048]}, WolframInstitute`TypeTheory`PackageScope`freeVariable[4049]],
	{WolframInstitute`TypeTheory`PackageScope`freeVariable[4048], WolframInstitute`TypeTheory`PackageScope`freeVariable[4049]},
	TestID -> "Append-5"
]

VerificationTest[
	Append[{}, {HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`a], WolframInstitute`TypeTheory`PackageScope`universeSort[0], "Explicit"}],
	{{HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`a], WolframInstitute`TypeTheory`PackageScope`universeSort[0], "Explicit"}},
	TestID -> "Append-6"
]

VerificationTest[
	Append[{{HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`a], WolframInstitute`TypeTheory`PackageScope`universeSort[0], "Explicit"}}, {HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`b], WolframInstitute`TypeTheory`PackageScope`universeSort[0], "Explicit"}],
	{{HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`a], WolframInstitute`TypeTheory`PackageScope`universeSort[0], "Explicit"}, {HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`b], WolframInstitute`TypeTheory`PackageScope`universeSort[0], "Explicit"}},
	TestID -> "Append-7"
]

VerificationTest[
	Append[<|"Name" -> HoldComplete[True], "Type" -> WolframInstitute`TypeTheory`PackageScope`universeSort[0], "Constant" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[True], {}], "IndexIds" -> {}, "Context" -> <||>, "Level" -> 0, "Nested" -> None|>["IndexIds"], 3544],
	{3544},
	TestID -> "Append-8"
]

VerificationTest[
	Append[<|"Name" -> HoldComplete[WolframInstitute`TypeTheory`TrueIntroduction], "Type" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[True], {}], "Owner" -> HoldComplete[True], "Original" -> None, "AfterParameters" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[True], {}], "FieldIds" -> {}, "FieldContext" -> <||>, "ConclusionIndices" -> {}, "RecursiveFields" -> {}, "Application" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[WolframInstitute`TypeTheory`TrueIntroduction], {}]|>["ConclusionIndices"], <|"Name" -> HoldComplete[WolframInstitute`TypeTheory`TrueIntroduction], "Type" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[True], {}], "Owner" -> HoldComplete[True], "Original" -> None, "AfterParameters" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[True], {}], "FieldIds" -> {}, "FieldContext" -> <||>, "ConclusionIndices" -> {}, "RecursiveFields" -> {}, "Application" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[WolframInstitute`TypeTheory`TrueIntroduction], {}]|>["Application"]],
	{WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[WolframInstitute`TypeTheory`TrueIntroduction], {}]},
	TestID -> "Append-9"
]

VerificationTest[
	Append[{True, WolframInstitute`TypeTheory`TrueIntroduction, WolframInstitute`TypeTheory`InductiveRecursor[True], False, WolframInstitute`TypeTheory`InductiveRecursor[False], Not, And, WolframInstitute`TypeTheory`AndIntroduction, WolframInstitute`TypeTheory`InductiveRecursor[And], Or, WolframInstitute`TypeTheory`OrIntroductionLeft, WolframInstitute`TypeTheory`OrIntroductionRight, WolframInstitute`TypeTheory`InductiveRecursor[Or], Equivalent, WolframInstitute`TypeTheory`EquivalentIntroduction, WolframInstitute`TypeTheory`InductiveRecursor[Equivalent], Equal, WolframInstitute`TypeTheory`EqualityReflexivity, WolframInstitute`TypeTheory`InductiveRecursor[Equal], Exists, WolframInstitute`TypeTheory`ExistsIntroduction, WolframInstitute`TypeTheory`InductiveRecursor[Exists], Unequal, Identity, Composition, NonNegativeIntegers, WolframInstitute`TypeTheory`NaturalNumberZero, WolframInstitute`TypeTheory`NaturalNumberSuccessor, WolframInstitute`TypeTheory`InductiveRecursor[NonNegativeIntegers], Plus, WolframInstitute`TypeTheory`NaturalNumberPredecessor, Subtract, Times, Power, LessEqual, WolframInstitute`TypeTheory`LessEqualReflexivity, WolframInstitute`TypeTheory`LessEqualStep, WolframInstitute`TypeTheory`InductiveRecursor[LessEqual], Less, GreaterEqual, Greater, WolframInstitute`TypeTheory`FalseElimination, WolframInstitute`TypeTheory`AndEliminationLeft, WolframInstitute`TypeTheory`AndEliminationRight, WolframInstitute`TypeTheory`EqualitySymmetry, WolframInstitute`TypeTheory`EqualityTransitivity, WolframInstitute`TypeTheory`EqualityCongruence, WolframInstitute`TypeTheory`EqualitySubstitution, WolframInstitute`TypeTheory`EquivalentForward, WolframInstitute`TypeTheory`EquivalentBackward, WolframInstitute`TypeTheory`EquivalentReflexivity, WolframInstitute`TypeTheory`EquivalentSymmetry, WolframInstitute`TypeTheory`EquivalentTransitivity, WolframInstitute`TypeTheory`AdditionZeroRight, WolframInstitute`TypeTheory`AdditionZeroLeft, WolframInstitute`TypeTheory`AdditionSuccessorRight, WolframInstitute`TypeTheory`AdditionSuccessorLeft, WolframInstitute`TypeTheory`AdditionCommutativity, WolframInstitute`TypeTheory`AdditionAssociativity, WolframInstitute`TypeTheory`MultiplicationZeroRight, WolframInstitute`TypeTheory`MultiplicationZeroLeft, WolframInstitute`TypeTheory`MultiplicationSuccessorRight, WolframInstitute`TypeTheory`MultiplicationOneRight, WolframInstitute`TypeTheory`MultiplicationOneLeft, WolframInstitute`TypeTheory`MultiplicationSuccessorLeft, WolframInstitute`TypeTheory`MultiplicationCommutativity, WolframInstitute`TypeTheory`MultiplicationDistributivityLeft, WolframInstitute`TypeTheory`MultiplicationDistributivityRight, WolframInstitute`TypeTheory`MultiplicationAssociativity, WolframInstitute`TypeTheory`SuccessorInjectivity, WolframInstitute`TypeTheory`SuccessorNotZero, WolframInstitute`TypeTheory`SubtractionZeroRight, WolframInstitute`TypeTheory`SubtractionZeroLeft, WolframInstitute`TypeTheory`SubtractionSuccessor, WolframInstitute`TypeTheory`SubtractionSelf, WolframInstitute`TypeTheory`AdditionSubtractionCancellation, WolframInstitute`TypeTheory`PowerZero, WolframInstitute`TypeTheory`PowerSuccessor, WolframInstitute`TypeTheory`PowerOne, WolframInstitute`TypeTheory`PowerAddition, WolframInstitute`TypeTheory`PredecessorLessEqual, WolframInstitute`TypeTheory`LessEqualZero, WolframInstitute`TypeTheory`LessEqualSuccessor, WolframInstitute`TypeTheory`LessEqualTransitivity, WolframInstitute`TypeTheory`LessEqualAddition, WolframInstitute`TypeTheory`SuccessorNotLessEqualZero, WolframInstitute`TypeTheory`LessEqualPredecessor, WolframInstitute`TypeTheory`LessIrreflexivity, WolframInstitute`TypeTheory`LessEqualAntisymmetry, Booleans, "false", "true", WolframInstitute`TypeTheory`InductiveRecursor[Booleans], "not", "and", "or", WolframInstitute`TypeTheory`Nonempty, WolframInstitute`TypeTheory`NonemptyIntroduction, WolframInstitute`TypeTheory`InductiveRecursor[WolframInstitute`TypeTheory`Nonempty], WolframInstitute`TypeTheory`Subtype, WolframInstitute`TypeTheory`SubtypeIntroduction, WolframInstitute`TypeTheory`InductiveRecursor[WolframInstitute`TypeTheory`Subtype], WolframInstitute`TypeTheory`PropositionalExtensionality, WolframInstitute`TypeTheory`FunctionExtensionality, WolframInstitute`TypeTheory`Choice, WolframInstitute`TypeTheory`ChosenWitness, WolframInstitute`TypeTheory`ChosenWitnessProperty, WolframInstitute`TypeTheory`ExcludedMiddle, WolframInstitute`TypeTheory`DoubleNegationElimination}, Point],
	{True, WolframInstitute`TypeTheory`TrueIntroduction, WolframInstitute`TypeTheory`InductiveRecursor[True], False, WolframInstitute`TypeTheory`InductiveRecursor[False], Not, And, WolframInstitute`TypeTheory`AndIntroduction, WolframInstitute`TypeTheory`InductiveRecursor[And], Or, WolframInstitute`TypeTheory`OrIntroductionLeft, WolframInstitute`TypeTheory`OrIntroductionRight, WolframInstitute`TypeTheory`InductiveRecursor[Or], Equivalent, WolframInstitute`TypeTheory`EquivalentIntroduction, WolframInstitute`TypeTheory`InductiveRecursor[Equivalent], Equal, WolframInstitute`TypeTheory`EqualityReflexivity, WolframInstitute`TypeTheory`InductiveRecursor[Equal], Exists, WolframInstitute`TypeTheory`ExistsIntroduction, WolframInstitute`TypeTheory`InductiveRecursor[Exists], Unequal, Identity, Composition, NonNegativeIntegers, WolframInstitute`TypeTheory`NaturalNumberZero, WolframInstitute`TypeTheory`NaturalNumberSuccessor, WolframInstitute`TypeTheory`InductiveRecursor[NonNegativeIntegers], Plus, WolframInstitute`TypeTheory`NaturalNumberPredecessor, Subtract, Times, Power, LessEqual, WolframInstitute`TypeTheory`LessEqualReflexivity, WolframInstitute`TypeTheory`LessEqualStep, WolframInstitute`TypeTheory`InductiveRecursor[LessEqual], Less, GreaterEqual, Greater, WolframInstitute`TypeTheory`FalseElimination, WolframInstitute`TypeTheory`AndEliminationLeft, WolframInstitute`TypeTheory`AndEliminationRight, WolframInstitute`TypeTheory`EqualitySymmetry, WolframInstitute`TypeTheory`EqualityTransitivity, WolframInstitute`TypeTheory`EqualityCongruence, WolframInstitute`TypeTheory`EqualitySubstitution, WolframInstitute`TypeTheory`EquivalentForward, WolframInstitute`TypeTheory`EquivalentBackward, WolframInstitute`TypeTheory`EquivalentReflexivity, WolframInstitute`TypeTheory`EquivalentSymmetry, WolframInstitute`TypeTheory`EquivalentTransitivity, WolframInstitute`TypeTheory`AdditionZeroRight, WolframInstitute`TypeTheory`AdditionZeroLeft, WolframInstitute`TypeTheory`AdditionSuccessorRight, WolframInstitute`TypeTheory`AdditionSuccessorLeft, WolframInstitute`TypeTheory`AdditionCommutativity, WolframInstitute`TypeTheory`AdditionAssociativity, WolframInstitute`TypeTheory`MultiplicationZeroRight, WolframInstitute`TypeTheory`MultiplicationZeroLeft, WolframInstitute`TypeTheory`MultiplicationSuccessorRight, WolframInstitute`TypeTheory`MultiplicationOneRight, WolframInstitute`TypeTheory`MultiplicationOneLeft, WolframInstitute`TypeTheory`MultiplicationSuccessorLeft, WolframInstitute`TypeTheory`MultiplicationCommutativity, WolframInstitute`TypeTheory`MultiplicationDistributivityLeft, WolframInstitute`TypeTheory`MultiplicationDistributivityRight, WolframInstitute`TypeTheory`MultiplicationAssociativity, WolframInstitute`TypeTheory`SuccessorInjectivity, WolframInstitute`TypeTheory`SuccessorNotZero, WolframInstitute`TypeTheory`SubtractionZeroRight, WolframInstitute`TypeTheory`SubtractionZeroLeft, WolframInstitute`TypeTheory`SubtractionSuccessor, WolframInstitute`TypeTheory`SubtractionSelf, WolframInstitute`TypeTheory`AdditionSubtractionCancellation, WolframInstitute`TypeTheory`PowerZero, WolframInstitute`TypeTheory`PowerSuccessor, WolframInstitute`TypeTheory`PowerOne, WolframInstitute`TypeTheory`PowerAddition, WolframInstitute`TypeTheory`PredecessorLessEqual, WolframInstitute`TypeTheory`LessEqualZero, WolframInstitute`TypeTheory`LessEqualSuccessor, WolframInstitute`TypeTheory`LessEqualTransitivity, WolframInstitute`TypeTheory`LessEqualAddition, WolframInstitute`TypeTheory`SuccessorNotLessEqualZero, WolframInstitute`TypeTheory`LessEqualPredecessor, WolframInstitute`TypeTheory`LessIrreflexivity, WolframInstitute`TypeTheory`LessEqualAntisymmetry, Booleans, "false", "true", WolframInstitute`TypeTheory`InductiveRecursor[Booleans], "not", "and", "or", WolframInstitute`TypeTheory`Nonempty, WolframInstitute`TypeTheory`NonemptyIntroduction, WolframInstitute`TypeTheory`InductiveRecursor[WolframInstitute`TypeTheory`Nonempty], WolframInstitute`TypeTheory`Subtype, WolframInstitute`TypeTheory`SubtypeIntroduction, WolframInstitute`TypeTheory`InductiveRecursor[WolframInstitute`TypeTheory`Subtype], WolframInstitute`TypeTheory`PropositionalExtensionality, WolframInstitute`TypeTheory`FunctionExtensionality, WolframInstitute`TypeTheory`Choice, WolframInstitute`TypeTheory`ChosenWitness, WolframInstitute`TypeTheory`ChosenWitnessProperty, WolframInstitute`TypeTheory`ExcludedMiddle, WolframInstitute`TypeTheory`DoubleNegationElimination, Point},
	TestID -> "Append-10"
]

VerificationTest[
	Apply[SameQ],
	Apply[SameQ],
	TestID -> "Apply-1"
]

VerificationTest[
	Alternatives @@ {HoldComplete[True]},
	Alternatives[HoldComplete[True]],
	TestID -> "Apply-2"
]

VerificationTest[
	HoldForm @@ First[{HoldComplete[Plus]}],
	HoldForm[Plus],
	TestID -> "Apply-3"
]

VerificationTest[
	HoldForm @@ HoldComplete[NonNegativeIntegers],
	HoldForm[NonNegativeIntegers],
	TestID -> "Apply-4"
]

VerificationTest[
	Function[{WolframInstitute`TypeTheory`Checking`NaturalNumbers`Private`m, WolframInstitute`TypeTheory`Checking`NaturalNumbers`Private`n}, WolframInstitute`TypeTheory`Checking`NaturalNumbers`Private`m + WolframInstitute`TypeTheory`Checking`NaturalNumbers`Private`n] @@ {0, 0},
	0,
	TestID -> "Apply-5"
]

VerificationTest[
	AssociationQ[None],
	False,
	TestID -> "AssociationQ-1"
]

VerificationTest[
	AssociationQ[<||>],
	True,
	TestID -> "AssociationQ-2"
]

VerificationTest[
	AtomQ[{{"Kernel", "Root" -> "Kernel", "Context" -> {"WolframInstitute`TypeTheory`"}}}],
	False,
	TestID -> "AtomQ-1"
]

VerificationTest[
	BooleanQ[True],
	True,
	TestID -> "BooleanQ-1"
]

VerificationTest[
	Cases[{1, 1}, {_, _}],
	{},
	TestID -> "Cases-1"
]

VerificationTest[
	Cases[{1, 1}, _Integer],
	{1, 1},
	TestID -> "Cases-2"
]

VerificationTest[
	Cases[WolframInstitute`TypeTheory`PackageScope`universeSort[0], _WolframInstitute`TypeTheory`PackageScope`metavariable | _WolframInstitute`TypeTheory`PackageScope`levelMetavariable, {0, Infinity}],
	{},
	TestID -> "Cases-3"
]

VerificationTest[
	Cases[{}, WolframInstitute`TypeTheory`PackageScope`levelParameter[WolframInstitute`TypeTheory`Checking`Declarations`Private`parameter_] :> WolframInstitute`TypeTheory`Checking`Declarations`Private`parameter],
	{},
	TestID -> "Cases-4"
]

VerificationTest[
	Cases[Hold["UniverseParameters" -> Automatic], (Rule | RuleDelayed)["UniverseParameters", WolframInstitute`TypeTheory`Checking`Declarations`Private`value_] :> HoldComplete[WolframInstitute`TypeTheory`Checking`Declarations`Private`value], {1, 2}],
	{HoldComplete[Automatic]},
	TestID -> "Cases-5"
]

VerificationTest[
	Cases[{WolframInstitute`TypeTheory`PackageScope`universeSort[0]}, WolframInstitute`TypeTheory`PackageScope`levelParameter[WolframInstitute`TypeTheory`Checking`Environment`Private`parameter_] :> WolframInstitute`TypeTheory`Checking`Environment`Private`parameter, Infinity],
	{},
	TestID -> "Cases-6"
]

VerificationTest[
	Cases[{WolframInstitute`TypeTheory`PackageScope`universeSort[0]}, WolframInstitute`TypeTheory`PackageScope`levelParameter[WolframInstitute`TypeTheory`Checking`Environment`Private`parameter_] :> WolframInstitute`TypeTheory`Checking`Environment`Private`parameter, Infinity],
	{},
	TestID -> "Cases-7"
]

VerificationTest[
	Cases[{WolframInstitute`TypeTheory`PackageScope`levelParameter[HoldComplete[WolframInstitute`TypeTheory`Library`HomotopyTypeTheory`Private`u]]}, WolframInstitute`TypeTheory`PackageScope`levelParameter[WolframInstitute`TypeTheory`Checking`Declarations`Private`parameter_] :> WolframInstitute`TypeTheory`Checking`Declarations`Private`parameter],
	{HoldComplete[WolframInstitute`TypeTheory`Library`HomotopyTypeTheory`Private`u]},
	TestID -> "Cases-8"
]

VerificationTest[
	Cases[Unevaluated[{}], (Rule | RuleDelayed)[WolframInstitute`TypeTheory`Checking`Declarations`Private`constructor_, WolframInstitute`TypeTheory`Checking`Declarations`Private`type_] :> {HoldComplete[WolframInstitute`TypeTheory`Checking`Declarations`Private`constructor], HoldComplete[WolframInstitute`TypeTheory`Checking`Declarations`Private`type]}],
	{},
	TestID -> "Cases-9"
]

VerificationTest[
	Cases[{WolframInstitute`TypeTheory`PackageScope`syntaxInteger[3]}, WolframInstitute`TypeTheory`PackageScope`syntaxApplication[WolframInstitute`TypeTheory`PackageScope`syntaxSymbol[HoldComplete[WolframInstitute`TypeTheory`TypeUniverse]], {WolframInstitute`TypeTheory`Checking`Declarations`Private`level_}] :> WolframInstitute`TypeTheory`Checking`Declarations`Private`level, {0, Infinity}],
	{},
	TestID -> "Cases-10"
]

VerificationTest[
	Cases[Hold[PacletObject[Association["Name" -> "WolframInstitute/TypeTheory", "PublisherID" -> "WolframInstitute", "Version" -> "0.12.4", "WolframVersion" -> "15.0+", "Description" -> "A proof engine for the Calculus of Inductive Constructions, written in the Wolfram Language", "Creator" -> "Nikolay Murzin", "License" -> "MIT", "Keywords" -> {"type theory", "dependent types", "inductive types", "proof assistant", "proof checking"}, "Categories" -> {"Mathematics"}, "PrimaryContext" -> "WolframInstitute`TypeTheory`", "Extensions" -> {{"Kernel", "Root" -> "Kernel", "Context" -> {"WolframInstitute`TypeTheory`"}}, {"Documentation", "Language" -> "English", "MainPage" -> "Guides/TypeTheory"}, {"Test", "Root" -> "Tests", "Method" -> "Experimental-v1"}}]]], (PacletManager`Paclet`Private`h_)[___] :> Hold[PacletManager`Paclet`Private`h], Infinity],
	{Hold[Rule], Hold[Rule], Hold[Rule], Hold[Rule], Hold[Rule], Hold[Rule], Hold[Rule], Hold[List], Hold[Rule], Hold[List], Hold[Rule], Hold[Rule], Hold[Rule], Hold[List], Hold[Rule], Hold[List], Hold[Rule], Hold[Rule], Hold[List], Hold[Rule], Hold[Rule], Hold[List], Hold[List], Hold[Rule], Hold[Association], Hold[PacletObject]},
	TestID -> "Cases-11"
]

VerificationTest[
	Cases[Hold[PacletObject[Association["Name" -> "WolframInstitute/TypeTheory", "PublisherID" -> "WolframInstitute", "Version" -> "0.12.4", "WolframVersion" -> "15.0+", "Description" -> "A proof engine for the Calculus of Inductive Constructions, written in the Wolfram Language", "Creator" -> "Nikolay Murzin", "License" -> "MIT", "Keywords" -> {"type theory", "dependent types", "inductive types", "proof assistant", "proof checking"}, "Categories" -> {"Mathematics"}, "PrimaryContext" -> "WolframInstitute`TypeTheory`", "Extensions" -> {{"Kernel", "Root" -> "Kernel", "Context" -> {"WolframInstitute`TypeTheory`"}}, {"Documentation", "Language" -> "English", "MainPage" -> "Guides/TypeTheory"}, {"Test", "Root" -> "Tests", "Method" -> "Experimental-v1"}}]]], (PacletManager`Paclet`Private`h_)[___] :> Hold[PacletManager`Paclet`Private`h], Infinity],
	{Hold[Rule], Hold[Rule], Hold[Rule], Hold[Rule], Hold[Rule], Hold[Rule], Hold[Rule], Hold[List], Hold[Rule], Hold[List], Hold[Rule], Hold[Rule], Hold[Rule], Hold[List], Hold[Rule], Hold[List], Hold[Rule], Hold[Rule], Hold[List], Hold[Rule], Hold[Rule], Hold[List], Hold[List], Hold[Rule], Hold[Association], Hold[PacletObject]},
	TestID -> "Cases-12"
]

VerificationTest[
	Catenate[{}],
	{},
	TestID -> "Catenate-1"
]

VerificationTest[
	Catenate[{{}}],
	{},
	TestID -> "Catenate-2"
]

VerificationTest[
	Catenate[Cases[{WolframInstitute`TypeTheory`PackageScope`syntaxInteger[3]}, WolframInstitute`TypeTheory`PackageScope`syntaxApplication[WolframInstitute`TypeTheory`PackageScope`syntaxSymbol[HoldComplete[Subscript]], {_, WolframInstitute`TypeTheory`Checking`Declarations`Private`levels__}] :> {WolframInstitute`TypeTheory`Checking`Declarations`Private`levels}, {0, Infinity}]],
	{},
	TestID -> "Catenate-3"
]

VerificationTest[
	Complement[{}, {}],
	{},
	TestID -> "Complement-1"
]

VerificationTest[
	Complement[{PacletObject[<|"Name" -> "WolframInstitute/TypeTheory", "PublisherID" -> "WolframInstitute", "Version" -> "0.12.4", "WolframVersion" -> "15.0+", "Description" -> "A proof engine for the Calculus of Inductive Constructions, written in the Wolfram Language", "Creator" -> "Nikolay Murzin", "License" -> "MIT", "Keywords" -> {"type theory", "dependent types", "inductive types", "proof assistant", "proof checking"}, "Categories" -> {"Mathematics"}, "PrimaryContext" -> "WolframInstitute`TypeTheory`", "Extensions" -> {{"Kernel", "Root" -> "Kernel", "Context" -> {"WolframInstitute`TypeTheory`"}}, {"Documentation", "Language" -> "English", "MainPage" -> "Guides/TypeTheory"}, {"Test", "Root" -> "Tests", "Method" -> "Experimental-v1"}}, "Location" -> "/Users/swish/src/wolfram/TypeTheory/TypeTheory"|>], PacletObject[<|"Name" -> "WolframInstitute/TypeTheory", "PublisherID" -> "WolframInstitute", "Version" -> "0.12.4", "WolframVersion" -> "15.0+", "Description" -> "A proof engine for the Calculus of Inductive Constructions, written in the Wolfram Language", "Creator" -> "Nikolay Murzin", "License" -> "MIT", "Keywords" -> {"type theory", "dependent types", "inductive types", "proof assistant", "proof checking"}, "Categories" -> {"Mathematics"}, "PrimaryContext" -> "WolframInstitute`TypeTheory`", "Extensions" -> {{"Kernel", "Root" -> "Kernel", "Context" -> {"WolframInstitute`TypeTheory`"}}, {"Documentation", "Language" -> "English", "MainPage" -> "Guides/TypeTheory"}, {"Test", "Root" -> "Tests", "Method" -> "Experimental-v1"}}, "Location" -> "/Users/swish/src/wolfram/TypeTheory/TypeTheory"|>]}, {PacletObject[<|"Name" -> "WolframInstitute/TypeTheory", "PublisherID" -> "WolframInstitute", "Version" -> "0.12.4", "WolframVersion" -> "15.0+", "Description" -> "A proof engine for the Calculus of Inductive Constructions, written in the Wolfram Language", "Creator" -> "Nikolay Murzin", "License" -> "MIT", "Keywords" -> {"type theory", "dependent types", "inductive types", "proof assistant", "proof checking"}, "Categories" -> {"Mathematics"}, "PrimaryContext" -> "WolframInstitute`TypeTheory`", "Extensions" -> {{"Kernel", "Root" -> "Kernel", "Context" -> {"WolframInstitute`TypeTheory`"}}, {"Documentation", "Language" -> "English", "MainPage" -> "Guides/TypeTheory"}, {"Test", "Root" -> "Tests", "Method" -> "Experimental-v1"}}, "Location" -> "/Users/swish/src/wolfram/TypeTheory/TypeTheory"|>]}],
	{},
	TestID -> "Complement-2"
]

VerificationTest[
	ConstantArray[WolframInstitute`TypeTheory`PackageScope`metavariable[0], 6],
	{WolframInstitute`TypeTheory`PackageScope`metavariable[0], WolframInstitute`TypeTheory`PackageScope`metavariable[0], WolframInstitute`TypeTheory`PackageScope`metavariable[0], WolframInstitute`TypeTheory`PackageScope`metavariable[0], WolframInstitute`TypeTheory`PackageScope`metavariable[0], WolframInstitute`TypeTheory`PackageScope`metavariable[0]},
	TestID -> "ConstantArray-1"
]

VerificationTest[
	ContainsAll[{Hold[PacletManager`Paclet`Private`Paclet], Hold[PacletManager`Paclet`Private`PacletGroup], Hold[PacletObject], Hold[PacletSite], Hold[Association], Hold[List], Hold[Rule], Hold[RuleDelayed], Hold[Except], Hold[Alternatives], Hold[StringJoin], Hold[Join], Hold[Append], Hold[Prepend], Hold[Plus], Hold[Times], Hold[Divide], Hold[Subtract]}, {Hold[Rule], Hold[List], Hold[Association], Hold[PacletObject]}],
	True,
	TestID -> "ContainsAll-1"
]

VerificationTest[
	DeleteCases[{<|"Placeholder" -> WolframInstitute`TypeTheory`PackageScope`metavariable[782], "Name" -> HoldComplete[False], "Arguments" -> {}, "Syntax" -> WolframInstitute`TypeTheory`PackageScope`syntaxSymbol[HoldComplete[False]]|>}, <|"Placeholder" -> WolframInstitute`TypeTheory`PackageScope`metavariable[782], "Name" -> HoldComplete[False], "Arguments" -> {}, "Syntax" -> WolframInstitute`TypeTheory`PackageScope`syntaxSymbol[HoldComplete[False]]|>, {1}, 1],
	{},
	TestID -> "DeleteCases-1"
]

VerificationTest[
	DeleteDuplicates[{}],
	{},
	TestID -> "DeleteDuplicates-1"
]

VerificationTest[
	DeleteDuplicates[{HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`u]}],
	{HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`u]},
	TestID -> "DeleteDuplicates-2"
]

VerificationTest[
	DeleteDuplicates[Cases[Hold[PacletObject[Association["Name" -> "WolframInstitute/TypeTheory", "PublisherID" -> "WolframInstitute", "Version" -> "0.12.4", "WolframVersion" -> "15.0+", "Description" -> "A proof engine for the Calculus of Inductive Constructions, written in the Wolfram Language", "Creator" -> "Nikolay Murzin", "License" -> "MIT", "Keywords" -> {"type theory", "dependent types", "inductive types", "proof assistant", "proof checking"}, "Categories" -> {"Mathematics"}, "PrimaryContext" -> "WolframInstitute`TypeTheory`", "Extensions" -> {{"Kernel", "Root" -> "Kernel", "Context" -> {"WolframInstitute`TypeTheory`"}}, {"Documentation", "Language" -> "English", "MainPage" -> "Guides/TypeTheory"}, {"Test", "Root" -> "Tests", "Method" -> "Experimental-v1"}}]]], (PacletManager`Paclet`Private`h_)[___] :> Hold[PacletManager`Paclet`Private`h], Infinity]],
	{Hold[Rule], Hold[List], Hold[Association], Hold[PacletObject]},
	TestID -> "DeleteDuplicates-3"
]

VerificationTest[
	DigitQ["505"],
	True,
	TestID -> "DigitQ-1"
]

VerificationTest[
	DirectoryQ["/Users/swish/src/wolfram/TypeTheory"],
	True,
	TestID -> "DirectoryQ-1"
]

VerificationTest[
	Drop[{}, 0],
	{},
	TestID -> "Drop-1"
]

VerificationTest[
	Drop[{6646}, -1],
	{},
	TestID -> "Drop-2"
]

VerificationTest[
	Drop[{6646}, -1*1],
	{},
	TestID -> "Drop-3"
]

VerificationTest[
	Drop[Last[{WolframInstitute`TypeTheory`PackageScope`universeSort[0], {}}], -1*0],
	{},
	TestID -> "Drop-4"
]

VerificationTest[
	Drop[{}, <|"Kind" -> "Recursor", "Type" -> WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`m], WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`t], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[Booleans], {}], WolframInstitute`TypeTheory`PackageScope`universeSort[WolframInstitute`TypeTheory`PackageScope`levelParameter[HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`u]]], "Explicit"], WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete["false"], WolframInstitute`TypeTheory`PackageScope`application[WolframInstitute`TypeTheory`PackageScope`boundVariable[0], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete["false"], {}]], WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete["true"], WolframInstitute`TypeTheory`PackageScope`application[WolframInstitute`TypeTheory`PackageScope`boundVariable[1], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete["true"], {}]], WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`t], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[Booleans], {}], WolframInstitute`TypeTheory`PackageScope`application[WolframInstitute`TypeTheory`PackageScope`boundVariable[3], WolframInstitute`TypeTheory`PackageScope`boundVariable[0]], "Explicit"], "Explicit"], "Explicit"], "Explicit"], "UniverseParameters" -> {HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`u]}, "InductiveType" -> HoldComplete[Booleans], "NumberOfParameters" -> 0, "NumberOfMotives" -> 1, "NumberOfIndices" -> 0, "NumberOfMinors" -> 2, "Rules" -> <|HoldComplete["false"] -> <|"NumberOfParameters" -> 0, "NumberOfFields" -> 0, "RightHandSide" -> WolframInstitute`TypeTheory`PackageScope`lambdaAbstraction[HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`m], WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`t], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[Booleans], {}], WolframInstitute`TypeTheory`PackageScope`universeSort[WolframInstitute`TypeTheory`PackageScope`levelParameter[HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`u]]], "Explicit"], WolframInstitute`TypeTheory`PackageScope`lambdaAbstraction[HoldComplete["false"], WolframInstitute`TypeTheory`PackageScope`application[WolframInstitute`TypeTheory`PackageScope`boundVariable[0], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete["false"], {}]], WolframInstitute`TypeTheory`PackageScope`lambdaAbstraction[HoldComplete["true"], WolframInstitute`TypeTheory`PackageScope`application[WolframInstitute`TypeTheory`PackageScope`boundVariable[1], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete["true"], {}]], WolframInstitute`TypeTheory`PackageScope`boundVariable[1], "Explicit"], "Explicit"], "Explicit"]|>, HoldComplete["true"] -> <|"NumberOfParameters" -> 0, "NumberOfFields" -> 0, "RightHandSide" -> WolframInstitute`TypeTheory`PackageScope`lambdaAbstraction[HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`m], WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`t], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[Booleans], {}], WolframInstitute`TypeTheory`PackageScope`universeSort[WolframInstitute`TypeTheory`PackageScope`levelParameter[HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`u]]], "Explicit"], WolframInstitute`TypeTheory`PackageScope`lambdaAbstraction[HoldComplete["false"], WolframInstitute`TypeTheory`PackageScope`application[WolframInstitute`TypeTheory`PackageScope`boundVariable[0], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete["false"], {}]], WolframInstitute`TypeTheory`PackageScope`lambdaAbstraction[HoldComplete["true"], WolframInstitute`TypeTheory`PackageScope`application[WolframInstitute`TypeTheory`PackageScope`boundVariable[1], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete["true"], {}]], WolframInstitute`TypeTheory`PackageScope`boundVariable[0], "Explicit"], "Explicit"], "Explicit"]|>|>, "EliminationUniverse" -> True, "KLike" -> False|>["Rules"][HoldComplete["true"]]["NumberOfParameters"]],
	{},
	TestID -> "Drop-5"
]

VerificationTest[
	DuplicateFreeQ[{}],
	True,
	TestID -> "DuplicateFreeQ-1"
]

VerificationTest[
	DuplicateFreeQ[Values[<||>]],
	True,
	TestID -> "DuplicateFreeQ-2"
]

VerificationTest[
	DuplicateFreeQ[{HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`u]}],
	True,
	TestID -> "DuplicateFreeQ-3"
]

VerificationTest[
	1 == 0,
	False,
	TestID -> "Equal-1"
]

VerificationTest[
	"" == "",
	True,
	TestID -> "Equal-2"
]

VerificationTest[
	Length[{}] == 0,
	True,
	TestID -> "Equal-3"
]

VerificationTest[
	Length[{}] == Length[{}],
	True,
	TestID -> "Equal-4"
]

VerificationTest[
	2 == <|"Kind" -> "Constructor", "Type" -> WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[a], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NonNegativeIntegers], {}], WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[b], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NonNegativeIntegers], {}], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NaturalPair], {}], "Explicit"], "Explicit"], "UniverseParameters" -> {}, "InductiveType" -> HoldComplete[NaturalPair], "ConstructorIndex" -> 1, "NumberOfParameters" -> 0, "NumberOfFields" -> 2|>["NumberOfParameters"] + <|"Kind" -> "Constructor", "Type" -> WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[a], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NonNegativeIntegers], {}], WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[b], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NonNegativeIntegers], {}], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NaturalPair], {}], "Explicit"], "Explicit"], "UniverseParameters" -> {}, "InductiveType" -> HoldComplete[NaturalPair], "ConstructorIndex" -> 1, "NumberOfParameters" -> 0, "NumberOfFields" -> 2|>["NumberOfFields"],
	True,
	TestID -> "Equal-5"
]

VerificationTest[
	ExpandFileName["/Users/swish/src/wolfram/TypeTheory"],
	"/Users/swish/src/wolfram/TypeTheory",
	TestID -> "ExpandFileName-1"
]

VerificationTest[
	FailureQ[WolframInstitute`TypeTheory`PackageScope`universeSort[0]],
	False,
	TestID -> "FailureQ-1"
]

VerificationTest[
	FailureQ[<|1407 -> WolframInstitute`TypeTheory`PackageScope`freeVariable[28256]|>],
	False,
	TestID -> "FailureQ-2"
]

VerificationTest[
	FileNameDrop["/Users/swish/src/wolfram/TypeTheory/TypeTheory/PacletInfo.wl"],
	"/Users/swish/src/wolfram/TypeTheory/TypeTheory",
	TestID -> "FileNameDrop-1"
]

VerificationTest[
	FileNameDrop[ExpandFileName["/Users/swish/src/wolfram/TypeTheory/TypeTheory/PacletInfo.wl"]],
	"/Users/swish/src/wolfram/TypeTheory/TypeTheory",
	TestID -> "FileNameDrop-2"
]

VerificationTest[
	FileNameTake["/Users/swish/src/wolfram/TypeTheory/TypeTheory/PacletInfo.wl"],
	"PacletInfo.wl",
	TestID -> "FileNameTake-1"
]

VerificationTest[
	First[{1}],
	1,
	TestID -> "First-1"
]

VerificationTest[
	First[HoldComplete["true"]],
	"true",
	TestID -> "First-2"
]

VerificationTest[
	First[WolframInstitute`TypeTheory`PackageScope`universeSort[1]],
	1,
	TestID -> "First-3"
]

VerificationTest[
	First[HoldComplete[True] -> WolframInstitute`TypeTheory`PackageScope`universeSort[0]],
	HoldComplete[True],
	TestID -> "First-4"
]

VerificationTest[
	FirstPosition[{}, {Verbatim[HoldComplete[True]], _}, None, {1}, Heads -> False],
	None,
	TestID -> "FirstPosition-1"
]

VerificationTest[
	FirstPosition[{{HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`a], WolframInstitute`TypeTheory`PackageScope`universeSort[0]}}, {Verbatim[HoldComplete[False]], _}, None, {1}, Heads -> False],
	None,
	TestID -> "FirstPosition-2"
]

VerificationTest[
	FirstPosition[{HoldComplete[True]}, Verbatim[<|"Name" -> HoldComplete[WolframInstitute`TypeTheory`TrueIntroduction], "Type" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[True], {}], "Owner" -> HoldComplete[True], "Original" -> None, "AfterParameters" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[True], {}], "FieldIds" -> {}, "FieldContext" -> <||>, "ConclusionIndices" -> {}, "RecursiveFields" -> {}, "Application" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[WolframInstitute`TypeTheory`TrueIntroduction], {}]|>["Owner"]], {0}, {1}, Heads -> False],
	{1},
	TestID -> "FirstPosition-3"
]

VerificationTest[
	FirstPosition[Lookup[{<|"Name" -> HoldComplete[True], "Type" -> WolframInstitute`TypeTheory`PackageScope`universeSort[0], "Constant" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[True], {}], "IndexIds" -> {}, "Context" -> <||>, "Level" -> 0, "Nested" -> None|>}, "Name"], Verbatim[<|"Name" -> HoldComplete[WolframInstitute`TypeTheory`TrueIntroduction], "Type" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[True], {}], "Owner" -> HoldComplete[True], "Original" -> None, "AfterParameters" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[True], {}], "FieldIds" -> {}, "FieldContext" -> <||>, "ConclusionIndices" -> {}, "RecursiveFields" -> {}, "Application" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[WolframInstitute`TypeTheory`TrueIntroduction], {}]|>["Owner"]], {0}, {1}, Heads -> False],
	{1},
	TestID -> "FirstPosition-4"
]

VerificationTest[
	Flatten[{}],
	{},
	TestID -> "Flatten-1"
]

VerificationTest[
	Flatten[{{}}],
	{},
	TestID -> "Flatten-2"
]

VerificationTest[
	Flatten[Position[{13, 17}, First[{1}]]],
	{},
	TestID -> "Flatten-3"
]

VerificationTest[
	Fold[WolframInstitute`TypeTheory`PackageScope`application, WolframInstitute`TypeTheory`PackageScope`freeVariable[3855], {}],
	WolframInstitute`TypeTheory`PackageScope`freeVariable[3855],
	TestID -> "Fold-1"
]

VerificationTest[
	Fold[WolframInstitute`TypeTheory`PackageScope`application, WolframInstitute`TypeTheory`PackageScope`freeVariable[3543], {WolframInstitute`TypeTheory`PackageScope`freeVariable[3544]}],
	WolframInstitute`TypeTheory`PackageScope`application[WolframInstitute`TypeTheory`PackageScope`freeVariable[3543], WolframInstitute`TypeTheory`PackageScope`freeVariable[3544]],
	TestID -> "Fold-2"
]

VerificationTest[
	Fold[WolframInstitute`TypeTheory`PackageScope`application, First[{WolframInstitute`TypeTheory`PackageScope`universeSort[0], {}}], Drop[Last[{WolframInstitute`TypeTheory`PackageScope`universeSort[0], {}}], -1*0]],
	WolframInstitute`TypeTheory`PackageScope`universeSort[0],
	TestID -> "Fold-3"
]

VerificationTest[
	Fold[Function[{WolframInstitute`TypeTheory`Elaboration`Elaboration`Private`accumulated, WolframInstitute`TypeTheory`Elaboration`Elaboration`Private`domainCore}, WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[\[FormalX]], WolframInstitute`TypeTheory`Elaboration`Elaboration`Private`domainCore, WolframInstitute`TypeTheory`Elaboration`Elaboration`Private`accumulated, "Explicit"]], WolframInstitute`TypeTheory`PackageScope`boundVariable[1], {WolframInstitute`TypeTheory`PackageScope`boundVariable[1]}],
	WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[\[FormalX]], WolframInstitute`TypeTheory`PackageScope`boundVariable[1], WolframInstitute`TypeTheory`PackageScope`boundVariable[1], "Explicit"],
	TestID -> "Fold-4"
]

VerificationTest[
	FoldList[Max, 0, {13, 17}],
	{0, 13, 17},
	TestID -> "FoldList-1"
]

VerificationTest[
	FreeQ[True, Rose],
	True,
	TestID -> "FreeQ-1"
]

VerificationTest[
	FreeQ[False, Rose],
	True,
	TestID -> "FreeQ-2"
]

VerificationTest[
	FreeQ["false", Rose],
	True,
	TestID -> "FreeQ-3"
]

VerificationTest[
	FreeQ[WolframInstitute`TypeTheory`TrueIntroduction, Rose],
	True,
	TestID -> "FreeQ-4"
]

VerificationTest[
	FreeQ[WolframInstitute`TypeTheory`InductiveRecursor[True], Rose],
	True,
	TestID -> "FreeQ-5"
]

VerificationTest[
	FreeQ[1, _WolframInstitute`TypeTheory`PackageScope`levelMetavariable],
	True,
	TestID -> "FreeQ-6"
]

VerificationTest[
	FreeQ[False, _Pattern | _Blank | _BlankSequence | _BlankNullSequence],
	True,
	TestID -> "FreeQ-7"
]

VerificationTest[
	FreeQ[{}, _WolframInstitute`TypeTheory`PackageScope`levelMetavariable],
	True,
	TestID -> "FreeQ-8"
]

VerificationTest[
	FreeQ[_Association, _Pattern | _Blank | _BlankSequence | _BlankNullSequence],
	False,
	TestID -> "FreeQ-9"
]

VerificationTest[
	FreeQ[Values[<||>], _WolframInstitute`TypeTheory`PackageScope`levelMetavariable],
	True,
	TestID -> "FreeQ-10"
]

VerificationTest[
	FreeQ[{}, WolframInstitute`TypeTheory`PackageScope`constantReference[Alternatives[HoldComplete[True]], _]],
	True,
	TestID -> "FreeQ-11"
]

VerificationTest[
	FreeQ[WolframInstitute`TypeTheory`PackageScope`freeVariable[3699], WolframInstitute`TypeTheory`PackageScope`metavariable[427]],
	True,
	TestID -> "FreeQ-12"
]

VerificationTest[
	FreeQ[{WolframInstitute`TypeTheory`PackageScope`freeVariable[28285]}, _WolframInstitute`TypeTheory`PackageScope`levelMetavariable],
	True,
	TestID -> "FreeQ-13"
]

VerificationTest[
	FreeQ[{WolframInstitute`TypeTheory`PackageScope`freeVariable[3714]}, WolframInstitute`TypeTheory`PackageScope`constantReference[Alternatives[HoldComplete[Equal]], _]],
	True,
	TestID -> "FreeQ-14"
]

VerificationTest[
	FromDigits["505"],
	505,
	TestID -> "FromDigits-1"
]

VerificationTest[
	1 > 1,
	False,
	TestID -> "Greater-1"
]

VerificationTest[
	Length[{WolframInstitute`TypeTheory`PackageScope`syntaxInteger[2], WolframInstitute`TypeTheory`PackageScope`syntaxInteger[2]}] > 2,
	False,
	TestID -> "Greater-2"
]

VerificationTest[
	1 >= 0,
	True,
	TestID -> "GreaterEqual-1"
]

VerificationTest[
	Last[{WolframInstitute`TypeTheory`PackageScope`levelMetavariable[1502], 0}] >= 1,
	False,
	TestID -> "GreaterEqual-2"
]

VerificationTest[
	1 >= Last[WolframInstitute`TypeTheory`PackageScope`levelSuccessor[WolframInstitute`TypeTheory`PackageScope`levelMetavariable[1709], 1]],
	True,
	TestID -> "GreaterEqual-3"
]

VerificationTest[
	Head[True],
	Symbol,
	TestID -> "Head-1"
]

VerificationTest[
	Head[InputStream["/Users/swish/src/wolfram/TypeTheory/TypeTheory/PacletInfo.wl", 4]],
	InputStream,
	TestID -> "Head-2"
]

VerificationTest[
	HoldCompleteForm[WolframInstitute`TypeTheory`Checking`Environment`Private`$storeTag],
	HoldCompleteForm[WolframInstitute`TypeTheory`Checking`Environment`Private`$storeTag],
	TestID -> "HoldCompleteForm-1"
]

VerificationTest[
	Identity[WolframInstitute`TypeTheory`PackageScope`universeSort[0]],
	WolframInstitute`TypeTheory`PackageScope`universeSort[0],
	TestID -> "Identity-1"
]

VerificationTest[
	If[True, 1, 0],
	1,
	TestID -> "If-1"
]

VerificationTest[
	If[False, 0, 0],
	0,
	TestID -> "If-2"
]

VerificationTest[
	If[True, Return[True]],
	Return[True],
	TestID -> "If-3"
]

VerificationTest[
	If[False, {}, Prepend[{}, 1]],
	{1},
	TestID -> "If-4"
]

VerificationTest[
	If[True, Rest[{1, 1}], {1, 1}],
	{1},
	TestID -> "If-5"
]

VerificationTest[
	If[True, Pick[{}, {}, "Explicit"], {}],
	{},
	TestID -> "If-6"
]

VerificationTest[
	If[1 <= PacletManager`Package`$LogLevel, Print["Rebuilding"]],
	If[1 <= PacletManager`Package`$LogLevel, Print["Rebuilding"]],
	TestID -> "If-7"
]

VerificationTest[
	If[False, Return[PacletManager`Paclet`Private`$$unsafePaclet]],
	Null,
	TestID -> "If-8"
]

VerificationTest[
	If[ListQ[{}] && Length[{}] == Length[{}], Pick[{}, {}, "Explicit"], {}],
	{},
	TestID -> "If-9"
]

VerificationTest[
	If[True, True, Message[SubsetQ::heads, Head[{}], Head[{}], 1, 2]; False],
	True,
	TestID -> "If-10"
]

VerificationTest[
	If[False, First[StringSplit["0.12.4", "+"~~___~~EndOfString]], "0.12.4"],
	"0.12.4",
	TestID -> "If-11"
]

VerificationTest[
	If[StringContainsQ["0.12.4", "+"], First[StringSplit["0.12.4", "+"~~___~~EndOfString]], "0.12.4"],
	"0.12.4",
	TestID -> "If-12"
]

VerificationTest[
	If[True, Last[{HoldComplete["false"], HoldComplete["true"]}], First[{HoldComplete["false"], HoldComplete["true"]}]],
	HoldComplete["true"],
	TestID -> "If-13"
]

VerificationTest[
	If[False, Last[{HoldComplete["false"], HoldComplete["true"]}], First[{HoldComplete["false"], HoldComplete["true"]}]],
	HoldComplete["false"],
	TestID -> "If-14"
]

VerificationTest[
	If[True, HoldComplete[True], Throw[None, WolframInstitute`TypeTheory`Elaboration`Elaboration`Private`$notExplicitTag]],
	HoldComplete[True],
	TestID -> "If-15"
]

VerificationTest[
	If[False, "/Users/swish/src/wolfram/TypeTheory/TypeTheory", ExpandFileName["/Users/swish/src/wolfram/TypeTheory/TypeTheory"]],
	"/Users/swish/src/wolfram/TypeTheory/TypeTheory",
	TestID -> "If-16"
]

VerificationTest[
	If[True, {{WolframInstitute`TypeTheory`PackageScope`levelMetavariable[2403], 1}}, Prepend[{{WolframInstitute`TypeTheory`PackageScope`levelMetavariable[2403], 1}}, 1]],
	{{WolframInstitute`TypeTheory`PackageScope`levelMetavariable[2403], 1}},
	TestID -> "If-17"
]

VerificationTest[
	If[False, {{WolframInstitute`TypeTheory`PackageScope`levelMetavariable[1502], 0}}, Prepend[{{WolframInstitute`TypeTheory`PackageScope`levelMetavariable[1502], 0}}, 1]],
	{1, {WolframInstitute`TypeTheory`PackageScope`levelMetavariable[1502], 0}},
	TestID -> "If-18"
]

VerificationTest[
	If[False, {{{"Kernel", "Root" -> "Kernel", "Context" -> {"WolframInstitute`TypeTheory`"}}}}, {{"Kernel", "Root" -> "Kernel", "Context" -> {"WolframInstitute`TypeTheory`"}}}],
	{{"Kernel", "Root" -> "Kernel", "Context" -> {"WolframInstitute`TypeTheory`"}}},
	TestID -> "If-19"
]

VerificationTest[
	If[MatchQ[First[{WolframInstitute`TypeTheory`PackageScope`universeSort[0], {}}], _WolframInstitute`TypeTheory`PackageScope`freeVariable] || 0 === Length[Last[{WolframInstitute`TypeTheory`PackageScope`universeSort[0], {}}]], 0, 0],
	0,
	TestID -> "If-20"
]

VerificationTest[
	If[AtomQ[{{"Kernel", "Root" -> "Kernel", "Context" -> {"WolframInstitute`TypeTheory`"}}}], {{{"Kernel", "Root" -> "Kernel", "Context" -> {"WolframInstitute`TypeTheory`"}}}}, {{"Kernel", "Root" -> "Kernel", "Context" -> {"WolframInstitute`TypeTheory`"}}}],
	{{"Kernel", "Root" -> "Kernel", "Context" -> {"WolframInstitute`TypeTheory`"}}},
	TestID -> "If-21"
]

VerificationTest[
	If[ListQ[{"Explicit"}] && Length[{"Explicit"}] == Length[{WolframInstitute`TypeTheory`PackageScope`naturalLiteral[2]}], Pick[{WolframInstitute`TypeTheory`PackageScope`naturalLiteral[2]}, {"Explicit"}, "Explicit"], {WolframInstitute`TypeTheory`PackageScope`naturalLiteral[2]}],
	{WolframInstitute`TypeTheory`PackageScope`naturalLiteral[2]},
	TestID -> "If-22"
]

VerificationTest[
	If[StringMatchQ["/Users/swish/src/wolfram/TypeTheory/TypeTheory", "http*:*", IgnoreCase -> True] || StringMatchQ["/Users/swish/src/wolfram/TypeTheory/TypeTheory", "file:*", IgnoreCase -> True], "/Users/swish/src/wolfram/TypeTheory/TypeTheory", ExpandFileName["/Users/swish/src/wolfram/TypeTheory/TypeTheory"]],
	"/Users/swish/src/wolfram/TypeTheory/TypeTheory",
	TestID -> "If-23"
]

VerificationTest[
	If[Length[{<|"Name" -> HoldComplete[Odd], "Type" -> WolframInstitute`TypeTheory`PackageScope`universeSort[1], "Constant" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[Odd], {}], "IndexIds" -> {}, "Context" -> <||>, "Level" -> 1, "Nested" -> None|>}] == 1, HoldForm @@ First[{<|"Name" -> HoldComplete[Odd], "Type" -> WolframInstitute`TypeTheory`PackageScope`universeSort[1], "Constant" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[Odd], {}], "IndexIds" -> {}, "Context" -> <||>, "Level" -> 1, "Nested" -> None|>}]["Name"], Function[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`name, HoldForm @@ WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`name] /@ Lookup[{<|"Name" -> HoldComplete[Odd], "Type" -> WolframInstitute`TypeTheory`PackageScope`universeSort[1], "Constant" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[Odd], {}], "IndexIds" -> {}, "Context" -> <||>, "Level" -> 1, "Nested" -> None|>}, "Name"]],
	HoldForm[Odd],
	TestID -> "If-24"
]

VerificationTest[
	IntegerQ[1],
	True,
	TestID -> "IntegerQ-1"
]

VerificationTest[
	InterpretationBox[TemplateBox[{_, _, "\"Sort\"", TemplateBox[{"\"(\"", TemplateBox[{_, _, "\"max\"", "1", "u"}, "RowWithSeparators"], "\")\""}, "RowDefault"]}, "RowWithSeparators"], _],
	InterpretationBox[TemplateBox[{_, _, "\"Sort\"", TemplateBox[{"\"(\"", TemplateBox[{_, _, "\"max\"", "1", "u"}, "RowWithSeparators"], "\")\""}, "RowDefault"]}, "RowWithSeparators"], _],
	TestID -> "InterpretationBox-1"
]

VerificationTest[
	Intersection[{}, {}],
	{},
	TestID -> "Intersection-1"
]

VerificationTest[
	Join[{}, {}],
	{},
	TestID -> "Join-1"
]

VerificationTest[
	Join[{1}, {1}],
	{1, 1},
	TestID -> "Join-2"
]

VerificationTest[
	Join[{3619}, {}],
	{3619},
	TestID -> "Join-3"
]

VerificationTest[
	Join[{}, {7291}],
	{7291},
	TestID -> "Join-4"
]

VerificationTest[
	Join[{}, {3552}, {}, {}, {3553}],
	{3552, 3553},
	TestID -> "Join-5"
]

VerificationTest[
	Join[{}, {3543}, {3545}, {}, {3544}],
	{3543, 3545, 3544},
	TestID -> "Join-6"
]

VerificationTest[
	Join[{6477}, {6483}, {6485}, {}, {6484}],
	{6477, 6483, 6485, 6484},
	TestID -> "Join-7"
]

VerificationTest[
	Join[HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`w]],
	HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`w],
	TestID -> "Join-8"
]

VerificationTest[
	Join[{HoldComplete[False]}, {HoldComplete[WolframInstitute`TypeTheory`InductiveRecursor[False]]}, {}],
	{HoldComplete[False], HoldComplete[WolframInstitute`TypeTheory`InductiveRecursor[False]]},
	TestID -> "Join-9"
]

VerificationTest[
	Join[Values[{HoldComplete[False] -> WolframInstitute`TypeTheory`PackageScope`universeSort[0]}], Values[{}]],
	{WolframInstitute`TypeTheory`PackageScope`universeSort[0]},
	TestID -> "Join-10"
]

VerificationTest[
	Join[HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`a], HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`b]],
	HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`a, WolframInstitute`TypeTheory`Library`Prelude`Private`b],
	TestID -> "Join-11"
]

VerificationTest[
	Join[HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`P], Join @@ {HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`w]}],
	HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`P, WolframInstitute`TypeTheory`Library`Prelude`Private`w],
	TestID -> "Join-12"
]

VerificationTest[
	Join[{HoldComplete[True]}, {HoldComplete[WolframInstitute`TypeTheory`InductiveRecursor[True]]}, {HoldComplete[WolframInstitute`TypeTheory`TrueIntroduction]}],
	{HoldComplete[True], HoldComplete[WolframInstitute`TypeTheory`InductiveRecursor[True]], HoldComplete[WolframInstitute`TypeTheory`TrueIntroduction]},
	TestID -> "Join-13"
]

VerificationTest[
	Join[HoldComplete[WolframInstitute`TypeTheory`LessEqualStep], HoldComplete[0], HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`k], HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`ih]],
	HoldComplete[WolframInstitute`TypeTheory`LessEqualStep, 0, WolframInstitute`TypeTheory`Library`Prelude`Private`k, WolframInstitute`TypeTheory`Library`Prelude`Private`ih],
	TestID -> "Join-14"
]

VerificationTest[
	Join[{}, <|"Name" -> HoldComplete[True], "Type" -> WolframInstitute`TypeTheory`PackageScope`universeSort[0], "Constant" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[True], {}], "IndexIds" -> {}, "Context" -> <||>, "Level" -> 0, "Nested" -> None|>["IndexIds"]],
	{},
	TestID -> "Join-15"
]

VerificationTest[
	Join[<|"Name" -> HoldComplete[WolframInstitute`TypeTheory`TrueIntroduction], "Type" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[True], {}], "Owner" -> HoldComplete[True], "Original" -> None, "AfterParameters" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[True], {}], "FieldIds" -> {}, "FieldContext" -> <||>, "ConclusionIndices" -> {}, "RecursiveFields" -> {}, "Application" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[WolframInstitute`TypeTheory`TrueIntroduction], {}]|>["FieldIds"], {}],
	{},
	TestID -> "Join-16"
]

VerificationTest[
	Join[{10059}, <|"Name" -> HoldComplete[Chain], "Type" -> WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[\[FormalX]], WolframInstitute`TypeTheory`PackageScope`universeSort[1], WolframInstitute`TypeTheory`PackageScope`universeSort[1], "Explicit"], "Constant" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[Chain], {}], "IndexIds" -> {}, "Context" -> <|10059 -> <|"Name" -> HoldComplete[\[FormalX]], "Type" -> WolframInstitute`TypeTheory`PackageScope`universeSort[1], "Binder" -> "Explicit"|>|>, "Level" -> 1, "Nested" -> None|>["IndexIds"]],
	{10059},
	TestID -> "Join-17"
]

VerificationTest[
	Join[<|"Name" -> HoldComplete[WolframInstitute`TypeTheory`NaturalNumberSuccessor], "Type" -> WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`n], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NonNegativeIntegers], {}], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NonNegativeIntegers], {}], "Explicit"], "Owner" -> HoldComplete[NonNegativeIntegers], "Original" -> None, "AfterParameters" -> WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`n], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NonNegativeIntegers], {}], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NonNegativeIntegers], {}], "Explicit"], "FieldIds" -> {3855}, "FieldContext" -> <|3855 -> <|"Name" -> HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`n], "Binder" -> "Explicit", "Type" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NonNegativeIntegers], {}]|>|>, "ConclusionIndices" -> {}, "RecursiveFields" -> {<|"Id" -> 3855, "Binders" -> {}, "Indices" -> {}, "Target" -> 1, "Context" -> <|3855 -> <|"Name" -> HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`n], "Binder" -> "Explicit", "Type" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NonNegativeIntegers], {}]|>|>|>}, "Application" -> WolframInstitute`TypeTheory`PackageScope`application[WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[WolframInstitute`TypeTheory`NaturalNumberSuccessor], {}], WolframInstitute`TypeTheory`PackageScope`freeVariable[3855]]|>["FieldIds"], {3860}],
	{3855, 3860},
	TestID -> "Join-18"
]

VerificationTest[
	Key[HoldComplete[True]],
	Key[HoldComplete[True]],
	TestID -> "Key-1"
]

VerificationTest[
	Key[WolframInstitute`TypeTheory`PackageScope`boundVariable[0]],
	Key[WolframInstitute`TypeTheory`PackageScope`boundVariable[0]],
	TestID -> "Key-2"
]

VerificationTest[
	Key[{WolframInstitute`TypeTheory`PackageScope`freeVariable[3543], 0}],
	Key[{WolframInstitute`TypeTheory`PackageScope`freeVariable[3543], 0}],
	TestID -> "Key-3"
]

VerificationTest[
	KeyExistsQ[<||>, 836],
	False,
	TestID -> "KeyExistsQ-1"
]

VerificationTest[
	KeyExistsQ[<||>, "Addition"],
	False,
	TestID -> "KeyExistsQ-2"
]

VerificationTest[
	KeyExistsQ[<||>, HoldComplete[True]],
	False,
	TestID -> "KeyExistsQ-3"
]

VerificationTest[
	KeyExistsQ[<|"Type" -> HoldComplete[NonNegativeIntegers], "Zero" -> HoldComplete[WolframInstitute`TypeTheory`NaturalNumberZero], "Successor" -> HoldComplete[WolframInstitute`TypeTheory`NaturalNumberSuccessor], "Operations" -> <||>, "Roles" -> <||>, "Registrations" -> {}|>["Operations"], "Addition"],
	False,
	TestID -> "KeyExistsQ-4"
]

VerificationTest[
	KeyExistsQ[<|"Type" -> HoldComplete[NonNegativeIntegers], "Zero" -> HoldComplete[WolframInstitute`TypeTheory`NaturalNumberZero], "Successor" -> HoldComplete[WolframInstitute`TypeTheory`NaturalNumberSuccessor], "Operations" -> <||>, "Roles" -> <||>, "Registrations" -> {}|>["Roles"], HoldComplete[Plus]],
	False,
	TestID -> "KeyExistsQ-5"
]

VerificationTest[
	Keys[{}],
	{},
	TestID -> "Keys-1"
]

VerificationTest[
	Keys[<||>],
	{},
	TestID -> "Keys-2"
]

VerificationTest[
	Keys[{"RewriteRules" -> True}],
	{"RewriteRules"},
	TestID -> "Keys-3"
]

VerificationTest[
	Keys[<|"Context" -> <|28255 -> <|"Name" -> HoldComplete[a], "Binder" -> "Explicit", "Type" -> WolframInstitute`TypeTheory`PackageScope`universeSort[0]|>, 28256 -> <|"Name" -> HoldComplete[b], "Binder" -> "Explicit", "Type" -> WolframInstitute`TypeTheory`PackageScope`universeSort[0]|>, 28257 -> <|"Name" -> HoldComplete[ha], "Binder" -> "Explicit", "Type" -> WolframInstitute`TypeTheory`PackageScope`freeVariable[28255]|>, 28258 -> <|"Name" -> HoldComplete[hb], "Binder" -> "Explicit", "Type" -> WolframInstitute`TypeTheory`PackageScope`freeVariable[28256]|>|>, "Type" -> WolframInstitute`TypeTheory`PackageScope`freeVariable[28255]|>["Context"]],
	{28255, 28256, 28257, 28258},
	TestID -> "Keys-4"
]

VerificationTest[
	KeyValuePattern["Kind" -> "Constructor" | "Recursor"],
	KeyValuePattern["Kind" -> "Constructor" | "Recursor"],
	TestID -> "KeyValuePattern-1"
]

VerificationTest[
	KeyValuePattern[{"Kind" -> "InductiveType", "Constructors" -> {_}}],
	KeyValuePattern[{"Kind" -> "InductiveType", "Constructors" -> {_}}],
	TestID -> "KeyValuePattern-2"
]

VerificationTest[
	Last[{<||>, {}}],
	{},
	TestID -> "Last-1"
]

VerificationTest[
	Last[HoldComplete[True] -> WolframInstitute`TypeTheory`PackageScope`universeSort[0]],
	WolframInstitute`TypeTheory`PackageScope`universeSort[0],
	TestID -> "Last-2"
]

VerificationTest[
	Last[WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[Equivalent], {}]],
	{},
	TestID -> "Last-3"
]

VerificationTest[
	Length[{}],
	0,
	TestID -> "Length-1"
]

VerificationTest[
	Length[{3716}],
	1,
	TestID -> "Length-2"
]

VerificationTest[
	Length[Unevaluated[{}]],
	0,
	TestID -> "Length-3"
]

VerificationTest[
	LengthWhile[{}, Apply[SameQ]],
	0,
	TestID -> "LengthWhile-1"
]

VerificationTest[
	LengthWhile[Transpose[{Take[{}, 0], Take[{}, 0]}], Apply[SameQ]],
	0,
	TestID -> "LengthWhile-2"
]

VerificationTest[
	LengthWhile[{{WolframInstitute`TypeTheory`PackageScope`freeVariable[4032], WolframInstitute`TypeTheory`PackageScope`freeVariable[4032]}}, Apply[SameQ]],
	1,
	TestID -> "LengthWhile-3"
]

VerificationTest[
	0 < 0,
	False,
	TestID -> "Less-1"
]

VerificationTest[
	{WolframInstitute`TypeTheory`PackageScope`freeVariable[4110], 1}[[2]] < 1,
	False,
	TestID -> "Less-2"
]

VerificationTest[
	0 < 0 + Length[{WolframInstitute`TypeTheory`PackageScope`freeVariable[3546]}],
	True,
	TestID -> "Less-3"
]

VerificationTest[
	Length[{WolframInstitute`TypeTheory`PackageScope`lambdaAbstraction[HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`t], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[Booleans], {}], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[Booleans], {}], "Explicit"], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete["true"], {}], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete["false"], {}], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete["true"], {}]}] < 0 + 1 + 2 + 0 + 1,
	False,
	TestID -> "Less-4"
]

VerificationTest[
	1 <= 0,
	False,
	TestID -> "LessEqual-1"
]

VerificationTest[
	1 <= PacletManager`Package`$LogLevel,
	1 <= PacletManager`Package`$LogLevel,
	TestID -> "LessEqual-2"
]

VerificationTest[
	First[{1}] <= Length[{HoldComplete[True]}],
	True,
	TestID -> "LessEqual-3"
]

VerificationTest[
	1 <= Max[Replace[{1}, {WolframInstitute`TypeTheory`Terms`CoreTerms`Private`m_Integer :> WolframInstitute`TypeTheory`Terms`CoreTerms`Private`m, {_, WolframInstitute`TypeTheory`Terms`CoreTerms`Private`offset_} :> WolframInstitute`TypeTheory`Terms`CoreTerms`Private`offset}, {1}]],
	True,
	TestID -> "LessEqual-4"
]

VerificationTest[
	ListQ[{}],
	True,
	TestID -> "ListQ-1"
]

VerificationTest[
	ListQ[Null],
	False,
	TestID -> "ListQ-2"
]

VerificationTest[
	ListQ[{"Explicit"}],
	True,
	TestID -> "ListQ-3"
]

VerificationTest[
	Literal[_String -> _PacletObject],
	Literal[_String -> _PacletObject],
	TestID -> "Literal-1"
]

VerificationTest[
	Lookup[<||>, {}],
	{},
	TestID -> "Lookup-1"
]

VerificationTest[
	Lookup[Values[<||>], "Name", {}],
	{},
	TestID -> "Lookup-2"
]

VerificationTest[
	Lookup[<|"Name" -> "CalculusOfInductiveConstructions", "Prop" -> True, "RewriteRules" -> False|>, "Prop", Missing["NotAvailable", "Prop"]],
	True,
	TestID -> "Lookup-3"
]

VerificationTest[
	Lookup[<|HoldComplete[WolframInstitute`TypeTheory`Library`HomotopyTypeTheory`Private`u] -> 0|>, {HoldComplete[WolframInstitute`TypeTheory`Library`HomotopyTypeTheory`Private`u]}],
	{0},
	TestID -> "Lookup-4"
]

VerificationTest[
	Lookup[Lookup[<|7107 -> <|"Name" -> HoldComplete[A], "Type" -> WolframInstitute`TypeTheory`PackageScope`universeSort[1], "Binder" -> "Implicit"|>|>, 7107, Association[]], "Name", HoldComplete[WolframInstitute`TypeTheory`Terms`SurfaceSyntax`Private`x]],
	HoldComplete[A],
	TestID -> "Lookup-5"
]

VerificationTest[
	Lookup[{<|"Name" -> HoldComplete[True], "Type" -> WolframInstitute`TypeTheory`PackageScope`universeSort[0], "Constant" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[True], {}], "IndexIds" -> {}, "Context" -> <||>, "Level" -> 0, "Nested" -> None|>}, "Name"],
	{HoldComplete[True]},
	TestID -> "Lookup-6"
]

VerificationTest[
	Lookup[<|"Type" -> HoldComplete[NonNegativeIntegers], "Zero" -> HoldComplete[WolframInstitute`TypeTheory`NaturalNumberZero], "Successor" -> HoldComplete[WolframInstitute`TypeTheory`NaturalNumberSuccessor], "Operations" -> <|"Addition" -> HoldComplete[Plus], "Subtraction" -> HoldComplete[Subtract], "Multiplication" -> HoldComplete[Times], "Power" -> HoldComplete[Power]|>, "Roles" -> <|HoldComplete[Plus] -> "Addition", HoldComplete[Subtract] -> "Subtraction", HoldComplete[Times] -> "Multiplication", HoldComplete[Power] -> "Power"|>, "Registrations" -> {{"Addition"}, {"Subtraction", "Multiplication", "Power"}}|>["Operations"], First[<|"Type" -> HoldComplete[NonNegativeIntegers], "Zero" -> HoldComplete[WolframInstitute`TypeTheory`NaturalNumberZero], "Successor" -> HoldComplete[WolframInstitute`TypeTheory`NaturalNumberSuccessor], "Operations" -> <|"Addition" -> HoldComplete[Plus], "Subtraction" -> HoldComplete[Subtract], "Multiplication" -> HoldComplete[Times], "Power" -> HoldComplete[Power]|>, "Roles" -> <|HoldComplete[Plus] -> "Addition", HoldComplete[Subtract] -> "Subtraction", HoldComplete[Times] -> "Multiplication", HoldComplete[Power] -> "Power"|>, "Registrations" -> {{"Addition"}, {"Subtraction", "Multiplication", "Power"}}|>["Registrations"]]],
	{HoldComplete[Plus]},
	TestID -> "Lookup-7"
]

VerificationTest[
	HoldComplete /@ Unevaluated[{}],
	{},
	TestID -> "Map-1"
]

VerificationTest[
	WolframInstitute`TypeTheory`PackageScope`freeVariable /@ {},
	{},
	TestID -> "Map-2"
]

VerificationTest[
	WolframInstitute`TypeTheory`PackageScope`freeVariable /@ {3544},
	{WolframInstitute`TypeTheory`PackageScope`freeVariable[3544]},
	TestID -> "Map-3"
]

VerificationTest[
	(FileNames[{"PacletInfo.m", "PacletInfo.wl"}, #1, 2] & ) /@ {"/Users/swish/src/wolfram/TypeTheory/TypeTheory", "/Users/swish/src/wolfram/TypeTheory"},
	{{"/Users/swish/src/wolfram/TypeTheory/TypeTheory/PacletInfo.wl"}, {"/Users/swish/src/wolfram/TypeTheory/TypeTheory/PacletInfo.wl"}},
	TestID -> "Map-4"
]

VerificationTest[
	Function[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`constructor, WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`constructor["FieldContext"]] /@ {},
	{},
	TestID -> "Map-5"
]

VerificationTest[
	Replace[{(PacletManager`Paclet`Private`name_)?StringQ, Association[PacletManager`Paclet`Private`options___]} :> {PacletManager`Paclet`Private`name, PacletManager`Paclet`Private`options}] /@ {{"Kernel", "Root" -> "Kernel", "Context" -> {"WolframInstitute`TypeTheory`"}}, {"Documentation", "Language" -> "English", "MainPage" -> "Guides/TypeTheory"}, {"Test", "Root" -> "Tests", "Method" -> "Experimental-v1"}},
	{{"Kernel", "Root" -> "Kernel", "Context" -> {"WolframInstitute`TypeTheory`"}}, {"Documentation", "Language" -> "English", "MainPage" -> "Guides/TypeTheory"}, {"Test", "Root" -> "Tests", "Method" -> "Experimental-v1"}},
	TestID -> "Map-6"
]

VerificationTest[
	List @@@ {},
	{},
	TestID -> "MapApply-1"
]

VerificationTest[
	List @@@ {WolframInstitute`TypeTheory`PackageScope`levelMetavariable[1502] -> 0},
	{{WolframInstitute`TypeTheory`PackageScope`levelMetavariable[1502], 0}},
	TestID -> "MapApply-2"
]

VerificationTest[
	MatchQ[{}, {"Explicit"...}],
	True,
	TestID -> "MatchQ-1"
]

VerificationTest[
	MatchQ[{"Explicit"}, {"Explicit"...}],
	True,
	TestID -> "MatchQ-2"
]

VerificationTest[
	MatchQ["InductiveType", "Constructor" | "Recursor"],
	False,
	TestID -> "MatchQ-3"
]

VerificationTest[
	MatchQ[HoldComplete[True], HoldComplete[True | False]],
	True,
	TestID -> "MatchQ-4"
]

VerificationTest[
	MatchQ[1, _WolframInstitute`TypeTheory`PackageScope`levelMetavariable],
	False,
	TestID -> "MatchQ-5"
]

VerificationTest[
	MatchQ[WolframInstitute`TypeTheory`Library`Prelude`Private`u, _Symbol | _String],
	True,
	TestID -> "MatchQ-6"
]

VerificationTest[
	MatchQ[WolframInstitute`TypeTheory`PackageScope`universeSort[2], WolframInstitute`TypeTheory`PackageScope`universeSort[0]],
	False,
	TestID -> "MatchQ-7"
]

VerificationTest[
	MatchQ[1, WolframInstitute`TypeTheory`PackageScope`levelSuccessor[_WolframInstitute`TypeTheory`PackageScope`levelMetavariable, _]],
	False,
	TestID -> "MatchQ-8"
]

VerificationTest[
	MatchQ[WolframInstitute`TypeTheory`PackageScope`levelMetavariable[836], _WolframInstitute`TypeTheory`PackageScope`levelMetavariable],
	True,
	TestID -> "MatchQ-9"
]

VerificationTest[
	MatchQ[Hold[Null], EndOfFile | $Failed | Hold[_PacletManager`Paclet`Private`Paclet] | Hold[_PacletManager`Paclet`Private`PacletGroup] | Hold[_PacletSite] | Hold[_PacletObject]],
	False,
	TestID -> "MatchQ-10"
]

VerificationTest[
	MatchQ[Last[{WolframInstitute`TypeTheory`PackageScope`metavariable[748], {WolframInstitute`TypeTheory`PackageScope`freeVariable[6646]}}], {__WolframInstitute`TypeTheory`PackageScope`freeVariable}],
	True,
	TestID -> "MatchQ-11"
]

VerificationTest[
	MatchQ[<|"Placeholder" -> WolframInstitute`TypeTheory`PackageScope`metavariable[914], "Name" -> HoldComplete[True], "Arguments" -> {}, "Syntax" -> WolframInstitute`TypeTheory`PackageScope`syntaxSymbol[HoldComplete[True]]|>["Name"], HoldComplete[Not | And | Or]],
	False,
	TestID -> "MatchQ-12"
]

VerificationTest[
	MatchQ[<|"MessageTemplate" -> "`1` could be a proposition or a Boolean here: write `2` for the Boolean, or Typed[`1`, TypeUniverse[0]] for the proposition.", "MessageParameters" -> {HoldForm[True], "true"}|>, KeyValuePattern[{(Rule | RuleDelayed)["MessageTemplate", _String | _MessageName | _TemplateObject | _StringTemplate]}]],
	True,
	TestID -> "MatchQ-13"
]

VerificationTest[
	MatchQ[{WolframInstitute`TypeTheory`PackageScope`naturalLiteral[4], WolframInstitute`TypeTheory`PackageScope`naturalLiteral[5]}, {_WolframInstitute`TypeTheory`PackageScope`dependentFunctionType, _WolframInstitute`TypeTheory`PackageScope`dependentFunctionType} | {_WolframInstitute`TypeTheory`PackageScope`lambdaAbstraction, _WolframInstitute`TypeTheory`PackageScope`lambdaAbstraction}],
	False,
	TestID -> "MatchQ-14"
]

VerificationTest[
	Max[{1}],
	1,
	TestID -> "Max-1"
]

VerificationTest[
	Max[0, 1],
	1,
	TestID -> "Max-2"
]

VerificationTest[
	Max[0, {}],
	0,
	TestID -> "Max-3"
]

VerificationTest[
	Max[0, {0}],
	0,
	TestID -> "Max-4"
]

VerificationTest[
	Max[Length[{}], 1],
	1,
	TestID -> "Max-5"
]

VerificationTest[
	Max[0, Cases[{1, 1}, _Integer]],
	1,
	TestID -> "Max-6"
]

VerificationTest[
	Max[Replace[{1}, {WolframInstitute`TypeTheory`Terms`CoreTerms`Private`m_Integer :> WolframInstitute`TypeTheory`Terms`CoreTerms`Private`m, {_, WolframInstitute`TypeTheory`Terms`CoreTerms`Private`offset_} :> WolframInstitute`TypeTheory`Terms`CoreTerms`Private`offset}, {1}]],
	1,
	TestID -> "Max-7"
]

VerificationTest[
	MemberQ[{}, "u"],
	False,
	TestID -> "MemberQ-1"
]

VerificationTest[
	MemberQ[{"u"}, "u"],
	True,
	TestID -> "MemberQ-2"
]

VerificationTest[
	MemberQ[{}, HoldComplete[u]],
	False,
	TestID -> "MemberQ-3"
]

VerificationTest[
	MemberQ[{}, {Verbatim[HoldComplete[Equal]], _}],
	False,
	TestID -> "MemberQ-4"
]

VerificationTest[
	MemberQ[{HoldComplete[True]}, HoldComplete[True]],
	True,
	TestID -> "MemberQ-5"
]

VerificationTest[
	MemberQ[{}, WolframInstitute`TypeTheory`PackageScope`freeVariable[3775]],
	False,
	TestID -> "MemberQ-6"
]

VerificationTest[
	MemberQ[{WolframInstitute`TypeTheory`PackageScope`freeVariable[7465]}, WolframInstitute`TypeTheory`PackageScope`freeVariable[7465]],
	True,
	TestID -> "MemberQ-7"
]

VerificationTest[
	MemberQ[{{"Wolfram__Chatbook-2.5.148", "/Applications/Wolfram 15.0.app/Contents/SystemFiles/Components/Chatbook"}}, {"WolframInstitute__TypeTheory-0.12.4", "/Users/swish/src/wolfram/TypeTheory/TypeTheory"}],
	False,
	TestID -> "MemberQ-8"
]

VerificationTest[
	MemberQ[<|"Name" -> HoldComplete[WolframInstitute`TypeTheory`NonemptyIntroduction], "Type" -> WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`\[Alpha]], WolframInstitute`TypeTheory`PackageScope`universeSort[WolframInstitute`TypeTheory`PackageScope`levelParameter[HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`u]]], WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`x], WolframInstitute`TypeTheory`PackageScope`boundVariable[0], WolframInstitute`TypeTheory`PackageScope`application[WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[WolframInstitute`TypeTheory`Nonempty], {WolframInstitute`TypeTheory`PackageScope`levelParameter[HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`u]]}], WolframInstitute`TypeTheory`PackageScope`boundVariable[1]], "Explicit"], "Implicit"], "Owner" -> HoldComplete[WolframInstitute`TypeTheory`Nonempty], "Original" -> None, "AfterParameters" -> WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`x], WolframInstitute`TypeTheory`PackageScope`freeVariable[6477], WolframInstitute`TypeTheory`PackageScope`application[WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[WolframInstitute`TypeTheory`Nonempty], {WolframInstitute`TypeTheory`PackageScope`levelParameter[HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`u]]}], WolframInstitute`TypeTheory`PackageScope`freeVariable[6477]], "Explicit"], "FieldIds" -> {6482}, "FieldContext" -> <|6477 -> <|"Name" -> HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`\[Alpha]], "Type" -> WolframInstitute`TypeTheory`PackageScope`universeSort[WolframInstitute`TypeTheory`PackageScope`levelParameter[HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`u]]], "Binder" -> "Explicit"|>, 6482 -> <|"Name" -> HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`x], "Type" -> WolframInstitute`TypeTheory`PackageScope`freeVariable[6477], "Binder" -> "Explicit"|>|>, "ConclusionIndices" -> {}, "RecursiveFields" -> {}|>["ConclusionIndices"], WolframInstitute`TypeTheory`PackageScope`freeVariable[6482]],
	False,
	TestID -> "MemberQ-9"
]

VerificationTest[
	Min[0, 0],
	0,
	TestID -> "Min-1"
]

VerificationTest[
	Min[0, {}, {}],
	0,
	TestID -> "Min-2"
]

VerificationTest[
	Min[0, {}, {0}],
	0,
	TestID -> "Min-3"
]

VerificationTest[
	Min[0, {0}, {0, 0}],
	0,
	TestID -> "Min-4"
]

VerificationTest[
	Min[Length[{}], Length[{}]],
	0,
	TestID -> "Min-5"
]

VerificationTest[
	Most[{WolframInstitute`TypeTheory`PackageScope`syntaxSymbol[HoldComplete[True]], WolframInstitute`TypeTheory`PackageScope`syntaxSymbol[HoldComplete[True]]}],
	{WolframInstitute`TypeTheory`PackageScope`syntaxSymbol[HoldComplete[True]]},
	TestID -> "Most-1"
]

VerificationTest[
	Negative[1],
	False,
	TestID -> "Negative-1"
]

VerificationTest[
	NonNegative[0],
	True,
	TestID -> "NonNegative-1"
]

VerificationTest[
	Normal[<||>],
	{},
	TestID -> "Normal-1"
]

VerificationTest[
	Normal[GroupBy[Cases[{1, 1}, {_, _}], First -> Last, Max]],
	{},
	TestID -> "Normal-2"
]

VerificationTest[
	 !True,
	False,
	TestID -> "Not-1"
]

VerificationTest[
	 !False,
	True,
	TestID -> "Not-2"
]

VerificationTest[
	 !DuplicateFreeQ[{}],
	False,
	TestID -> "Not-3"
]

VerificationTest[
	True === True || True === False,
	True,
	TestID -> "Or-1"
]

VerificationTest[
	PadRight[{"13", "5"}, 2, "0"],
	{"13", "5"},
	TestID -> "PadRight-1"
]

VerificationTest[
	{3543}[[1]],
	3543,
	TestID -> "Part-1"
]

VerificationTest[
	{6646}[[-1*1]],
	6646,
	TestID -> "Part-2"
]

VerificationTest[
	Last[{WolframInstitute`TypeTheory`PackageScope`freeVariable[6638], {WolframInstitute`TypeTheory`PackageScope`freeVariable[6646]}}][[-1*1]],
	WolframInstitute`TypeTheory`PackageScope`freeVariable[6646],
	TestID -> "Part-3"
]

VerificationTest[
	Success["EnvironmentChecked", <|"MessageTemplate" -> "All `1` constants of the environment check again from their declarations.", "MessageParameters" -> {110}, "Constants" -> 110|>][[1]],
	"EnvironmentChecked",
	TestID -> "Part-4"
]

VerificationTest[
	{WolframInstitute`TypeTheory`PackageScope`lambdaAbstraction[HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`x], WolframInstitute`TypeTheory`PackageScope`universeSort[0], WolframInstitute`TypeTheory`PackageScope`boundVariable[0], "Explicit"], 0}[[1,3]],
	WolframInstitute`TypeTheory`PackageScope`boundVariable[0],
	TestID -> "Part-5"
]

VerificationTest[
	Pick[{}, {}, "Explicit"],
	{},
	TestID -> "Pick-1"
]

VerificationTest[
	Pick[{WolframInstitute`TypeTheory`PackageScope`naturalLiteral[2]}, {"Explicit"}, "Explicit"],
	{WolframInstitute`TypeTheory`PackageScope`naturalLiteral[2]},
	TestID -> "Pick-2"
]

VerificationTest[
	0 + 1,
	1,
	TestID -> "Plus-1"
]

VerificationTest[
	0 - 0,
	0,
	TestID -> "Plus-2"
]

VerificationTest[
	1 + v,
	1 + v,
	TestID -> "Plus-3"
]

VerificationTest[
	v + 1,
	1 + v,
	TestID -> "Plus-4"
]

VerificationTest[
	0 + 0 + 1,
	1,
	TestID -> "Plus-5"
]

VerificationTest[
	0 - 0 + 1,
	1,
	TestID -> "Plus-6"
]

VerificationTest[
	Length[{}] + 1,
	1,
	TestID -> "Plus-7"
]

VerificationTest[
	0 + 1 + 2 + 0 + 1,
	4,
	TestID -> "Plus-8"
]

VerificationTest[
	First[{2}] - Length[{HoldComplete[Rose]}],
	1,
	TestID -> "Plus-9"
]

VerificationTest[
	Position[{13, 17}, 1],
	{},
	TestID -> "Position-1"
]

VerificationTest[
	Position[{13, 17}, First[{1}]],
	{},
	TestID -> "Position-2"
]

VerificationTest[
	Position[{HoldComplete[True], HoldComplete[False], HoldComplete[Not], HoldComplete[And], HoldComplete[Or], HoldComplete[Equivalent], HoldComplete[Equal], HoldComplete[Exists], HoldComplete[Unequal], HoldComplete[Identity], HoldComplete[Composition], HoldComplete[NonNegativeIntegers], HoldComplete[Plus], HoldComplete[WolframInstitute`TypeTheory`NaturalNumberPredecessor], HoldComplete[Subtract], HoldComplete[Times], HoldComplete[Power], HoldComplete[LessEqual], HoldComplete[Less], HoldComplete[GreaterEqual], HoldComplete[Greater], HoldComplete[WolframInstitute`TypeTheory`FalseElimination], HoldComplete[WolframInstitute`TypeTheory`AndEliminationLeft], HoldComplete[WolframInstitute`TypeTheory`AndEliminationRight], HoldComplete[WolframInstitute`TypeTheory`EqualitySymmetry], HoldComplete[WolframInstitute`TypeTheory`EqualityTransitivity], HoldComplete[WolframInstitute`TypeTheory`EqualityCongruence], HoldComplete[WolframInstitute`TypeTheory`EqualitySubstitution], HoldComplete[WolframInstitute`TypeTheory`EquivalentForward], HoldComplete[WolframInstitute`TypeTheory`EquivalentBackward], HoldComplete[WolframInstitute`TypeTheory`EquivalentReflexivity], HoldComplete[WolframInstitute`TypeTheory`EquivalentSymmetry], HoldComplete[WolframInstitute`TypeTheory`EquivalentTransitivity], HoldComplete[WolframInstitute`TypeTheory`AdditionZeroRight], HoldComplete[WolframInstitute`TypeTheory`AdditionZeroLeft], HoldComplete[WolframInstitute`TypeTheory`AdditionSuccessorRight], HoldComplete[WolframInstitute`TypeTheory`AdditionSuccessorLeft], HoldComplete[WolframInstitute`TypeTheory`AdditionCommutativity], HoldComplete[WolframInstitute`TypeTheory`AdditionAssociativity], HoldComplete[WolframInstitute`TypeTheory`MultiplicationZeroRight], HoldComplete[WolframInstitute`TypeTheory`MultiplicationZeroLeft], HoldComplete[WolframInstitute`TypeTheory`MultiplicationSuccessorRight], HoldComplete[WolframInstitute`TypeTheory`MultiplicationOneRight], HoldComplete[WolframInstitute`TypeTheory`MultiplicationOneLeft], HoldComplete[WolframInstitute`TypeTheory`MultiplicationSuccessorLeft], HoldComplete[WolframInstitute`TypeTheory`MultiplicationCommutativity], HoldComplete[WolframInstitute`TypeTheory`MultiplicationDistributivityLeft], HoldComplete[WolframInstitute`TypeTheory`MultiplicationDistributivityRight], HoldComplete[WolframInstitute`TypeTheory`MultiplicationAssociativity], HoldComplete[WolframInstitute`TypeTheory`SuccessorInjectivity], HoldComplete[WolframInstitute`TypeTheory`SuccessorNotZero], HoldComplete[WolframInstitute`TypeTheory`SubtractionZeroRight], HoldComplete[WolframInstitute`TypeTheory`SubtractionZeroLeft], HoldComplete[WolframInstitute`TypeTheory`SubtractionSuccessor], HoldComplete[WolframInstitute`TypeTheory`SubtractionSelf], HoldComplete[WolframInstitute`TypeTheory`AdditionSubtractionCancellation], HoldComplete[WolframInstitute`TypeTheory`PowerZero], HoldComplete[WolframInstitute`TypeTheory`PowerSuccessor], HoldComplete[WolframInstitute`TypeTheory`PowerOne], HoldComplete[WolframInstitute`TypeTheory`PowerAddition], HoldComplete[WolframInstitute`TypeTheory`PredecessorLessEqual], HoldComplete[WolframInstitute`TypeTheory`LessEqualZero], HoldComplete[WolframInstitute`TypeTheory`LessEqualSuccessor], HoldComplete[WolframInstitute`TypeTheory`LessEqualTransitivity], HoldComplete[WolframInstitute`TypeTheory`LessEqualAddition], HoldComplete[WolframInstitute`TypeTheory`SuccessorNotLessEqualZero], HoldComplete[WolframInstitute`TypeTheory`LessEqualPredecessor], HoldComplete[WolframInstitute`TypeTheory`LessIrreflexivity], HoldComplete[WolframInstitute`TypeTheory`LessEqualAntisymmetry], HoldComplete[Booleans], HoldComplete["not"], HoldComplete["and"], HoldComplete["or"], HoldComplete[WolframInstitute`TypeTheory`Nonempty], HoldComplete[WolframInstitute`TypeTheory`Subtype], HoldComplete[WolframInstitute`TypeTheory`PropositionalExtensionality], HoldComplete[WolframInstitute`TypeTheory`FunctionExtensionality], HoldComplete[WolframInstitute`TypeTheory`Choice], HoldComplete[WolframInstitute`TypeTheory`ChosenWitness], HoldComplete[WolframInstitute`TypeTheory`ChosenWitnessProperty], HoldComplete[WolframInstitute`TypeTheory`ExcludedMiddle], HoldComplete[WolframInstitute`TypeTheory`DoubleNegationElimination], HoldComplete[NaturalNumberEqual]}, Alternatives[HoldComplete[NaturalNumberEqual]], {1}],
	{{83}},
	TestID -> "Position-3"
]

VerificationTest[
	Positive[1],
	True,
	TestID -> "Positive-1"
]

VerificationTest[
	2^64,
	18446744073709551616,
	TestID -> "Power-1"
]

VerificationTest[
	Prepend[{}, 1],
	{1},
	TestID -> "Prepend-1"
]

VerificationTest[
	Prepend[{4538}, 4539],
	{4539, 4538},
	TestID -> "Prepend-2"
]

VerificationTest[
	Prepend[{}, "Explicit"],
	{"Explicit"},
	TestID -> "Prepend-3"
]

VerificationTest[
	Prepend[{"Explicit"}, "Explicit"],
	{"Explicit", "Explicit"},
	TestID -> "Prepend-4"
]

VerificationTest[
	Prepend[{}, WolframInstitute`TypeTheory`PackageScope`freeVariable[3565]],
	{WolframInstitute`TypeTheory`PackageScope`freeVariable[3565]},
	TestID -> "Prepend-5"
]

VerificationTest[
	Prepend[{}, HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`u]],
	{HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`u]},
	TestID -> "Prepend-6"
]

VerificationTest[
	Prepend[{WolframInstitute`TypeTheory`PackageScope`freeVariable[3565]}, WolframInstitute`TypeTheory`PackageScope`freeVariable[3564]],
	{WolframInstitute`TypeTheory`PackageScope`freeVariable[3564], WolframInstitute`TypeTheory`PackageScope`freeVariable[3565]},
	TestID -> "Prepend-7"
]

VerificationTest[
	Prepend[{}, {HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`a], WolframInstitute`TypeTheory`PackageScope`universeSort[0]}],
	{{HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`a], WolframInstitute`TypeTheory`PackageScope`universeSort[0]}},
	TestID -> "Prepend-8"
]

VerificationTest[
	Prepend[{HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`u]}, HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`v]],
	{HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`v], HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`u]},
	TestID -> "Prepend-9"
]

VerificationTest[
	Prepend[{{HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`a], WolframInstitute`TypeTheory`PackageScope`universeSort[0]}}, {HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`b], WolframInstitute`TypeTheory`PackageScope`universeSort[0]}],
	{{HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`b], WolframInstitute`TypeTheory`PackageScope`universeSort[0]}, {HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`a], WolframInstitute`TypeTheory`PackageScope`universeSort[0]}},
	TestID -> "Prepend-10"
]

VerificationTest[
	Range[1],
	{1},
	TestID -> "Range-1"
]

VerificationTest[
	Range[0, -1],
	{},
	TestID -> "Range-2"
]

VerificationTest[
	Range[0, 0 - 1],
	{},
	TestID -> "Range-3"
]

VerificationTest[
	Range[-1, 0, -1],
	{},
	TestID -> "Range-4"
]

VerificationTest[
	Range[Length[{}] + 1],
	{1},
	TestID -> "Range-5"
]

VerificationTest[
	RegularExpression["^[0-9]+(\\.[0-9]*)*(\\-.+)*(\\+.+)*$"],
	RegularExpression["^[0-9]+(\\.[0-9]*)*(\\-.+)*(\\+.+)*$"],
	TestID -> "RegularExpression-1"
]

VerificationTest[
	ReleaseHold[HoldComplete[Unit]],
	Unit,
	TestID -> "ReleaseHold-1"
]

VerificationTest[
	(_String -> _String | _Symbol | _List)..,
	(_String -> _String | _Symbol | _List)..,
	TestID -> "Repeated-1"
]

VerificationTest[
	Replace[None, None :> HoldComplete[True]],
	HoldComplete[True],
	TestID -> "Replace-1"
]

VerificationTest[
	Replace[HoldComplete[tree], Automatic -> HoldComplete[tree]],
	HoldComplete[tree],
	TestID -> "Replace-2"
]

VerificationTest[
	Replace[HoldComplete[A], HoldComplete[Null] -> HoldComplete[WolframInstitute`TypeTheory`Terms`SurfaceSyntax`Private`x]],
	HoldComplete[A],
	TestID -> "Replace-3"
]

VerificationTest[
	Replace[ForAll, {ForAll -> WolframInstitute`TypeTheory`PackageScope`dependentFunctionType, Function -> WolframInstitute`TypeTheory`PackageScope`lambdaAbstraction}],
	WolframInstitute`TypeTheory`PackageScope`dependentFunctionType,
	TestID -> "Replace-4"
]

VerificationTest[
	Replace[{"WolframInstitute`TypeTheory`"}, {PacletManager`Paclet`Private`ctxt_String, PacletManager`Paclet`Private`path_String} :> PacletManager`Paclet`Private`ctxt, {1}],
	{"WolframInstitute`TypeTheory`"},
	TestID -> "Replace-5"
]

VerificationTest[
	Replace[{(PacletManager`Paclet`Private`name_)?StringQ, Association[PacletManager`Paclet`Private`options___]} :> {PacletManager`Paclet`Private`name, PacletManager`Paclet`Private`options}],
	Replace[{(PacletManager`Paclet`Private`name_)?StringQ, Association[PacletManager`Paclet`Private`options___]} :> {PacletManager`Paclet`Private`name, PacletManager`Paclet`Private`options}],
	TestID -> "Replace-6"
]

VerificationTest[
	Replace[{}, {{WolframInstitute`TypeTheory`Elaboration`Elaboration`Private`only_} :> WolframInstitute`TypeTheory`Elaboration`Elaboration`Private`only, {} :> HoldComplete[True], _ :> None}],
	HoldComplete[True],
	TestID -> "Replace-7"
]

VerificationTest[
	Replace[{HoldComplete[Not]}, {{WolframInstitute`TypeTheory`Elaboration`Elaboration`Private`only_} :> WolframInstitute`TypeTheory`Elaboration`Elaboration`Private`only, {} :> HoldComplete[Not], _ :> None}],
	HoldComplete[Not],
	TestID -> "Replace-8"
]

VerificationTest[
	Replace[WolframInstitute`TypeTheory`PackageScope`universeSort[0], {_WolframInstitute`TypeTheory`PackageScope`universeSort :> HoldComplete[Not], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[Booleans], {}] :> HoldComplete["not"], _ :> None}],
	HoldComplete[Not],
	TestID -> "Replace-9"
]

VerificationTest[
	Replace[{1}, {WolframInstitute`TypeTheory`Terms`CoreTerms`Private`m_Integer :> WolframInstitute`TypeTheory`Terms`CoreTerms`Private`m, {_, WolframInstitute`TypeTheory`Terms`CoreTerms`Private`offset_} :> WolframInstitute`TypeTheory`Terms`CoreTerms`Private`offset}, {1}],
	{1},
	TestID -> "Replace-10"
]

VerificationTest[
	Replace[None, {HoldComplete[WolframInstitute`TypeTheory`Elaboration`Elaboration`Private`constant_] :> HoldComplete[WolframInstitute`TypeTheory`InductiveRecursor[WolframInstitute`TypeTheory`Elaboration`Elaboration`Private`constant]], None :> HoldComplete[WolframInstitute`TypeTheory`InductiveRecursor[NonNegativeIntegers]]}],
	HoldComplete[WolframInstitute`TypeTheory`InductiveRecursor[NonNegativeIntegers]],
	TestID -> "Replace-11"
]

VerificationTest[
	Replace[Join[HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`P], Join @@ {HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`w]}], HoldComplete[WolframInstitute`TypeTheory`Terms`SurfaceSyntax`Private`function_, WolframInstitute`TypeTheory`Terms`SurfaceSyntax`Private`arguments___] :> HoldComplete[WolframInstitute`TypeTheory`Terms`SurfaceSyntax`Private`function[WolframInstitute`TypeTheory`Terms`SurfaceSyntax`Private`arguments]]],
	HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`P[WolframInstitute`TypeTheory`Library`Prelude`Private`w]],
	TestID -> "Replace-12"
]

VerificationTest[
	Replace[<|"Type" -> HoldComplete[NonNegativeIntegers], "Zero" -> HoldComplete[WolframInstitute`TypeTheory`NaturalNumberZero], "Successor" -> HoldComplete[WolframInstitute`TypeTheory`NaturalNumberSuccessor], "Operations" -> <|"Addition" -> HoldComplete[Plus]|>, "Roles" -> <|HoldComplete[Plus] -> "Addition"|>, "Registrations" -> {{"Addition"}}|>, {WolframInstitute`TypeTheory`Checking`Queries`Private`registered_Association :> Length[WolframInstitute`TypeTheory`Checking`Queries`Private`registered["Registrations"]] + 1, None -> 1}],
	2,
	TestID -> "Replace-13"
]

VerificationTest[
	Replace[HoldComplete[ChainEmpty], None :> <|"Name" -> HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`nestedAuxiliary[HoldComplete[Rose], 1, First[{1}]]], "Type" -> None, "Owner" -> HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`nestedAuxiliary[HoldComplete[Rose], 1]], "Original" -> HoldComplete[ChainEmpty], "AfterParameters" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`nestedAuxiliary[HoldComplete[Rose], 1]], {}]|>["Name"]],
	HoldComplete[ChainEmpty],
	TestID -> "Replace-14"
]

VerificationTest[
	Replace[{HoldPattern[PacletObject[PacletManager`Paclet`Private`assoc0:KeyValuePattern[{"Extensions" -> (PacletManager`Paclet`Private`extensions0_)?ListQ}]]] :> Module[{PacletManager`Paclet`Private`extensions = PacletManager`Paclet`Private`extensions0}, PacletManager`Paclet`Private`extensions = Replace[{(PacletManager`Paclet`Private`name_)?StringQ, Association[PacletManager`Paclet`Private`options___]} :> {PacletManager`Paclet`Private`name, PacletManager`Paclet`Private`options}] /@ PacletManager`Paclet`Private`extensions; PacletObject[Join[PacletManager`Paclet`Private`assoc0, Association["Extensions" -> PacletManager`Paclet`Private`extensions]]]]}],
	Replace[{HoldPattern[PacletObject[PacletManager`Paclet`Private`assoc0:KeyValuePattern[{"Extensions" -> (PacletManager`Paclet`Private`extensions0_)?ListQ}]]] :> Module[{PacletManager`Paclet`Private`extensions = PacletManager`Paclet`Private`extensions0}, PacletManager`Paclet`Private`extensions = Replace[{(PacletManager`Paclet`Private`name_)?StringQ, Association[PacletManager`Paclet`Private`options___]} :> {PacletManager`Paclet`Private`name, PacletManager`Paclet`Private`options}] /@ PacletManager`Paclet`Private`extensions; PacletObject[Join[PacletManager`Paclet`Private`assoc0, Association["Extensions" -> PacletManager`Paclet`Private`extensions]]]]}],
	TestID -> "Replace-15"
]

VerificationTest[
	Replace[<|"Name" -> HoldComplete[WolframInstitute`TypeTheory`TrueIntroduction], "Type" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[True], {}], "Owner" -> HoldComplete[True], "Original" -> None, "AfterParameters" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[True], {}]|>["Original"], None :> <|"Name" -> HoldComplete[WolframInstitute`TypeTheory`TrueIntroduction], "Type" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[True], {}], "Owner" -> HoldComplete[True], "Original" -> None, "AfterParameters" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[True], {}]|>["Name"]],
	HoldComplete[WolframInstitute`TypeTheory`TrueIntroduction],
	TestID -> "Replace-16"
]

VerificationTest[
	"SystemID" /. "SystemID" -> "MacOSX-ARM64",
	"MacOSX-ARM64",
	TestID -> "ReplaceAll-1"
]

VerificationTest[
	{"WolframInstitute`TypeTheory`"} /. "Context" -> {},
	{"WolframInstitute`TypeTheory`"},
	TestID -> "ReplaceAll-2"
]

VerificationTest[
	"MathematicaVersion" /. {"Root" -> "Kernel", "Context" -> {"WolframInstitute`TypeTheory`"}},
	"MathematicaVersion",
	TestID -> "ReplaceAll-3"
]

VerificationTest[
	InputStream /. {InputStream -> Close, OutputStream -> Close, String -> Protect, _ -> (Null & )},
	Close,
	TestID -> "ReplaceAll-4"
]

VerificationTest[
	"MathematicaVersion" /. Rest[{"Kernel", "Root" -> "Kernel", "Context" -> {"WolframInstitute`TypeTheory`"}}],
	"MathematicaVersion",
	TestID -> "ReplaceAll-5"
]

VerificationTest[
	"SystemID" /. Rest[{"Kernel", "Root" -> "Kernel", "Context" -> {"WolframInstitute`TypeTheory`"}}] /. "SystemID" -> "MacOSX-ARM64",
	"MacOSX-ARM64",
	TestID -> "ReplaceAll-6"
]

VerificationTest[
	0 /. {WolframInstitute`TypeTheory`PackageScope`levelParameter[HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`u]] -> 0},
	0,
	TestID -> "ReplaceAll-7"
]

VerificationTest[
	{} /. {WolframInstitute`TypeTheory`PackageScope`levelParameter[HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`u]] -> 1},
	{},
	TestID -> "ReplaceAll-8"
]

VerificationTest[
	{WolframInstitute`TypeTheory`PackageScope`levelParameter[HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`u]]} /. {WolframInstitute`TypeTheory`PackageScope`levelParameter[HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`u]] -> 1},
	{1},
	TestID -> "ReplaceAll-9"
]

VerificationTest[
	WolframInstitute`TypeTheory`PackageScope`levelParameter[HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`u]] /. {WolframInstitute`TypeTheory`PackageScope`levelParameter[HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`u]] -> 1},
	1,
	TestID -> "ReplaceAll-10"
]

VerificationTest[
	Rest[{WolframInstitute`TypeTheory`PackageScope`universeSort[0]}],
	{},
	TestID -> "Rest-1"
]

VerificationTest[
	Rest[Most[{WolframInstitute`TypeTheory`PackageScope`syntaxSymbol[HoldComplete[True]], WolframInstitute`TypeTheory`PackageScope`syntaxSymbol[HoldComplete[True]], WolframInstitute`TypeTheory`PackageScope`syntaxSymbol[HoldComplete[False]]}]],
	{WolframInstitute`TypeTheory`PackageScope`syntaxSymbol[HoldComplete[True]]},
	TestID -> "Rest-2"
]

VerificationTest[
	Reverse[{}],
	{},
	TestID -> "Reverse-1"
]

VerificationTest[
	Reverse[{3544}],
	{3544},
	TestID -> "Reverse-2"
]

VerificationTest[
	Reverse[Most[{WolframInstitute`TypeTheory`PackageScope`syntaxSymbol[HoldComplete[True]], WolframInstitute`TypeTheory`PackageScope`syntaxSymbol[HoldComplete[True]]}]],
	{WolframInstitute`TypeTheory`PackageScope`syntaxSymbol[HoldComplete[True]]},
	TestID -> "Reverse-3"
]

VerificationTest[
	ReverseApplied[Automatic],
	ReverseApplied[Automatic],
	TestID -> "ReverseApplied-1"
]

VerificationTest[
	RowBox[{"\[Not]", _}],
	RowBox[{"\[Not]", _}],
	TestID -> "RowBox-1"
]

VerificationTest[
	0 === 0,
	True,
	TestID -> "SameQ-1"
]

VerificationTest[
	{} === {},
	True,
	TestID -> "SameQ-2"
]

VerificationTest[
	1 === None,
	False,
	TestID -> "SameQ-3"
]

VerificationTest[
	{0} === {0},
	True,
	TestID -> "SameQ-4"
]

VerificationTest[
	<||> === None,
	False,
	TestID -> "SameQ-5"
]

VerificationTest[
	None === None,
	True,
	TestID -> "SameQ-6"
]

VerificationTest[
	<||> === <||>,
	True,
	TestID -> "SameQ-7"
]

VerificationTest[
	True === True,
	True,
	TestID -> "SameQ-8"
]

VerificationTest[
	{"Extra"} === All,
	False,
	TestID -> "SameQ-9"
]

VerificationTest[
	<||> === Association[],
	True,
	TestID -> "SameQ-10"
]

VerificationTest[
	Automatic === Automatic,
	True,
	TestID -> "SameQ-11"
]

VerificationTest[
	InputStream === InputStream,
	True,
	TestID -> "SameQ-12"
]

VerificationTest[
	"InductiveType" === "Definition",
	False,
	TestID -> "SameQ-13"
]

VerificationTest[
	HoldComplete[ArrowyMake] === None,
	False,
	TestID -> "SameQ-14"
]

VerificationTest[
	HoldComplete[True] === HoldComplete[True],
	True,
	TestID -> "SameQ-15"
]

VerificationTest[
	WolframInstitute`TypeTheory`PackageScope`metavariable[765] === None,
	False,
	TestID -> "SameQ-16"
]

VerificationTest[
	{WolframInstitute`TypeTheory`PackageScope`freeVariable[7746]} === {},
	False,
	TestID -> "SameQ-17"
]

VerificationTest[
	1 === WolframInstitute`TypeTheory`PackageScope`levelMetavariable[864],
	False,
	TestID -> "SameQ-18"
]

VerificationTest[
	WolframInstitute`TypeTheory`PackageScope`levelMetavariable[1035] === 1,
	False,
	TestID -> "SameQ-19"
]

VerificationTest[
	WolframInstitute`TypeTheory`PackageScope`universeSort[0] === WolframInstitute`TypeTheory`PackageScope`universeSort[0],
	True,
	TestID -> "SameQ-20"
]

VerificationTest[
	<|"Kind" -> "Axiom", "Type" -> WolframInstitute`TypeTheory`PackageScope`universeSort[0], "UniverseParameters" -> {}|>["Kind"] === "RewriteRule",
	False,
	TestID -> "SameQ-21"
]

VerificationTest[
	<|"Placeholder" -> WolframInstitute`TypeTheory`PackageScope`metavariable[914], "Name" -> HoldComplete[True], "Arguments" -> {}, "Syntax" -> WolframInstitute`TypeTheory`PackageScope`syntaxSymbol[HoldComplete[True]]|>["Arguments"] === {},
	True,
	TestID -> "SameQ-22"
]

VerificationTest[
	<|"Name" -> HoldComplete[WolframInstitute`TypeTheory`TrueIntroduction], "Type" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[True], {}], "Owner" -> HoldComplete[True], "AfterParameters" -> WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[True], {}], "Original" -> None|>["Owner"] === HoldComplete[True],
	True,
	TestID -> "SameQ-23"
]

VerificationTest[
	<|"Kind" -> "InductiveType", "Type" -> WolframInstitute`TypeTheory`PackageScope`universeSort[1], "UniverseParameters" -> {}, "NumberOfParameters" -> 0, "NumberOfIndices" -> 0, "Constructors" -> {HoldComplete[NaturalPairIntroduction]}, "LargeElimination" -> True, "Recursive" -> False, "Block" -> {HoldComplete[NaturalPair]}|>["Constructors"] === {HoldComplete[NaturalPairIntroduction]},
	True,
	TestID -> "SameQ-24"
]

VerificationTest[
	Scan[Remove, {}],
	Null,
	TestID -> "Scan-1"
]

VerificationTest[
	Scan[Function[WolframInstitute`TypeTheory`Checking`Environment`Private`store, Sow[WolframInstitute`TypeTheory`Checking`Environment`Private`store, WolframInstitute`TypeTheory`Checking`Environment`Private`$storeTag]], {}],
	Null,
	TestID -> "Scan-2"
]

VerificationTest[
	Select[{True, WolframInstitute`TypeTheory`TrueIntroduction, WolframInstitute`TypeTheory`InductiveRecursor[True], False, WolframInstitute`TypeTheory`InductiveRecursor[False], Not, And, WolframInstitute`TypeTheory`AndIntroduction, WolframInstitute`TypeTheory`InductiveRecursor[And], Or, WolframInstitute`TypeTheory`OrIntroductionLeft, WolframInstitute`TypeTheory`OrIntroductionRight, WolframInstitute`TypeTheory`InductiveRecursor[Or], Equivalent, WolframInstitute`TypeTheory`EquivalentIntroduction, WolframInstitute`TypeTheory`InductiveRecursor[Equivalent], Equal, WolframInstitute`TypeTheory`EqualityReflexivity, WolframInstitute`TypeTheory`InductiveRecursor[Equal], Exists, WolframInstitute`TypeTheory`ExistsIntroduction, WolframInstitute`TypeTheory`InductiveRecursor[Exists], Unequal, Identity, Composition, NonNegativeIntegers, WolframInstitute`TypeTheory`NaturalNumberZero, WolframInstitute`TypeTheory`NaturalNumberSuccessor, WolframInstitute`TypeTheory`InductiveRecursor[NonNegativeIntegers], Plus, WolframInstitute`TypeTheory`NaturalNumberPredecessor, Subtract, Times, Power, LessEqual, WolframInstitute`TypeTheory`LessEqualReflexivity, WolframInstitute`TypeTheory`LessEqualStep, WolframInstitute`TypeTheory`InductiveRecursor[LessEqual], Less, GreaterEqual, Greater, WolframInstitute`TypeTheory`FalseElimination, WolframInstitute`TypeTheory`AndEliminationLeft, WolframInstitute`TypeTheory`AndEliminationRight, WolframInstitute`TypeTheory`EqualitySymmetry, WolframInstitute`TypeTheory`EqualityTransitivity, WolframInstitute`TypeTheory`EqualityCongruence, WolframInstitute`TypeTheory`EqualitySubstitution, WolframInstitute`TypeTheory`EquivalentForward, WolframInstitute`TypeTheory`EquivalentBackward, WolframInstitute`TypeTheory`EquivalentReflexivity, WolframInstitute`TypeTheory`EquivalentSymmetry, WolframInstitute`TypeTheory`EquivalentTransitivity, WolframInstitute`TypeTheory`AdditionZeroRight, WolframInstitute`TypeTheory`AdditionZeroLeft, WolframInstitute`TypeTheory`AdditionSuccessorRight, WolframInstitute`TypeTheory`AdditionSuccessorLeft, WolframInstitute`TypeTheory`AdditionCommutativity, WolframInstitute`TypeTheory`AdditionAssociativity, WolframInstitute`TypeTheory`MultiplicationZeroRight, WolframInstitute`TypeTheory`MultiplicationZeroLeft, WolframInstitute`TypeTheory`MultiplicationSuccessorRight, WolframInstitute`TypeTheory`MultiplicationOneRight, WolframInstitute`TypeTheory`MultiplicationOneLeft, WolframInstitute`TypeTheory`MultiplicationSuccessorLeft, WolframInstitute`TypeTheory`MultiplicationCommutativity, WolframInstitute`TypeTheory`MultiplicationDistributivityLeft, WolframInstitute`TypeTheory`MultiplicationDistributivityRight, WolframInstitute`TypeTheory`MultiplicationAssociativity, WolframInstitute`TypeTheory`SuccessorInjectivity, WolframInstitute`TypeTheory`SuccessorNotZero, WolframInstitute`TypeTheory`SubtractionZeroRight, WolframInstitute`TypeTheory`SubtractionZeroLeft, WolframInstitute`TypeTheory`SubtractionSuccessor, WolframInstitute`TypeTheory`SubtractionSelf, WolframInstitute`TypeTheory`AdditionSubtractionCancellation, WolframInstitute`TypeTheory`PowerZero, WolframInstitute`TypeTheory`PowerSuccessor, WolframInstitute`TypeTheory`PowerOne, WolframInstitute`TypeTheory`PowerAddition, WolframInstitute`TypeTheory`PredecessorLessEqual, WolframInstitute`TypeTheory`LessEqualZero, WolframInstitute`TypeTheory`LessEqualSuccessor, WolframInstitute`TypeTheory`LessEqualTransitivity, WolframInstitute`TypeTheory`LessEqualAddition, WolframInstitute`TypeTheory`SuccessorNotLessEqualZero, WolframInstitute`TypeTheory`LessEqualPredecessor, WolframInstitute`TypeTheory`LessIrreflexivity, WolframInstitute`TypeTheory`LessEqualAntisymmetry, Booleans, "false", "true", WolframInstitute`TypeTheory`InductiveRecursor[Booleans], "not", "and", "or", WolframInstitute`TypeTheory`Nonempty, WolframInstitute`TypeTheory`NonemptyIntroduction, WolframInstitute`TypeTheory`InductiveRecursor[WolframInstitute`TypeTheory`Nonempty], WolframInstitute`TypeTheory`Subtype, WolframInstitute`TypeTheory`SubtypeIntroduction, WolframInstitute`TypeTheory`InductiveRecursor[WolframInstitute`TypeTheory`Subtype], WolframInstitute`TypeTheory`PropositionalExtensionality, WolframInstitute`TypeTheory`FunctionExtensionality, WolframInstitute`TypeTheory`Choice, WolframInstitute`TypeTheory`ChosenWitness, WolframInstitute`TypeTheory`ChosenWitnessProperty, WolframInstitute`TypeTheory`ExcludedMiddle, WolframInstitute`TypeTheory`DoubleNegationElimination}, StringQ],
	{"false", "true", "not", "and", "or"},
	TestID -> "Select-1"
]

VerificationTest[
	SelectFirst[{}, Function[WolframInstitute`TypeTheory`Elaboration`Elaboration`Private`pair, Last[WolframInstitute`TypeTheory`Elaboration`Elaboration`Private`pair] =!= None], None],
	None,
	TestID -> "SelectFirst-1"
]

VerificationTest[
	SelectFirst[{{<|"Placeholder" -> WolframInstitute`TypeTheory`PackageScope`metavariable[914], "Name" -> HoldComplete[True], "Arguments" -> {}, "Syntax" -> WolframInstitute`TypeTheory`PackageScope`syntaxSymbol[HoldComplete[True]]|>, None}}, Function[WolframInstitute`TypeTheory`Elaboration`Elaboration`Private`pair, Last[WolframInstitute`TypeTheory`Elaboration`Elaboration`Private`pair] =!= None], None],
	None,
	TestID -> "SelectFirst-2"
]

VerificationTest[
	Sort[{"Name", "Prop", "RewriteRules"}],
	{"Name", "Prop", "RewriteRules"},
	TestID -> "Sort-1"
]

VerificationTest[
	Sort[Keys[<|"Name" -> "MartinLofTypeTheory", "Prop" -> False, "RewriteRules" -> False|>]],
	{"Name", "Prop", "RewriteRules"},
	TestID -> "Sort-2"
]

VerificationTest[
	SortBy[{}, First],
	{},
	TestID -> "SortBy-1"
]

VerificationTest[
	SortBy[List @@@ {}, First],
	{},
	TestID -> "SortBy-2"
]

VerificationTest[
	SortBy[{{WolframInstitute`TypeTheory`PackageScope`levelMetavariable[1502], 0}}, First],
	{{WolframInstitute`TypeTheory`PackageScope`levelMetavariable[1502], 0}},
	TestID -> "SortBy-3"
]

VerificationTest[
	StringContainsQ["0.12.4", "+"],
	False,
	TestID -> "StringContainsQ-1"
]

VerificationTest[
	StringFreeQ["InterpretationBox[RowBox[{SubscriptBox[\"\\[ForAll]\", TemplateBox[{\"\\\"{\\\"\", RowBox[{\"\\\"a\\\"\", \"\\[Colon]\", \"\\\"Prop\\\"\"}], \"\\\"}\\\"\"}, \"RowDefault\"]], RowBox[{SubscriptBox[\"\\[ForAll]\", TemplateBox[{\"\\\"{\\\"\", RowBox[{\"\\\"b\\\"\", \"\\[Colon]\", \"\\\"Prop\\\"\"}], \"\\\"}\\\"\"}, \"RowDefault\"]], RowBox[{\"\\\"a\\\"\", \"\\[DoubleRightArrow]\", \"\\\"b\\\"\", \"\\[DoubleRightArrow]\", RowBox[{\"(\", RowBox[{\"\\\"a\\\"\", \"\\[And]\", \"\\\"b\\\"\"}], \")\"}]}]}]}], TypeTheoryTerm[ForAll[{TypedImplicit[WolframInstitute`TypeTheory`Library`Prelude`Private`a, TypeUniverse[0]], TypedImplicit[WolframInstitute`TypeTheory`Library`Prelude`Private`b, TypeUniverse[0]]}, Implies[WolframInstitute`TypeTheory`Library`Prelude`Private`a, Implies[WolframInstitute`TypeTheory`Library`Prelude`Private`b, WolframInstitute`TypeTheory`Library`Prelude`Private`a && WolframInstitute`TypeTheory`Library`Prelude`Private`b]]], TypeTheoryEnvironment[WolframInstitute`TypeTheory`Checking`Environment`Private`store$9428]]]", "Formal"],
	True,
	TestID -> "StringFreeQ-1"
]

VerificationTest[
	StringJoin["Accelerators", "-", "OSX", "-", "15.0.505"],
	"Accelerators-OSX-15.0.505",
	TestID -> "StringJoin-1"
]

VerificationTest[
	StringJoin["WolframInstitute__TypeTheory", "-", "0.12.4"],
	"WolframInstitute__TypeTheory-0.12.4",
	TestID -> "StringJoin-2"
]

VerificationTest[
	StringJoin["WolframInstitute`TypeTheory`PackageScope`", "$emptyEnvironment"],
	"WolframInstitute`TypeTheory`PackageScope`$emptyEnvironment",
	TestID -> "StringJoin-3"
]

VerificationTest[
	StringJoin[Context[Unevaluated[A]], SymbolName[Unevaluated[A]], ToString[1]],
	"Global`A1",
	TestID -> "StringJoin-4"
]

VerificationTest[
	StringLength["WolframInstitute__TypeTheory"],
	28,
	TestID -> "StringLength-1"
]

VerificationTest[
	StringMatchQ["PacletInfo.wl", "PacletInfo.m"],
	False,
	TestID -> "StringMatchQ-1"
]

VerificationTest[
	StringMatchQ["0.12.4", RegularExpression["^[0-9]+(\\.[0-9]*)*(\\-.+)*(\\+.+)*$"]],
	True,
	TestID -> "StringMatchQ-2"
]

VerificationTest[
	StringMatchQ["/Users/swish/src/wolfram/TypeTheory/TypeTheory", "http*:*", IgnoreCase -> True],
	False,
	TestID -> "StringMatchQ-3"
]

VerificationTest[
	StringMatchQ[FileNameTake["/Users/swish/src/wolfram/TypeTheory/TypeTheory/PacletInfo.wl"], "PacletInfo.m"],
	False,
	TestID -> "StringMatchQ-4"
]

VerificationTest[
	StringQ[True],
	False,
	TestID -> "StringQ-1"
]

VerificationTest[
	StringQ[False],
	False,
	TestID -> "StringQ-2"
]

VerificationTest[
	StringQ["WolframInstitute/TypeTheory"],
	True,
	TestID -> "StringQ-3"
]

VerificationTest[
	StringQ[WolframInstitute`TypeTheory`TrueIntroduction],
	False,
	TestID -> "StringQ-4"
]

VerificationTest[
	StringQ[WolframInstitute`TypeTheory`InductiveRecursor[True]],
	False,
	TestID -> "StringQ-5"
]

VerificationTest[
	StringReplace["WolframInstitute/TypeTheory", "/" -> "__"],
	"WolframInstitute__TypeTheory",
	TestID -> "StringReplace-1"
]

VerificationTest[
	StringSplit["0.12.4", "."],
	{"0", "12", "4"},
	TestID -> "StringSplit-1"
]

VerificationTest[
	SubscriptBox["\[ForAll]" | "\[Exists]", _],
	SubscriptBox["\[ForAll]" | "\[Exists]", _],
	TestID -> "SubscriptBox-1"
]

VerificationTest[
	SubsetQ[{}, {}],
	True,
	TestID -> "SubsetQ-1"
]

VerificationTest[
	SubsetQ[{"Prop", "RewriteRules"}, {"RewriteRules"}],
	True,
	TestID -> "SubsetQ-2"
]

VerificationTest[
	SubsetQ[{}, Cases[{WolframInstitute`TypeTheory`PackageScope`universeSort[0]}, WolframInstitute`TypeTheory`PackageScope`levelParameter[WolframInstitute`TypeTheory`Checking`Environment`Private`parameter_] :> WolframInstitute`TypeTheory`Checking`Environment`Private`parameter, Infinity]],
	True,
	TestID -> "SubsetQ-3"
]

VerificationTest[
	SubsetQ[{HoldComplete[u]}, Cases[{WolframInstitute`TypeTheory`PackageScope`universeSort[WolframInstitute`TypeTheory`PackageScope`levelParameter[HoldComplete[u]]]}, WolframInstitute`TypeTheory`PackageScope`levelParameter[WolframInstitute`TypeTheory`Checking`Environment`Private`parameter_] :> WolframInstitute`TypeTheory`Checking`Environment`Private`parameter, Infinity]],
	True,
	TestID -> "SubsetQ-4"
]

VerificationTest[
	SymbolName[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`u],
	"u",
	TestID -> "SymbolName-1"
]

VerificationTest[
	SymbolName[Unevaluated[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`u]],
	"u",
	TestID -> "SymbolName-2"
]

VerificationTest[
	Table[WolframInstitute`TypeTheory`PackageScope`projection[HoldComplete[NaturalPair], WolframInstitute`TypeTheory`Checking`TypeChecking`Private`index, WolframInstitute`TypeTheory`PackageScope`freeVariable[22592]], {WolframInstitute`TypeTheory`Checking`TypeChecking`Private`index, 0, <|"Kind" -> "Recursor", "Type" -> WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`m], WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`t], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NaturalPair], {}], WolframInstitute`TypeTheory`PackageScope`universeSort[WolframInstitute`TypeTheory`PackageScope`levelParameter[HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`u]]], "Explicit"], WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[NaturalPairIntroduction], WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[\[FormalX]], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NonNegativeIntegers], {}], WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[\[FormalX]], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NonNegativeIntegers], {}], WolframInstitute`TypeTheory`PackageScope`application[WolframInstitute`TypeTheory`PackageScope`boundVariable[2], WolframInstitute`TypeTheory`PackageScope`application[WolframInstitute`TypeTheory`PackageScope`application[WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NaturalPairIntroduction], {}], WolframInstitute`TypeTheory`PackageScope`boundVariable[1]], WolframInstitute`TypeTheory`PackageScope`boundVariable[0]]], "Explicit"], "Explicit"], WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`t], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NaturalPair], {}], WolframInstitute`TypeTheory`PackageScope`application[WolframInstitute`TypeTheory`PackageScope`boundVariable[2], WolframInstitute`TypeTheory`PackageScope`boundVariable[0]], "Explicit"], "Explicit"], "Explicit"], "UniverseParameters" -> {HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`u]}, "InductiveType" -> HoldComplete[NaturalPair], "NumberOfParameters" -> 0, "NumberOfMotives" -> 1, "NumberOfIndices" -> 0, "NumberOfMinors" -> 1, "Rules" -> <|HoldComplete[NaturalPairIntroduction] -> <|"NumberOfParameters" -> 0, "NumberOfFields" -> 2, "RightHandSide" -> WolframInstitute`TypeTheory`PackageScope`lambdaAbstraction[HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`m], WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`t], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NaturalPair], {}], WolframInstitute`TypeTheory`PackageScope`universeSort[WolframInstitute`TypeTheory`PackageScope`levelParameter[HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`u]]], "Explicit"], WolframInstitute`TypeTheory`PackageScope`lambdaAbstraction[HoldComplete[NaturalPairIntroduction], WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[\[FormalX]], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NonNegativeIntegers], {}], WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[\[FormalX]], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NonNegativeIntegers], {}], WolframInstitute`TypeTheory`PackageScope`application[WolframInstitute`TypeTheory`PackageScope`boundVariable[2], WolframInstitute`TypeTheory`PackageScope`application[WolframInstitute`TypeTheory`PackageScope`application[WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NaturalPairIntroduction], {}], WolframInstitute`TypeTheory`PackageScope`boundVariable[1]], WolframInstitute`TypeTheory`PackageScope`boundVariable[0]]], "Explicit"], "Explicit"], WolframInstitute`TypeTheory`PackageScope`lambdaAbstraction[HoldComplete[\[FormalX]], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NonNegativeIntegers], {}], WolframInstitute`TypeTheory`PackageScope`lambdaAbstraction[HoldComplete[\[FormalX]], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NonNegativeIntegers], {}], WolframInstitute`TypeTheory`PackageScope`application[WolframInstitute`TypeTheory`PackageScope`application[WolframInstitute`TypeTheory`PackageScope`boundVariable[2], WolframInstitute`TypeTheory`PackageScope`boundVariable[1]], WolframInstitute`TypeTheory`PackageScope`boundVariable[0]], "Explicit"], "Explicit"], "Explicit"], "Explicit"]|>|>, "EliminationUniverse" -> True, "KLike" -> False|>["Rules"][First[Keys[<|"Kind" -> "Recursor", "Type" -> WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`m], WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`t], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NaturalPair], {}], WolframInstitute`TypeTheory`PackageScope`universeSort[WolframInstitute`TypeTheory`PackageScope`levelParameter[HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`u]]], "Explicit"], WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[NaturalPairIntroduction], WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[\[FormalX]], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NonNegativeIntegers], {}], WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[\[FormalX]], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NonNegativeIntegers], {}], WolframInstitute`TypeTheory`PackageScope`application[WolframInstitute`TypeTheory`PackageScope`boundVariable[2], WolframInstitute`TypeTheory`PackageScope`application[WolframInstitute`TypeTheory`PackageScope`application[WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NaturalPairIntroduction], {}], WolframInstitute`TypeTheory`PackageScope`boundVariable[1]], WolframInstitute`TypeTheory`PackageScope`boundVariable[0]]], "Explicit"], "Explicit"], WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`t], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NaturalPair], {}], WolframInstitute`TypeTheory`PackageScope`application[WolframInstitute`TypeTheory`PackageScope`boundVariable[2], WolframInstitute`TypeTheory`PackageScope`boundVariable[0]], "Explicit"], "Explicit"], "Explicit"], "UniverseParameters" -> {HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`u]}, "InductiveType" -> HoldComplete[NaturalPair], "NumberOfParameters" -> 0, "NumberOfMotives" -> 1, "NumberOfIndices" -> 0, "NumberOfMinors" -> 1, "Rules" -> <|HoldComplete[NaturalPairIntroduction] -> <|"NumberOfParameters" -> 0, "NumberOfFields" -> 2, "RightHandSide" -> WolframInstitute`TypeTheory`PackageScope`lambdaAbstraction[HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`m], WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`t], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NaturalPair], {}], WolframInstitute`TypeTheory`PackageScope`universeSort[WolframInstitute`TypeTheory`PackageScope`levelParameter[HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`u]]], "Explicit"], WolframInstitute`TypeTheory`PackageScope`lambdaAbstraction[HoldComplete[NaturalPairIntroduction], WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[\[FormalX]], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NonNegativeIntegers], {}], WolframInstitute`TypeTheory`PackageScope`dependentFunctionType[HoldComplete[\[FormalX]], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NonNegativeIntegers], {}], WolframInstitute`TypeTheory`PackageScope`application[WolframInstitute`TypeTheory`PackageScope`boundVariable[2], WolframInstitute`TypeTheory`PackageScope`application[WolframInstitute`TypeTheory`PackageScope`application[WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NaturalPairIntroduction], {}], WolframInstitute`TypeTheory`PackageScope`boundVariable[1]], WolframInstitute`TypeTheory`PackageScope`boundVariable[0]]], "Explicit"], "Explicit"], WolframInstitute`TypeTheory`PackageScope`lambdaAbstraction[HoldComplete[\[FormalX]], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NonNegativeIntegers], {}], WolframInstitute`TypeTheory`PackageScope`lambdaAbstraction[HoldComplete[\[FormalX]], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[NonNegativeIntegers], {}], WolframInstitute`TypeTheory`PackageScope`application[WolframInstitute`TypeTheory`PackageScope`application[WolframInstitute`TypeTheory`PackageScope`boundVariable[2], WolframInstitute`TypeTheory`PackageScope`boundVariable[1]], WolframInstitute`TypeTheory`PackageScope`boundVariable[0]], "Explicit"], "Explicit"], "Explicit"], "Explicit"]|>|>, "EliminationUniverse" -> True, "KLike" -> False|>["Rules"]]]]["NumberOfFields"] - 1}],
	{WolframInstitute`TypeTheory`PackageScope`projection[HoldComplete[NaturalPair], 0, WolframInstitute`TypeTheory`PackageScope`freeVariable[22592]], WolframInstitute`TypeTheory`PackageScope`projection[HoldComplete[NaturalPair], 1, WolframInstitute`TypeTheory`PackageScope`freeVariable[22592]]},
	TestID -> "Table-1"
]

VerificationTest[
	Take[{}, 0],
	{},
	TestID -> "Take-1"
]

VerificationTest[
	Take[{6474}, 1],
	{6474},
	TestID -> "Take-2"
]

VerificationTest[
	Take[{}, UpTo[0]],
	{},
	TestID -> "Take-3"
]

VerificationTest[
	Take[{WolframInstitute`TypeTheory`PackageScope`freeVariable[7243]}, UpTo[1]],
	{WolframInstitute`TypeTheory`PackageScope`freeVariable[7243]},
	TestID -> "Take-4"
]

VerificationTest[
	TakeList[{WolframInstitute`TypeTheory`PackageScope`lambdaAbstraction[HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`t], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[Booleans], {}], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[Booleans], {}], "Explicit"], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete["true"], {}], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete["false"], {}], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete["true"], {}]}, {0, 1, 2, 0, 1, All}],
	{{}, {WolframInstitute`TypeTheory`PackageScope`lambdaAbstraction[HoldComplete[WolframInstitute`TypeTheory`Library`Prelude`Private`t], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[Booleans], {}], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[Booleans], {}], "Explicit"]}, {WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete["true"], {}], WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete["false"], {}]}, {}, {WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete["true"], {}]}, {}},
	TestID -> "TakeList-1"
]

VerificationTest[
	TemplateBox[{"\"{\"", _, "\"}\""}, "RowDefault"],
	TemplateBox[{"\"{\"", _, "\"}\""}, "RowDefault"],
	TestID -> "TemplateBox-1"
]

VerificationTest[
	Thread[{{"13", "5"}, {"13", "4"}}],
	{{"13", "13"}, {"5", "4"}},
	TestID -> "Thread-1"
]

VerificationTest[
	Thread[{WolframInstitute`TypeTheory`PackageScope`levelParameter[HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`u]]} -> {1}],
	{WolframInstitute`TypeTheory`PackageScope`levelParameter[HoldComplete[WolframInstitute`TypeTheory`Checking`InductiveTypes`Private`u]] -> 1},
	TestID -> "Thread-2"
]

VerificationTest[
	-1*0,
	0,
	TestID -> "Times-1"
]

VerificationTest[
	-Length[{WolframInstitute`TypeTheory`PackageScope`freeVariable[4539]}],
	-1,
	TestID -> "Times-2"
]

VerificationTest[
	ToCharacterCode["WolframInstitute__TypeTheory", "UTF8"],
	{87, 111, 108, 102, 114, 97, 109, 73, 110, 115, 116, 105, 116, 117, 116, 101, 95, 95, 84, 121, 112, 101, 84, 104, 101, 111, 114, 121},
	TestID -> "ToCharacterCode-1"
]

VerificationTest[
	Transpose[{{}, {}}],
	{},
	TestID -> "Transpose-1"
]

VerificationTest[
	TrueQ[True],
	True,
	TestID -> "TrueQ-1"
]

VerificationTest[
	TrueQ[False],
	False,
	TestID -> "TrueQ-2"
]

VerificationTest[
	TrueQ[Failure["Ambiguous", <|"MessageTemplate" -> "`1` could be a proposition or a Boolean here: write `2` for the Boolean, or Typed[`1`, TypeUniverse[0]] for the proposition.", "MessageParameters" -> {HoldForm[True], "true"}|>]],
	False,
	TestID -> "TrueQ-3"
]

VerificationTest[
	TypeSpecifier[{WolframInstitute`TypeTheory`TypeUniverse[1 + v]} -> WolframInstitute`TypeTheory`TypeUniverse[2 + v]],
	TypeSpecifier[{WolframInstitute`TypeTheory`TypeUniverse[1 + v]} -> WolframInstitute`TypeTheory`TypeUniverse[2 + v]],
	TestID -> "TypeSpecifier-1"
]

VerificationTest[
	Union[{}],
	{},
	TestID -> "Union-1"
]

VerificationTest[
	Union[{"/Users/swish/src/wolfram/TypeTheory/TypeTheory/PacletInfo.wl"}],
	{"/Users/swish/src/wolfram/TypeTheory/TypeTheory/PacletInfo.wl"},
	TestID -> "Union-2"
]

VerificationTest[
	Union[Union[{"/Users/swish/src/wolfram/TypeTheory/TypeTheory/PacletInfo.wl"}]],
	{"/Users/swish/src/wolfram/TypeTheory/TypeTheory/PacletInfo.wl"},
	TestID -> "Union-3"
]

VerificationTest[
	1 =!= 1,
	False,
	TestID -> "UnsameQ-1"
]

VerificationTest[
	{} =!= {},
	False,
	TestID -> "UnsameQ-2"
]

VerificationTest[
	All =!= All,
	False,
	TestID -> "UnsameQ-3"
]

VerificationTest[
	{1438} =!= {},
	True,
	TestID -> "UnsameQ-4"
]

VerificationTest[
	None =!= None,
	False,
	TestID -> "UnsameQ-5"
]

VerificationTest[
	Null =!= Null,
	False,
	TestID -> "UnsameQ-6"
]

VerificationTest[
	True =!= Null,
	True,
	TestID -> "UnsameQ-7"
]

VerificationTest[
	False =!= Null,
	True,
	TestID -> "UnsameQ-8"
]

VerificationTest[
	HoldComplete[True] =!= None,
	True,
	TestID -> "UnsameQ-9"
]

VerificationTest[
	"InductiveType" =!= "RewriteRule",
	True,
	TestID -> "UnsameQ-10"
]

VerificationTest[
	HoldComplete[True] =!= HoldComplete[True],
	False,
	TestID -> "UnsameQ-11"
]

VerificationTest[
	("Kernel" | "Application" | "Path") =!= All,
	True,
	TestID -> "UnsameQ-12"
]

VerificationTest[
	WolframInstitute`TypeTheory`PackageScope`freeVariable[4110] =!= None,
	True,
	TestID -> "UnsameQ-13"
]

VerificationTest[
	Last[{WolframInstitute`TypeTheory`PackageScope`metavariable[427], {}}] =!= {},
	False,
	TestID -> "UnsameQ-14"
]

VerificationTest[
	WolframInstitute`TypeTheory`PackageScope`freeVariable[4132] =!= WolframInstitute`TypeTheory`PackageScope`freeVariable[4132],
	False,
	TestID -> "UnsameQ-15"
]

VerificationTest[
	{WolframInstitute`TypeTheory`PackageScope`freeVariable[4037]} =!= {WolframInstitute`TypeTheory`PackageScope`freeVariable[4037]},
	False,
	TestID -> "UnsameQ-16"
]

VerificationTest[
	<|"Kind" -> "Axiom", "Type" -> WolframInstitute`TypeTheory`PackageScope`universeSort[1], "UniverseParameters" -> {}|> =!= <|"Kind" -> "Axiom", "Type" -> WolframInstitute`TypeTheory`PackageScope`universeSort[1], "UniverseParameters" -> {}|>,
	False,
	TestID -> "UnsameQ-17"
]

VerificationTest[
	{<|"Placeholder" -> WolframInstitute`TypeTheory`PackageScope`metavariable[767], "Name" -> HoldComplete[True], "Arguments" -> {}, "Syntax" -> WolframInstitute`TypeTheory`PackageScope`syntaxSymbol[HoldComplete[True]]|>, HoldComplete[True]} =!= None,
	True,
	TestID -> "UnsameQ-18"
]

VerificationTest[
	First[<|"Kind" -> "InductiveType", "Type" -> WolframInstitute`TypeTheory`PackageScope`universeSort[0], "UniverseParameters" -> {}, "NumberOfParameters" -> 0, "NumberOfIndices" -> 0, "Constructors" -> {}, "LargeElimination" -> True, "Recursive" -> False, "Block" -> {HoldComplete[False]}|>["Block"]] =!= HoldComplete[False],
	False,
	TestID -> "UnsameQ-19"
]

VerificationTest[
	<|"Type" -> HoldComplete[NonNegativeIntegers], "Zero" -> HoldComplete[WolframInstitute`TypeTheory`NaturalNumberZero], "Successor" -> HoldComplete[WolframInstitute`TypeTheory`NaturalNumberSuccessor], "Operations" -> <|"Addition" -> HoldComplete[Plus]|>, "Roles" -> <|HoldComplete[Plus] -> "Addition"|>, "Registrations" -> {{"Addition"}}|> =!= None,
	True,
	TestID -> "UnsameQ-20"
]

VerificationTest[
	Lookup[<|"Type" -> HoldComplete[NonNegativeIntegers], "Zero" -> HoldComplete[WolframInstitute`TypeTheory`NaturalNumberZero], "Successor" -> HoldComplete[WolframInstitute`TypeTheory`NaturalNumberSuccessor], "Operations" -> <|"Addition" -> HoldComplete[Plus]|>, "Roles" -> <|HoldComplete[Plus] -> "Addition"|>, "Registrations" -> {{"Addition"}}|>, {"Type", "Zero", "Successor"}] =!= {HoldComplete[NonNegativeIntegers], HoldComplete[WolframInstitute`TypeTheory`NaturalNumberZero], HoldComplete[WolframInstitute`TypeTheory`NaturalNumberSuccessor]},
	False,
	TestID -> "UnsameQ-21"
]

VerificationTest[
	Hold[PacletObject[Association["Name" -> "WolframInstitute/TypeTheory", "PublisherID" -> "WolframInstitute", "Version" -> "0.12.4", "WolframVersion" -> "15.0+", "Description" -> "A proof engine for the Calculus of Inductive Constructions, written in the Wolfram Language", "Creator" -> "Nikolay Murzin", "License" -> "MIT", "Keywords" -> {"type theory", "dependent types", "inductive types", "proof assistant", "proof checking"}, "Categories" -> {"Mathematics"}, "PrimaryContext" -> "WolframInstitute`TypeTheory`", "Extensions" -> {{"Kernel", "Root" -> "Kernel", "Context" -> {"WolframInstitute`TypeTheory`"}}, {"Documentation", "Language" -> "English", "MainPage" -> "Guides/TypeTheory"}, {"Test", "Root" -> "Tests", "Method" -> "Experimental-v1"}}]]] =!= EndOfFile,
	True,
	TestID -> "UnsameQ-22"
]

VerificationTest[
	UpTo[0],
	UpTo[0],
	TestID -> "UpTo-1"
]

VerificationTest[
	UpTo[Length[{}]],
	UpTo[0],
	TestID -> "UpTo-2"
]

VerificationTest[
	Values[{}],
	{},
	TestID -> "Values-1"
]

VerificationTest[
	Values[<||>],
	{},
	TestID -> "Values-2"
]

VerificationTest[
	Values[{"RewriteRules" -> True}],
	{True},
	TestID -> "Values-3"
]

VerificationTest[
	$Off[],
	$Off[],
	TestID -> "$Off-1"
]
