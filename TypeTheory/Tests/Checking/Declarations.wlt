(* ::Package:: *)

(* Tests for Checking/Declarations.wl: axioms, definitions and theorems, universe parameters, and that a
   failed declaration leaves $TypeTheoryEnvironment as it was. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

SetAttributes[withPrelude, HoldAll]
withPrelude[body_] := Block[{$TypeTheoryEnvironment = $TypeTheoryEnvironment}, body]


VerificationTest[
	withPrelude[
		DeclareAxiom[Excluded, ForAll[{Typed[p, TypeUniverse[0]]}, Or[p, Not[p]]]];
		TypeOf[TypeTheoryTerm[Excluded[True]]]
	],
	TypeTheoryTerm[Or[True, Not[True]]],
	TestID -> "An-axiom-can-be-used"
]

VerificationTest[
	withPrelude[
		DeclareDefinition[Double, Function[{Typed[n, NonNegativeIntegers]}, n + n]];
		{TypeOf[TypeTheoryTerm[Double]], WeakHeadNormalForm[TypeTheoryTerm[Double[21]]]}
	],
	{TypeTheoryTerm[TypeSpecifier[{NonNegativeIntegers} -> NonNegativeIntegers]], TypeTheoryTerm[42]},
	TestID -> "A-definition-has-its-inferred-type-and-unfolds"
]

VerificationTest[
	withPrelude[
		DeclareDefinition[PolymorphicIdentity, Function[{Annotation[Typed[A, TypeUniverse[u]], "Implicit"], Typed[x, A]}, x]];
		{
			TypeOf[TypeTheoryTerm[PolymorphicIdentity[3]]],
			TypeOf[TypeTheoryTerm[PolymorphicIdentity[TrueIntroduction]]],
			TypeOf[TypeTheoryTerm[PolymorphicIdentity[NonNegativeIntegers]]]
		}
	],
	{TypeTheoryTerm[NonNegativeIntegers], TypeTheoryTerm[True], TypeTheoryTerm[TypeUniverse[1]]},
	TestID -> "A-universe-polymorphic-definition-is-used-at-each-level"
]

VerificationTest[
	withPrelude[
		DeclareTheorem[TwoPlusTwo, 2 + 2 == 4, EqualityReflexivity[4]];
		TypeOf[TypeTheoryTerm[TwoPlusTwo]]
	],
	TypeTheoryTerm[2 + 2 == 4],
	TestID -> "A-theorem-proved-by-computation"
]

VerificationTest[
	withPrelude[First @ DeclareTheorem[Bogus, 2 + 2 == 5, EqualityReflexivity[4]]],
	"TypeMismatch",
	TestID -> "A-wrong-proof-is-rejected"
]

VerificationTest[
	withPrelude[First @ DeclareTheorem[NotAProposition, NonNegativeIntegers, 3]],
	"PropositionExpected",
	TestID -> "A-theorem-must-be-a-proposition"
]

VerificationTest[
	withPrelude[First @ DeclareAxiom[Plus, True]],
	"AlreadyDeclared",
	TestID -> "A-name-is-declared-once"
]

VerificationTest[
	withPrelude[First @ DeclareDefinition[Loop, Typed[Function[{Typed[n, NonNegativeIntegers]}, Loop[n]], TypeSpecifier[{NonNegativeIntegers} -> NonNegativeIntegers]]]],
	"ElaborationFailed",
	TestID -> "A-definition-cannot-refer-to-itself"
]

VerificationTest[
	withPrelude[First @ DeclareAxiom[Weird, TypeUniverse[u], "UniverseParameters" -> {}]],
	"ElaborationFailed",
	TestID -> "A-universe-parameter-must-be-declared"
]

VerificationTest[
	withPrelude[
		With[{before = $TypeTheoryEnvironment},
			DeclareTheorem[Bogus, 2 + 2 == 5, EqualityReflexivity[4]];
			$TypeTheoryEnvironment === before
		]
	],
	True,
	TestID -> "A-failed-declaration-leaves-the-environment-unchanged"
]

VerificationTest[
	With[{before = $TypeTheoryEnvironment},
		Block[{$TypeTheoryEnvironment = before}, DeclareAxiom[Scratch, True]];
		$TypeTheoryEnvironment === before
	],
	True,
	TestID -> "Block-declares-into-a-copy"
]

VerificationTest[
	withPrelude[Head @ DeclareAxiom[OnlyOneArgument]],
	DeclareAxiom,
	TestID -> "A-declaration-without-a-type-stays-unevaluated"
]
