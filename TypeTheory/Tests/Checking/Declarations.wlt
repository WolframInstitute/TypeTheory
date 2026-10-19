(* ::Package:: *)

(* Tests for Checking/Declarations.wl: the declaration constructors, environments built from them, and
   that adding a declaration leaves the old environment as it was. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

prelude = TypeTheoryEnvironment["Prelude"]


VerificationTest[
	TypeTheoryAxiom[Excluded, ForAll[{Typed[p, TypeUniverse[0]]}, Or[p, Not[p]]]],
	TypeTheoryAxiom[Excluded, ForAll[{Typed[p, TypeUniverse[0]]}, Or[p, Not[p]]]],
	SameTest -> MatchQ,
	TestID -> "A-declaration-is-inert"
]

VerificationTest[
	With[{classical = Append[prelude, TypeTheoryAxiom[Excluded, ForAll[{Typed[p, TypeUniverse[0]]}, Or[p, Not[p]]]]]},
		TypeOf[TypeTheoryTerm[Excluded[True], classical]] === TypeTheoryTerm[Or[True, Not[True]], classical]
	],
	True,
	TestID -> "An-axiom-can-be-used"
]

VerificationTest[
	With[{doubled = Append[prelude, TypeTheoryDefinition[Double, Function[{Typed[n, NonNegativeIntegers]}, n + n]]]},
		{
			TypeOf[TypeTheoryTerm[Double, doubled]] === TypeTheoryTerm[TypeSpecifier[{NonNegativeIntegers} -> NonNegativeIntegers], doubled],
			WeakHeadNormalForm[TypeTheoryTerm[Double[21], doubled]] === TypeTheoryTerm[42, doubled]
		}
	],
	{True, True},
	TestID -> "A-definition-has-its-inferred-type-and-unfolds"
]

VerificationTest[
	With[{identity = Append[prelude, TypeTheoryDefinition[PolymorphicIdentity, Function[{TypedImplicit[A, TypeUniverse[u]], Typed[x, A]}, x]]]},
		First /@ {
			TypeOf[TypeTheoryTerm[PolymorphicIdentity[3], identity]],
			TypeOf[TypeTheoryTerm[PolymorphicIdentity[TrueIntroduction], identity]],
			TypeOf[TypeTheoryTerm[PolymorphicIdentity[NonNegativeIntegers], identity]]
		}
	],
	{NonNegativeIntegers, True, TypeUniverse[1]},
	TestID -> "A-universe-polymorphic-definition-is-used-at-each-level"
]

VerificationTest[
	With[
		{
			identity = Append[prelude, TypeTheoryDefinition[
				ExplicitIdentity,
				Typed[Function[{Typed[A, TypeUniverse[1]], Typed[x, A]}, x], ForAll[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A]}, A]]
			]]
		},
		{
			identity[ExplicitIdentity],
			TypeOf[TypeTheoryTerm[ExplicitIdentity[3], identity]] === TypeTheoryTerm[NonNegativeIntegers, identity]
		}
	],
	{
		TypeTheoryDefinition[
			ExplicitIdentity,
			Typed[Function[{Typed[A, TypeUniverse[1]], Typed[x, A]}, x], ForAll[{TypedImplicit[A, TypeUniverse[1]]}, TypeSpecifier[{A} -> A]]]
		],
		True
	},
	TestID -> "A-definition-keeps-the-implicit-binders-of-the-type-it-is-given"
]

VerificationTest[
	With[{arithmetic = Append[prelude, TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, EqualityReflexivity[4]]]},
		TypeOf[TypeTheoryTerm[TwoPlusTwo, arithmetic]] === TypeTheoryTerm[2 + 2 == 4, arithmetic]
	],
	True,
	TestID -> "A-theorem-proved-by-computation"
]

VerificationTest[
	First /@ {
		Append[prelude, TypeTheoryTheorem[Bogus, 2 + 2 == 5, EqualityReflexivity[4]]],
		Append[prelude, TypeTheoryTheorem[NotAProposition, NonNegativeIntegers, 3]],
		Append[prelude, TypeTheoryAxiom[Plus, True]],
		Append[prelude, TypeTheoryDefinition[Loop, Typed[Function[{Typed[n, NonNegativeIntegers]}, Loop[n]], TypeSpecifier[{NonNegativeIntegers} -> NonNegativeIntegers]]]],
		Append[prelude, TypeTheoryAxiom[Weird, TypeUniverse[u], "UniverseParameters" -> {}]],
		Append[prelude, 42]
	},
	{"TypeMismatch", "PropositionExpected", "AlreadyDeclared", "ElaborationFailed", "ElaborationFailed", "DeclarationExpected"},
	TestID -> "A-declaration-that-does-not-check-gives-a-Failure"
]

VerificationTest[
	With[{extended = Append[prelude, TypeTheoryAxiom[Scratch, True]]},
		{KeyExistsQ[extended, Scratch], KeyExistsQ[prelude, Scratch], Length[extended] - Length[prelude]}
	],
	{True, False, 1},
	TestID -> "Adding-a-declaration-leaves-the-old-environment-as-it-was"
]

VerificationTest[
	Keys[TypeTheoryEnvironment[TypeTheoryEnvironment[], {TypeTheoryInductiveType[Unit, TypeUniverse[1], {UnitIntroduction -> Unit}], TypeTheoryAxiom[Point, Unit]}]],
	{Unit, UnitIntroduction, InductiveRecursor[Unit], Point},
	TestID -> "An-environment-from-declarations-alone"
]

VerificationTest[
	With[{extended = TypeTheoryEnvironment[{TypeTheoryAxiom[Point, NonNegativeIntegers]}]},
		{Keys[extended] === Append[Keys[prelude], Point], Keys[TypeTheoryEnvironment[TypeTheoryAxiom[Point, NonNegativeIntegers]]] === Keys[extended]}
	],
	{True, True},
	TestID -> "Declarations-without-an-environment-extend-the-prelude"
]

VerificationTest[
	{Head @ TypeTheoryAxiom[OnlyOneArgument], Head @ TypeTheoryEnvironment[42]},
	{TypeTheoryAxiom, TypeTheoryEnvironment},
	TestID -> "Arguments-that-do-not-match-stay-unevaluated"
]

(* the default environment is a value: Block restores it, as each test here must *)
VerificationTest[
	Block[{$TypeTheoryEnvironment},
		With[{doubled = TypeTheoryEnvironment[{TypeTheoryDefinition[Doubled, Function[{Typed[n, Naturals]}, n + n]]}]},
			{
				SetTypeTheoryEnvironment[doubled] === doubled,
				First[WeakHeadNormalForm[TypeTheoryTerm[Doubled[21]]]],
				TypeTheoryProof[Doubled[2] == 4, {TypeTheoryTactic["Reflexivity"]}]["Goals"],
				KeyExistsQ[TypeTheoryEnvironment[{TypeTheoryAxiom[Point, Naturals]}], Doubled],
				SetTypeTheoryEnvironment["Prelude"] === prelude
			}
		]
	],
	{True, 42, {}, True, True},
	TestID -> "SetTypeTheoryEnvironment-sets-the-environment-of-what-names-none"
]

VerificationTest[
	{
		$TypeTheoryEnvironment === prelude,
		Block[{$TypeTheoryEnvironment = TypeTheoryEnvironment["Constructive"]}, KeyExistsQ[TypeTheoryEnvironment[{TypeTheoryAxiom[Point, Naturals]}], ExcludedMiddle]],
		Block[{$TypeTheoryEnvironment}, Keys[SetTypeTheoryEnvironment[{TypeTheoryAxiom[Point, Naturals]}]] === Append[Keys[prelude], Point]],
		First[SetTypeTheoryEnvironment[42]]
	},
	{True, False, True, "NotAnEnvironment"},
	TestID -> "The-default-environment-is-the-prelude-and-Block-scopes-it"
]
