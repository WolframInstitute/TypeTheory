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
			TypeOf[TypeTheoryTerm[Double, doubled]] === TypeTheoryTerm[NonNegativeIntegers -> NonNegativeIntegers, doubled],
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
			TypeOf[TypeTheoryTerm[PolymorphicIdentity["trueIntroduction"], identity]],
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
			Typed[Function[{Typed[A, TypeUniverse[1]], Typed[x, A]}, x], ForAll[{TypedImplicit[A, TypeUniverse[1]]}, A -> A]]
		],
		True
	},
	TestID -> "A-definition-keeps-the-implicit-binders-of-the-type-it-is-given"
]

VerificationTest[
	With[{secret = Append[prelude, TypeTheoryDefinition[Secret, Typed[42, NonNegativeIntegers], "Opaque" -> True]]},
		{
			TypeOf[TypeTheoryTerm[Secret, secret]] === TypeTheoryTerm[NonNegativeIntegers, secret],
			WeakHeadNormalForm[TypeTheoryTerm[Secret, secret]] === TypeTheoryTerm[Secret, secret],
			DefinitionallyEqualQ[TypeTheoryTerm[Secret, secret], TypeTheoryTerm[42, secret]],
			secret[Secret],
			Information[secret, "Kinds"]["Opaque"]
		}
	],
	{True, True, False, TypeTheoryDefinition[Secret, Typed[42, NonNegativeIntegers], "Opaque" -> True], 1},
	TestID -> "An-opaque-definition-has-its-type-but-never-unfolds"
]

VerificationTest[
	With[{secret = Append[prelude, TypeTheoryDefinition[Secret, Typed[42, NonNegativeIntegers], "Opaque" -> True]]},
		{
			Head[Append[secret, TypeTheoryTheorem[SecretItself, Secret == Secret, "equalityReflexivity"[Secret]]]],
			Head[Append[secret, TypeTheoryTheorem[SecretValue, Secret == 42, "equalityReflexivity"[42]]]]
		}
	],
	{TypeTheoryEnvironment, Failure},
	TestID -> "An-opaque-definition-equals-only-itself"
]

VerificationTest[
	Head[Append[prelude, TypeTheoryDefinition[Forged, Typed["trueIntroduction", NonNegativeIntegers], "Opaque" -> True]]],
	Failure,
	TestID -> "An-opaque-definition-whose-value-has-another-type-gives-a-Failure"
]

VerificationTest[
	With[{arithmetic = Append[prelude, TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, "equalityReflexivity"[4]]]},
		TypeOf[TypeTheoryTerm[TwoPlusTwo, arithmetic]] === TypeTheoryTerm[2 + 2 == 4, arithmetic]
	],
	True,
	TestID -> "A-theorem-proved-by-computation"
]

VerificationTest[
	With[
		{
			lemmas = TypeTheoryEnvironment[prelude, {
				TypeTheoryAxiom[ZeroAtMost, ForAll[{TypedImplicit[n, NonNegativeIntegers]}, 0 <= n]],
				TypeTheoryDefinition[MonomorphicIdentity, Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A]}, x]]
			}]
		},
		Head /@ {
			Append[lemmas, TypeTheoryTheorem[ZeroAtMostThree, 0 <= 3, ZeroAtMost]],
			Append[lemmas, TypeTheoryDefinition[NaturalIdentity, Typed[MonomorphicIdentity, TypeSpecifier[{NonNegativeIntegers} -> NonNegativeIntegers]]]]
		}
	],
	{TypeTheoryEnvironment, TypeTheoryEnvironment},
	TestID -> "A-constant-given-on-its-own-gets-its-implicit-arguments"
]

VerificationTest[
	With[
		{
			named = TypeTheoryEnvironment[prelude, {
				TypeTheoryAxiom[Shift, TypeSpecifier[{NonNegativeIntegers} -> NonNegativeIntegers]],
				TypeTheoryAxiom[Shift[0], NonNegativeIntegers]
			}]
		},
		{
			! FreeQ[
				WolframInstitute`TypeTheory`PackageScope`constantRecord[Append[named, TypeTheoryAxiom[ShiftAtMostFive, LessEqual[Shift[0], 5]]], HoldComplete[ShiftAtMostFive]]["Type"],
				WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[Shift[0]], {}]
			],
			FreeQ[
				WolframInstitute`TypeTheory`PackageScope`constantRecord[Append[prelude, TypeTheoryDefinition[Six, Typed[With[{n = Typed[3, NonNegativeIntegers]}, n + n], NonNegativeIntegers]]], HoldComplete[Six]]["Value"],
				_WolframInstitute`TypeTheory`PackageScope`localDefinition
			]
		}
	],
	{True, True},
	TestID -> "A-declaration-reads-a-constant-named-by-an-application-and-a-With-as-elaboration-does"
]

VerificationTest[
	{
		First[Append[prelude, TypeTheoryDefinition[Zero, Typed[With[{x = Typed[NonNegativeIntegers, NonNegativeIntegers]}, 0], NonNegativeIntegers]]]],
		First[Append[prelude, TypeTheoryDefinition[Four, Typed[With[{x = Typed[3, Booleans]}, x + 1], NonNegativeIntegers]]]],
		With[{negated = TypeTheoryEnvironment[prelude, {TypeTheoryAxiom[Q, TypeUniverse[0]], TypeTheoryAxiom[Not[Q], TypeUniverse[0]]}]},
			FreeQ[
				WolframInstitute`TypeTheory`PackageScope`constantRecord[Append[negated, TypeTheoryAxiom[NotQ, Not[Q]]], HoldComplete[NotQ]]["Type"],
				WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[Not[Q]], _]
			]
		]
	},
	{"TypeMismatch", "TypeMismatch", True},
	TestID -> "A-declaration-checks-a-With-binding-and-reads-an-overloaded-name-before-a-declared-one"
]

VerificationTest[
	With[
		{
			pairs = TypeTheoryEnvironment[prelude, {
				TypeTheoryAxiom[P, TypeUniverse[0]],
				TypeTheoryAxiom[Q, TypeUniverse[0]],
				TypeTheoryAxiom[BothEverywhere, ForAll[{Typed[n, NonNegativeIntegers]}, And[P, Q]]]
			}]
		},
		Head /@ {
			Append[pairs, TypeTheoryTheorem[FirstEverywhere, ForAll[{Typed[n, NonNegativeIntegers]}, P],
				With[{A = Typed[NonNegativeIntegers, TypeUniverse[1]]}, Function[{Typed[n, A]}, BothEverywhere[n][[1]]]]
			]],
			Append[pairs, TypeTheoryTheorem[FirstEverywhereAgain, ForAll[{Typed[n, NonNegativeIntegers]}, P],
				With[{A = Typed[NonNegativeIntegers, TypeUniverse[1]]}, Function[{Typed[n, A]}, With[{p = Typed[BothEverywhere[n][[1]], P]}, Identity[p]]]]
			]]
		}
	],
	{TypeTheoryEnvironment, TypeTheoryEnvironment},
	TestID -> "A-projection-under-a-binder-whose-type-a-With-names"
]

VerificationTest[
	First /@ {
		Append[prelude, TypeTheoryTheorem[Bogus, 2 + 2 == 5, "equalityReflexivity"[4]]],
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
		Block[{$TypeTheoryEnvironment = TypeTheoryEnvironment["Constructive"]}, KeyExistsQ[TypeTheoryEnvironment[{TypeTheoryAxiom[Point, Naturals]}], "excludedMiddle"]],
		Block[{$TypeTheoryEnvironment}, Keys[SetTypeTheoryEnvironment[{TypeTheoryAxiom[Point, Naturals]}]] === Append[Keys[prelude], Point]],
		First[SetTypeTheoryEnvironment[42]]
	},
	{True, False, True, "NotAnEnvironment"},
	TestID -> "The-default-environment-is-the-prelude-and-Block-scopes-it"
]

(* a library environment's name stands for it in a Block, as in SetTypeTheoryEnvironment; any other value that is no
   environment leaves the prelude *)
VerificationTest[
	{
		Block[{$TypeTheoryEnvironment = "Constructive"}, KeyExistsQ[TypeTheoryEnvironment[{TypeTheoryAxiom[Point, Naturals]}], "excludedMiddle"]],
		Block[{$TypeTheoryEnvironment = "Integers"}, KeyExistsQ[TypeTheoryEnvironment[{TypeTheoryAxiom[Point, Naturals]}], "integerAdditionCommutativity"]],
		Block[{$TypeTheoryEnvironment = "Classical"}, KeyExistsQ[TypeTheoryEnvironment[{TypeTheoryAxiom[Point, Naturals]}], "excludedMiddle"]]
	},
	{False, True, True},
	TestID -> "A-library-environment-name-stands-for-it-in-a-Block"
]

(* an axiom may name the Wolfram Language function that computes it, as a symbol: it is kept in the record, read back,
   replayed and saved by name, and the kernel never runs it; anything but a symbol is refused *)
VerificationTest[
	With[
		{
			environment = TypeTheoryEnvironment[prelude, {
				TypeTheoryAxiom["Expressions", TypeUniverse[1]],
				TypeTheoryAxiom["simplify", "Expressions" -> "Expressions", "Implementation" -> Simplify]
			}],
			file = FileNameJoin[{$TemporaryDirectory, "implementation-" <> CreateUUID[] <> ".wxf"}]
		},
		Export[file, environment];
		{
			environment["simplify"],
			Information[TypeTheoryTerm["simplify", environment], "Implementation"],
			Information[TypeTheoryTerm["Expressions", environment], "Implementation"],
			Information[TypeTheoryTerm["simplify", TypeTheoryEnvironment[File[file], "Check" -> True]], "Implementation"],
			Information[TypeTheoryTerm["simplify", TypeTheoryEnvironment[TypeTheoryEnvironment[], Normal[environment]]], "Implementation"],
			First[TypeTheoryEnvironment[prelude, {TypeTheoryAxiom[Opaque, TypeUniverse[1], "Implementation" -> Function[x, x]]}]],
			DeleteFile[file]
		}
	],
	{TypeTheoryAxiom["simplify", "Expressions" -> "Expressions", "Implementation" -> Simplify], Simplify, None, Simplify, Simplify, "InvalidOption", Null},
	TestID -> "An-axiom-names-the-function-that-computes-it"
]

(* a declaration holds a sequence, Sequence[a, b], as one term, not as the arguments a and b: one of the type its elements
   give is declared, and one of another type, a forged one, is still rejected *)
VerificationTest[
	With[{wolfram = TypeTheoryEnvironment["WolframLanguage"]},
		{
			Head[TypeTheoryEnvironment[wolfram, {TypeTheoryDefinition[numbers, Typed[Sequence[1, 2], Sequence[NonNegativeIntegers, NonNegativeIntegers]]]}]],
			First[TypeTheoryEnvironment[wolfram, {TypeTheoryDefinition[forged, Typed[Sequence[1, 2], Sequence[NonNegativeIntegers]]]}]],
			First[TypeTheoryEnvironment[wolfram, {TypeTheoryTheorem[forgedTheorem, 1 == 2, Sequence["equalityReflexivity"[1]]]}]]
		}
	],
	{TypeTheoryEnvironment, "TypeMismatch", "TypeMismatch"},
	TestID -> "A-declared-sequence-is-one-term-and-a-forged-one-is-rejected"
]
