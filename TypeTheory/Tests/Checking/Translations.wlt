(* ::Package:: *)

(* Tests for TypeTheoryTranslate in Checking/Queries.wl: declarations move to environments of other rules,
   whose kernels check them again; Prop becomes the lowest universe of types where the rules lose it, and
   what needs it, or the quotient types, is left out with what mentions it. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

martinLof = TypeTheoryRules["MartinLofTypeTheory"]

translated = TypeTheoryTranslate[TypeTheoryEnvironment["Constructive"], martinLof]


VerificationTest[
	{
		translated["MessageParameters"],
		Keys[translated["Failures"]],
		Information[translated["Environment"], "Rules"]["Name"],
		MatchQ[TypeTheoryCheck[translated["Environment"]], _Success]
	},
	{{114, 115, "MartinLofTypeTheory"}, {QuotientType}, "MartinLofTypeTheory", True},
	TestID -> "The-constructive-prelude-translates-to-Martin-Lof-type-theory"
]

VerificationTest[
	With[{back = TypeTheoryTranslate[translated["Environment"], TypeTheoryRules["CalculusOfInductiveConstructions"]]},
		{back["Failures"], MatchQ[TypeTheoryCheck[back["Environment"]], _Success], MatchQ[back["Environment"][AdditionCommutativity], _TypeTheoryDefinition]}
	],
	{<||>, True, True},
	TestID -> "A-translation-goes-back-its-theorems-definitions"
]

(* an inductive proposition takes the universe of its fields, and a proof that 0 is no successor keeps the
   level of its motive into Prop *)
VerificationTest[
	With[{environment = translated["Environment"]},
		{
			TypeOf[TypeTheoryTerm[Exists, environment]],
			TypeTheoryProof[ForAll[{Typed[n, Naturals]}, 0 + n == n], environment, {TypeTheoryTactic["Introduce", n], TypeTheoryTactic["Exact", AdditionZeroLeft[n]]}]["Goals"],
			TypeTheoryProof[2 + 2 == 4 && Not[NaturalNumberSuccessor[3] == 0], environment, {TypeTheoryTactic["Decide"]}]["Goals"]
		}
	],
	{
		With[{\[Alpha] = WolframInstitute`TypeTheory`Library`Prelude`Private`\[Alpha], u = WolframInstitute`TypeTheory`Library`Prelude`Private`u},
			TypeTheoryTerm[ForAll[{TypedImplicit[\[Alpha], TypeUniverse[Max[1, u]]]}, TypeSpecifier[{TypeSpecifier[{\[Alpha]} -> TypeUniverse[1]]} -> TypeUniverse[Max[1, u]]]], translated["Environment"]]
		],
		{},
		{}
	},
	SameTest -> Function[{actual, expected}, actual[[2 ;;]] === expected[[2 ;;]] && MatchQ[actual[[1]], _TypeTheoryTerm]],
	TestID -> "A-translated-environment-elaborates-and-decides"
]

VerificationTest[
	With[{withAxioms = TypeTheoryTranslate[TypeTheoryEnvironment["Prelude"], martinLof, "Axioms" -> True]},
		{
			First @ translated["Failures"][QuotientType],
			First @ TypeTheoryTranslate[TypeTheoryEnvironment["Prelude"], martinLof]["Failures"][PropositionalExtensionality],
			KeyExistsQ[withAxioms["Failures"], PropositionalExtensionality],
			KeyExistsQ[withAxioms["Environment"], Choice]
		}
	],
	{"QuotientsNotAllowed", "AxiomLeftOut", True, True},
	TestID -> "Axioms-are-kept-only-when-asked-and-propositional-extensionality-does-not-hold-of-types"
]

(* a proposition about all propositions is a proposition only by impredicativity *)
VerificationTest[
	With[
		{
			impredicative = TypeTheoryEnvironment[{
				TypeTheoryDefinition[Everything, Typed[ForAll[{Typed[p, TypeUniverse[0]]}, Implies[p, p]], TypeUniverse[0]]]
			}]
		},
		First @ TypeTheoryTranslate[impredicative, martinLof]["Failures"][Everything]
	],
	"TypeMismatch",
	TestID -> "Impredicativity-does-not-translate"
]

VerificationTest[
	With[
		{
			hott = TypeTheoryTranslate[
				TypeTheoryEnvironment["HomotopyTypeTheory"],
				TypeTheoryRules["CalculusOfInductiveConstructions", "RewriteRules" -> True],
				"Axioms" -> True
			]
		},
		{hott["Failures"], MatchQ[TypeTheoryCheck[hott["Environment"]], _Success], KeyExistsQ[hott["Environment"], UniverseNotSet]}
	],
	{<||>, True, True},
	TestID -> "Homotopy-type-theory-translates-to-the-calculus-of-inductive-constructions-with-rewrite-rules"
]
