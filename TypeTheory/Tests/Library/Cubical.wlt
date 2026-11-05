(* ::Package:: *)

(* Tests for Library/Cubical.wl: the cubical environment, its operations on paths, its equivalences, and
   univalence, which computes. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

cubical = TypeTheoryEnvironment["Cubical"]


VerificationTest[
	{
		MatchQ[TypeTheoryCheck[cubical], _Success],
		Information[cubical, "Rules"]["Name"],
		Information[cubical, "Axioms"],
		Function[name, MatchQ[cubical[name], TypeTheoryDefinition[__]]] /@ {
			"pathSymmetry", "pathTransitivity", "pathCongruence", "pathFunctionExtensionality", "pathInduction",
			Fiber, IsContractible, IsEquivalence, Equivalence, "identityEquivalence", "isomorphismEquivalence", "negationEquivalence", "equivalenceToPath"
		}
	},
	{True, "CubicalTypeTheory", {}, ConstantArray[True, 13]},
	TestID -> "The-cubical-environment-checks-with-no-axiom"
]

VerificationTest[
	{
		MatchQ[
			TypeOf[TypeTheoryTerm["equivalenceToPath", cubical]],
			TypeTheoryTerm[ForAll[{TypedImplicit[a_, _], TypedImplicit[b_, _]}, Equivalence[a_, b_] -> Path[_, a_, b_]], _]
		],
		WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport["equivalenceToPath"["negationEquivalence"], 0, "true"], cubical]],
		WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport["pathSymmetry"["equivalenceToPath"["negationEquivalence"]], 0, "false"], cubical]]
	},
	{True, TypeTheoryTerm["false", cubical], TypeTheoryTerm["true", cubical]},
	TestID -> "\"univalence\"-is-a-path-of-Glue-types-along-which-transport-computes"
]

VerificationTest[
	{
		DefinitionallyEqualQ[
			TypeTheoryTerm["pathFunctionExtensionality"[Function[{Typed[b, Booleans]}, "negationInvolution"[b]]][0], cubical],
			TypeTheoryTerm[Function[{Typed[b, Booleans]}, "not"["not"[b]]], cubical]
		],
		WeakHeadNormalForm[TypeTheoryTerm["pathInduction"[Function[{Typed[y, Booleans], Typed[p, Path[Booleans, "true", y]]}, Booleans], "false", Function[{i}, "true"]], cubical]],
		DefinitionallyEqualQ[
			TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]]}, "pathSymmetry"["pathSymmetry"[p]]], cubical],
			TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]]}, p], cubical]
		]
	},
	{True, TypeTheoryTerm["false", cubical], True},
	TestID -> "Function-extensionality-and-path-induction-are-terms-that-compute"
]

(* the cubical primitives need cubical rules; a translation leaves them out, with what mentions them *)
VerificationTest[
	With[{translated = TypeTheoryTranslate[cubical, TypeTheoryRules["MartinLofTypeTheory"]]},
		{First[translated["Failures"][Interval]], KeyExistsQ[translated["Failures"], "equivalenceToPath"], KeyExistsQ[translated["Failures"], Booleans]}
	],
	{"CubicalNotAllowed", True, False},
	TestID -> "A-translation-leaves-out-the-cubical-primitives"
]
