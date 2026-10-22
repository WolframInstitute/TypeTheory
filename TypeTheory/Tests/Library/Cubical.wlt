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
			PathSymmetry, PathTransitivity, PathCongruence, PathFunctionExtensionality, PathInduction,
			Fiber, IsContractible, IsEquivalence, Equivalence, IdentityEquivalence, IsomorphismEquivalence, NegationEquivalence, EquivalenceToPath
		}
	},
	{True, "CubicalTypeTheory", {}, ConstantArray[True, 13]},
	TestID -> "The-cubical-environment-checks-with-no-axiom"
]

VerificationTest[
	{
		MatchQ[
			TypeOf[TypeTheoryTerm[EquivalenceToPath, cubical]],
			TypeTheoryTerm[ForAll[{TypedImplicit[a_, _], TypedImplicit[b_, _]}, TypeSpecifier[{Equivalence[a_, b_]} -> Path[_, a_, b_]]], _]
		],
		WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport[EquivalenceToPath[NegationEquivalence], 0, "true"], cubical]],
		WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport[PathSymmetry[EquivalenceToPath[NegationEquivalence]], 0, "false"], cubical]]
	},
	{True, TypeTheoryTerm["false", cubical], TypeTheoryTerm["true", cubical]},
	TestID -> "Univalence-is-a-path-of-Glue-types-along-which-transport-computes"
]

VerificationTest[
	{
		DefinitionallyEqualQ[
			TypeTheoryTerm[PathFunctionExtensionality[Function[{Typed[b, Booleans]}, NegationInvolution[b]]][0], cubical],
			TypeTheoryTerm[Function[{Typed[b, Booleans]}, "not"["not"[b]]], cubical]
		],
		WeakHeadNormalForm[TypeTheoryTerm[PathInduction[Function[{Typed[y, Booleans], Typed[p, Path[Booleans, "true", y]]}, Booleans], "false", Function[{i}, "true"]], cubical]],
		DefinitionallyEqualQ[
			TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]]}, PathSymmetry[PathSymmetry[p]]], cubical],
			TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]]}, p], cubical]
		]
	},
	{True, TypeTheoryTerm["false", cubical], True},
	TestID -> "Function-extensionality-and-path-induction-are-terms-that-compute"
]

(* the cubical primitives need cubical rules; a translation leaves them out, with what mentions them *)
VerificationTest[
	With[{translated = TypeTheoryTranslate[cubical, TypeTheoryRules["MartinLofTypeTheory"]]},
		{First[translated["Failures"][Interval]], KeyExistsQ[translated["Failures"], EquivalenceToPath], KeyExistsQ[translated["Failures"], Booleans]}
	],
	{"CubicalNotAllowed", True, False},
	TestID -> "A-translation-leaves-out-the-cubical-primitives"
]
