(* ::Package:: *)

(* Tests for Library/ZFC.wl: Aczel's model of ZFC, its axioms proved from the prelude's axioms alone, its
   computation on classes, and a forged proof still rejected. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

zfc = TypeTheoryEnvironment["ZFC"]


VerificationTest[
	{Information[zfc, "Axioms"] === Information[TypeTheoryEnvironment["Prelude"], "Axioms"], MatchQ[TypeTheoryCheck[zfc], _Success]},
	{True, True},
	TestID -> "The-ZFC-environment-declares-no-axiom-of-its-own"
]

VerificationTest[
	Map[
		Function[name, Sort[Keys[TypeTheoryAxiomClosure[TypeTheoryTerm @@ {name, zfc}]]]],
		{"extensionality", "elementOfPair", "elementOfUnion", "elementOfPower", "elementOfSeparation", "emptySetEmpty", "regularity", "replacement", "infinity", "choiceAxiom"}
	],
	{
		{"propositionalExtensionality", "quotientSoundness"},
		{"choice", "propositionalExtensionality", "quotientSoundness"},
		{"choice", "propositionalExtensionality", "quotientSoundness"},
		{"choice", "propositionalExtensionality", "quotientSoundness"},
		{"choice", "propositionalExtensionality", "quotientSoundness"},
		{"choice", "propositionalExtensionality", "quotientSoundness"},
		{"choice", "propositionalExtensionality", "quotientSoundness"},
		{"choice", "propositionalExtensionality", "quotientSoundness"},
		{"choice", "propositionalExtensionality", "quotientSoundness"},
		{"choice", "propositionalExtensionality", "quotientSoundness"}
	},
	TestID -> "The-axioms-of-ZFC-rest-on-the-prelude's-axioms-alone"
]

(* membership of classes of pre-sets computes: the class of x is a member of the class of "preSet"[α, f] when x is
   equivalent to some f[i], by the computation of the two lifts, with no proof *)
VerificationTest[
	DefinitionallyEqualQ[
		TypeTheoryTerm[
			Function[{Typed[\[Alpha], TypeUniverse[1]], Typed[f, TypeSpecifier[{\[Alpha]} -> "PreSet"]], Typed[x, "PreSet"]},
				Element["setOfPreSet"[x], "setOfPreSet"["preSet"[\[Alpha], f]]]
			],
			zfc
		],
		TypeTheoryTerm[
			Function[{Typed[\[Alpha], TypeUniverse[1]], Typed[f, TypeSpecifier[{\[Alpha]} -> "PreSet"]], Typed[x, "PreSet"]},
				Exists[{Typed[i, \[Alpha]]}, "preSetEquivalent"[x, f[i]]]
			],
			zfc
		]
	],
	True,
	TestID -> "Membership-of-classes-computes-to-membership-of-pre-sets"
]

VerificationTest[
	MatchQ[
		TypeTheoryCheck[
			TypeTheoryTerm["classElementFunction", zfc],
			TypeTheoryTerm[
				Function[{Typed[B, "Class"], Typed[z, "Set"]}, "classElement"["setClass"[z], B]] == Function[{Typed[B, "Class"], Typed[z, "Set"]}, B[z]],
				zfc
			]
		],
		_Success
	],
	True,
	TestID -> "\"classElementFunction\"-carries-set.mm's-membership-to-sets"
]

(* a forged extensionality: the theorem's statement with a proof of another statement, and an empty set
   claimed to have a member, are rejected *)
VerificationTest[
	{
		FailureQ[TypeTheoryEnvironment[zfc, {TypeTheoryTheorem[
			"forgedExtensionality",
			ForAll[{Typed[a, "Set"], Typed[b, "Set"]}, a == b],
			Function[{Typed[a, "Set"], Typed[b, "Set"]}, "extensionality"[a, b]]
		]}]],
		FailureQ[TypeTheoryEnvironment[zfc, {TypeTheoryTheorem[
			"forgedMember",
			Element["emptySet", "emptySet"],
			"emptySetEmpty"["emptySet"]
		]}]]
	},
	{True, True},
	TestID -> "Forged-proofs-about-sets-are-rejected"
]
