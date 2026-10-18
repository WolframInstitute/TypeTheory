(* ::Package:: *)

(* Tests for Library/HomotopyTypeTheory.wl: the HoTT environment, its computation, univalence refuting
   the uniqueness of paths, and the same library proving False on the rules of the prelude. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

hott = TypeTheoryEnvironment["HomotopyTypeTheory"]

univalent = Select[Symbol["WolframInstitute`TypeTheory`PackageScope`$univalentDeclarations"], ! MatchQ[#, _TypeTheoryTheorem] &]

strictEqual = TypeTheoryInductiveType[
	StrictEqual,
	ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[x, A], Typed[y, A]}, TypeUniverse[0]],
	{StrictEqualReflexivity -> ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[x, A]}, StrictEqual[x, x]]}
]


VerificationTest[
	{Information[hott, "Rules"]["Name"], Information[hott, "Axioms"], Information[hott, "RewriteRules"], MatchQ[TypeTheoryCheck[hott], _Success]},
	{"MartinLofTypeTheory", {Univalence, Circle, CircleBase, CircleLoop, CircleInduction, CircleInductionLoop}, {CircleInductionBase}, True},
	TestID -> "The-HoTT-environment-and-its-assumptions"
]

VerificationTest[
	{
		WeakHeadNormalForm[TypeTheoryTerm[Transport[Function[{Typed[b, Booleans]}, Booleans], EqualityReflexivity["true"], "false"], hott]],
		WeakHeadNormalForm[TypeTheoryTerm[CircleInduction[Function[{Typed[x, Circle]}, Booleans], "true", TransportConstant[CircleLoop, "true"], CircleBase], hott]]
	},
	{TypeTheoryTerm["false", hott], TypeTheoryTerm["true", hott]},
	TestID -> "Transport-computes-on-reflexivity-and-the-circle-on-its-base"
]

VerificationTest[
	{
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[UniverseNotSet, hott], TypeTheoryTerm[Not[IsSet[TypeUniverse[1]]], hott]], _Success],
		TypeOf[TypeTheoryTerm[Typed[True, Booleans], hott]],
		TypeOf[TypeTheoryTerm[TrueIntroduction, hott]]
	},
	{True, TypeTheoryTerm[Booleans, hott], TypeTheoryTerm[True, hott]},
	TestID -> "Univalence-shows-the-universe-is-not-a-set"
]

VerificationTest[
	First @ TypeTheoryEnvironment[hott, {strictEqual}],
	"NoProp",
	TestID -> "The-HoTT-rules-have-no-strict-equality-in-Prop"
]

(* On the rules of the prelude, a Prop-valued equality, whose proofs are all equal, eliminates into types,
   and paths map into it; transport along its proofs is then the identity, while univalence makes
   transport along the path of negation be negation. *)
VerificationTest[
	With[
		{
			contradiction = TypeTheoryEnvironment[TypeTheoryEnvironment[], Join[univalent, {
				strictEqual,
				TypeTheoryDefinition[UnivalenceContradiction, Typed[
					With[
						{
							negationPath = EquivalenceToEquality[NegationEquivalence],
							toStrict = Function[{Typed[C, TypeUniverse[1]], Typed[q, Booleans == C]},
								InductiveRecursor[Equal][Function[{Typed[D, TypeUniverse[1]], Typed[r, Booleans == D]}, StrictEqual[Booleans, D]], StrictEqualReflexivity[Booleans], q]
							],
							cast = Function[{Typed[C, TypeUniverse[1]], Typed[e, StrictEqual[Booleans, C]], Typed[b, Booleans]},
								InductiveRecursor[StrictEqual][Function[{Typed[D, TypeUniverse[1]], Typed[k, StrictEqual[Booleans, D]]}, D], b, e]
							],
							onTrue = Function[{Typed[e, Equivalence[Booleans, Booleans]]}, e[[1]]["true"]]
						},
						With[
							{
								agree = InductiveRecursor[Equal][
									Function[{Typed[C, TypeUniverse[1]], Typed[q, Booleans == C]}, ForAll[{Typed[b, Booleans]}, EqualityToEquivalence[q][[1]][b] == cast[C, toStrict[C, q], b]]],
									Function[{Typed[b, Booleans]}, EqualityReflexivity[b]],
									negationPath
								],
								viaUnivalence = EqualityCongruence[onTrue, Univalence[Booleans, Booleans][[4]][NegationEquivalence]]
							},
							Transport[
								Function[{Typed[b, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, TypeUniverse[1]], True, False, b]],
								EqualityTransitivity[EqualitySymmetry[viaUnivalence], agree["true"]],
								TrueIntroduction
							]
						]
					],
					False
				]]
			}]]
		},
		{Information[contradiction, "Rules"]["Name"], TypeTheoryCheck[TypeTheoryTerm[UnivalenceContradiction, contradiction]] === TypeTheoryTerm[False, contradiction]}
	],
	{"CalculusOfInductiveConstructions", True},
	TestID -> "On-the-rules-of-the-prelude-the-same-axioms-prove-False"
]
