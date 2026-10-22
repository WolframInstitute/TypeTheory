(* ::Package:: *)

(* Tests for Checking/Cubical.wl: the interval and its normal forms, paths as functions of the interval with
   their endpoints, transport and composition with their side conditions and computation rules, and forged
   records of the primitives. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

cubical = TypeTheoryEnvironment[TypeTheoryRules["CubicalTypeTheory"], {
	TypeTheoryInductiveType[DependentSum, ForAll[{Typed[A, TypeUniverse[u + 1]], Typed[B, TypeSpecifier[{A} -> TypeUniverse[v + 1]]]}, TypeUniverse[Max[u + 1, v + 1]]], {
		DependentPair -> ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeSpecifier[{A} -> TypeUniverse[v + 1]]], Typed[a, A], Typed[b, B[a]]}, DependentSum[A, B]]
	}],
	TypeTheoryCubical[DependentSum],
	TypeTheoryInductiveType[Booleans, TypeUniverse[1], {"false" -> Booleans, "true" -> Booleans}],
	TypeTheoryDefinition["not", Function[{Typed[a, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Booleans], "true", "false", a]]]
}]

paths = TypeTheoryEnvironment[cubical, {
	TypeTheoryDefinition[Symmetry, Function[{TypedImplicit[A, TypeUniverse[1]], TypedImplicit[x, A], TypedImplicit[y, A], Typed[p, Path[A, x, y]]}, Typed[Function[{i}, p[1 - i]], Path[A, y, x]]]],
	TypeTheoryDefinition[FunctionExtensionality, Function[
		{TypedImplicit[A, TypeUniverse[1]], TypedImplicit[B, TypeUniverse[1]], TypedImplicit[f, TypeSpecifier[{A} -> B]], TypedImplicit[g, TypeSpecifier[{A} -> B]], Typed[h, ForAll[{Typed[x, A]}, Path[B, f[x], g[x]]]]},
		Typed[Function[{i}, Function[{Typed[x, A]}, h[x][i]]], Path[TypeSpecifier[{A} -> B], f, g]]
	]],
	TypeTheoryDefinition[PathInduction, Function[
		{TypedImplicit[A, TypeUniverse[1]], TypedImplicit[x, A], Typed[P, ForAll[{Typed[y, A]}, TypeSpecifier[{Path[A, x, y]} -> TypeUniverse[1]]]], Typed[d, P[x, Function[{i}, x]]], TypedImplicit[y, A], Typed[p, Path[A, x, y]]},
		CubicalTransport[Function[{i}, P[p[i], Function[{j}, p[Min[i, j]]]]], 0, d]
	]],
	TypeTheoryDefinition[Transitivity, Function[
		{TypedImplicit[A, TypeUniverse[1]], TypedImplicit[x, A], TypedImplicit[y, A], TypedImplicit[z, A], Typed[p, Path[A, x, y]], Typed[q, Path[A, y, z]]},
		Function[{Typed[i, Interval]}, CubicalComposition[A, Function[{j}, {i == 0 -> x, i == 1 -> q[j]}], p[i]]]
	]]
}]

(* a copy of the environment's store with one record changed by hand *)
forge[TypeTheoryEnvironment[store_Symbol], name_HoldComplete, change_] := Module[{copy},
	DownValues[copy] = DownValues[store] /. store -> copy;
	copy["Records"] = MapAt[change, copy["Records"], Key[name]];
	TypeTheoryEnvironment[copy]
]

SetAttributes[definitionFailure, HoldRest]
definitionFailure[environment_, value_] := Replace[TypeTheoryEnvironment[environment, {TypeTheoryDefinition[f, value]}], {failure_Failure :> First[failure], _ -> "Checked"}]


VerificationTest[
	{
		First @ TypeTheoryEnvironment[TypeTheoryEnvironment[TypeTheoryRules["MartinLofTypeTheory"]], {TypeTheoryCubical[DependentSum]}],
		First @ TypeTheoryEnvironment[TypeTheoryEnvironment[TypeTheoryRules["CalculusOfInductiveConstructions", "Cubical" -> True]], {TypeTheoryCubical[DependentSum]}],
		First @ TypeTheoryEnvironment[TypeTheoryEnvironment[TypeTheoryRules["CubicalTypeTheory"]], {TypeTheoryCubical[DependentSum]}],
		First @ TypeTheoryEnvironment[cubical, {TypeTheoryCubical[DependentSum]}],
		Last[Normal[TypeTheoryEnvironment[TypeTheoryRules["CubicalTypeTheory"], Take[Normal[cubical], 2]]]],
		First @ TypeTheoryCheck[paths]
	},
	{"CubicalNotAllowed", "CubicalNotAllowed", "SumExpected", "AlreadyDeclared", TypeTheoryCubical[DependentSum], "EnvironmentChecked"},
	TestID -> "Cubical-primitives-need-cubical-rules-and-a-sum"
]

VerificationTest[
	{
		TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[i, Interval]}, "true"], cubical], TypeTheoryTerm[Path[Booleans, "true", "true"], cubical]][[1]],
		First @ TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[i, Interval]}, "true"], cubical], TypeTheoryTerm[Path[Booleans, "true", "false"], cubical]],
		DefinitionallyEqualQ[
			TypeOf[TypeTheoryTerm[Symmetry, paths]],
			TypeTheoryTerm[ForAll[{TypedImplicit[A, TypeUniverse[1]], TypedImplicit[x, A], TypedImplicit[y, A]}, TypeSpecifier[{Path[A, x, y]} -> Path[A, y, x]]], paths]
		],
		DefinitionallyEqualQ[
			TypeOf[TypeTheoryTerm[FunctionExtensionality, paths]],
			TypeTheoryTerm[ForAll[
				{TypedImplicit[A, TypeUniverse[1]], TypedImplicit[B, TypeUniverse[1]], TypedImplicit[f, TypeSpecifier[{A} -> B]], TypedImplicit[g, TypeSpecifier[{A} -> B]]},
				TypeSpecifier[{ForAll[{Typed[x, A]}, Path[B, f[x], g[x]]]} -> Path[TypeSpecifier[{A} -> B], f, g]]
			], paths]
		]
	},
	{"TypeChecked", "TypeMismatch", True, True},
	TestID -> "A-function-of-the-interval-is-a-path-between-its-endpoints"
]

VerificationTest[
	{
		DefinitionallyEqualQ[
			TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]]}, p[0]], cubical],
			TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[p, Path[A, x, y]]}, x], cubical]
		],
		DefinitionallyEqualQ[
			TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[p, Path[A, x, x]], Typed[i, Interval], Typed[j, Interval]}, p[Min[i, Max[i, j]]]], cubical],
			TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[p, Path[A, x, x]], Typed[i, Interval], Typed[j, Interval]}, p[i]], cubical]
		],
		DefinitionallyEqualQ[
			TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[p, Path[A, x, x]], Typed[i, Interval]}, p[1 - (1 - i)]], cubical],
			TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[p, Path[A, x, x]], Typed[i, Interval]}, p[i]], cubical]
		],
		DefinitionallyEqualQ[
			TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[p, Path[A, x, x]], Typed[i, Interval]}, p[Min[i, 1 - i]]], cubical],
			TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[p, Path[A, x, x]], Typed[i, Interval]}, p[0]], cubical]
		]
	},
	{True, True, True, False},
	TestID -> "Elements-of-the-interval-are-equal-by-their-De-Morgan-normal-forms"
]

VerificationTest[
	{
		First @ TypeTheoryEnvironment[cubical, {TypeTheoryAxiom[IntervalFunction, ForAll[{Typed[i, Interval]}, Booleans]]}],
		First @ TypeTheoryEnvironment[cubical, {TypeTheoryDefinition[IntervalPoint, Typed[IntervalZero, Interval]]}],
		First @ TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[p, Path[TypeUniverse[1], Booleans, Booleans]]}, Construct[CubicalTransport, p, 0]], cubical]]
	},
	{"TypeExpected", "TypeExpected", "CubicalUnsaturated"},
	TestID -> "The-interval-is-no-type-and-transport-is-applied-in-full"
]

VerificationTest[
	{
		WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport[Function[{i}, TypeUniverse[1]], 0, Booleans], cubical]],
		WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport[Booleans, 0, "true"], cubical]],
		WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport[Function[{i}, TypeSpecifier[{Booleans} -> Booleans]], 0, "not"]["true"], cubical]],
		WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport[Function[{i}, Path[Booleans, "true", "true"]], 0, Function[{j}, "true"]][1], cubical]],
		DefinitionallyEqualQ[
			TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[p, Path[TypeUniverse[1], Booleans, Booleans]]}, CubicalTransport[p, 0, "true"]], cubical]],
			TypeTheoryTerm[ForAll[{Typed[p, Path[TypeUniverse[1], Booleans, Booleans]]}, p[1]], cubical]
		],
		First @ TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[p, Path[TypeUniverse[1], Booleans, Booleans]]}, CubicalTransport[p, 1, "true"]], cubical]]
	},
	{
		TypeTheoryTerm[Booleans, cubical],
		TypeTheoryTerm["true", cubical],
		TypeTheoryTerm["false", cubical],
		TypeTheoryTerm["true", cubical],
		True,
		"TransportNotConstant"
	},
	TestID -> "Transport-computes-by-its-type-and-needs-a-constant-line-on-its-face"
]

VerificationTest[
	{
		DefinitionallyEqualQ[
			TypeOf[TypeTheoryTerm[Transitivity, paths]],
			TypeTheoryTerm[ForAll[{TypedImplicit[A, TypeUniverse[1]], TypedImplicit[x, A], TypedImplicit[y, A], TypedImplicit[z, A]}, TypeSpecifier[{Path[A, x, y]} -> TypeSpecifier[{Path[A, y, z]} -> Path[A, x, z]]]], paths]
		],
		DefinitionallyEqualQ[
			TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[z, A], Typed[p, Path[A, x, y]], Typed[q, Path[A, y, z]]}, Transitivity[p, q][1]], paths],
			TypeTheoryTerm[Function[{TypedImplicit[A, TypeUniverse[1]], Typed[x, A], Typed[y, A], Typed[z, A], Typed[p, Path[A, x, y]], Typed[q, Path[A, y, z]]}, z], paths]
		],
		WeakHeadNormalForm[TypeTheoryTerm[CubicalComposition[Booleans, Function[{j}, {1 -> "true"}], "true"], cubical]],
		WeakHeadNormalForm[TypeTheoryTerm[CubicalComposition[TypeSpecifier[{Booleans} -> Booleans], Function[{j}, {1 -> "not"}], "not"]["true"], cubical]]
	},
	{
		True,
		True,
		TypeTheoryTerm["true", cubical],
		TypeTheoryTerm["false", cubical]
	},
	TestID -> "Composition-is-its-side-where-a-face-holds"
]

VerificationTest[
	{
		definitionFailure[cubical, Function[{TypedImplicit[A, TypeUniverse[1]], TypedImplicit[x, A], TypedImplicit[y, A], Typed[p, Path[A, x, y]]},
			Function[{Typed[i, Interval]}, CubicalComposition[A, Function[{j}, {i == 0 -> y}], p[i]]]
		]],
		definitionFailure[cubical, Function[{TypedImplicit[A, TypeUniverse[1]], TypedImplicit[x, A], TypedImplicit[y, A], Typed[p, Path[A, x, y]], Typed[q, Path[A, x, y]]},
			Function[{Typed[i, Interval]}, CubicalComposition[A, Function[{j}, {i == 0 -> p[j], i == 0 -> q[j]}], x]]
		]],
		definitionFailure[cubical, Function[{TypedImplicit[A, TypeUniverse[1]], TypedImplicit[x, A], TypedImplicit[y, A], Typed[p, Path[A, x, y]], Typed[q, Path[A, x, y]]},
			Function[{Typed[i, Interval]}, CubicalComposition[A, Function[{j}, {i == 0 -> p[j], Min[1 - i, i] == 1 -> q[j]}], x]]
		]],
		definitionFailure[cubical, Function[{TypedImplicit[A, TypeUniverse[1]], TypedImplicit[x, A], Typed[p, Path[A, x, x]]},
			CubicalComposition[A, Function[{j}, {j == 0 -> x}], x]
		]]
	},
	{"CapMismatch", "SystemDisagreement", "Checked", "FaceOfTube"},
	TestID -> "A-system-is-checked-under-its-faces"
]

(* the line of the transport forged into the composition's place, and the endpoints of Path swapped *)
VerificationTest[
	{
		First @ TypeTheoryCheck[forge[cubical, HoldComplete[Path], Function[record, Append[record, "Type" -> First[cubical]["Records"][HoldComplete[CubicalTransport]]["Type"]]]]],
		First @ TypeTheoryCheck[forge[cubical, HoldComplete[CubicalTransport], Function[record, Append[record, "CubicalRole" -> "Composition"]]]]
	},
	{"DeclarationMismatch", "DeclarationMismatch"},
	TestID -> "A-forged-cubical-record-is-caught"
]

(* Glue types in the cubical environment, whose library gives the equivalences *)
library = TypeTheoryEnvironment["Cubical"]

VerificationTest[
	{
		definitionFailure[library, Function[{Typed[i, Interval]}, GlueType[Booleans, {i == 0 -> {Booleans, "not"}}]]],
		DefinitionallyEqualQ[TypeTheoryTerm[GlueType[Booleans, {1 -> {Booleans, NegationEquivalence}}], library], TypeTheoryTerm[Booleans, library]],
		WeakHeadNormalForm[TypeTheoryTerm[GlueElimination[Booleans, {1 -> {Booleans, NegationEquivalence}}, "true"], library]],
		MatchQ[TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[i, Interval]}, GlueIntroduction[Booleans, {i == 0 -> {Booleans, NegationEquivalence}}, {i == 0 -> "true"}, "false"]], library]], TypeTheoryTerm[Path[__], _]],
		definitionFailure[library, Function[{Typed[i, Interval]}, GlueIntroduction[Booleans, {i == 0 -> {Booleans, NegationEquivalence}}, {i == 0 -> "true"}, "true"]]],
		DefinitionallyEqualQ[
			TypeTheoryTerm[Function[{Typed[i, Interval]}, GlueElimination[GlueIntroduction[Booleans, {i == 0 -> {Booleans, NegationEquivalence}}, {i == 0 -> "true"}, "false"]]], library],
			TypeTheoryTerm[Function[{Typed[i, Interval]}, "false"], library]
		]
	},
	{"TypeMismatch", True, TypeTheoryTerm["false", library], True, "GlueMismatch", True},
	TestID -> "A-Glue-type-is-its-glued-type-where-a-face-holds"
]

(* transport in a Glue type: along the path univalence gives, the equivalence is applied *)
VerificationTest[
	{
		WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport[EquivalenceToPath[NegationEquivalence], 0, "true"], library]],
		WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport[EquivalenceToPath[NegationEquivalence], 0, "false"], library]],
		WeakHeadNormalForm[TypeTheoryTerm[CubicalTransport[EquivalenceToPath[IdentityEquivalence[Booleans]], 0, "true"], library]]
	},
	{TypeTheoryTerm["false", library], TypeTheoryTerm["true", library], TypeTheoryTerm["true", library]},
	TestID -> "Transport-along-univalence-applies-the-equivalence"
]

VerificationTest[
	{
		First @ TypeTheoryCheck[forge[library, HoldComplete[GlueType], Function[record, Append[record, "Sum"-> HoldComplete[Booleans]]]]],
		First @ TypeTheoryEnvironment[TypeTheoryEnvironment[TypeTheoryRules["CubicalTypeTheory"]], {
			TypeTheoryInductiveType[Pairs, ForAll[{Typed[A, TypeUniverse[u + 1]], Typed[B, TypeUniverse[v + 1]]}, TypeUniverse[Max[u + 1, v + 1]]], {
				MakePair -> ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[v + 1]], Typed[a, A], Typed[b, B]}, Pairs[A, B]]
			}],
			TypeTheoryCubical[Pairs]
		}]
	},
	{"DeclarationMismatch", "SumExpected"},
	TestID -> "Glue-types-need-the-dependent-sum"
]
