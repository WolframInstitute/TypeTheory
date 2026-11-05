(* ::Package:: *)

(*
The cubical environment: TypeTheoryEnvironment["Cubical"] is cubical type theory with a small library,
built and checked the first time it is asked for. Its rules are "CubicalTypeTheory", Martin-Löf type theory
with the primitives of Cubical.wl, so it has no Prop.

	DependentSum[A, B], "dependentPair"[a, b]     the dependent sum Σ x : A, B[x] and its pairs, which Glue types use
	Booleans, "false", "true", "not"            the Booleans and negation
	"pathSymmetry", "pathTransitivity", "pathCongruence", "pathFunctionExtensionality", "pathInduction"
	                                            the operations on paths, as functions of the interval and
	                                            compositions: function extensionality is a term, and path
	                                            induction transports along the path's connection
	Fiber, IsContractible, IsEquivalence, Equivalence
	                                            equivalences as functions with contractible fibers, the kernel's
	"identityEquivalence", "isomorphismEquivalence", "negationEquivalence"
	                                            the identity, an isomorphism made an equivalence by the cubical
	                                            library's construction, and negation
	"equivalenceToPath"[e]                        univalence: the path of Glue types from A to B that the equivalence
	                                            e gives, along which transport applies e

Transport along "equivalenceToPath"["negationEquivalence"] takes "true" to "false" by computation, which an
axiom of univalence, as in the HoTT environment, cannot do.
*)


(* ::Section:: *)
(*PackageExported*)


PackageExported[DependentSum]
PackageExported[Fiber]
PackageExported[IsContractible]


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[cubicalEnvironment]


(* ::Section:: *)
(*Usage Messages*)


DependentSum::usage = "DependentSum[A, B] is the dependent sum Σ x : A, B[x] of the cubical environment, whose elements are the pairs \"dependentPair\"[a, b]; \
TypeTheoryCubical names it for Glue types."
Fiber::usage = "Fiber[f, y] is the type of the elements x with a path from f[x] to y, in the cubical environment."
IsContractible::usage = "IsContractible[X] is the type of an element c of X with a path from c to every element, in the cubical environment."

cubicalEnvironment::usage = "cubicalEnvironment[] gives TypeTheoryEnvironment[\"Cubical\"], built and checked once per session."


(* ::Section:: *)
(*Function Definitions*)


cubicalEnvironment[] := cubicalEnvironment[] = withoutStoreTracking[With[{empty = emptyEnvironmentOf[TypeTheoryRules["CubicalTypeTheory"]]},
	libraryEnvironment["Cubical", empty, withStoreCleanup[TypeTheoryEnvironment[empty, $cubicalDeclarations]]]
]]

$cubicalDeclarations = {
	TypeTheoryInductiveType[DependentSum, ForAll[{Typed[A, TypeUniverse[u + 1]], Typed[B, TypeSpecifier[{A} -> TypeUniverse[v + 1]]]}, TypeUniverse[Max[u + 1, v + 1]]], {
		"dependentPair" -> ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeSpecifier[{A} -> TypeUniverse[v + 1]]], Typed[a, A], Typed[b, B[a]]}, DependentSum[A, B]]
	}],
	TypeTheoryCubical[DependentSum],
	TypeTheoryInductiveType[Booleans, TypeUniverse[1], {"false" -> Booleans, "true" -> Booleans}],
	TypeTheoryDefinition["not", Function[{Typed[a, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Booleans], "true", "false", a]]],

	(* paths *)
	TypeTheoryDefinition["pathSymmetry", Typed[
		Function[{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[x, A], TypedImplicit[y, A], Typed[p, Path[A, x, y]], Typed[i, Interval]}, p[1 - i]],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[x, A], TypedImplicit[y, A]}, Path[A, x, y] -> Path[A, y, x]]
	]],
	TypeTheoryDefinition["pathTransitivity", Typed[
		Function[
			{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[x, A], TypedImplicit[y, A], TypedImplicit[z, A], Typed[p, Path[A, x, y]], Typed[q, Path[A, y, z]], Typed[i, Interval]},
			CubicalComposition[A, Function[{j}, {i == 0 -> x, i == 1 -> q[j]}], p[i]]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[x, A], TypedImplicit[y, A], TypedImplicit[z, A]}, Path[A, x, y] -> Path[A, y, z] -> Path[A, x, z]]
	]],
	TypeTheoryDefinition["pathCongruence", Typed[
		Function[
			{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[v + 1]], Typed[f, A -> B], TypedImplicit[x, A], TypedImplicit[y, A], Typed[p, Path[A, x, y]], Typed[i, Interval]},
			f[p[i]]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[v + 1]], Typed[f, A -> B], TypedImplicit[x, A], TypedImplicit[y, A]}, Path[A, x, y] -> Path[B, f[x], f[y]]]
	]],
	TypeTheoryDefinition["pathFunctionExtensionality", Typed[
		Function[
			{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[v + 1]], TypedImplicit[f, A -> B], TypedImplicit[g, A -> B], Typed[h, ForAll[{Typed[x, A]}, Path[B, f[x], g[x]]]], Typed[i, Interval]},
			Function[{Typed[x, A]}, h[x][i]]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[v + 1]], TypedImplicit[f, A -> B], TypedImplicit[g, A -> B]}, ForAll[{Typed[x, A]}, Path[B, f[x], g[x]]] -> Path[A -> B, f, g]]
	]],
	TypeTheoryDefinition["pathInduction", Typed[
		Function[
			{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[x, A], Typed[P, ForAll[{Typed[y, A]}, Path[A, x, y] -> TypeUniverse[v + 1]]], Typed[d, P[x, Function[{i}, x]]], TypedImplicit[y, A], Typed[p, Path[A, x, y]]},
			CubicalTransport[Function[{i}, P[p[i], Function[{j}, p[Min[i, j]]]]], 0, d]
		],
		ForAll[
			{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[x, A], Typed[P, ForAll[{Typed[y, A]}, Path[A, x, y] -> TypeUniverse[v + 1]]], Typed[d, P[x, Function[{i}, x]]], TypedImplicit[y, A], Typed[p, Path[A, x, y]]},
			P[y, p]
		]
	]],

	(* equivalences: functions with contractible fibers, as the kernel writes them *)
	TypeTheoryDefinition[Fiber, Function[{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[u + 1]], Typed[f, A -> B], Typed[y, B]}, DependentSum[A, Function[{Typed[x, A]}, Path[B, f[x], y]]]]],
	TypeTheoryDefinition[IsContractible, Function[{Typed[A, TypeUniverse[u + 1]]}, DependentSum[A, Function[{Typed[c, A]}, ForAll[{Typed[z, A]}, Path[A, c, z]]]]]],
	TypeTheoryDefinition[IsEquivalence, Function[{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[u + 1]], Typed[f, A -> B]}, ForAll[{Typed[y, B]}, IsContractible[Fiber[f, y]]]]],
	TypeTheoryDefinition[Equivalence, Function[{Typed[A, TypeUniverse[u + 1]], Typed[B, TypeUniverse[u + 1]]}, DependentSum[A -> B, Function[{Typed[f, A -> B]}, IsEquivalence[f]]]]],

	(* the fiber of the identity over y is contractible to {y, the constant path}: an element {x, p} is
	   joined to it along p reversed and its connection *)
	TypeTheoryDefinition["identityEquivalence", Typed[
		Function[{Typed[A, TypeUniverse[u + 1]]}, "dependentPair"[
			Function[{Typed[x, A]}, x],
			Function[{Typed[y, A]}, "dependentPair"[
				"dependentPair"[y, Function[{j}, y]],
				Function[{Typed[w, Fiber[Function[{Typed[x, A]}, x], y]]}, Function[{Typed[i, Interval]}, "dependentPair"[w[[2]][1 - i], Function[{j}, w[[2]][Max[1 - i, j]]]]]]
			]]
		]],
		ForAll[{Typed[A, TypeUniverse[u + 1]]}, Equivalence[A, A]]
	]],

	(* An isomorphism is an equivalence: the center of the fiber over y is {g[y], s[y]}, and any element
	   {x1, p1} of it is joined to the center by the square of the cubical library's lemIso, built from
	   compositions that fill the sides t and s give. *)
	TypeTheoryDefinition["isomorphismEquivalence", Typed[
		Function[
			{
				TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[u + 1]], Typed[f, A -> B], Typed[g, B -> A],
				Typed[s, ForAll[{Typed[b, B]}, Path[B, f[g[b]], b]]], Typed[t, ForAll[{Typed[a, A]}, Path[A, g[f[a]], a]]]
			},
			"dependentPair"[f, Function[{Typed[y, B]}, "dependentPair"[
				"dependentPair"[g[y], s[y]],
				Function[{Typed[w, Fiber[f, y]]}, With[
					{x0 = g[y], p0 = s[y], x1 = w[[1]], p1 = w[[2]]},
					With[
						{
							fill0 = Function[{Typed[i, Interval], Typed[k, Interval]},
								CubicalComposition[A, Function[{m}, {i == 1 -> t[x0][Min[k, m]], i == 0 -> g[y], k == 0 -> g[p0[1 - i]]}], g[p0[1 - i]]]
							],
							fill1 = Function[{Typed[i, Interval], Typed[k, Interval]},
								CubicalComposition[A, Function[{m}, {i == 1 -> t[x1][Min[k, m]], i == 0 -> g[y], k == 0 -> g[p1[1 - i]]}], g[p1[1 - i]]]
							]
						},
						With[
							{
								fill2 = Function[{Typed[i, Interval], Typed[k, Interval]},
									CubicalComposition[A, Function[{m}, {i == 1 -> fill1[Min[k, m], 1], i == 0 -> fill0[Min[k, m], 1], k == 0 -> g[y]}], g[y]]
								]
							},
							With[
								{
									square = Function[{Typed[i, Interval], Typed[j, Interval]},
										CubicalComposition[A, Function[{k}, {i == 1 -> fill1[j, 1 - k], i == 0 -> fill0[j, 1 - k], j == 1 -> t[fill2[i, 1]][1 - k], j == 0 -> g[y]}], fill2[i, j]]
									]
								},
								Function[{Typed[i, Interval]}, "dependentPair"[
									fill2[i, 1],
									Function[{j}, CubicalComposition[B,
										Function[{k}, {i == 1 -> s[p1[j]][k], i == 0 -> s[p0[j]][k], j == 0 -> s[f[fill2[i, 1]]][k], j == 1 -> s[y][k]}],
										f[square[i, 1 - j]]
									]]
								]]
							]
						]
					]
				]]
			]]]
		],
		ForAll[
			{
				TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[u + 1]], Typed[f, A -> B], Typed[g, B -> A],
				Typed[s, ForAll[{Typed[b, B]}, Path[B, f[g[b]], b]]], Typed[t, ForAll[{Typed[a, A]}, Path[A, g[f[a]], a]]]
			},
			Equivalence[A, B]
		]
	]],
	TypeTheoryDefinition["negationInvolution", Typed[
		Function[{Typed[b, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[c, Booleans]}, Path[Booleans, "not"["not"[c]], c]], Function[{i}, "false"], Function[{i}, "true"], b]],
		ForAll[{Typed[b, Booleans]}, Path[Booleans, "not"["not"[b]], b]]
	]],
	TypeTheoryDefinition["negationEquivalence", Typed["isomorphismEquivalence"["not", "not", "negationInvolution", "negationInvolution"], Equivalence[Booleans, Booleans]]],

	(* univalence: B with A glued along e at 0 and B along the identity at 1 *)
	TypeTheoryDefinition["equivalenceToPath", Typed[
		Function[
			{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[u + 1]], Typed[e, Equivalence[A, B]], Typed[i, Interval]},
			GlueType[B, {i == 0 -> {A, e}, i == 1 -> {B, "identityEquivalence"[B]}}]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[u + 1]]}, Equivalence[A, B] -> Path[TypeUniverse[u + 1], A, B]]
	]]
}
