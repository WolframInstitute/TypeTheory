(* ::Package:: *)

(*
The cubical environment: TypeTheoryEnvironment["Cubical"] is cubical type theory with a small library,
built and checked the first time it is asked for. Its rules are "CubicalTypeTheory", Martin-Löf type theory
with the primitives of Cubical.wl, so it has no Prop.

	DependentSum[A, B], DependentPair[a, b]     the dependent sum Σ x : A, B[x] and its pairs, which Glue types use
	Booleans, "false", "true", "not"            the Booleans and negation
	PathSymmetry, PathTransitivity, PathCongruence, PathFunctionExtensionality, PathInduction
	                                            the operations on paths, as functions of the interval and
	                                            compositions: function extensionality is a term, and path
	                                            induction transports along the path's connection
	Fiber, IsContractible, IsEquivalence, Equivalence
	                                            equivalences as functions with contractible fibers, the kernel's
	IdentityEquivalence, IsomorphismEquivalence, NegationEquivalence
	                                            the identity, an isomorphism made an equivalence by the cubical
	                                            library's construction, and negation
	EquivalenceToPath[e]                        univalence: the path of Glue types from A to B that the equivalence
	                                            e gives, along which transport applies e

Transport along EquivalenceToPath[NegationEquivalence] takes "true" to "false" by computation, which an
axiom of univalence, as in the HoTT environment, cannot do.
*)


(* ::Section:: *)
(*PackageExported*)


PackageExported[DependentSum]
PackageExported[DependentPair]
PackageExported[PathSymmetry]
PackageExported[PathTransitivity]
PackageExported[PathCongruence]
PackageExported[PathFunctionExtensionality]
PackageExported[PathInduction]
PackageExported[Fiber]
PackageExported[IsContractible]
PackageExported[IsomorphismEquivalence]
PackageExported[NegationInvolution]
PackageExported[EquivalenceToPath]


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[cubicalEnvironment]


(* ::Section:: *)
(*Usage Messages*)


DependentSum::usage = "DependentSum[A, B] is the dependent sum Σ x : A, B[x] of the cubical environment, whose elements are the pairs DependentPair[a, b]; \
TypeTheoryCubical names it for Glue types."
DependentPair::usage = "DependentPair[a, b] is the pair of a and b : B[a] in DependentSum[A, B], in the cubical environment."
PathSymmetry::usage = "PathSymmetry[p] is the path p reversed, the function of i that is p[1 - i]. It is a definition of the cubical environment."
PathTransitivity::usage = "PathTransitivity[p, q] is the path p followed by q, a composition. It is a definition of the cubical environment."
PathCongruence::usage = "PathCongruence[f, p] is the path f[x] to f[y] that a function f gives from a path p from x to y, the function of i that is f[p[i]]. \
It is a definition of the cubical environment."
PathFunctionExtensionality::usage = "PathFunctionExtensionality[h] is the path from f to g that a path h[x] from f[x] to g[x] for every x gives: the function \
of i that is the function of x that is h[x][i]. It is a definition of the cubical environment."
PathInduction::usage = "PathInduction[P, d, p] gives P[y, p] for a path p from x to y from d : P[x, the constant path]: transport along the path's \
connection, the function of i that is P[p[i], the function of j that is p[Min[i, j]]]. It is a definition of the cubical environment."
Fiber::usage = "Fiber[f, y] is the type of the elements x with a path from f[x] to y, in the cubical environment."
IsContractible::usage = "IsContractible[X] is the type of an element c of X with a path from c to every element, in the cubical environment."
IsomorphismEquivalence::usage = "IsomorphismEquivalence[f, g, s, t] is the equivalence a function f with an inverse g gives, s and t the paths f[g[b]] to b and \
g[f[a]] to a, by the construction of the cubical library of Agda. It is a definition of the cubical environment."
NegationInvolution::usage = "NegationInvolution[b] is the path from \"not\"[\"not\"[b]] to b for a Boolean b, in the cubical environment."
EquivalenceToPath::usage = "EquivalenceToPath[e] is the path of types from A to B that an equivalence e from A to B gives, the function of i that is the Glue \
type over B with A glued along e where i is 0 and B along the identity where i is 1: univalence, which computes. It is a definition of the cubical environment."

cubicalEnvironment::usage = "cubicalEnvironment[] gives TypeTheoryEnvironment[\"Cubical\"], built and checked once per session."


(* ::Section:: *)
(*Function Definitions*)


cubicalEnvironment[] := cubicalEnvironment[] = withoutStoreTracking[withStoreCleanup[
	TypeTheoryEnvironment[TypeTheoryRules["CubicalTypeTheory"], $cubicalDeclarations]
]]

$cubicalDeclarations = {
	TypeTheoryInductiveType[DependentSum, ForAll[{Typed[A, TypeUniverse[u + 1]], Typed[B, TypeSpecifier[{A} -> TypeUniverse[v + 1]]]}, TypeUniverse[Max[u + 1, v + 1]]], {
		DependentPair -> ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeSpecifier[{A} -> TypeUniverse[v + 1]]], Typed[a, A], Typed[b, B[a]]}, DependentSum[A, B]]
	}],
	TypeTheoryCubical[DependentSum],
	TypeTheoryInductiveType[Booleans, TypeUniverse[1], {"false" -> Booleans, "true" -> Booleans}],
	TypeTheoryDefinition["not", Function[{Typed[a, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Booleans], "true", "false", a]]],

	(* paths *)
	TypeTheoryDefinition[PathSymmetry, Typed[
		Function[{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[x, A], TypedImplicit[y, A], Typed[p, Path[A, x, y]], Typed[i, Interval]}, p[1 - i]],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[x, A], TypedImplicit[y, A]}, Path[A, x, y] -> Path[A, y, x]]
	]],
	TypeTheoryDefinition[PathTransitivity, Typed[
		Function[
			{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[x, A], TypedImplicit[y, A], TypedImplicit[z, A], Typed[p, Path[A, x, y]], Typed[q, Path[A, y, z]], Typed[i, Interval]},
			CubicalComposition[A, Function[{j}, {i == 0 -> x, i == 1 -> q[j]}], p[i]]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[x, A], TypedImplicit[y, A], TypedImplicit[z, A]}, Path[A, x, y] -> Path[A, y, z] -> Path[A, x, z]]
	]],
	TypeTheoryDefinition[PathCongruence, Typed[
		Function[
			{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[v + 1]], Typed[f, A -> B], TypedImplicit[x, A], TypedImplicit[y, A], Typed[p, Path[A, x, y]], Typed[i, Interval]},
			f[p[i]]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[v + 1]], Typed[f, A -> B], TypedImplicit[x, A], TypedImplicit[y, A]}, Path[A, x, y] -> Path[B, f[x], f[y]]]
	]],
	TypeTheoryDefinition[PathFunctionExtensionality, Typed[
		Function[
			{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[v + 1]], TypedImplicit[f, A -> B], TypedImplicit[g, A -> B], Typed[h, ForAll[{Typed[x, A]}, Path[B, f[x], g[x]]]], Typed[i, Interval]},
			Function[{Typed[x, A]}, h[x][i]]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[v + 1]], TypedImplicit[f, A -> B], TypedImplicit[g, A -> B]}, ForAll[{Typed[x, A]}, Path[B, f[x], g[x]]] -> Path[A -> B, f, g]]
	]],
	TypeTheoryDefinition[PathInduction, Typed[
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
	TypeTheoryDefinition[IdentityEquivalence, Typed[
		Function[{Typed[A, TypeUniverse[u + 1]]}, DependentPair[
			Function[{Typed[x, A]}, x],
			Function[{Typed[y, A]}, DependentPair[
				DependentPair[y, Function[{j}, y]],
				Function[{Typed[w, Fiber[Function[{Typed[x, A]}, x], y]]}, Function[{Typed[i, Interval]}, DependentPair[w[[2]][1 - i], Function[{j}, w[[2]][Max[1 - i, j]]]]]]
			]]
		]],
		ForAll[{Typed[A, TypeUniverse[u + 1]]}, Equivalence[A, A]]
	]],

	(* An isomorphism is an equivalence: the center of the fiber over y is {g[y], s[y]}, and any element
	   {x1, p1} of it is joined to the center by the square of the cubical library's lemIso, built from
	   compositions that fill the sides t and s give. *)
	TypeTheoryDefinition[IsomorphismEquivalence, Typed[
		Function[
			{
				TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[u + 1]], Typed[f, A -> B], Typed[g, B -> A],
				Typed[s, ForAll[{Typed[b, B]}, Path[B, f[g[b]], b]]], Typed[t, ForAll[{Typed[a, A]}, Path[A, g[f[a]], a]]]
			},
			DependentPair[f, Function[{Typed[y, B]}, DependentPair[
				DependentPair[g[y], s[y]],
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
								Function[{Typed[i, Interval]}, DependentPair[
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
	TypeTheoryDefinition[NegationInvolution, Typed[
		Function[{Typed[b, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[c, Booleans]}, Path[Booleans, "not"["not"[c]], c]], Function[{i}, "false"], Function[{i}, "true"], b]],
		ForAll[{Typed[b, Booleans]}, Path[Booleans, "not"["not"[b]], b]]
	]],
	TypeTheoryDefinition[NegationEquivalence, Typed[IsomorphismEquivalence["not", "not", NegationInvolution, NegationInvolution], Equivalence[Booleans, Booleans]]],

	(* univalence: B with A glued along e at 0 and B along the identity at 1 *)
	TypeTheoryDefinition[EquivalenceToPath, Typed[
		Function[
			{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[u + 1]], Typed[e, Equivalence[A, B]], Typed[i, Interval]},
			GlueType[B, {i == 0 -> {A, e}, i == 1 -> {B, IdentityEquivalence[B]}}]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[u + 1]]}, Equivalence[A, B] -> Path[TypeUniverse[u + 1], A, B]]
	]]
}
