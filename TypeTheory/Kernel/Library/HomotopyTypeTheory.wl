(* ::Package:: *)

(*
The HoTT environment: homotopy type theory as the HoTT book presents it, on the rules of Martin-Löf type
theory with rewrite rules. TypeTheoryEnvironment["HomotopyTypeTheory"] gives it, built the first time it
is asked for.

The rules have no Prop, so no two proofs of an equality are made equal, and univalence is consistent with
them. Propositions are types: True has one element, False none, and Not[a] is a function into False.
Equal is the type of paths: x == y has an element for each path from x to y, and its recursor is path
induction. The operations on paths are definitions, so they compute on reflexivity:

	"equalitySymmetry"[p], "equalityTransitivity"[p, q]    the inverse and the concatenation of paths
	"equalityCongruence"[f, p]                            the path f[x] == f[y] from p : x == y
	Transport[P, p, b]                                  b : P[x] carried along p : x == y to P[y]
	"dependentCongruence"[f, p]                           Transport[P, p, f[x]] == f[y], for f : (x : A) -> P[x]

An equivalence is bi-invertible: a function with a left inverse and a right inverse. "univalence" is the
axiom that "equalityToEquivalence", which takes a path between types to an equivalence, is itself an
equivalence; "equivalenceToEquality" is its right inverse. With it, "universeNotSet" proves that two types can
be equal in more than one way: the negation of the Booleans gives a path Booleans == Booleans that is not
reflexivity.

The circle is a higher inductive type, given by axioms: a point "circleBase", a path "circleLoop" from it to
itself, and "circleInduction". On "circleBase", "circleInduction" computes, by the rewrite rule
"circleInductionBase"; on "circleLoop" it does so up to a path, by the axiom "circleInductionLoop", whose
statement only type-checks because the rewrite rule computes.
*)


(* ::Section:: *)
(*PackageExported*)


PackageExported[Transport]
PackageExported[IsEquivalence]
PackageExported[EquivalenceProof]
PackageExported[Equivalence]
PackageExported[IsSet]


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[homotopyTypeTheoryEnvironment]
PackageScoped[$homotopyTypeTheoryRules]
PackageScoped[$univalentDeclarations]
PackageScoped[$circleDeclarations]


(* ::Section:: *)
(*Usage Messages*)


Transport::usage = "Transport[P, p, b] carries b, an element of P[x], along the path p : x == y to an element of P[y]; it is b when p is reflexivity. \
It is a definition of the HoTT environment."
IsEquivalence::usage = "IsEquivalence[f] is the type of proofs that f is an equivalence. In the HoTT environment it is an inductive type, a left inverse and a \
right inverse, each with its path, with the one constructor EquivalenceProof; in the cubical environment it is a definition, the contractibility of every fiber of f."
EquivalenceProof::usage = "EquivalenceProof[g, retraction, h, section] proves IsEquivalence[f] from a function g with g[f[x]] == x for every x and a function h \
with f[h[y]] == y for every y."
Equivalence::usage = "Equivalence[A, B] is the type of equivalences from A to B: a function with a proof that it is an equivalence, and e[[1]] is the function \
of an equivalence e. In the HoTT environment its one constructor is \"equivalenceIntroduction\"; in the cubical environment it is a dependent sum, DependentSum[A -> B, IsEquivalence]."
IsSet::usage = "IsSet[A] is the type of proofs that any two paths between the same elements of A are equal."

homotopyTypeTheoryEnvironment::usage = "homotopyTypeTheoryEnvironment[] gives the HoTT environment, built and checked the first time."
$homotopyTypeTheoryRules::usage = "$homotopyTypeTheoryRules is the rules of the HoTT environment: Martin-Löf type theory with rewrite rules."
$univalentDeclarations::usage = "$univalentDeclarations is the declarations of the HoTT environment up to univalence and its consequences."
$circleDeclarations::usage = "$circleDeclarations is the declarations of the circle, with its rewrite rule."


(* ::Section:: *)
(*Function Definitions*)


$homotopyTypeTheoryRules = TypeTheoryRules["MartinLofTypeTheory", "RewriteRules" -> True]

homotopyTypeTheoryEnvironment[] := homotopyTypeTheoryEnvironment[] = withoutStoreTracking[With[{empty = emptyEnvironmentOf[$homotopyTypeTheoryRules]},
	libraryEnvironment["HomotopyTypeTheory", empty, TypeTheoryEnvironment[empty, Join[$univalentDeclarations, $circleDeclarations]]]
]]


$univalentDeclarations = {
	(* propositions as types *)
	TypeTheoryInductiveType[True, TypeUniverse[1], {"trueIntroduction" -> True}],
	TypeTheoryInductiveType[False, TypeUniverse[1], {}],
	TypeTheoryDefinition[Not, Function[{Typed[a, TypeUniverse[u + 1]]}, Implies[a, False]]],
	TypeTheoryDefinition[
		"falseElimination",
		Function[{TypedImplicit[a, TypeUniverse[u + 1]], Typed[h, False]}, InductiveRecursor[False][Function[{Typed[t, False]}, a], h]]
	],

	(* paths: the type of equalities, whose recursor is path induction *)
	TypeTheoryInductiveType[
		Equal,
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[x, A], Typed[y, A]}, TypeUniverse[u + 1]],
		{"equalityReflexivity" -> ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[x, A]}, x == x]}
	],
	TypeTheoryDefinition[
		"equalitySymmetry",
		Function[
			{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[x, A], TypedImplicit[y, A], Typed[p, x == y]},
			InductiveRecursor[Equal][Function[{Typed[z, A], Typed[q, x == z]}, z == x], "equalityReflexivity"[x], p]
		]
	],
	TypeTheoryDefinition[
		"equalityTransitivity",
		Function[
			{
				TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[x, A], TypedImplicit[y, A],
				TypedImplicit[z, A], Typed[p, x == y], Typed[q, y == z]
			},
			InductiveRecursor[Equal][Function[{Typed[w, A], Typed[r, y == w]}, x == w], p, q]
		]
	],
	TypeTheoryDefinition[
		"equalityCongruence",
		Function[
			{
				TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[v + 1]], Typed[f, TypeSpecifier[{A} -> B]],
				TypedImplicit[x, A], TypedImplicit[y, A], Typed[p, x == y]
			},
			InductiveRecursor[Equal][Function[{Typed[z, A], Typed[q, x == z]}, f[x] == f[z]], "equalityReflexivity"[f[x]], p]
		]
	],
	TypeTheoryDefinition[
		Transport,
		Function[
			{
				TypedImplicit[A, TypeUniverse[u + 1]], Typed[P, TypeSpecifier[{A} -> TypeUniverse[v + 1]]],
				TypedImplicit[x, A], TypedImplicit[y, A], Typed[p, x == y], Typed[b, P[x]]
			},
			InductiveRecursor[Equal][Function[{Typed[z, A], Typed[q, x == z]}, P[z]], b, p]
		]
	],
	TypeTheoryDefinition[
		"dependentCongruence",
		Function[
			{
				TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[P, TypeSpecifier[{A} -> TypeUniverse[v + 1]]],
				Typed[f, ForAll[{Typed[z, A]}, P[z]]], TypedImplicit[x, A], TypedImplicit[y, A], Typed[p, x == y]
			},
			InductiveRecursor[Equal][Function[{Typed[z, A], Typed[q, x == z]}, Transport[P, q, f[x]] == f[z]], "equalityReflexivity"[f[x]], p]
		]
	],
	TypeTheoryDefinition[
		"transportConstant",
		Function[
			{
				TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[v + 1]],
				TypedImplicit[x, A], TypedImplicit[y, A], Typed[p, x == y], Typed[b, B]
			},
			InductiveRecursor[Equal][Function[{Typed[z, A], Typed[q, x == z]}, Transport[Function[{Typed[w, A]}, B], q, b] == b], "equalityReflexivity"[b], p]
		]
	],

	(* the Booleans *)
	TypeTheoryInductiveType[Booleans, TypeUniverse[1], {"false" -> Booleans, "true" -> Booleans}],
	TypeTheoryDefinition["not", Function[{Typed[a, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, Booleans], "true", "false", a]]],

	(* equivalences, bi-invertible *)
	TypeTheoryInductiveType[
		IsEquivalence,
		ForAll[
			{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[v + 1]], Typed[f, TypeSpecifier[{A} -> B]]},
			TypeUniverse[Max[u, v] + 1]
		],
		{
			EquivalenceProof -> ForAll[
				{
					TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[v + 1]],
					TypedImplicit[f, TypeSpecifier[{A} -> B]],
					Typed[g, TypeSpecifier[{B} -> A]], Typed[retraction, ForAll[{Typed[x, A]}, g[f[x]] == x]],
					Typed[h, TypeSpecifier[{B} -> A]], Typed[section, ForAll[{Typed[y, B]}, f[h[y]] == y]]
				},
				IsEquivalence[f]
			]
		}
	],
	TypeTheoryInductiveType[
		Equivalence,
		ForAll[{Typed[A, TypeUniverse[u + 1]], Typed[B, TypeUniverse[v + 1]]}, TypeUniverse[Max[u, v] + 1]],
		{
			"equivalenceIntroduction" -> ForAll[
				{
					TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[v + 1]],
					Typed[f, TypeSpecifier[{A} -> B]], Typed[e, IsEquivalence[f]]
				},
				Equivalence[A, B]
			]
		}
	],
	TypeTheoryDefinition[
		"identityEquivalence",
		Function[{Typed[A, TypeUniverse[u + 1]]},
			"equivalenceIntroduction"[
				Function[{Typed[x, A]}, x],
				EquivalenceProof[Function[{Typed[x, A]}, x], Function[{Typed[x, A]}, "equalityReflexivity"[x]], Function[{Typed[x, A]}, x], Function[{Typed[x, A]}, "equalityReflexivity"[x]]]
			]
		]
	],
	TypeTheoryDefinition[
		"equalityToEquivalence",
		Function[
			{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[u + 1]], Typed[p, A == B]},
			InductiveRecursor[Equal][Function[{Typed[C, TypeUniverse[u + 1]], Typed[q, A == C]}, Equivalence[A, C]], "identityEquivalence"[A], p]
		]
	],

	(* univalence *)
	TypeTheoryAxiom[
		"univalence",
		ForAll[{Typed[A, TypeUniverse[u + 1]], Typed[B, TypeUniverse[u + 1]]}, IsEquivalence[Function[{Typed[p, A == B]}, "equalityToEquivalence"[p]]]]
	],
	TypeTheoryDefinition[
		"equivalenceToEquality",
		Function[
			{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[u + 1]], Typed[e, Equivalence[A, B]]},
			"univalence"[A, B][[3]][e]
		]
	],
	TypeTheoryTheorem[
		"univalenceComputation",
		ForAll[
			{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[u + 1]], Typed[e, Equivalence[A, B]]},
			"equalityToEquivalence"["equivalenceToEquality"[e]] == e
		],
		Function[
			{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[u + 1]], Typed[e, Equivalence[A, B]]},
			"univalence"[A, B][[4]][e]
		]
	],

	(* the universe is not a set: negation is a second path from the Booleans to themselves *)
	TypeTheoryDefinition[
		IsSet,
		Function[{Typed[A, TypeUniverse[u + 1]]}, ForAll[{Typed[x, A], Typed[y, A], Typed[p, x == y], Typed[q, x == y]}, p == q]]
	],
	TypeTheoryDefinition[
		"negationEquivalence",
		Typed[
			With[
				{
					involution = Function[{Typed[b, Booleans]},
						InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, "not"["not"[t]] == t], "equalityReflexivity"["false"], "equalityReflexivity"["true"], b]
					]
				},
				"equivalenceIntroduction"["not", EquivalenceProof["not", involution, "not", involution]]
			],
			Equivalence[Booleans, Booleans]
		]
	],
	TypeTheoryTheorem[
		"universeNotSet",
		Not[IsSet[TypeUniverse[1]]],
		Function[{Typed[s, IsSet[TypeUniverse[1]]]},
			With[
				{
					negationPath = "equivalenceToEquality"["negationEquivalence"],
					onTrue = Function[{Typed[e, Equivalence[Booleans, Booleans]]}, e[[1]]["true"]]
				},
				With[
					{
						(* if every path were reflexivity, carrying true along the negation path would give true *)
						viaSet = "equalityCongruence"[
							Function[{Typed[r, Booleans == Booleans]}, onTrue["equalityToEquivalence"[r]]],
							s[Booleans, Booleans, negationPath, "equalityReflexivity"[Booleans]]
						],
						(* by univalence it gives what negation does, false *)
						viaUnivalence = "equalityCongruence"[onTrue, "univalenceComputation"["negationEquivalence"]]
					},
					Transport[
						Function[{Typed[b, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, TypeUniverse[1]], True, False, b]],
						"equalityTransitivity"["equalitySymmetry"[viaUnivalence], viaSet],
						"trueIntroduction"
					]
				]
			]
		]
	]
}

$circleDeclarations = {
	TypeTheoryAxiom[Circle, TypeUniverse[1]],
	TypeTheoryAxiom["circleBase", Circle],
	TypeTheoryAxiom["circleLoop", "circleBase" == "circleBase"],
	TypeTheoryAxiom[
		"circleInduction",
		ForAll[
			{
				Typed[P, TypeSpecifier[{Circle} -> TypeUniverse[u + 1]]], Typed[b, P["circleBase"]], Typed[l, Transport[P, "circleLoop", b] == b],
				Typed[x, Circle]
			},
			P[x]
		]
	],
	TypeTheoryRewriteRule[
		"circleInductionBase",
		ForAll[
			{Typed[P, TypeSpecifier[{Circle} -> TypeUniverse[u + 1]]], Typed[b, P["circleBase"]], Typed[l, Transport[P, "circleLoop", b] == b]},
			"circleInduction"[P, b, l, "circleBase"] -> b
		]
	],
	TypeTheoryAxiom[
		"circleInductionLoop",
		ForAll[
			{Typed[P, TypeSpecifier[{Circle} -> TypeUniverse[u + 1]]], Typed[b, P["circleBase"]], Typed[l, Transport[P, "circleLoop", b] == b]},
			"dependentCongruence"[Function[{Typed[x, Circle]}, "circleInduction"[P, b, l, x]], "circleLoop"] == l
		]
	]
}
