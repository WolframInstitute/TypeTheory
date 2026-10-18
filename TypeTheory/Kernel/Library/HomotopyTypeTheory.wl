(* ::Package:: *)

(*
The HoTT environment: homotopy type theory as the HoTT book presents it, on the rules of Martin-Löf type
theory with rewrite rules. TypeTheoryEnvironment["HomotopyTypeTheory"] gives it, built the first time it
is asked for.

The rules have no Prop, so no two proofs of an equality are made equal, and univalence is consistent with
them. Propositions are types: True has one element, False none, and Not[a] is a function into False.
Equal is the type of paths: x == y has an element for each path from x to y, and its recursor is path
induction. The operations on paths are definitions, so they compute on reflexivity:

	EqualitySymmetry[p], EqualityTransitivity[p, q]    the inverse and the concatenation of paths
	EqualityCongruence[f, p]                            the path f[x] == f[y] from p : x == y
	Transport[P, p, b]                                  b : P[x] carried along p : x == y to P[y]
	DependentCongruence[f, p]                           Transport[P, p, f[x]] == f[y], for f : (x : A) -> P[x]

An equivalence is bi-invertible: a function with a left inverse and a right inverse. Univalence is the
axiom that EqualityToEquivalence, which takes a path between types to an equivalence, is itself an
equivalence; EquivalenceToEquality is its right inverse. With it, UniverseNotSet proves that two types can
be equal in more than one way: the negation of the Booleans gives a path Booleans == Booleans that is not
reflexivity.

The circle is a higher inductive type, given by axioms: a point CircleBase, a path CircleLoop from it to
itself, and CircleInduction. On CircleBase, CircleInduction computes, by the rewrite rule
CircleInductionBase; on CircleLoop it does so up to a path, by the axiom CircleInductionLoop, whose
statement only type-checks because the rewrite rule computes.
*)


(* ::Section:: *)
(*PackageExported*)


PackageExported[Transport]
PackageExported[DependentCongruence]
PackageExported[TransportConstant]
PackageExported[IsEquivalence]
PackageExported[EquivalenceProof]
PackageExported[Equivalence]
PackageExported[EquivalenceIntroduction]
PackageExported[IdentityEquivalence]
PackageExported[EqualityToEquivalence]
PackageExported[Univalence]
PackageExported[EquivalenceToEquality]
PackageExported[UnivalenceComputation]
PackageExported[NegationEquivalence]
PackageExported[IsSet]
PackageExported[UniverseNotSet]
PackageExported[CircleBase]
PackageExported[CircleLoop]
PackageExported[CircleInduction]
PackageExported[CircleInductionBase]
PackageExported[CircleInductionLoop]


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
DependentCongruence::usage = "DependentCongruence[f, p] is the path Transport[P, p, f[x]] == f[y] that a dependent function f : (x : A) -> P[x] gives from \
a path p : x == y. It is a definition of the HoTT environment."
TransportConstant::usage = "TransportConstant[p, b] is the path Transport[Function[{x}, B], p, b] == b: transport in a constant family leaves b where it is."
IsEquivalence::usage = "IsEquivalence[f] is the type of proofs that f is an equivalence: a left inverse and a right inverse, each with its path. \
It is an inductive type of the HoTT environment, with the one constructor EquivalenceProof."
EquivalenceProof::usage = "EquivalenceProof[g, retraction, h, section] proves IsEquivalence[f] from a function g with g[f[x]] == x for every x and a function h \
with f[h[y]] == y for every y."
Equivalence::usage = "Equivalence[A, B] is the type of equivalences from A to B: a function with a proof that it is an equivalence. \
Its one constructor is EquivalenceIntroduction, and e[[1]] is the function of an equivalence e."
EquivalenceIntroduction::usage = "EquivalenceIntroduction[f, e] is the equivalence given by the function f and the proof e of IsEquivalence[f]."
IdentityEquivalence::usage = "IdentityEquivalence[A] is the identity function of A as an equivalence."
EqualityToEquivalence::usage = "EqualityToEquivalence[p] is the equivalence a path p : A == B between types gives; reflexivity gives the identity."
Univalence::usage = "Univalence[A, B] proves IsEquivalence[EqualityToEquivalence] for the types A and B: equivalent types are equal, in as many ways as \
they are equivalent. It is the axiom of the HoTT environment."
EquivalenceToEquality::usage = "EquivalenceToEquality[e] is the path A == B that univalence gives for the equivalence e from A to B."
UnivalenceComputation::usage = "UnivalenceComputation[e] proves EqualityToEquivalence[EquivalenceToEquality[e]] == e: carrying along the path of an \
equivalence is that equivalence."
NegationEquivalence::usage = "NegationEquivalence is the negation of Booleans, \"not\", as an equivalence from Booleans to Booleans, its own inverse."
IsSet::usage = "IsSet[A] is the type of proofs that any two paths between the same elements of A are equal."
UniverseNotSet::usage = "UniverseNotSet proves Not[IsSet[TypeUniverse[1]]]: by univalence, NegationEquivalence gives a path Booleans == Booleans that is not \
reflexivity, as the HoTT book shows."
CircleBase::usage = "CircleBase is the point of the circle, Circle, in the HoTT environment."
CircleLoop::usage = "CircleLoop is the path CircleBase == CircleBase that goes once around the circle."
CircleInduction::usage = "CircleInduction[P, b, l, x] gives an element of P[x] for every point x of the circle, from b : P[CircleBase] and a path \
l : Transport[P, CircleLoop, b] == b. It computes to b on CircleBase, by the rewrite rule CircleInductionBase."
CircleInductionBase::usage = "CircleInductionBase is the rewrite rule CircleInduction[P, b, l, CircleBase] -> b of the HoTT environment."
CircleInductionLoop::usage = "CircleInductionLoop[P, b, l] proves DependentCongruence[CircleInduction[P, b, l, #] &, CircleLoop] == l: on the loop, \
induction gives the path l."

homotopyTypeTheoryEnvironment::usage = "homotopyTypeTheoryEnvironment[] gives the HoTT environment, built and checked the first time."
$homotopyTypeTheoryRules::usage = "$homotopyTypeTheoryRules is the rules of the HoTT environment: Martin-Löf type theory with rewrite rules."
$univalentDeclarations::usage = "$univalentDeclarations is the declarations of the HoTT environment up to univalence and its consequences."
$circleDeclarations::usage = "$circleDeclarations is the declarations of the circle, with its rewrite rule."


(* ::Section:: *)
(*Function Definitions*)


$homotopyTypeTheoryRules = TypeTheoryRules["MartinLofTypeTheory", "RewriteRules" -> True]

homotopyTypeTheoryEnvironment[] := homotopyTypeTheoryEnvironment[] =
	withoutStoreTracking[TypeTheoryEnvironment[emptyEnvironmentOf[$homotopyTypeTheoryRules], Join[$univalentDeclarations, $circleDeclarations]]]


$univalentDeclarations = {
	(* propositions as types *)
	TypeTheoryInductiveType[True, TypeUniverse[1], {TrueIntroduction -> True}],
	TypeTheoryInductiveType[False, TypeUniverse[1], {}],
	TypeTheoryDefinition[Not, Function[{Typed[a, TypeUniverse[u + 1]]}, Implies[a, False]]],
	TypeTheoryDefinition[
		FalseElimination,
		Function[{TypedImplicit[a, TypeUniverse[u + 1]], Typed[h, False]}, InductiveRecursor[False][Function[{Typed[t, False]}, a], h]]
	],

	(* paths: the type of equalities, whose recursor is path induction *)
	TypeTheoryInductiveType[
		Equal,
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[x, A], Typed[y, A]}, TypeUniverse[u + 1]],
		{EqualityReflexivity -> ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[x, A]}, x == x]}
	],
	TypeTheoryDefinition[
		EqualitySymmetry,
		Function[
			{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[x, A], TypedImplicit[y, A], Typed[p, x == y]},
			InductiveRecursor[Equal][Function[{Typed[z, A], Typed[q, x == z]}, z == x], EqualityReflexivity[x], p]
		]
	],
	TypeTheoryDefinition[
		EqualityTransitivity,
		Function[
			{
				TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[x, A], TypedImplicit[y, A],
				TypedImplicit[z, A], Typed[p, x == y], Typed[q, y == z]
			},
			InductiveRecursor[Equal][Function[{Typed[w, A], Typed[r, y == w]}, x == w], p, q]
		]
	],
	TypeTheoryDefinition[
		EqualityCongruence,
		Function[
			{
				TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[v + 1]], Typed[f, TypeSpecifier[{A} -> B]],
				TypedImplicit[x, A], TypedImplicit[y, A], Typed[p, x == y]
			},
			InductiveRecursor[Equal][Function[{Typed[z, A], Typed[q, x == z]}, f[x] == f[z]], EqualityReflexivity[f[x]], p]
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
		DependentCongruence,
		Function[
			{
				TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[P, TypeSpecifier[{A} -> TypeUniverse[v + 1]]],
				Typed[f, ForAll[{Typed[z, A]}, P[z]]], TypedImplicit[x, A], TypedImplicit[y, A], Typed[p, x == y]
			},
			InductiveRecursor[Equal][Function[{Typed[z, A], Typed[q, x == z]}, Transport[P, q, f[x]] == f[z]], EqualityReflexivity[f[x]], p]
		]
	],
	TypeTheoryDefinition[
		TransportConstant,
		Function[
			{
				TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[v + 1]],
				TypedImplicit[x, A], TypedImplicit[y, A], Typed[p, x == y], Typed[b, B]
			},
			InductiveRecursor[Equal][Function[{Typed[z, A], Typed[q, x == z]}, Transport[Function[{Typed[w, A]}, B], q, b] == b], EqualityReflexivity[b], p]
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
			EquivalenceIntroduction -> ForAll[
				{
					TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[v + 1]],
					Typed[f, TypeSpecifier[{A} -> B]], Typed[e, IsEquivalence[f]]
				},
				Equivalence[A, B]
			]
		}
	],
	TypeTheoryDefinition[
		IdentityEquivalence,
		Function[{Typed[A, TypeUniverse[u + 1]]},
			EquivalenceIntroduction[
				Function[{Typed[x, A]}, x],
				EquivalenceProof[Function[{Typed[x, A]}, x], Function[{Typed[x, A]}, EqualityReflexivity[x]], Function[{Typed[x, A]}, x], Function[{Typed[x, A]}, EqualityReflexivity[x]]]
			]
		]
	],
	TypeTheoryDefinition[
		EqualityToEquivalence,
		Function[
			{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[u + 1]], Typed[p, A == B]},
			InductiveRecursor[Equal][Function[{Typed[C, TypeUniverse[u + 1]], Typed[q, A == C]}, Equivalence[A, C]], IdentityEquivalence[A], p]
		]
	],

	(* univalence *)
	TypeTheoryAxiom[
		Univalence,
		ForAll[{Typed[A, TypeUniverse[u + 1]], Typed[B, TypeUniverse[u + 1]]}, IsEquivalence[Function[{Typed[p, A == B]}, EqualityToEquivalence[p]]]]
	],
	TypeTheoryDefinition[
		EquivalenceToEquality,
		Function[
			{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[u + 1]], Typed[e, Equivalence[A, B]]},
			Univalence[A, B][[3]][e]
		]
	],
	TypeTheoryTheorem[
		UnivalenceComputation,
		ForAll[
			{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[u + 1]], Typed[e, Equivalence[A, B]]},
			EqualityToEquivalence[EquivalenceToEquality[e]] == e
		],
		Function[
			{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[u + 1]], Typed[e, Equivalence[A, B]]},
			Univalence[A, B][[4]][e]
		]
	],

	(* the universe is not a set: negation is a second path from the Booleans to themselves *)
	TypeTheoryDefinition[
		IsSet,
		Function[{Typed[A, TypeUniverse[u + 1]]}, ForAll[{Typed[x, A], Typed[y, A], Typed[p, x == y], Typed[q, x == y]}, p == q]]
	],
	TypeTheoryDefinition[
		NegationEquivalence,
		Typed[
			With[
				{
					involution = Function[{Typed[b, Booleans]},
						InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, "not"["not"[t]] == t], EqualityReflexivity["false"], EqualityReflexivity["true"], b]
					]
				},
				EquivalenceIntroduction["not", EquivalenceProof["not", involution, "not", involution]]
			],
			Equivalence[Booleans, Booleans]
		]
	],
	TypeTheoryTheorem[
		UniverseNotSet,
		Not[IsSet[TypeUniverse[1]]],
		Function[{Typed[s, IsSet[TypeUniverse[1]]]},
			With[
				{
					negationPath = EquivalenceToEquality[NegationEquivalence],
					onTrue = Function[{Typed[e, Equivalence[Booleans, Booleans]]}, e[[1]]["true"]]
				},
				With[
					{
						(* if every path were reflexivity, carrying true along the negation path would give true *)
						viaSet = EqualityCongruence[
							Function[{Typed[r, Booleans == Booleans]}, onTrue[EqualityToEquivalence[r]]],
							s[Booleans, Booleans, negationPath, EqualityReflexivity[Booleans]]
						],
						(* by univalence it gives what negation does, false *)
						viaUnivalence = EqualityCongruence[onTrue, UnivalenceComputation[NegationEquivalence]]
					},
					Transport[
						Function[{Typed[b, Booleans]}, InductiveRecursor[Booleans][Function[{Typed[t, Booleans]}, TypeUniverse[1]], True, False, b]],
						EqualityTransitivity[EqualitySymmetry[viaUnivalence], viaSet],
						TrueIntroduction
					]
				]
			]
		]
	]
}

$circleDeclarations = {
	TypeTheoryAxiom[Circle, TypeUniverse[1]],
	TypeTheoryAxiom[CircleBase, Circle],
	TypeTheoryAxiom[CircleLoop, CircleBase == CircleBase],
	TypeTheoryAxiom[
		CircleInduction,
		ForAll[
			{
				Typed[P, TypeSpecifier[{Circle} -> TypeUniverse[u + 1]]], Typed[b, P[CircleBase]], Typed[l, Transport[P, CircleLoop, b] == b],
				Typed[x, Circle]
			},
			P[x]
		]
	],
	TypeTheoryRewriteRule[
		CircleInductionBase,
		ForAll[
			{Typed[P, TypeSpecifier[{Circle} -> TypeUniverse[u + 1]]], Typed[b, P[CircleBase]], Typed[l, Transport[P, CircleLoop, b] == b]},
			CircleInduction[P, b, l, CircleBase] -> b
		]
	],
	TypeTheoryAxiom[
		CircleInductionLoop,
		ForAll[
			{Typed[P, TypeSpecifier[{Circle} -> TypeUniverse[u + 1]]], Typed[b, P[CircleBase]], Typed[l, Transport[P, CircleLoop, b] == b]},
			DependentCongruence[Function[{Typed[x, Circle]}, CircleInduction[P, b, l, x]], CircleLoop] == l
		]
	]
}
