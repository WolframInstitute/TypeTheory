(* ::Package::"Tags"-><|"BadSymbol" -> <|"Match" -> <|Enabled -> False|>|>|>:: *)

(*
The Wolfram Language: TypeTheoryEnvironment["WolframLanguage"] is the prelude with the expressions of the Wolfram
Language and the monad of pattern matching, built and checked the first time it is asked for.

	Strings                         the strings, each the list of its character codes, "string"[{97, 98}], which a
	                                string literal "ab" is where a string is expected
	Atoms                           the expressions with no parts, as data: "symbolAtom" of a symbol's full name,
	                                "naturalAtom" and "negativeAtom" of an integer, "stringAtom" of a string, and
	                                "otherAtom" of the head and the InputForm of any other atom
	Expressions                     an expression: "atom"[a], or "normal"[h, {a, ...}], h applied to the
	                                list of its arguments
	Head, Arguments, AtomQ          the head of an expression, the list of its arguments, {} for an atom, and whether it
	                                is an atom
	Sequence[A, B, ...]             where a type is expected, the type of the sequences Sequence[a, b, ...] of an element
	                                of A, then of B, ...: a list of elements of different types, its length and their
	                                types given by its type, as Lean's HList, indexed by the list {A, B, ...};
	                                "emptySequence" and "sequencePrepend" construct it, and Sequence[a, ...] writes them
	SameQ                           whether two expressions are the same, a Boolean the kernel computes: atoms by their
	                                names and values, normal expressions part by part
	ExpressionValue                 the value the Wolfram Language evaluates an expression to, opaque
	Drop                            a list without its first n elements
	Match[A]                        the results of a match, {A}: none, one, or several in the order they are tried
	MatchValue, {}                  one result, a single value, and none
	MatchSum                        the results of one match, then those of another: a pattern's alternatives in order,
	                                where every match with several results comes from
	MatchBind                       the results of a match, each continued by another match: a pattern's parts in turn
	Condition                       the results of a match where a Boolean holds: a condition
	MatchPart                       a match at the part of an expression at a position, 0 its head, none out of range
	MatchQ                          whether a match has a result
	MatchFirst                      the first result, an Option: the rule the Wolfram Language applies, none where no
	                                rule matches and the expression stays as it is
	Replace, ReplaceList, ReplaceAll, ReplaceRepeated   rewriting by rules, lhs -> rhs and lhs :> rhs written as a term
	                                where a function from an expression to its matches is expected
Match, MatchValue, MatchSum and MatchPart follow the match objects of the prototype paclet Wolfram/Patterns and the
Match IR the WolframKernel project's compiler built from them: Values is MatchValue, one result of one value, Sum is
MatchSum, which holds every multiplicity, Product is MatchBind, the parts in turn, and a Guard is Condition.
Match is the monad of lists, the monad of nondeterminism, with its alternatives in order, so a pattern that matches in
several ways, as an Orderless or a sequence pattern does, has several results, and the first is the one the Wolfram
Language takes. A natural number and a string are expressions where one is expected, by coercions, and so is a symbol
that names nothing, which stands for itself as a Wolfram Language symbol without a value does: Replace[f[1, 2], ...]
rewrites the expression f[1, 2], and HoldForm keeps a constant that computes, as 1 + 2, from computing.

A Wolfram Language function is applied to a sequence: f[a, b] gives f the sequence of a and b, and the curried f[a][b]
gives f the sequence of a, then gives its value that of b. A binder of a type Sequence[...] takes the arguments of an
application that are left as one Sequence, so a function of the type Sequence[A, B] -> C is applied as f[a, b],
and is another function than one of the curried type A -> B -> C.
*)


(* ::Section:: *)
(*PackageExported*)


PackageExported[Atoms]
PackageExported[Expressions]
PackageExported[Arguments]
PackageExported[ExpressionValue]
PackageExported[Strings]
PackageExported[Match]
PackageExported[MatchValue]
PackageExported[MatchSum]
PackageExported[MatchPart]
PackageExported[MatchBind]
PackageExported[MatchFirst]


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[wolframLanguageEnvironment]


(* ::Section:: *)
(*Usage Messages*)


Atoms::usage = "Atoms is the type of the expressions of the Wolfram Language with no parts, as data: a symbol by its full name, an integer, a string, or another atom by its head and InputForm. It is a constant of TypeTheoryEnvironment[\"WolframLanguage\"]."
Expressions::usage = "Expressions is the type of the expressions of the Wolfram Language, each \"atom\"[a] or \"normal\"[h, s]. It is a constant of TypeTheoryEnvironment[\"WolframLanguage\"]."
Arguments::usage = "Arguments[e] is the list of the arguments of the expression e, {} for an atom."
Strings::usage = "Strings is the type of the strings of the Wolfram Language, each the list of its character codes: a string literal \"abc\" is one where a string is expected, and an expression where one is expected."
ExpressionValue::usage = "ExpressionValue[e] is the expression the Wolfram Language evaluates the expression e to: an axiom, which the kernel never computes."
Match::usage = "Match[A] is the type of the matches with results in A: the list of their results, none, one, or several in the order they are tried. It is a constant of TypeTheoryEnvironment[\"WolframLanguage\"]."
MatchValue::usage = "MatchValue[a] is the match with one result, the value a."
MatchSum::usage = "MatchSum[m1, m2] is the match whose results are those of m1, then those of m2: the alternatives of a pattern, in order."
MatchPart::usage = "MatchPart[e, k, f] is the match f of the part of the expression e at the position k, 0 its head and k its k-th argument, with no result where e has no such part."
MatchBind::usage = "MatchBind[m, f] is the match whose results are those of f applied to each result of m, in order."
MatchFirst::usage = "MatchFirst[m] is the first result of the match m, \"some\" of it, or \"none\" where m has none: the rule the Wolfram Language applies."
wolframLanguageEnvironment::usage = "wolframLanguageEnvironment[] gives the prelude with the expressions of the Wolfram Language and the monad of pattern matching, built and checked the first time it is asked for."


(* ::Section:: *)
(*Function Definitions*)


wolframLanguageEnvironment[] := builtWolframLanguageEnvironment[]

builtWolframLanguageEnvironment[] := builtWolframLanguageEnvironment[] = withoutStoreTracking[
	libraryEnvironment["WolframLanguage", preludeEnvironment[], withStoreCleanup[TypeTheoryEnvironment[preludeEnvironment[], $wolframLanguageDeclarations]]]
]

$wolframLanguageDeclarations = {
	(* a string is the list of the codes of its characters, so that two strings compare by computation; an atom is a
	   symbol by its full name, a natural number, a negative integer, -(n + 1) for n, a string, or any other atom by its
	   head and its InputForm *)
	TypeTheoryInductiveType[Strings, TypeUniverse[1], {"string" -> ({NonNegativeIntegers} -> Strings)}],
	TypeTheoryInductiveType[Atoms, TypeUniverse[1], {
		"symbolAtom" -> (Strings -> Atoms),
		"naturalAtom" -> (NonNegativeIntegers -> Atoms),
		"negativeAtom" -> (NonNegativeIntegers -> Atoms),
		"stringAtom" -> (Strings -> Atoms),
		"otherAtom" -> (Strings -> Strings -> Atoms)
	}],
	TypeTheoryInductiveType[Expressions, TypeUniverse[1], {
		"atom" -> (Atoms -> Expressions),
		"normal" -> (Expressions -> {Expressions} -> Expressions)
	}],
	(* the sequences of elements of the types of a list, as Lean's HList, a universe above its elements *)
	TypeTheoryInductiveType[
		Sequence,
		ForAll[{Typed[types, {TypeUniverse[u + 1]}]}, TypeUniverse[u + 2]],
		{
			"emptySequence" -> Sequence[Typed[{}, {TypeUniverse[u + 1]}]],
			"sequencePrepend" -> ForAll[
				{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[As, {TypeUniverse[u + 1]}], Typed[x, A], Typed[xs, Sequence[As]]},
				Sequence[Prepend[A][As]]
			]
		}
	],
	TypeTheoryDefinition["NaturalExpressionCoercion", Typed[n, NonNegativeIntegers] |-> "atom"["naturalAtom"[n]], "Coercion" -> True],
	TypeTheoryDefinition["StringExpressionCoercion", Typed[s, Strings] |-> "atom"["stringAtom"[s]], "Coercion" -> True],

	(* whether two lists of natural numbers, two strings and two atoms are the same *)
	TypeTheoryDefinition["naturalListSameQ", Typed[
		Function[{Typed[l, {NonNegativeIntegers}]},
			InductiveRecursor[List][
				Function[{Typed[t, {NonNegativeIntegers}]}, {NonNegativeIntegers} -> Booleans],
				Function[{Typed[m, {NonNegativeIntegers}]}, InductiveRecursor[List][Typed[t, {NonNegativeIntegers}] |-> Booleans, "true", {Typed[y, NonNegativeIntegers], Typed[ys, {NonNegativeIntegers}], Typed[r, Booleans]} |-> "false", m]],
				Function[{Typed[x, NonNegativeIntegers], Typed[rest, {NonNegativeIntegers}], Typed[same, {NonNegativeIntegers} -> Booleans]},
					Function[{Typed[m, {NonNegativeIntegers}]}, InductiveRecursor[List][
						Typed[t, {NonNegativeIntegers}] |-> Booleans,
						"false",
						{Typed[y, NonNegativeIntegers], Typed[ys, {NonNegativeIntegers}], Typed[r, Booleans]} |-> And[Decide[x == y], same[ys]],
						m
					]]
				],
				l
			]
		],
		{NonNegativeIntegers} -> {NonNegativeIntegers} -> Booleans
	]],
	TypeTheoryDefinition["stringSameQ", Typed[
		Function[{Typed[s, Strings], Typed[t, Strings]},
			InductiveRecursor[Strings][Typed[x, Strings] |-> Booleans, Typed[codes, {NonNegativeIntegers}] |->
				InductiveRecursor[Strings][Typed[y, Strings] |-> Booleans, Typed[others, {NonNegativeIntegers}] |-> "naturalListSameQ"[codes, others], t],
				s
			]
		],
		Strings -> Strings -> Booleans
	]],
	TypeTheoryDefinition["atomSameQ", Typed[
		Function[{Typed[a, Atoms], Typed[b, Atoms]},
			InductiveRecursor[Atoms][
				Typed[x, Atoms] |-> Booleans,
				Typed[s, Strings] |-> InductiveRecursor[Atoms][Typed[y, Atoms] |-> Booleans,
					Typed[t, Strings] |-> "stringSameQ"[s, t], Typed[m, NonNegativeIntegers] |-> "false", Typed[m, NonNegativeIntegers] |-> "false",
					Typed[t, Strings] |-> "false", {Typed[h, Strings], Typed[t, Strings]} |-> "false", b],
				Typed[n, NonNegativeIntegers] |-> InductiveRecursor[Atoms][Typed[y, Atoms] |-> Booleans,
					Typed[t, Strings] |-> "false", Typed[m, NonNegativeIntegers] |-> Decide[n == m], Typed[m, NonNegativeIntegers] |-> "false",
					Typed[t, Strings] |-> "false", {Typed[h, Strings], Typed[t, Strings]} |-> "false", b],
				Typed[n, NonNegativeIntegers] |-> InductiveRecursor[Atoms][Typed[y, Atoms] |-> Booleans,
					Typed[t, Strings] |-> "false", Typed[m, NonNegativeIntegers] |-> "false", Typed[m, NonNegativeIntegers] |-> Decide[n == m],
					Typed[t, Strings] |-> "false", {Typed[h, Strings], Typed[t, Strings]} |-> "false", b],
				Typed[s, Strings] |-> InductiveRecursor[Atoms][Typed[y, Atoms] |-> Booleans,
					Typed[t, Strings] |-> "false", Typed[m, NonNegativeIntegers] |-> "false", Typed[m, NonNegativeIntegers] |-> "false",
					Typed[t, Strings] |-> "stringSameQ"[s, t], {Typed[h, Strings], Typed[t, Strings]} |-> "false", b],
				{Typed[g, Strings], Typed[s, Strings]} |-> InductiveRecursor[Atoms][Typed[y, Atoms] |-> Booleans,
					Typed[t, Strings] |-> "false", Typed[m, NonNegativeIntegers] |-> "false", Typed[m, NonNegativeIntegers] |-> "false",
					Typed[t, Strings] |-> "false", {Typed[h, Strings], Typed[t, Strings]} |-> And["stringSameQ"[g, h], "stringSameQ"[s, t]], b],
				a
			]
		],
		Atoms -> Atoms -> Booleans
	]],
	(* the head of an atom, the symbol Symbol, Integer, String or the head it was given *)
	TypeTheoryDefinition["atomHead", Typed[
		Function[{Typed[a, Atoms]},
			InductiveRecursor[Atoms][
				Typed[x, Atoms] |-> Atoms,
				Typed[s, Strings] |-> "symbolAtom"["System`Symbol"],
				Typed[n, NonNegativeIntegers] |-> "symbolAtom"["System`Integer"],
				Typed[n, NonNegativeIntegers] |-> "symbolAtom"["System`Integer"],
				Typed[s, Strings] |-> "symbolAtom"["System`String"],
				{Typed[h, Strings], Typed[s, Strings]} |-> "symbolAtom"[h],
				a
			]
		],
		Atoms -> Atoms
	]],

	(* an expression's head and its arguments, by the recursor of expressions, whose second motive is that of their
	   sequences of arguments *)
	TypeTheoryDefinition[Head, Typed[
		Function[{Typed[e, Expressions]},
			InductiveRecursor[Expressions][
				Function[{Typed[x, Expressions]}, Expressions],
				Function[{Typed[xs, {Expressions}]}, {Expressions}],
				Function[{Typed[a, Atoms]}, "atom"["atomHead"[a]]],
				Function[{Typed[h, Expressions], Typed[arguments, {Expressions}], Typed[hr, Expressions], Typed[ar, {Expressions}]}, h],
				{},
				Function[{Typed[x, Expressions], Typed[rest, {Expressions}], Typed[xr, Expressions], Typed[rr, {Expressions}]}, rr],
				e
			]
		],
		Expressions -> Expressions
	]],
	TypeTheoryDefinition[Arguments, Typed[
		Function[{Typed[e, Expressions]},
			InductiveRecursor[Expressions][
				Function[{Typed[x, Expressions]}, {Expressions}],
				Function[{Typed[xs, {Expressions}]}, {Expressions}],
				Function[{Typed[a, Atoms]}, {}],
				Function[{Typed[h, Expressions], Typed[arguments, {Expressions}], Typed[hr, {Expressions}], Typed[ar, {Expressions}]}, arguments],
				{},
				Function[{Typed[x, Expressions], Typed[rest, {Expressions}], Typed[xr, {Expressions}], Typed[rr, {Expressions}]}, rr],
				e
			]
		],
		Expressions -> {Expressions}
	]],

	TypeTheoryDefinition[AtomQ, Typed[
		Function[{Typed[e, Expressions]},
			InductiveRecursor[Expressions][
				Function[{Typed[x, Expressions]}, Booleans],
				Function[{Typed[xs, {Expressions}]}, Booleans],
				Function[{Typed[a, Atoms]}, "true"],
				Function[{Typed[h, Expressions], Typed[arguments, {Expressions}], Typed[hr, Booleans], Typed[ar, Booleans]}, "false"],
				"false",
				Function[{Typed[x, Expressions], Typed[rest, {Expressions}], Typed[xr, Booleans], Typed[rr, Booleans]}, rr],
				e
			]
		],
		Expressions -> Booleans
	]],
	(* whether two expressions are the same: the same atom, or the same head and the same arguments *)
	TypeTheoryDefinition[SameQ, Typed[
		Function[{Typed[e, Expressions], Typed[f, Expressions]},
			InductiveRecursor[Expressions][
				Function[{Typed[x, Expressions]}, Expressions -> Booleans],
				Function[{Typed[xs, {Expressions}]}, {Expressions} -> Booleans],
				Function[{Typed[a, Atoms]}, Function[{Typed[g, Expressions]}, InductiveRecursor[Expressions][
					Typed[y, Expressions] |-> Booleans, Typed[ys, {Expressions}] |-> Booleans,
					Typed[b, Atoms] |-> "atomSameQ"[a, b],
					{Typed[h, Expressions], Typed[arguments, {Expressions}], Typed[hr, Booleans], Typed[ar, Booleans]} |-> "false",
					"false",
					{Typed[y, Expressions], Typed[rest, {Expressions}], Typed[yr, Booleans], Typed[rr, Booleans]} |-> "false",
					g
				]]],
				Function[{Typed[h, Expressions], Typed[arguments, {Expressions}], Typed[sameHead, Expressions -> Booleans], Typed[sameArguments, {Expressions} -> Booleans]},
					Function[{Typed[g, Expressions]}, InductiveRecursor[Expressions][
						Typed[y, Expressions] |-> Booleans, Typed[ys, {Expressions}] |-> Booleans,
						Typed[b, Atoms] |-> "false",
						{Typed[k, Expressions], Typed[others, {Expressions}], Typed[kr, Booleans], Typed[or, Booleans]} |-> And[sameHead[k], sameArguments[others]],
						"false",
						{Typed[y, Expressions], Typed[rest, {Expressions}], Typed[yr, Booleans], Typed[rr, Booleans]} |-> "false",
						g
					]]
				],
				Function[{Typed[l, {Expressions}]}, InductiveRecursor[List][Typed[t, {Expressions}] |-> Booleans, "true", {Typed[y, Expressions], Typed[ys, {Expressions}], Typed[r, Booleans]} |-> "false", l]],
				Function[{Typed[x, Expressions], Typed[rest, {Expressions}], Typed[sameFirst, Expressions -> Booleans], Typed[sameRest, {Expressions} -> Booleans]},
					Function[{Typed[l, {Expressions}]}, InductiveRecursor[List][
						Typed[t, {Expressions}] |-> Booleans,
						"false",
						{Typed[y, Expressions], Typed[ys, {Expressions}], Typed[r, Booleans]} |-> And[sameFirst[y], sameRest[ys]],
						l
					]]
				],
				e
			][f]
		],
		Expressions -> Expressions -> Booleans
	]],
	(* evaluation, as the Wolfram Language does it, taken as given: what a condition tests *)
	TypeTheoryAxiom[ExpressionValue, Expressions -> Expressions],
	(* a list without its first n elements, all of them where it has fewer *)
	TypeTheoryDefinition[Drop, Typed[
		Function[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[l, {A}], Typed[n, NonNegativeIntegers]},
			InductiveRecursor[List][
				Function[{Typed[t, {A}]}, NonNegativeIntegers -> {A}],
				Function[{Typed[k, NonNegativeIntegers]}, Typed[{}, {A}]],
				Function[{Typed[x, A], Typed[rest, {A}], Typed[r, NonNegativeIntegers -> {A}]},
					Function[{Typed[k, NonNegativeIntegers]},
						InductiveRecursor[NonNegativeIntegers][Typed[j, NonNegativeIntegers] |-> {A}, Prepend[x][rest], {Typed[j, NonNegativeIntegers], Typed[s, {A}]} |-> r[j], k]
					]
				],
				l
			][n]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, {A} -> NonNegativeIntegers -> {A}]
	]],

	(* the monad of matches: the lists of results, in the order they are tried *)
	TypeTheoryDefinition[Match, Typed[Typed[A, TypeUniverse[u + 1]] |-> {A}, TypeUniverse[u + 1] -> TypeUniverse[u + 1]]],
	TypeTheoryDefinition[MatchValue, Typed[
		Function[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[a, A]}, Prepend[a][{}]],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, A -> Match[A]]
	]],
	TypeTheoryDefinition[MatchSum, Typed[
		Function[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[m, Match[A]], Typed[n, Match[A]]}, Join[m, n]],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, Match[A] -> Match[A] -> Match[A]]
	]],
	TypeTheoryDefinition[MatchBind, Typed[
		Function[{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[v + 1]], Typed[m, Match[A]], Typed[f, A -> Match[B]]},
			InductiveRecursor[List][
				Function[{Typed[t, {A}]}, {B}],
				Typed[{}, {B}],
				Function[{Typed[x, A], Typed[rest, {A}], Typed[r, {B}]}, Join[f[x], r]],
				m
			]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[v + 1]]}, Match[A] -> (A -> Match[B]) -> Match[B]]
	]],
	TypeTheoryDefinition[Condition, Typed[
		Function[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[m, Match[A]], Typed[c, Booleans]},
			InductiveRecursor[Booleans][Typed[b, Booleans] |-> {A}, Typed[{}, {A}], m, c]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, Match[A] -> Booleans -> Match[A]]
	]],
	TypeTheoryDefinition[MatchQ, Typed[
		Function[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[m, Match[A]]},
			InductiveRecursor[List][Typed[t, {A}] |-> Booleans, "false", {Typed[x, A], Typed[rest, {A}], Typed[r, Booleans]} |-> "true", m]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, Match[A] -> Booleans]
	]],
	TypeTheoryDefinition[MatchFirst, Typed[
		Function[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[m, Match[A]]},
			InductiveRecursor[List][Typed[t, {A}] |-> Option[A], Typed["none", Option[A]], {Typed[x, A], Typed[rest, {A}], Typed[r, Option[A]]} |-> "some"[x], m]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, Match[A] -> Option[A]]
	]],

	(* the splits of a list into a prefix and the rest, as pairs: the shortest prefix first, as a sequence pattern tries
	   them, or the longest first, as Longest does *)
	TypeTheoryDefinition["splits", Typed[
		Function[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[l, {A}]},
			InductiveRecursor[List][
				Function[{Typed[t, {A}]}, Match[CartesianProductType[{A}, {A}]]],
				MatchValue["pair"[Typed[{}, {A}], Typed[{}, {A}]]],
				Function[{Typed[x, A], Typed[rest, {A}], Typed[r, Match[CartesianProductType[{A}, {A}]]]},
					MatchSum[
						MatchValue["pair"[Typed[{}, {A}], Prepend[x][rest]]],
						MatchBind[r, Function[{Typed[p, CartesianProductType[{A}, {A}]]}, MatchValue["pair"[Prepend[x][p[[1]]], p[[2]]]]]]
					]
				],
				l
			]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, {A} -> Match[CartesianProductType[{A}, {A}]]]
	]],
	TypeTheoryDefinition["longestSplits", Typed[
		Function[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[l, {A}]},
			InductiveRecursor[List][
				Function[{Typed[t, {A}]}, Match[CartesianProductType[{A}, {A}]]],
				MatchValue["pair"[Typed[{}, {A}], Typed[{}, {A}]]],
				Function[{Typed[x, A], Typed[rest, {A}], Typed[r, Match[CartesianProductType[{A}, {A}]]]},
					MatchSum[
						MatchBind[r, Function[{Typed[p, CartesianProductType[{A}, {A}]]}, MatchValue["pair"[Prepend[x][p[[1]]], p[[2]]]]]],
						MatchValue["pair"[Typed[{}, {A}], Prepend[x][rest]]]
					]
				],
				l
			]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, {A} -> Match[CartesianProductType[{A}, {A}]]]
	]],
	(* each element of a list with the others, in order; the permutations of a list, in the order of Permutations *)
	TypeTheoryDefinition["picks", Typed[
		Function[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[l, {A}]},
			InductiveRecursor[List][
				Function[{Typed[t, {A}]}, Match[CartesianProductType[A, {A}]]],
				Typed[{}, Match[CartesianProductType[A, {A}]]],
				Function[{Typed[x, A], Typed[rest, {A}], Typed[r, Match[CartesianProductType[A, {A}]]]},
					MatchSum[
						MatchValue["pair"[x, rest]],
						MatchBind[r, Function[{Typed[p, CartesianProductType[A, {A}]]}, MatchValue["pair"[p[[1]], Prepend[x][p[[2]]]]]]]
					]
				],
				l
			]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, {A} -> Match[CartesianProductType[A, {A}]]]
	]],
	TypeTheoryDefinition["permutations", Typed[
		Function[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[l, {A}]},
			InductiveRecursor[NonNegativeIntegers][
				Function[{Typed[k, NonNegativeIntegers]}, {A} -> Match[{A}]],
				Function[{Typed[m, {A}]}, MatchValue[m]],
				Function[{Typed[k, NonNegativeIntegers], Typed[r, {A} -> Match[{A}]]},
					Function[{Typed[m, {A}]}, MatchBind["picks"[m], Function[{Typed[p, CartesianProductType[A, {A}]]},
						MatchBind[r[p[[2]]], Function[{Typed[q, {A}]}, MatchValue[Prepend[p[[1]]][q]]]]
					]]]
				],
				Length[l]
			][l]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, {A} -> Match[{A}]]
	]],

	(* rules as Replace takes them are a function from an expression to its matches: ReplaceList gives every result,
	   Replace the first or the expression where no rule matches, ReplaceAll the first at each part, the parts tried from
	   the whole expression down, and ReplaceRepeated ReplaceAll again until the expression no longer changes, at most
	   MaxIterations times, 65536 *)
	TypeTheoryDefinition[ReplaceList, Typed[
		Function[{Typed[e, Expressions], Typed[rules, Expressions -> Match[Expressions]]}, rules[e]],
		Expressions -> (Expressions -> Match[Expressions]) -> {Expressions}
	]],
	TypeTheoryDefinition[Replace, Typed[
		Function[{Typed[e, Expressions], Typed[rules, Expressions -> Match[Expressions]]},
			InductiveRecursor[Option][Typed[o, Option[Expressions]] |-> Expressions, e, Typed[r, Expressions] |-> r, MatchFirst[rules[e]]]
		],
		Expressions -> (Expressions -> Match[Expressions]) -> Expressions
	]],
	TypeTheoryDefinition[ReplaceAll, Typed[
		Function[{Typed[e, Expressions], Typed[rules, Expressions -> Match[Expressions]]},
			InductiveRecursor[Expressions][
				Typed[x, Expressions] |-> Expressions,
				Typed[xs, {Expressions}] |-> {Expressions},
				Typed[a, Atoms] |-> InductiveRecursor[Option][Typed[o, Option[Expressions]] |-> Expressions, "atom"[a], Typed[r, Expressions] |-> r, MatchFirst[rules["atom"[a]]]],
				{Typed[h, Expressions], Typed[arguments, {Expressions}], Typed[hr, Expressions], Typed[ar, {Expressions}]} |->
					InductiveRecursor[Option][Typed[o, Option[Expressions]] |-> Expressions, "normal"[hr, ar], Typed[r, Expressions] |-> r, MatchFirst[rules["normal"[h, arguments]]]],
				Typed[{}, {Expressions}],
				{Typed[x, Expressions], Typed[rest, {Expressions}], Typed[xr, Expressions], Typed[rr, {Expressions}]} |-> Prepend[xr][rr],
				e
			]
		],
		Expressions -> (Expressions -> Match[Expressions]) -> Expressions
	]],
	TypeTheoryDefinition["replaceRepeatedSteps", Typed[
		Function[{Typed[n, NonNegativeIntegers], Typed[rules, Expressions -> Match[Expressions]]},
			InductiveRecursor[NonNegativeIntegers][
				Typed[k, NonNegativeIntegers] |-> (Expressions -> Expressions),
				Typed[e, Expressions] |-> e,
				{Typed[k, NonNegativeIntegers], Typed[again, Expressions -> Expressions]} |-> Function[{Typed[e, Expressions]},
					InductiveRecursor[Booleans][Typed[b, Booleans] |-> Expressions, again[ReplaceAll[e, rules]], e, SameQ[ReplaceAll[e, rules], e]]
				],
				n
			]
		],
		NonNegativeIntegers -> (Expressions -> Match[Expressions]) -> Expressions -> Expressions
	]],
	TypeTheoryDefinition[ReplaceRepeated, Typed[
		Function[{Typed[e, Expressions], Typed[rules, Expressions -> Match[Expressions]]}, "replaceRepeatedSteps"[65536, rules][e]],
		Expressions -> (Expressions -> Match[Expressions]) -> Expressions
	]],

	(* the element of a list at an index from 0, no result out of range; a match at the part of an expression at a position,
	   0 its head and k its k-th argument *)
	TypeTheoryDefinition["matchElement", Typed[
		Function[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[l, {A}]},
			InductiveRecursor[List][
				Function[{Typed[t, {A}]}, NonNegativeIntegers -> Match[A]],
				Function[{Typed[k, NonNegativeIntegers]}, Typed[{}, {A}]],
				Function[{Typed[x, A], Typed[rest, {A}], Typed[r, NonNegativeIntegers -> Match[A]]},
					Function[{Typed[k, NonNegativeIntegers]},
						InductiveRecursor[NonNegativeIntegers][Typed[j, NonNegativeIntegers] |-> Match[A], MatchValue[x], {Typed[j, NonNegativeIntegers], Typed[s, Match[A]]} |-> r[j], k]
					]
				],
				l
			]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, {A} -> NonNegativeIntegers -> Match[A]]
	]],
	TypeTheoryDefinition[MatchPart, Typed[
		Function[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[e, Expressions], Typed[k, NonNegativeIntegers], Typed[f, Expressions -> Match[A]]},
			MatchBind[
				Typed[
					InductiveRecursor[NonNegativeIntegers][
						Function[{Typed[j, NonNegativeIntegers]}, Match[Expressions]],
						MatchValue[Head[e]],
						Function[{Typed[j, NonNegativeIntegers], Typed[s, Match[Expressions]]}, "matchElement"[Arguments[e], j]],
						k
					],
					Match[Expressions]
				],
				f
			]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, Expressions -> NonNegativeIntegers -> (Expressions -> Match[A]) -> Match[A]]
	]]
}
