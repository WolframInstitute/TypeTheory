(* ::Package:: *)

(*
The Wolfram Language: TypeTheoryEnvironment["WolframLanguage"] is the prelude with the expressions of the Wolfram
Language and the monad of pattern matching, built and checked the first time it is asked for.

	Atoms                           the expressions with no parts, symbols, numbers and strings, opaque
	Expressions                     an expression: "atom"[a], or "normal"[h, {a, ...}], h applied to the
	                                list of its arguments
	Head, Arguments, AtomQ          the head of an expression, the list of its arguments, {} for an atom, and whether it
	                                is an atom
	Sequence[A, B, ...]             where a type is expected, the type of the sequences Sequence[a, b, ...] of an element
	                                of A, then of B, ...: a list of elements of different types, its length and their
	                                types given by its type, as Lean's HList, indexed by the list {A, B, ...};
	                                "emptySequence" and "sequencePrepend" construct it, and Sequence[a, ...] writes them
	Strings                         the strings, opaque, a literal "abc" a constant named by its InputForm
	SameQ                           whether two expressions are the same, a Boolean the Wolfram Language computes
	ExpressionValue                 the value the Wolfram Language evaluates an expression to, opaque
	Drop                            a list without its first n elements
	Match[A]                        the results of a match, {A}: none, one, or several in the order they are tried
	MatchValues, {}          one result and none
	MatchSum                        the results of one match, then those of another: a pattern's alternatives in order
	MatchProduct                    every pair of a result of one match and one of another, in order: independent parts
	MatchBind                       the results of a match, each continued by another match: a pattern's parts in turn
	Condition                       the results of a match where a Boolean holds: a condition
	MatchPart                       a match at the part of an expression at a position, 0 its head, none out of range
	MatchQ                          whether a match has a result
	MatchFirst                      the first result, an Option: the rule the Wolfram Language applies, none where no
	                                rule matches and the expression stays as it is
Match, MatchValues, MatchSum, MatchProduct and MatchPart are the symbols of the paclet Wolfram/Patterns, whose match
objects they type: TypeTheory names its constants by them, as it names others by Join or Length, and exports none of
them, so loading both paclets shadows nothing. The WolframKernel project's compiler built its Match IR from the same
objects: Values is MatchValues, Sum is MatchSum, Product is MatchProduct and MatchBind, and a Guard is Condition.
Match is the monad of lists, the monad of nondeterminism, with its alternatives in order, so a pattern that matches in
several ways, as an Orderless or a sequence pattern does, has several results, and the first is the one the Wolfram
Language takes. A natural number is an expression where one is expected, by a coercion.

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
PackageExported[MatchBind]
PackageExported[MatchFirst]


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[wolframLanguageEnvironment]


(* ::Section:: *)
(*Usage Messages*)


Atoms::usage = "Atoms is the type of the expressions of the Wolfram Language with no parts: symbols, numbers and strings. It is a constant of TypeTheoryEnvironment[\"WolframLanguage\"]."
Expressions::usage = "Expressions is the type of the expressions of the Wolfram Language, each \"atom\"[a] or \"normal\"[h, s]. It is a constant of TypeTheoryEnvironment[\"WolframLanguage\"]."
Arguments::usage = "Arguments[e] is the list of the arguments of the expression e, {} for an atom."
Strings::usage = "Strings is the type of the strings of the Wolfram Language, opaque: a string literal \"abc\" is a constant of it, named by its InputForm, and an expression where one is expected."
ExpressionValue::usage = "ExpressionValue[e] is the expression the Wolfram Language evaluates the expression e to: an axiom, which the kernel never computes."
MatchBind::usage = "MatchBind[m, f] is the match whose results are those of f applied to each result of m, in order."
MatchFirst::usage = "MatchFirst[m] is the first result of the match m, \"some\" of it, or \"none\" where m has none: the rule the Wolfram Language applies."
wolframLanguageEnvironment::usage = "wolframLanguageEnvironment[] gives the prelude with the expressions of the Wolfram Language and the monad of pattern matching, built and checked the first time it is asked for."


(* ::Section:: *)
(*Function Definitions*)


(* the environment puts the context of Wolfram/Patterns at the end of the context path, so that its symbols, the names of
   the constants of matches, are written without their context and shadow nothing *)
wolframLanguageEnvironment[] := (
	If[! MemberQ[$ContextPath, "Wolfram`Patterns`"], AppendTo[$ContextPath, "Wolfram`Patterns`"]];
	builtWolframLanguageEnvironment[]
)

builtWolframLanguageEnvironment[] := builtWolframLanguageEnvironment[] = withoutStoreTracking[
	libraryEnvironment["WolframLanguage", preludeEnvironment[], withStoreCleanup[TypeTheoryEnvironment[preludeEnvironment[], $wolframLanguageDeclarations]]]
]

$wolframLanguageDeclarations = {
	TypeTheoryAxiom[Atoms, TypeUniverse[1]],
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
	TypeTheoryAxiom["atomHead", Atoms -> Atoms, "Implementation" -> Head],
	TypeTheoryAxiom[SameQ, Expressions -> Expressions -> Booleans, "Implementation" -> SameQ],
	TypeTheoryAxiom["naturalAtom", NonNegativeIntegers -> Atoms, "Implementation" -> Identity],
	TypeTheoryDefinition["NaturalExpressionCoercion", Typed[n, NonNegativeIntegers] |-> "atom"["naturalAtom"[n]], "Coercion" -> True],
	(* the strings, opaque, each literal a constant named by its InputForm, and an expression where one is expected *)
	TypeTheoryAxiom[Strings, TypeUniverse[1]],
	TypeTheoryAxiom["stringAtom", Strings -> Atoms, "Implementation" -> Identity],
	TypeTheoryDefinition["StringExpressionCoercion", Typed[s, Strings] |-> "atom"["stringAtom"[s]], "Coercion" -> True],

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
	TypeTheoryDefinition[Wolfram`Patterns`Match, Typed[Typed[A, TypeUniverse[u + 1]] |-> {A}, TypeUniverse[u + 1] -> TypeUniverse[u + 1]]],
	TypeTheoryDefinition[Wolfram`Patterns`MatchValues, Typed[
		Function[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[a, A]}, Prepend[a][{}]],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, A -> Wolfram`Patterns`Match[A]]
	]],
	TypeTheoryDefinition[Wolfram`Patterns`MatchSum, Typed[
		Function[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[m, Wolfram`Patterns`Match[A]], Typed[n, Wolfram`Patterns`Match[A]]}, Join[m, n]],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, Wolfram`Patterns`Match[A] -> Wolfram`Patterns`Match[A] -> Wolfram`Patterns`Match[A]]
	]],
	TypeTheoryDefinition[MatchBind, Typed[
		Function[{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[v + 1]], Typed[m, Wolfram`Patterns`Match[A]], Typed[f, A -> Wolfram`Patterns`Match[B]]},
			InductiveRecursor[List][
				Function[{Typed[t, {A}]}, {B}],
				Typed[{}, {B}],
				Function[{Typed[x, A], Typed[rest, {A}], Typed[r, {B}]}, Join[f[x], r]],
				m
			]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[v + 1]]}, Wolfram`Patterns`Match[A] -> (A -> Wolfram`Patterns`Match[B]) -> Wolfram`Patterns`Match[B]]
	]],
	TypeTheoryDefinition[Condition, Typed[
		Function[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[m, Wolfram`Patterns`Match[A]], Typed[c, Booleans]},
			InductiveRecursor[Booleans][Typed[b, Booleans] |-> {A}, Typed[{}, {A}], m, c]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, Wolfram`Patterns`Match[A] -> Booleans -> Wolfram`Patterns`Match[A]]
	]],
	TypeTheoryDefinition[MatchQ, Typed[
		Function[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[m, Wolfram`Patterns`Match[A]]},
			InductiveRecursor[List][Typed[t, {A}] |-> Booleans, "false", {Typed[x, A], Typed[rest, {A}], Typed[r, Booleans]} |-> "true", m]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, Wolfram`Patterns`Match[A] -> Booleans]
	]],
	TypeTheoryDefinition[MatchFirst, Typed[
		Function[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[m, Wolfram`Patterns`Match[A]]},
			InductiveRecursor[List][Typed[t, {A}] |-> Option[A], Typed["none", Option[A]], {Typed[x, A], Typed[rest, {A}], Typed[r, Option[A]]} |-> "some"[x], m]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, Wolfram`Patterns`Match[A] -> Option[A]]
	]],

	(* the element of a list at an index from 0, no result out of range; a match at the part of an expression at a position,
	   0 its head and k its k-th argument *)
	TypeTheoryDefinition["matchElement", Typed[
		Function[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[l, {A}]},
			InductiveRecursor[List][
				Function[{Typed[t, {A}]}, NonNegativeIntegers -> Wolfram`Patterns`Match[A]],
				Function[{Typed[k, NonNegativeIntegers]}, Typed[{}, {A}]],
				Function[{Typed[x, A], Typed[rest, {A}], Typed[r, NonNegativeIntegers -> Wolfram`Patterns`Match[A]]},
					Function[{Typed[k, NonNegativeIntegers]},
						InductiveRecursor[NonNegativeIntegers][Typed[j, NonNegativeIntegers] |-> Wolfram`Patterns`Match[A], Wolfram`Patterns`MatchValues[x], {Typed[j, NonNegativeIntegers], Typed[s, Wolfram`Patterns`Match[A]]} |-> r[j], k]
					]
				],
				l
			]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, {A} -> NonNegativeIntegers -> Wolfram`Patterns`Match[A]]
	]],
	TypeTheoryDefinition[Wolfram`Patterns`MatchPart, Typed[
		Function[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[e, Expressions], Typed[k, NonNegativeIntegers], Typed[f, Expressions -> Wolfram`Patterns`Match[A]]},
			MatchBind[
				Typed[
					InductiveRecursor[NonNegativeIntegers][
						Function[{Typed[j, NonNegativeIntegers]}, Wolfram`Patterns`Match[Expressions]],
						Wolfram`Patterns`MatchValues[Head[e]],
						Function[{Typed[j, NonNegativeIntegers], Typed[s, Wolfram`Patterns`Match[Expressions]]}, "matchElement"[Arguments[e], j]],
						k
					],
					Wolfram`Patterns`Match[Expressions]
				],
				f
			]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, Expressions -> NonNegativeIntegers -> (Expressions -> Wolfram`Patterns`Match[A]) -> Wolfram`Patterns`Match[A]]
	]],
	(* every pair of a result of one match and one of another, in the order of the first *)
	TypeTheoryDefinition[Wolfram`Patterns`MatchProduct, Typed[
		Function[{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[v + 1]], Typed[m, Wolfram`Patterns`Match[A]], Typed[n, Wolfram`Patterns`Match[B]]},
			MatchBind[m, Typed[a, A] |-> MatchBind[n, Typed[b, B] |-> Wolfram`Patterns`MatchValues["pair"[a, b]]]]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[v + 1]]}, Wolfram`Patterns`Match[A] -> Wolfram`Patterns`Match[B] -> Wolfram`Patterns`Match[CartesianProductType[A, B]]]
	]]
}
