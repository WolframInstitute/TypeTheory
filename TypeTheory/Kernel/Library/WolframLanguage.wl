(* ::Package:: *)

(*
The Wolfram Language: TypeTheoryEnvironment["WolframLanguage"] is the prelude with the expressions of the Wolfram
Language and the monad of pattern matching, built and checked the first time it is asked for.

	"Atoms"                         the expressions with no parts, symbols, numbers and strings, opaque
	"atomSameQ", "atomHead"         SameQ and Head on atoms, Booleans and atoms, which the Wolfram Language computes
	"atomOfNatural"                 a natural number as an atom
	"Expressions"                   an expression: "expressionAtom"[a], or "expressionNormal"[h, {e1, ...}], h[e1, ...]
	"expressionHead"                the head of an expression, "atomHead" of an atom's
	"expressionArguments"           the parts of an expression after its head, {} for an atom
	"Match"[A]                      the results of a match, Lists[A]: none, one, or several in the order they are tried
	"matchPure", "matchFailure"     one result and none
	"matchAlternative"              the results of one match, then those of another: a pattern's alternatives in order
	"matchBind"                     the results of a match, each continued by another match: a pattern's parts in turn
	"matchGuard"                    the results of a match where a Boolean holds: a condition
	"matchFirst"                    the first result, an Option: the rule the Wolfram Language applies, none where no
	                                rule matches and the expression stays as it is
	"matchPart"                     the part of an expression at a position, 0 its head, no result out of range

A match space of the WolframKernel project's compiler, its Match IR, is a term of "Match": Values is "matchPure",
Sum is "matchAlternative", Product is "matchBind", and a Guard is "matchGuard". The Match monad is the monad of
lists, the monad of nondeterminism, with its alternatives in order, so a pattern that matches in several ways, as an
Orderless or a sequence pattern does, has several results, and the first is the one the Wolfram Language takes.
*)


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[wolframLanguageEnvironment]


(* ::Section:: *)
(*Usage Messages*)


wolframLanguageEnvironment::usage = "wolframLanguageEnvironment[] gives the prelude with the expressions of the Wolfram Language and the monad of pattern matching, built and checked the first time it is asked for."


(* ::Section:: *)
(*Function Definitions*)


wolframLanguageEnvironment[] := wolframLanguageEnvironment[] = withoutStoreTracking[
	libraryEnvironment["WolframLanguage", preludeEnvironment[], withStoreCleanup[TypeTheoryEnvironment[preludeEnvironment[], $wolframLanguageDeclarations]]]
]

$wolframLanguageDeclarations = {
	TypeTheoryAxiom["Atoms", TypeUniverse[1]],
	TypeTheoryAxiom["atomSameQ", "Atoms" -> "Atoms" -> Booleans, "Implementation" -> SameQ],
	TypeTheoryAxiom["atomHead", "Atoms" -> "Atoms", "Implementation" -> Head],
	TypeTheoryAxiom["atomOfNatural", NonNegativeIntegers -> "Atoms", "Implementation" -> Identity],
	TypeTheoryInductiveType["Expressions", TypeUniverse[1], {
		"expressionAtom" -> ("Atoms" -> "Expressions"),
		"expressionNormal" -> ("Expressions" -> Lists["Expressions"] -> "Expressions")
	}],

	(* an expression's head and its other parts, by the recursor of expressions, whose second motive is that of their
	   lists of parts *)
	TypeTheoryDefinition["expressionHead", Typed[
		Function[{Typed[e, "Expressions"]},
			InductiveRecursor["Expressions"][
				Function[{Typed[x, "Expressions"]}, "Expressions"],
				Function[{Typed[xs, Lists["Expressions"]]}, Lists["Expressions"]],
				Function[{Typed[a, "Atoms"]}, "expressionAtom"["atomHead"[a]]],
				Function[{Typed[h, "Expressions"], Typed[arguments, Lists["Expressions"]], Typed[hr, "Expressions"], Typed[ar, Lists["Expressions"]]}, h],
				EmptyList,
				Function[{Typed[x, "Expressions"], Typed[rest, Lists["Expressions"]], Typed[xr, "Expressions"], Typed[rr, Lists["Expressions"]]}, rr],
				e
			]
		],
		"Expressions" -> "Expressions"
	]],
	TypeTheoryDefinition["expressionArguments", Typed[
		Function[{Typed[e, "Expressions"]},
			InductiveRecursor["Expressions"][
				Function[{Typed[x, "Expressions"]}, Lists["Expressions"]],
				Function[{Typed[xs, Lists["Expressions"]]}, Lists["Expressions"]],
				Function[{Typed[a, "Atoms"]}, EmptyList],
				Function[{Typed[h, "Expressions"], Typed[arguments, Lists["Expressions"]], Typed[hr, Lists["Expressions"]], Typed[ar, Lists["Expressions"]]}, arguments],
				EmptyList,
				Function[{Typed[x, "Expressions"], Typed[rest, Lists["Expressions"]], Typed[xr, Lists["Expressions"]], Typed[rr, Lists["Expressions"]]}, rr],
				e
			]
		],
		"Expressions" -> Lists["Expressions"]
	]],

	(* the monad of matches: the lists of results, in the order they are tried *)
	TypeTheoryDefinition["Match", Typed[Function[{Typed[A, TypeUniverse[u + 1]]}, Lists[A]], TypeUniverse[u + 1] -> TypeUniverse[u + 1]]],
	TypeTheoryDefinition["matchPure", Typed[
		Function[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[a, A]}, ListPrepend[a, EmptyList]],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, A -> "Match"[A]]
	]],
	TypeTheoryDefinition["matchFailure", Typed[
		Function[{TypedImplicit[A, TypeUniverse[u + 1]]}, Typed[EmptyList, Lists[A]]],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, "Match"[A]]
	]],
	TypeTheoryDefinition["matchAlternative", Typed[
		Function[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[m, "Match"[A]], Typed[n, "Match"[A]]}, Join[m, n]],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, "Match"[A] -> "Match"[A] -> "Match"[A]]
	]],
	TypeTheoryDefinition["matchBind", Typed[
		Function[{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[u + 1]], Typed[m, "Match"[A]], Typed[f, A -> "Match"[B]]},
			InductiveRecursor[Lists][
				Function[{Typed[t, Lists[A]]}, Lists[B]],
				Typed[EmptyList, Lists[B]],
				Function[{Typed[x, A], Typed[rest, Lists[A]], Typed[r, Lists[B]]}, Join[f[x], r]],
				m
			]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]], TypedImplicit[B, TypeUniverse[u + 1]]}, "Match"[A] -> (A -> "Match"[B]) -> "Match"[B]]
	]],
	TypeTheoryDefinition["matchGuard", Typed[
		Function[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[c, Booleans], Typed[m, "Match"[A]]},
			InductiveRecursor[Booleans][Function[{Typed[b, Booleans]}, Lists[A]], Typed[EmptyList, Lists[A]], m, c]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, Booleans -> "Match"[A] -> "Match"[A]]
	]],
	TypeTheoryDefinition["matchFirst", Typed[
		Function[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[m, "Match"[A]]},
			InductiveRecursor[Lists][Function[{Typed[t, Lists[A]]}, Option[A]], Typed[OptionNone, Option[A]], Function[{Typed[x, A], Typed[rest, Lists[A]], Typed[r, Option[A]]}, OptionSome[x]], m]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, "Match"[A] -> Option[A]]
	]],

	(* the element of a list at an index from 0, no result out of range; the part of an expression at a position, 0 its
	   head and k its k-th argument *)
	TypeTheoryDefinition["matchElement", Typed[
		Function[{TypedImplicit[A, TypeUniverse[u + 1]], Typed[l, Lists[A]]},
			InductiveRecursor[Lists][
				Function[{Typed[t, Lists[A]]}, NonNegativeIntegers -> "Match"[A]],
				Function[{Typed[k, NonNegativeIntegers]}, "matchFailure"],
				Function[{Typed[x, A], Typed[rest, Lists[A]], Typed[r, NonNegativeIntegers -> "Match"[A]]},
					Function[{Typed[k, NonNegativeIntegers]},
						InductiveRecursor[NonNegativeIntegers][Function[{Typed[j, NonNegativeIntegers]}, "Match"[A]], "matchPure"[x], Function[{Typed[j, NonNegativeIntegers], Typed[s, "Match"[A]]}, r[j]], k]
					]
				],
				l
			]
		],
		ForAll[{TypedImplicit[A, TypeUniverse[u + 1]]}, Lists[A] -> NonNegativeIntegers -> "Match"[A]]
	]],
	TypeTheoryDefinition["matchPart", Typed[
		Function[{Typed[e, "Expressions"], Typed[k, NonNegativeIntegers]},
			InductiveRecursor[NonNegativeIntegers][
				Function[{Typed[j, NonNegativeIntegers]}, "Match"["Expressions"]],
				"matchPure"["expressionHead"[e]],
				Function[{Typed[j, NonNegativeIntegers], Typed[s, "Match"["Expressions"]]}, "matchElement"["expressionArguments"[e], j]],
				k
			]
		],
		"Expressions" -> NonNegativeIntegers -> "Match"["Expressions"]
	]]
}
