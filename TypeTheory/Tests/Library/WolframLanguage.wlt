(* ::Package::"Tags"-><|"BadSymbol" -> <|"Match" -> <|Enabled -> False|>|>|>:: *)

(* Tests for Library/WolframLanguage.wl: the expressions of the Wolfram Language as an inductive type, and the monad of
   pattern matching, the lists of results in the order they are tried, with its operations computing. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

wolfram = TypeTheoryEnvironment["Prelude"]

SetAttributes[equalQ, HoldAll]
equalQ[a_, b_] := DefinitionallyEqualQ[TypeTheoryTerm[a, wolfram], TypeTheoryTerm[b, wolfram]]

VerificationTest[
	{Head[wolfram], MemberQ[Keys[wolfram], Expressions], MemberQ[Keys[wolfram], MatchBind], MemberQ[Keys[wolfram], MatchSum], Context[MatchValue]},
	{TypeTheoryEnvironment, True, True, True, "WolframInstitute`TypeTheory`"},
	TestID -> "The-Wolfram-Language-environment-checks"
]

(* the part of an expression at a position: 0 its head, k its k-th argument, no result out of range *)
VerificationTest[
	{
		equalQ[MatchPart[Construct[7, 1, 2], 2, MatchValue], MatchValue[Typed[2, Expressions]]],
		equalQ[MatchPart[Construct[7, 1], 0, MatchValue], MatchValue[Typed[7, Expressions]]],
		equalQ[MatchPart[Construct[7, 1], 5, MatchValue], Typed[{}, Match[Expressions]]]
	},
	{True, True, True},
	TestID -> "The-parts-of-an-expression-are-matches"
]

(* alternatives in order, the first result the one taken, none where nothing matches; bind sequences, guard filters *)
VerificationTest[
	{
		equalQ[MatchFirst[MatchSum[MatchValue[1], MatchValue[2]]], "some"[1]],
		equalQ[MatchFirst[MatchSum[Typed[{}, Match[NonNegativeIntegers]], MatchValue[3]]], "some"[3]],
		equalQ[MatchFirst[Typed[{}, Match[NonNegativeIntegers]]], Typed["none", Option[NonNegativeIntegers]]],
		equalQ[MatchBind[{1, 2}, Function[{Typed[x, NonNegativeIntegers]}, {x, x}]], {1, 1, 2, 2}],
		equalQ[Condition[MatchValue[1], "false"], Typed[{}, Match[NonNegativeIntegers]]],
		equalQ[Condition[MatchValue[1], "true"], MatchValue[1]]
	},
	{True, True, True, True, True, True},
	TestID -> "The-match-monad-tries-alternatives-in-order"
]

(* the arguments of an expression are a sequence, {Arguments[e]} their list, and Construct[Head[e], Arguments[e]] the
   expression; a query that names a constant only the Wolfram Language environment has is in it; a value is one result,
   a sequence of values is one result written MatchValue[Sequence[...]], and several results are a sum *)
VerificationTest[
	{
		equalQ[Arguments[Construct[7, 1, 2]], Typed[Unevaluated[1, 2], Expressions...]],
		equalQ[{Arguments[Construct[7, 1, 2]]}, Typed[{1, 2}, {Expressions}]],
		equalQ[Construct[Head[f[1, g[2]]], Arguments[f[1, g[2]]]], Typed[f[1, g[2]], Expressions]],
		equalQ[Typed[{0, Arguments[f[1, 2]], 3}, {Expressions}], Typed[{0, 1, 2, 3}, {Expressions}]],
		TypeTheoryType[Arguments] === TypeTheoryTerm[Expressions -> Expressions..., wolfram],
		TypeTheoryType[Head] === TypeTheoryTerm[Expressions -> Expressions, wolfram],
		TypeTheoryType[MatchValue[Sequence[1, "true"]], wolfram] === TypeTheoryTerm[Match[Sequence[NonNegativeIntegers, Booleans]], wolfram],
		equalQ[MatchFirst[MatchValue[Sequence[1, "true"]]], "some"[Sequence[1, "true"]]],
		equalQ[MatchSum[MatchValue[1], MatchValue[2]], {1, 2}]
	},
	{True, True, True, True, True, True, True, True, True},
	TestID -> "A-value-is-one-result-a-sequence-is-one-result-and-several-are-a-sum"
]

(* an expression is written as it is: its variables the expressions they stand for, a sequence of them among the
   arguments spliced in, as is Sequence @@ l of a list, and it shows so, with no HoldForm; a symbol is an atom by its name, which
   nothing declares; a string literal is a string, the list of its character codes, where a string is expected, and an
   expression where one is; where an expression is expected, a symbol that names nothing stands for itself *)
VerificationTest[
	With[{quoting = TypeTheoryEnvironment["Prelude"]},
		{
			DefinitionallyEqualQ[TypeTheoryTerm[f[1, 2], quoting], TypeTheoryTerm[Construct["atom"["symbolAtom"["Global`f"]], 1, 2], quoting]],
			Head[TypeTheoryType[TypeTheoryTerm[{Typed[x, Expressions], Typed[l, {Expressions}]} |-> f[x, l, Sequence @@ l], quoting]]] === TypeTheoryTerm,
			DefinitionallyEqualQ[
				TypeTheoryTerm[({Typed[x, Expressions], Typed[rest, Expressions...]} |-> f[x, rest])[1, 2, 3], quoting],
				TypeTheoryTerm[f[1, 2, 3], quoting]
			],
			FreeQ[ToBoxes[NormalForm[TypeTheoryTerm[(Typed[x, Expressions] |-> f[x])[2], quoting]]], "HoldForm" | "\"HoldForm\"", Infinity],
			First[TypeTheoryType[TypeTheoryTerm[Typed["abc", Strings], quoting]]],
			First[TypeTheoryType[TypeTheoryTerm[Typed["abc", Expressions], quoting]]],
			First[TypeTheoryType[TypeTheoryTerm[g[1], quoting]]],
			DefinitionallyEqualQ[TypeTheoryTerm[Typed["abc", Strings], quoting], TypeTheoryTerm["string"[{97, 98, 99}], quoting]],
			DefinitionallyEqualQ[TypeTheoryTerm[Typed[g[1 + 1], Expressions], quoting], TypeTheoryTerm[g[2], quoting]]
		}
	],
	{True, True, True, True, Strings, Expressions, Expressions, True, True},
	TestID -> "An-expression-is-written-as-it-is-and-a-string-literal-is-a-string"
]

(* rules written as a term are a function from an expression to its matches, and Replace, ReplaceList, ReplaceAll and
   ReplaceRepeated rewrite with them in the kernel, as the Wolfram Language does: an expression where one is expected
   needs no HoldForm, a symbol that names nothing standing for itself *)
VerificationTest[
	{
		equalQ[Replace[f[1, 2], f[x_, y_] :> {y, x}], Typed[{2, 1}, Expressions]],
		equalQ[Replace[g[1, 2], f[x_, y_] :> {y, x}], Typed[g[1, 2], Expressions]],
		equalQ[Replace[h[1, "s"], {h[x_Integer, y_String] :> y, h[x_, y_] :> x}], Typed["s", Expressions]],
		equalQ[ReplaceList[f[1, 2, 3], f[x__, y__] :> {{x}, {y}}], {Typed[{{1}, {2, 3}}, Expressions], Typed[{{1, 2}, {3}}, Expressions]}],
		equalQ[ReplaceAll[f[a, g[a]], a -> b], Typed[f[b, g[b]], Expressions]],
		equalQ[ReplaceRepeated[f[f[f[x]]], f[y_] :> y], Typed[x, Expressions]],
		equalQ[SameQ[f[1, "a"], f[1, "a"]], "true"],
		equalQ[SameQ[f[1], f[-1]], "false"]
	},
	ConstantArray[True, 8],
	TestID -> "Replace-ReplaceList-ReplaceAll-and-ReplaceRepeated-rewrite-in-the-kernel"
]

(* Construct[h, a, b] is the expression h[a, b], h applied to the sequence of its arguments, Expressions...:
   a sequence among them spliced in, Unevaluated[a, b] as the Wolfram Language holds one, a list one argument; Prepend[s, x]
   puts x in front of a sequence, which shows in brackets, [a, b]; Construct of a function applies it; a term reads back
   as it is written. Unevaluated[...] is kept inside a term: the Wolfram Language strips it from an argument of a function
   with rules, even a HoldAll one *)
VerificationTest[
	{
		equalQ[Construct[f, 1, 2], Typed[f[1, 2], Expressions]],
		equalQ[Construct[f, Unevaluated[]], Typed[f[], Expressions]],
		equalQ[Construct[f, {1, 2}], Typed[f[{1, 2}], Expressions]],
		equalQ[Construct[f, Unevaluated[1, 2], 3], Typed[f[1, 2, 3], Expressions]],
		equalQ[Function[{Typed[s, Expressions...]}, Construct[f, s]][1, 2], Typed[f[1, 2], Expressions]],
		equalQ[Prepend[Unevaluated[1, 2, 3], 0], Typed[Unevaluated[0, 1, 2, 3], NonNegativeIntegers...]],
		equalQ[Typed[Unevaluated[Unevaluated[1], 2, Unevaluated @@ {3, 4}], NonNegativeIntegers...], Typed[Unevaluated[1, 2, 3, 4], NonNegativeIntegers...]],
		equalQ[Construct[Function[{Typed[n, NonNegativeIntegers]}, n + 1], 2], 3],
		TypeTheoryType[Construct, wolfram] === TypeTheoryTerm[Expressions -> Expressions... -> Expressions, wolfram],
		MatchQ[NormalForm[TypeTheoryTerm[Prepend[Unevaluated[1, 2], 0], wolfram]], HoldPattern[TypeTheoryTerm[Unevaluated[0, 1, 2], _]]],
		MatchQ[NormalForm[TypeTheoryTerm[Replace[f[1, 2], f[x_, y_] :> {y, x}], wolfram]], HoldPattern[TypeTheoryTerm[Unevaluated[{2, 1}], _]]],
		MatchQ[NormalForm[TypeTheoryTerm[StringJoin["ab", "c"] /. _ -> "abc", wolfram]], _TypeTheoryTerm | _Failure],
		ToString[NormalForm[TypeTheoryTerm[ReplaceList[f[1, "a"], f[x__, y___] :> {{x}, {y}}], wolfram]], OutputForm],
		ToString[NormalForm[TypeTheoryTerm[Prepend[Unevaluated[Unevaluated[1], 2], 0], wolfram]], OutputForm],
		ToString[TypeTheoryTerm[Unevaluated[1, Unevaluated[2, 3], Unevaluated @@ {4}], wolfram], OutputForm]
	},
	{True, True, True, True, True, True, True, True, True, True, True, True, "{{{1}, {\"a\"}}, {{1, \"a\"}, {}}}", "[0, 1, 2]", "[1, 2, 3, Sequence @@ {4}]"},
	TestID -> "Construct-takes-a-sequence-of-arguments-and-terms-read-back-as-written"
]

(* alternatives that bind no names match once, as the Wolfram Language's ReplaceList gives {1} for
   f[x : (_Integer | _)]; alternatives that bind names are each a way to match, {1, 1} for f[x_Integer | x_] *)
VerificationTest[
	{
		equalQ[ReplaceList[f[1], f[x : (_Integer | _)] :> x], {Typed[1, Expressions]}],
		equalQ[ReplaceList[f[1], f[_Integer | _] :> 0], {Typed[0, Expressions]}],
		equalQ[ReplaceList[f[1], f[x_Integer | x_] :> x], {Typed[1, Expressions], Typed[1, Expressions]}],
		equalQ[ReplaceList[f[g[1]], f[g[x_] | g[y_]] :> 0], {Typed[0, Expressions], Typed[0, Expressions]}]
	},
	{True, True, True, True},
	TestID -> "Alternatives-without-names-match-once-as-in-the-Wolfram-Language"
]

(* Failure[tag, details] is a failure; Enclose[body] binds each Confirm[e] of body with "confirmBind", so it gives the
   value of body as the left of A | Failure, or the first failure confirmed; Confirm outside an Enclose is refused *)
VerificationTest[
	With[{sum = Function[{Typed[a, NonNegativeIntegers | Failure], Typed[b, NonNegativeIntegers | Failure]}, Enclose[Confirm[a] + Confirm[b]]]},
		{
			MatchQ[TypeTheoryType[Failure["NotPositive", <|"Value" -> 3|>]], HoldPattern[TypeTheoryTerm[Failure, _]]],
			DefinitionallyEqualQ[TypeTheoryType[sum], TypeTheoryTerm[(NonNegativeIntegers | Failure) -> (NonNegativeIntegers | Failure) -> (NonNegativeIntegers | Failure)]],
			DefinitionallyEqualQ[TypeTheoryTerm[sum[2, 3]], TypeTheoryTerm[Typed["left"[5], NonNegativeIntegers | Failure]]],
			DefinitionallyEqualQ[TypeTheoryTerm[sum[2, Failure["Missing", 0]]], TypeTheoryTerm[Typed["right"[Failure["Missing", 0]], NonNegativeIntegers | Failure]]],
			DefinitionallyEqualQ[TypeTheoryTerm[sum[Failure["First", 1], Failure["Second", 2]]], TypeTheoryTerm[Typed["right"[Failure["First", 1]], NonNegativeIntegers | Failure]]],
			First[TypeTheoryType[Typed[x, NonNegativeIntegers | Failure] |-> Confirm[x]]]
		}
	],
	{True, True, True, True, True, "ElaborationFailed"},
	TestID -> "Enclose-and-Confirm-give-the-first-failure"
]

(* the prelude declares If, by the decision of its condition: a function that fails on some inputs branches with If,
   and each branch is injected into A | Failure *)
VerificationTest[
	With[{predecessor = Typed[x, NonNegativeIntegers] |-> Typed[If[x == 0, Failure["Zero", <|"Value" -> x|>], x - 1], NonNegativeIntegers | Failure]},
		{
			DefinitionallyEqualQ[TypeTheoryType[predecessor], TypeTheoryTerm[NonNegativeIntegers -> (NonNegativeIntegers | Failure)]],
			DefinitionallyEqualQ[TypeTheoryTerm[predecessor[4]], TypeTheoryTerm[Typed["left"[3], NonNegativeIntegers | Failure]]],
			DefinitionallyEqualQ[TypeTheoryTerm[predecessor[0]], TypeTheoryTerm[Typed["right"[Failure["Zero", <|"Value" -> 0|>]], NonNegativeIntegers | Failure]]]
		}
	],
	{True, True, True},
	TestID -> "If-is-declared-and-a-branch-may-fail"
]

(* <|k -> v, ...|> is an association, each key once, a later value of a key replacing an earlier in its place; Lookup
   gives V | Missing, and Keys, Values, KeyExistsQ and Length are their meanings for associations, beside lists *)
VerificationTest[
	{
		DefinitionallyEqualQ[TypeTheoryType[<|"a" -> 1, "b" -> 2|>], TypeTheoryTerm[Association[Strings, NonNegativeIntegers]]],
		DefinitionallyEqualQ[TypeTheoryTerm[<|"a" -> 1, "b" -> 2, "a" -> 3|>], TypeTheoryTerm[<|"a" -> 3, "b" -> 2|>]],
		DefinitionallyEqualQ[TypeTheoryType[Typed[a, Association[Strings, NonNegativeIntegers]] |-> Lookup[a, "count"]], TypeTheoryTerm[Association[Strings, NonNegativeIntegers] -> (NonNegativeIntegers | Missing)]],
		DefinitionallyEqualQ[TypeTheoryTerm[Lookup[<|"a" -> 1, "b" -> 2|>, "b"]], TypeTheoryTerm[Typed["left"[2], NonNegativeIntegers | Missing]]],
		DefinitionallyEqualQ[TypeTheoryTerm[Lookup[<|"a" -> 1|>, "c"]], TypeTheoryTerm[Typed["right"[Missing["KeyAbsent", "c"]], NonNegativeIntegers | Missing]]],
		DefinitionallyEqualQ[TypeTheoryTerm[Lookup[<|1 -> "one", 2 -> "two"|>, 2]], TypeTheoryTerm[Typed["left"["two"], Strings | Missing]]],
		DefinitionallyEqualQ[TypeTheoryTerm[Keys[<|"a" -> 1, "b" -> 2|>]], TypeTheoryTerm[{"a", "b"}]] && DefinitionallyEqualQ[TypeTheoryTerm[Values[<|"a" -> 1, "b" -> 2|>]], TypeTheoryTerm[{1, 2}]],
		DefinitionallyEqualQ[TypeTheoryTerm[KeyExistsQ[<|"a" -> 1|>, "a"]], TypeTheoryTerm["true"]],
		DefinitionallyEqualQ[TypeTheoryTerm[Length[<|"a" -> 1, "b" -> 2|>] + Length[{1, 2, 3}]], TypeTheoryTerm[5]],
		DefinitionallyEqualQ[TypeTheoryTerm[Typed[<||>, Association[Strings, NonNegativeIntegers]]], TypeTheoryTerm[Typed["association"[{}], Association[Strings, NonNegativeIntegers]]]]
	},
	{True, True, True, True, True, True, True, True, True, True},
	TestID -> "An-association-looks-up-its-keys-and-a-missing-key-is-Missing"
]

(* Missing[reason, details...] is a value that is not there, its details a sequence of expressions, none for one
   reason alone; where an expression is expected, as in a failure's details, an association and a Missing are the
   expressions they write, and TypeTheoryFormalize still reads Keys of an expression as the built-in's *)
VerificationTest[
	Block[{settingOf},
		settingOf[options_] := Keys[options];
		{
			MatchQ[TypeTheoryType[Missing["NotAvailable"]], HoldPattern[TypeTheoryTerm[Missing, _]]],
			MatchQ[TypeTheoryType[Missing["KeyAbsent", "x", 2]], HoldPattern[TypeTheoryTerm[Missing, _]]],
			MatchQ[TypeTheoryType[Failure["Tag", <|"Value" -> 3, "Missing" -> Missing["NotFound"]|>]], HoldPattern[TypeTheoryTerm[Failure, _]]],
			MatchQ[Last[TypeTheoryFormalize[settingOf]], _TypeTheoryDefinition]
		}
	],
	{True, True, True, True},
	TestID -> "Missing-is-a-value-that-is-not-there-and-an-expression-where-one-is-expected"
]

(* a string on its own names a constant, and one that names none is refused, as a misspelled name; FromString[s] is the
   value of the type expected whose string is s, by the instance of "IsString" of that type, and the string where
   nothing decides, inside a function too, its literal the string even where it names a constant, as "true"; TypeHint[e, type] is e ascribed the type, or e alone where the type is the compiler's *)
VerificationTest[
	Block[{increment},
		increment[x_] := TypeHint[x + 1, "MachineInteger"];
		{
			First[TypeTheoryType["sucessor"]],
			DefinitionallyEqualQ[TypeTheoryType[FromString["Hi"]], TypeTheoryTerm[Strings]],
			DefinitionallyEqualQ[TypeTheoryTerm[Typed[FromString["Hi"], Expressions]], TypeTheoryTerm[Typed["Hi", Expressions]]],
			DefinitionallyEqualQ[TypeTheoryTerm[Typed[FromString["Hi"], Atoms]], TypeTheoryTerm["stringAtom"[Typed["Hi", Strings]]]],
			First[TypeTheoryType[Typed[FromString["12"], NonNegativeIntegers]]],
			DefinitionallyEqualQ[TypeTheoryType[TypeHint[3, NonNegativeIntegers | Strings]], TypeTheoryTerm[NonNegativeIntegers | Strings]],
			DefinitionallyEqualQ[TypeTheoryType[Typed[x, NonNegativeIntegers] |-> TypeHint[x + 1, "MachineInteger"]], TypeTheoryTerm[NonNegativeIntegers -> NonNegativeIntegers]],
			First[TypeTheoryType[TypeHint[3, Strings]]],
			MatchQ[TypeTheoryFormalize[increment], {HoldPattern[TypeTheoryDefinition[_, Function[{x_}, x_ + 1]]]}],
			DefinitionallyEqualQ[TypeTheoryTerm[FromString["true"]], TypeTheoryTerm["string"[{116, 114, 117, 101}]]],
			DefinitionallyEqualQ[TypeTheoryType[Typed[n, NonNegativeIntegers] |-> If[n == 0, FromString["none"], FromString["some"]]], TypeTheoryTerm[NonNegativeIntegers -> Strings]],
			DefinitionallyEqualQ[TypeTheoryType[Typed[Typed[n, NonNegativeIntegers] |-> FromString["a"], NonNegativeIntegers -> Expressions]], TypeTheoryTerm[NonNegativeIntegers -> Expressions]]
		}
	],
	{"ElaborationFailed", True, True, True, "NoInstance", True, True, "TypeMismatch", True, True, True, True},
	TestID -> "A-lone-string-names-a-constant-FromString-and-TypeHint"
]

(* Unevaluated is the one head that quotes, as the Wolfram Language passes an argument on unevaluated: Unevaluated[1 + 2]
   is the expression 1 + 2; HoldForm is a head as any other, so HoldForm[1, 2, 3] has three arguments *)
VerificationTest[
	{
		DefinitionallyEqualQ[TypeTheoryTerm[{Arguments[HoldForm[1, 2, 3]]}], TypeTheoryTerm[Typed[{1, 2, 3}, {Expressions}]]],
		DefinitionallyEqualQ[TypeTheoryTerm[Head[HoldForm[1, 2, 3]]], TypeTheoryTerm[Typed[HoldForm, Expressions]]],
		DefinitionallyEqualQ[TypeTheoryTerm[Typed[Unevaluated[1 + 2], Expressions]], TypeTheoryTerm[Construct[Head[a + b], 1, 2]]],
		DefinitionallyEqualQ[TypeTheoryTerm[Typed[1 + 2, Expressions]], TypeTheoryTerm[Typed[3, Expressions]]],
		MatchQ[NormalForm[TypeTheoryTerm[f[1, 2]]], HoldPattern[TypeTheoryTerm[Unevaluated[f[1, 2]], _]]]
	},
	{True, True, True, True, True},
	TestID -> "Unevaluated-quotes-and-HoldForm-is-a-head-as-any-other"
]

(* Unevaluated of one expression is one argument, as the Wolfram Language passes it on: among the arguments of
   Construct, of the type Expressions..., it is quoted, and where a natural number is expected it is the element itself;
   Unevaluated of several is a sequence, spliced in *)
VerificationTest[
	{
		DefinitionallyEqualQ[TypeTheoryTerm[Construct[f, 1 + 2, Unevaluated[1 + 2]]], TypeTheoryTerm[Construct[f, 3, Construct[Head[a + b], 1, 2]]]],
		DefinitionallyEqualQ[TypeTheoryTerm[Typed[Unevaluated[1 + 2], NonNegativeIntegers]], TypeTheoryTerm[3]],
		DefinitionallyEqualQ[TypeTheoryTerm[Construct[f, Unevaluated[1, 2], 3]], TypeTheoryTerm[Construct[f, 1, 2, 3]]],
		DefinitionallyEqualQ[TypeTheoryType[TypeTheoryTerm[{Unevaluated[1 + 2], 4}]], TypeTheoryTerm[{Expressions}]],
		DefinitionallyEqualQ[TypeTheoryType[TypeTheoryTerm[Prepend[Unevaluated[Unevaluated[1], 2], 0]]], TypeTheoryTerm[NonNegativeIntegers...]]
	},
	{True, True, True, True, True},
	TestID -> "Unevaluated-of-one-expression-is-one-argument-quoted-where-an-expression-is-expected"
]

(* TypeTheoryType and TypeTheoryProof keep an Unevaluated they are given, as HoldAllComplete functions do in the Wolfram
   Language, so a quotation means the same at the top as inside a term *)
VerificationTest[
	{
		DefinitionallyEqualQ[TypeTheoryType[Unevaluated[1 + 2]], TypeTheoryTerm[Expressions]],
		DefinitionallyEqualQ[TypeTheoryType[1 + 2], TypeTheoryTerm[NonNegativeIntegers]],
		TypeTheoryProof[Unevaluated[1 + 2] == Construct[Head[a + b], 1, 2], {"Reflexivity"}]["Goals"]
	},
	{True, True, {}},
	TestID -> "A-quotation-at-the-top-of-a-query-is-kept"
]

(* where nothing is expected, the whole term of a query may be an expression of a name that names nothing, f[1, 2] or
   a + b c; inside a term, as in the value of a declaration, such a name applied to numbers alone is no term: it is most
   often misspelled, or the name being defined, which a definition may not use; applied to a variable of expressions it
   makes a template *)
VerificationTest[
	{
		DefinitionallyEqualQ[TypeTheoryType[f[1, 2]], TypeTheoryTerm[Expressions]],
		DefinitionallyEqualQ[TypeTheoryType[a + b c], TypeTheoryTerm[Expressions]],
		First[TypeTheoryType[Typed[n, NonNegativeIntegers] |-> Loop[n] + 1]],
		First[TypeTheoryEnvironment[{TypeTheoryDefinition[Loop, Typed[n, NonNegativeIntegers] |-> Loop[n] + 1]}]],
		First[TypeTheoryEnvironment[{TypeTheoryDefinition[Double, Typed[n, NonNegativeIntegers] |-> twice[n]]}]],
		DefinitionallyEqualQ[TypeTheoryType[Typed[x, Expressions] |-> x^2 + x], TypeTheoryTerm[Expressions -> Expressions]],
		DefinitionallyEqualQ[TypeTheoryType[Typed[n, NonNegativeIntegers] |-> Typed[g[n], Expressions]], TypeTheoryTerm[NonNegativeIntegers -> Expressions]],
		DefinitionallyEqualQ[TypeTheoryType[Typed[x, Expressions] |-> g[x, 2]], TypeTheoryTerm[Expressions -> Expressions]]
	},
	{True, True, "ElaborationFailed", "ElaborationFailed", "ElaborationFailed", True, True, True},
	TestID -> "A-name-that-names-nothing-makes-an-expression-only-as-the-whole-term-of-a-query"
]
