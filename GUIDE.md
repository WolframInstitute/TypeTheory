# Wolfram Language style guide

Conventions for Wolfram Language code: `.wl` package files, `.wls` scripts,
`.wlt` test files, and code in ` ```wl ` markdown code cells. They keep
code readable and consistent across a codebase.

## Code as narrative: the guiding philosophy

A function is a narrative. Your code is a conversation with four readers:
the kernel (which runs it), you-in-the-future, future developers, and
current collaborators who call or change your code. Only the first does
not care whether the code is clear to a human; the other three are why
you write for readability.

Your time is worth far more than the CPU time to run the computation. Make
the code understandable to a human even if it costs a few cycles or
megabytes. Writing this way also surfaces where refactoring could buy
real performance.

## Naming

The first thing to do when writing a function is decide its name. Revisit
the name as the function evolves; renaming is part of refactoring. The
name is part of the documentation.

- The names of symbols consist of complete English words.
- American spelling is used.
- The first letter of each word is capitalized, except that the first letter
  of the names of internal symbols, function arguments, and localized
  variables should be lowercase.
- Functions whose names end with `Q` "ask a question", and always return
  either `True` or `False`.
- Mathematical functions that are named after people usually have names in
  the Wolfram Language of the form `PersonSymbol`.
- Global parameters / configuration symbols start with `$`.

### A name must say what the object is

An exported name has to carry enough context to identify
the object on its own. That usually takes two or more words:
`SingularValueDecomposition`, `IrreduciblePolynomialQ`, `FindShortestPath`,
`DiscreteUniformDistribution`.

A single word is admissible only when that word is unique, i.e. a term with
no alternate meaning in the Wolfram Language or ordinary English. `Poset`
and `Matroid` qualify. `Group`, `Ring`, `Field`, `Term` and `Variety`
do not, because each has alternate meanings in ordinary English.

### Never abbreviate, contract, or initialise

```wolfram
(* BAD *)   SVDResidual
(* GOOD *)  SingularValueDecompositionResidual
```

This holds even where the abbreviation is standard within its
field. `SVD`, `PID` and `ODE` are clear to a specialist but unreadable to
a layperson. Established Wolfram Language idioms are not abbreviations:
`Q` for a predicate and `$` for a global are followed as-is, as are single
letters that are the subject's own notation inside a longer name:
`BesselJ`, `LegendreP` and `ChebyshevT` carry the letter the
literature uses for the family, and `KEdgeConnectedGraphQ` carries the
k of k-edge-connected.

### Never collide with a System symbol

Before naming an exported function, check ```NameQ["System`" <> name]```
(or just try the bare name in a clean kernel). If the Wolfram Language
already has it, do not redefine it.

This causes a silent issue under StructuredPackageFormat:
`PackageExported[Foo]` silently does nothing if `Foo` is a `` System` ``
symbol (the first-pass reader strips `` System` `` names), and your
`Foo[...] :=` then tries to write to the protected built-in and fails. For
example, `SymmetricDifference` is a built-in: if a name like that is
already taken, rename your symbol, or just use the built-in.

Also ask whether a general name *might* become a System function later
(`CellularAutomatonPlot` doesn't exist yet, but could). Prefer specific,
unlikely-to-collide names. Specificity also means *unambiguous in meaning*:
if a proposed name has other unrelated uses - another field's notion, or
a common word carrying a separate technical sense - revisit it and pick a
name that picks out this concept alone. And make sure localized symbols
inside a `Module`/`Block`/`With` don't share a name with a function in
your codebase, or a global rename will rewrite both.

### Avoid depending on `` System`Private` `` internals

Never call undocumented `` System`Private` `` symbols (or other
unpublished internal kernel functions) in implementation code, with the exceptions of
HoldValidQ,HoldSetValid,HoldNotValidQ,SetNoEntry,HoldSetNoEntry,ValidQ, and HasAnyEvaluationsQ,
and only use these if necessary. 
Unpublished internal kernel functions are
not part of the public language, they can change or disappear between
versions, and a reader cannot look them up. If you need the functionality
one provides, prefer to re-implement
it as a plain, documented paclet helper rather than reaching into the
kernel's private context. A predicate that re-runs its structural check
each time is the simplest such replacement:

```wolfram
(* AVOID: leans on undocumented kernel internals to cache validity *)
c_Foo /; System`Private`HoldNotValidQ[c] && fooDataQ[Unevaluated[c]] :=
	System`Private`SetNoEntry[System`Private`HoldSetValid[c]]
FooQ[c_Foo] := System`Private`HoldValidQ[c] || fooDataQ[Unevaluated[c]]

(* PREFER: a plain predicate that re-validates *)
FooQ[c_Foo] := fooDataQ[Unevaluated[c]]
```

### Formal symbols for variables a function introduces

When a definition puts a *fresh* symbol into its output - a bound/dummy
variable, a generic point, a placeholder in a returned expression like
a generating function's variable - use a Formal symbol (`\[FormalX]`,
`\[FormalY]`, ..., entered `Esc fx Esc`), not a plain `x`. Formal symbols
are `Protected`, carry no global value, and can't be captured by or
collide with the caller's `x`, so the returned expression stays clean.

## Designing High-Level Forms

What a function accepts and returns is settled before any of the mechanics
below. These rules apply to every area of development, and to new core
objects in particular, see
[Wolfram Language Principles and Concepts](https://www.wolfram.com/language/principles/).

- A new symbol that is similar in intent and conceptual use to a built-in
  symbol should get a similar design, in code and in documentation: the same
  argument conventions and the same output formatting.
- Where a built-in function already covers a property, such as `GroupOrder`,
  `GroupGenerators` or `GroupElements`, use it and teach it in the
  documentation rather than adding an `obj["Order"]` accessor beside it.
- Give an object properties, read with an accessor, only where several kinds
  of the object carry different extra data (a presentation, coset
  representatives, product factors). The accessor must not be the only way to
  get at information a user is likely to want.

## Indentation and spacing

- Use tabs rather than space indentation. Never use spaces for indentation.
- Spaces around infix operators (`+`, `*`, `->`, `:>`, `&&`, etc.),
  including the pattern colon (`x : pattern`) and `Alternatives`
  (`a | b`). Two exceptions take no surrounding space:
  - `PatternTest` (`?`) binds tightly to the blank in front of it:
    write `t_?NumericQ`, never `t_ ? NumericQ`. It never applies to
    more than one argument, so the tight form is unambiguous.
  - A blank stays attached to its head (`_Integer`, not `_ Integer`),
    since a stray space there is read as `Times` (`_ Plus` parses as
    `Blank[] * Plus`).
- Prefer structural indentation over column alignment.
- One semantic unit per line in long forms (`Which`, `Switch`,
  `Association`, `Table`, option lists).

### Code width

Keep lines within **200 characters** (a hard "you shall not pass" ceiling);
treat **150** as a gentle suggestion to start breaking a line up. Shorter
lines read more easily and stay legible regardless of a developer's screen
size or editor setup. Some structures (long URLs, complex scanner-style
signatures, deeply nested definitions) will unavoidably run long;
prioritize clarity over a strict character count.

When continuing a string use a "\" as the line continuation character. Do
not add indentation when continuing a string to a new line.

### Never split a binary operator's operands across lines

Operators (`+`, `-`, `*`, `/`, `.`, `&&`, `||`, etc.) must have both
operands on the same line. The Wolfram IDE flags split operands as
`DifferentLine` and the resulting form reads worse than a longer single
line.

```wolfram
(* BAD: trips DifferentLine lint *)
TSet[wTen, wTen - lrHat * mTen
                  / (Sqrt[vTen] * invSqrtB2cor + eps)];

(* GOOD: keep the whole arithmetic chain on one line, even if it's
   long; or factor an intermediate into a named binding first. *)
TSet[wTen, wTen - lrHat * mTen / (Sqrt[vTen] * invSqrtB2cor + eps)];

(* GOOD: factor when the line gets unreadably wide *)
denom = Sqrt[vTen] * invSqrtB2cor + eps;
TSet[wTen, wTen - lrHat * mTen / denom];
```

The lint rule is `wolfram lint(DifferentLine)`; if you see it, either
join the line or factor.

When a long boolean or arithmetic chain genuinely cannot be factored and
would go past the width limit, rewrite it in `InputForm` functional head
form (`Or[...]`, `And[...]`, `Plus[...]`) with one operand per line. Each
continuation operand starts its own line; never leave an operator dangling
at the end of the previous line.

```wolfram
(* BAD: operators trailing at the ends of lines *)
result = veryLongConditionOne ||
	veryLongConditionTwo ||
	veryLongConditionThree

(* GOOD: functional head, one operand per line *)
result = Or[
	veryLongConditionOne,
	veryLongConditionTwo,
	veryLongConditionThree
]
```

A valid alternative approach is to put the operands inside of () brackets
as in

```wolfram
result =
	(
		veryLongConditionOne
	) ||
	(
		veryLongConditionTwo
	) ||
	(
		veryLongConditionThree
	)
```

### Commas, semicolons, and line breaks

- Put a space after every in-line comma: `good[Sin[x], a, b]`, not
  `bad[Sin[x],a,b]`.
- When a comma-separated form wraps onto multiple lines, the comma ends
  the line; never start a continuation line with a leading comma.
- One statement per line: break after each `;`. Don't pack
  `a = 1; b = 2; c = 3` onto a single line.
- Never leave `;;` (`Span`) at the end of a line. It is too easily
  misread as `;` (`CompoundExpression`) 
   - `var = {1, 2, a, b};;` quietly
  assigns `Span[{1, 2, a, b}, All]`, not the list you meant.
- No semicolon immediately before a comma, or before the final closing
  bracket of a scoping/control structure. A hanging `;` silently
  evaluates to `Null`.

```wolfram
(* BAD: the hanging ; makes var = Null *)
var = If[True, code;]
var = If[True, code1;, code2]

(* GOOD *)
var = If[True, code]
var = If[True, code1, code2]
```

- Indent one level deeper for each new level of expression, so the tree
  structure is visible at a glance. In `Which`/`Switch`, indent each
  body one level past its test:

```wolfram
Which[
	test1,
		code1,
	test2,
		code2,
	True,
		code3
]
```

## Definitions

Prefer `Module` for local workspaces unless `Block`'s ability to
temporarilly assign a value to a parameter is needed.  Don't add a
trailing `;` to any top-level assignment - `SetDelayed` (`:=`) AND `Set`
(`=`). Each definition is a complete expression; line breaks separate them.

```wolfram
(* GOOD *)
Options[myFn] = {GraphLayout -> "LayeredDigraphEmbedding"}

myFn[x_] := x + 1

(* BAD *)
Options[myFn] = {GraphLayout -> "LayeredDigraphEmbedding"};
myFn[x_] := x + 1;
```

```wolfram
f[x_] := x + 1

g[args__] := Block[{
	x = ...,
	y
},
	body
]
```

The `Block`/`Module` variable list opens on the same line as the head
(`Module[{`), variable bindings are indented one level deeper, and `}`,
body, and the closing `]` all return to the column where the line that
opens `Module[` starts.

`With` does not need nesting for sequential bindings; these are equivalent,
so prefer the flat form:

```wolfram
(* nested - avoid *)
With[{a = 5}, With[{b = 2 a}, Sqrt[b]]]

(* flat - preferred *)
With[{a = 5}, {b = 2 a}, Sqrt[b]]
```

If a `With` gets very complicated and its scoping isn't critical, use
`Block` instead.

### Check a System symbol's attributes before reusing it as notation

Reusing a built-in operator for abstract notation inherits its attributes,
and an attribute rewrites your expressions before any of your definitions
see them.

```wolfram
Attributes[NonCommutativeMultiply]   (* {Flat, OneIdentity, Protected} - reassociates *)
Attributes[CircleTimes]              (* {} - inert, safe as abstract notation *)
```

`NonCommutativeMultiply` is `Flat`, so it reassociates every
expression written with it, which is wrong for any product that is not
associative. `CircleTimes` and `CirclePlus` carry no attributes, which
is what makes them usable.

For an operator that is pure notation the default is **no attributes at
all**: the operator is inert syntax, and every algebraic law belongs to
the structure that interprets the expression rather than to the notation.

### Function Arguments

The main expression or object on which a function acts is usually given as
the first argument to the function. Subsidiary parameters appear as subsequent
arguments.

A function should maximize flexibility of possible forms it accepts for the
main objects on which it acts so that everything fits together to ensure
coherence of design and interoperability across all domains.

### Argument patterns and fall-throughs

Write every downvalue with specific patterns, so that input a function
does not handle matches nothing and returns unevaluated rather than
half-evaluated. Reserve a `Failure` object for when the function
matched, tried, and an attempt failed: validate intermediate steps with
`Enclose`/`Confirm` (see *Invalid input and failure*), and never signal
failure with a `Message`-and-`$Failed` fall-through.

```wolfram
(* BAD: pattern too loose, silent on misuse *)
foo[str_] := StringLength[str]

(* GOOD: specific pattern; foo[5] matches nothing and returns unevaluated *)
foo[str_String] := StringLength[str]
```

If a function is meant to take only a specific pattern make sure that that
pattern is specified in the argument of the function's definition. This
is also critically important when a function has several valid argument
forms, give each its own specific pattern; input that matches none of
them returns unevaluated:

```wolfram
foo[str_String] := StringLength[str]
foo[int_Integer] := IntegerLength[int]
foo[nList : {__Integer}] := foo /@ nList
```

For a predicate (a `...Q` function), the natural fall-through is
`predicateQ[___] := False`, not a `Failure`.

### Don't require a `Hold` around arguments

A function should not require its caller to wrap arguments in
`Hold[...]`, nor in `HoldForm`, `HoldComplete`, `HoldPattern`,
`Unevaluated`, `Defer` or `Inactive`. Design functions to take
ordinary, already-evaluated arguments so calls compose normally.
Where a function genuinely must see an argument unevaluated, give the
function a `HoldFirst` or `HoldAll` attribute, so the holding lives in
the definition instead of at every call site.

### Optional arguments

For functions that take Wolfram Language-style options, use
`opts : OptionsPattern[]`, not `opts___?OptionQ`. The former integrates
with `Options[fn]` declarations and `OptionValue[fn, key]`.

```wolfram
Options[myFn] = {GraphLayout -> "LayeredDigraphEmbedding"};

myFn[args___, opts : OptionsPattern[]] :=
	With[{layout = OptionValue[GraphLayout]},
		...
	]
```

Document what values each option accepts - especially what `Automatic`
resolves to - in the usage message or a comment, so a later reader need
not reverse-engineer it.

The bare `OptionValue[key]` shorthand is the norm; reach for the explicit
`OptionValue[fn, {opts}, key]` form only where the shorthand cannot
resolve: inside a condition attached to the left-hand side, and in a helper
function that resolves another (public) symbol's options from a forwarded
`opts` sequence. Defaults always live in one `Options[fn]` declaration -
never in an ad-hoc defaults list spliced into each `OptionValue` call.

### Boolean options: `TrueQ[OptionValue[...]]`

Wrap boolean options in `TrueQ` so non-`True` values (unbound symbols,
typos, `Automatic`, etc.) collapse to `False` instead of propagating into
`If` as an unevaluated test.

```wolfram
(* GOOD *)
If[ TrueQ[OptionValue["Branchial"]], ..., ...]

(* BAD: if user passes "Branchial" -> Bogus, the If never evaluates *)
If[ OptionValue["Branchial"], ..., ...]
```

For stricter validation, confirm the value and fail loudly:

```wolfram
Options[function] = {"UseMyThing" -> True};

function[opts : OptionsPattern[]] :=
	Enclose @ Module[{useMyThing},
		useMyThing = OptionValue["UseMyThing"];
		ConfirmMatch[useMyThing, True | False,
			Message[function::opttf, "UseMyThing", useMyThing]];
		...
	]
```

### First option wins - forced overrides go FIRST

When a wrapper needs to force certain options on the inner call but
also let the user pass through extras, put the forced overrides
FIRST and the user's filtered options LATER in the argument
list. Wolfram functions take the FIRST setting on collision (verify
with `Options[Graph[..., EdgeLabels -> "a", EdgeLabels -> "b"]]` ->
`"a"`). Don't `/. (Key -> _) -> Nothing` to scrub user options out -
just place the forced override first.

```wolfram
(* GOOD: our forced VertexLabels wins; user's GraphLayout /
   ImageSize / etc. pass through. *)
Graph[
	vs, es,
	VertexLabels -> myLabels,
	Background -> LightDarkSwitched[White, GrayLevel[0.13]],
	FilterRules[Flatten[{opts}], Options[Graph]]
]
```

Thread options to inner functions through `FilterRules`. Always wrap
the options in `Flatten[{opts}]`: `opts` may arrive as a single `Rule`,
a list, or a `Sequence`.

```wolfram
Options[moo1] = {"MyMoo1Exponent" -> 3};
Options[moo2] = Flatten[{Options[moo1], "MyMoo2Exponent" -> 3}];

moo2[x_, opts : OptionsPattern[]] :=
	Enclose @ Module[{e},
		e = OptionValue["MyMoo2Exponent"];
		ConfirmMatch[e, _Integer];
		x^e * moo1[x, FilterRules[Flatten[{opts}], Options[moo1]]]
	]
```

## Patterns and downvalues

### Make patterns as specific as possible

Patterns, pattern tests, and conditions are how a function controls which
inputs each downvalue handles. The more specific the pattern, the more of
your input validation the evaluator does for free, and the less a loose
clause can swallow inputs it was never meant to.

```wolfram
(* BAD: too loose; this clause catches everything *)
f[a_, b_] := a + b

(* GOOD: each clause says exactly what it accepts *)
f[a_?NumericQ, b_?NumericQ] := a + b
f[a_String, b : Except[_String]] := a <> ToString[b]
```

### Order downvalues most-specific first, and watch the auto-reordering

The evaluator tries to apply more specific definitions before more general
ones, and it *reorders* the downvalues of a symbol by specificity as you
enter them - so the textual order you typed is not always the order that
runs. Write definitions most-specific first anyway, so the code reads in
the order it (usually) evaluates.

The reordering is purely structural. A `Condition` (`/;`) or a
`PatternTest` (`?`) with non-trivial logic on the **left-hand side**
defeats it: the evaluator can't see that one such clause is more specific
than another, so they stay in entry order and you can get the wrong clause.

```wolfram
(* likely not intended: the general clause is entered first and is
   NOT promoted, because the Condition hides the specificity *)
f[x_Integer?Positive] := "a"
f[x_Integer] /; Positive[x] && EvenQ[x] := "b"
f[2]   (* -> "a", probably not what you wanted *)

(* fix by ordering the clauses manually, most specific first *)
f[x_Integer?(Positive[#] && EvenQ[#] &)] := "b"
f[x_Integer?Positive] := "a"
f[2]   (* -> "b" *)
```

In general, prefer conditions on the right-hand side (see below) and
avoid `Condition` on the LHS when you have many downvalues. You can probe
relative specificity with ``Internal`ComparePatterns[lhs1, lhs2]``.

### Prefer conditions on the right-hand side

For a function with many downvalues, putting the branch logic on the RHS
(via `Which`/`Switch` or a guarded result) keeps the dispatch readable
and sidesteps the LHS-condition reordering trap above.

```wolfram
(* instead of one guarded clause per case on the LHS *)
dv[args_ /; condition1] := code1
dv[args_ /; condition2] := code2

(* gather the branch logic on the RHS *)
dv[args_] := Which[
	condition1,
		code1,
	condition2,
		code2
]
```

### A too-general pattern also matches inside replacements

The same looseness causes issues in `Replace`/`ReplaceAll`. A blank
matches  everything, including the parts you meant to leave alone.

```wolfram
list = {1, "a", 2, "b", 3}

list /. _ -> "NOPE"         (* {"NOPE", "NOPE", ...} - everything *)
list /. _String -> "NOPE"   (* {1, "NOPE", 2, "NOPE", 3} - intended *)
```

### Avoid `Part` (`[[ ]]`)

Reaching into an expression by position is brittle: a positional index
says nothing about what it is pulling out, and it breaks when the shape
shifts. Prefer named patterns, `First`/`Last`/`Rest`/`Most`/`Drop`,
or a small helper function.

```wolfram
(* BAD *)
abbreviation = {letters[[1]], letters[[8]]}

(* GOOD: First / Drop *)
abbreviation = {First[letters], First[Drop[letters, 7]]}

(* GOOD: a named-pattern replacement *)
abbreviation = letters /. {i1_?UpperCaseQ, ___, i2_?UpperCaseQ, ___} :> {i1, i2}
```

### `Set`/`SetDelayed` and `Rule`/`RuleDelayed`: pick the one you mean

Use the delayed form (`:=`, `:>`) whenever the right-hand side names a
pattern variable or should re-evaluate on each use; use the immediate form
(`=`, `->`) when you want the RHS evaluated once, now.

```wolfram
(* immediate: RHS evaluated once, frozen *)
f[x_] = RandomInteger[{0, 10}]   (* every f[x] returns the same number *)

(* delayed: RHS re-evaluated on each call *)
f[x_] := RandomInteger[{0, 10}]  (* a fresh number each time *)
```

A subtle trap: with `Rule`, a pattern name that already has a global
value is substituted before the rule applies, so prefer `:>` whenever
the left-hand side binds a name.

```wolfram
y = 3;
{f[x], g[x]} /. _[y_] -> y   (* y is replaced by 3 first - surprise *)
{f[x], g[x]} /. _[y_] :> y   (* binds y per match, as intended *)
```

## Control flow

Avoid procedural code. If you find yourself writing C/Fortran-style loops
with explicit counters and mutation, step back and use a functional form.

### No `For` loops

Don't write `For[i = 1, i <= n, i++, ...]`. Use:

- `Do[body, {i, n}]` for side effects with a counter.
- `Table[expr, {i, n}]` to build a list.
- `Nest`, `NestList`, `NestWhile`, `Fold`, `FoldList` when there's
  iterative state to thread through a fixed transition.
- `Map`, `Scan` to act over a list.

```wolfram
(* BAD *)
For[i = 1, i <= n, i++,
	AppendTo[acc, f[i]]
]

(* GOOD *)
acc = Table[f[i], {i, n}]
```

### Listability over `Map`

Arithmetic heads (`Power`, `Times`, `Plus`, `Sqrt`, ...) are `Listable`:
they thread over lists on their own. Write the threaded expression
directly and save `Map` for operations that genuinely are not Listable
(applying a derivative to each function in a list, property extraction).

```wolfram
(* BAD *)
Total[Map[#^2 &, s["Velocities"]]]

(* GOOD *)
Total[s["Velocities"]^2]

(* GOOD - Derivative over a list of functions is not Listable *)
#'[t] & /@ paths
```

Where a map is genuinely wanted, write it infix: `f /@ list`, not
`Map[f, list]`. Parenthesize where precedence needs it, since a trailing
`&` takes everything to its left and a prefix `@` binds tighter than `/@`:
`Association[(f &) /@ list]`, not `Association @ f & /@ list`. The
three-argument form with a level specification has no infix spelling and
stays `Map[f, expr, {2}]`.

### `Replace` over `Switch` for value-to-value mapping

When the cases are simple value patterns mapping to values (no structural
tests, no side effects), `Replace` with a rule list is more concise and
reads as data, not control flow.

```wolfram
(* GOOD *)
legend = Replace[OptionValue[PlotLegends], {
	None | False -> None,
	Automatic | True :> familyLegend[presentFamilies]
}]
```

Use `Switch` (or `Which`) when branches have side effects, dispatch on
richer patterns, or need fallthrough `_` to the original value.

### No Comma-on-own-line between multi-line branches

When the branches of `If` (or args of `Block`, `Switch`, `With`, etc.) are
each multi-line, put a carriage return between each argument.  The carriage
reads as a branch boundary, like a horizontal rule. If the code blocks in
the arguments are large then put a short comment before each to indicate
where that block starts. Do not put a comma on its own line.

```wolfram
(* GOOD *)
branchial = If[ TrueQ[OptionValue["Branchial"]],
	DeleteDuplicates @ Catenate @ Map[
		s |-> ...,
		sliceKeys
	],

	{}
]

(* GOOD: short branches keep commas inline *)
If[Length[dirs] === 0,
	counter = 0,
	counter += 1
]
```

### No `Head[expr] === Foo` - use `MatchQ`

`Head[x] === Foo` is a structural test that doesn't compose with
patterns. `MatchQ[x, _Foo]` (or `MatchQ[x, Foo[args...]]` for a shape
check) is the canonical form.

```wolfram
(* BAD *)
If[ Head[expr] === Inactive[Equal] && expr[[1]] === expr[[2]], ...]

(* GOOD *)
If[ MatchQ[expr, Inactive[Equal][x_, x_]], ...]
```

### Equality: exact vs approximate

Use `===` (`SameQ`) and `=!=` (`UnsameQ`) to compare exact values and
structure. Use `==` (`Equal`) / `!=` (`Unequal`) when comparing approximate
(machine/real) values, where structural identity is the wrong question
(`1.4142135623730951 == Sqrt[2]` is `True`; `===` is `False`). In cases of
a boolean test you will typically use `===` (`SameQ`) or `=!=` (`UnsameQ`).

### Keep control structures local

Wrap a control structure (`If`, `Which`, `Switch`) around only the part
that actually varies, not around a whole duplicated expression. It is
shorter and the difference between branches jumps out.

```wolfram
(* BAD: the call is duplicated just to swap one argument *)
If[ test,
	func[arg1, arg2, Blue],
	func[arg1, arg2, Red]
]

(* GOOD: the If sits in the argument that changes *)
func[arg1, arg2, If[test, Blue, Red]]

(* GOOD: when logic can't live inline, bind it just above *)
With[{color = If[test, Blue, Red]},
	func[arg1, arg2, color]
]
```

## Invalid input and failure

First separate two things a function can do with input it returns no
value for - they are not the same and must not be conflated:

- **A wrong-type or wrong-shape argument is a non-match, not an error.** Put
  the validity in the pattern (see *Argument patterns and fall-throughs*) so
  the call matches no clause and is **returned unevaluated**. Do *not* give the
  function a wide pattern and then `Confirm` the argument's type to manufacture
  a `Failure` - that turns an ordinary non-match (which is free to be used
  symbolically or gain a definition later) into a spurious error. The same
  goes for a well-formed case you deliberately scoped out: it issues a
  message and returns unevaluated, and **never a `Missing`**. A `Missing` is
  a *value*: it flows silently into arithmetic downstream, and it prevents
  the later definition that would have handled the case. An unevaluated
  expression does neither, and says plainly that nothing was computed.
- **A `Failure` is for an attempt that engaged and could not finish** - a
  clause matched, computation started, and a step only checkable *after*
  starting did not work out. Signal it by **returning a `Failure` object, not
  by throwing a `Message` and returning `$Failed`.**

A function with no guard does not return nothing; it returns a wrong
answer. Write the in-scope pattern so that the cases the algorithm assumes
(finite, square, non-degenerate, characteristic 0) are the cases it can
match, and test the boundary. A predicate needs the same care in the
other direction: the `predicateQ[___] := False` fall-through answers "no"
to ill-typed and out-of-scope input, but input that is valid and merely
undecided returns unevaluated instead of `False`.

Handle the second case with the `Confirm`/`Enclose` paradigm:

- Wrap the body in `Enclose` (`Enclose @ Module[...]` when you need
  locals) and validate intermediate results with `Confirm`, `ConfirmBy`,
  `ConfirmMatch`, `ConfirmAssert`. The first failed `Confirm` sends control
  to the enclosing `Enclose`, which returns a `Failure`. The third argument
  to a `Confirm*` is the message that `Failure` carries:

```wolfram
(* Type is in the pattern, so a non-matrix is a non-match (left unevaluated);
   singularity cannot be seen in the pattern - it is only discovered by
   attempting the inverse, so it is Confirmed and becomes a Failure. *)
safeInverse[m_?MatrixQ] := Enclose[
	ConfirmBy[Quiet @ Inverse[m], MatrixQ, "matrix is singular."]
]
(* safeInverse[5]                  -> safeInverse[5]   (no match, unevaluated) *)
(* safeInverse[{{1, 1}, {1, 1}}]   -> Failure["ConfirmationFailed", <|...|>]   *)
```

- Prefer a `Failure[...]` over `Message[...]; $Failed`. A `Failure` is a
  value: it carries its own message (`failure["Message"]`), is inspectable,
  composes, and propagates cleanly through `Confirm` and `FailureQ`. A
  thrown `Message` is a side effect that a caller cannot catch structurally.
  When constructing one directly, give it a tag and a message template:

```wolfram
Failure["badArgument", <|
	"MessageTemplate" -> "`1` is not a valid argument.",
	"MessageParameters" -> {arg}
|>]
```

- A `Failure[...]` (or `$Failed`) returned by any inner function should be
  always be passed upward immediately; test with `FailureQ`, or just `Confirm` it.
- Never use `Return`. Structure the code so the value falls out, or use
  `Confirm`/`Enclose` to return control upward.

## Efficiency

Readability comes first, but a handful of habits give real speed at no
cost to clarity.

### Collapse repeated tests of one symbol into `Switch`/`Which`

A stack of `If`s that all test the same value is both slower and harder
to read than a single `Switch` (or `Which`).

```wolfram
(* BAD *)
If[ MatchQ[n, 0], m = "a"];
If[ MatchQ[n, 1], m = "b"];
If[ !MatchQ[n, 0 | 1], m = "c"]

(* GOOD *)
m = Switch[n,
	0,
		"a",
	1,
		"b",
	_,
		"c"
]
```

### Promote a repeated check into a named flag

If the same test appears in several branches, compute it once into a
`With` binding and reuse the flag.

```wolfram
With[{aFlag = NumericQ[a], bFlag = NumericQ[b]},
	Which[
		aFlag && bFlag,
			code1,
		aFlag && !bFlag,
			code2
	]
]
```

### Order tests fastest-first

Inside `And`/`Or`, put the cheap tests first so an early `False`/`True`
short-circuits before the expensive one runs. A `MatchQ` is far cheaper
than an `Integrate`, so test the shape first.

```wolfram
(* GOOD: cheap MatchQ guards the expensive Integrate *)
MatchQ[Hold[expr], Hold[pattern_]] && Integrate[expr, x] == 1
```

### `And[...]`/`AllTrue` over `And @@ {...}`

`And @@ {a, b, c}` builds the whole list first, evaluating every element;
`And[a, b, c]` stops at the first `False`. When you are testing a list
with one predicate, `AllTrue`/`AnyTrue`/`NoneTrue` run the test only as
far as the logic requires.

```wolfram
And[5 > 3, 6 > 4, 7 > 5]
AllTrue[{-3, -2, -1, 0, 1}, Positive]
```

### `Lookup` with a default over nested `Replace`

When you want a keyed value with a fallback, `Lookup` is clearer and
faster than chaining `Replace`/`ReplaceAll` to patch in the default.

```wolfram
(* BAD *)
"Result" /. rules /. "Result" -> None

(* GOOD *)
Lookup[rules, "Result", None]
```

### Check validity before expensive work

Do the cheap rejections first so you never pay for a computation whose
result you are about to discard. Use `Confirm`/`Enclose` (see *Invalid
input and failure*) to stop the moment an input fails, rather than
computing a result and validating it afterward. For a function that scans
a list or expression, `Catch`/`Throw` lets you exit as soon as a trigger
is hit instead of finishing the scan.

```wolfram
Catch[
	Map[
		If[ContainsQ[#, Root | RootSum] && approximatableQ[#], Throw[#]] &,
		exprList
	]
]
```

### Don't reassign one variable through a pipeline

Reusing a single mutable name for each stage obscures the data flow and
makes debugging harder (you can't inspect an earlier stage). Give each
stage its own descriptive binding instead.

```wolfram
(* BAD: one name, reassigned twice *)
variable = Range[5];
variable = 2 * variable;
variable = Riffle[variable, 0]

(* GOOD: a name per stage *)
Module[{base = Range[5], doubled, riffled},
	doubled = 2 * base;
	riffled = Riffle[doubled, 0]
]
```

(This is about *staged reassignment*, not the single-use values that
should still be inlined - see Composition.)

### Multi-argument `Quiet`, `Sow`/`Reap`, `Catch`/`Throw`

Quiet only the messages you expect, not everything; tag `Sow`/`Reap` and
`Catch`/`Throw` so each sown or thrown value has a known destination.

```wolfram
(* instead of silencing every message *)
Quiet[1/0, Power::infy]

(* tag thrown values so the right Catch picks them up *)
Catch[
	Throw[$Failed, "failureTag"],
	"failureTag"
]
```

### Keep arguments held when a function shouldn't evaluate them

If you must pass an unevaluated expression into a function that lacks
a `Hold*` attribute, wrap it in `Hold` (and unwrap where needed). Any
developer utility like a `debugPrint` should carry `HoldAllComplete`
so it never adds evaluation to normal runtime.

## Mutation

### No `AppendTo` (or other list-growing mutation)

`AppendTo[xs, y]` is `xs = Append[xs, y]`, which copies on every
step. Build the result with `Table`, `Map`, or `Fold` so the final list
is allocated once.

```wolfram
(* BAD *)
out = {};
Do[ AppendTo[out, f[i]], {i, n} ];
out

(* GOOD *)
out = Table[f[i], {i, n}]

(* GOOD: state threaded by Fold *)
acc = Fold[step, init, xs]
```

Same for Associations: use `Association[Table[k -> v, ...]]`,
`AssociationMap`, or `Fold[Append, <||>, kvPairs]` rather than
`assoc[k] = v` inside a `Do`.

### Bracket alignment

A closing `]` (or `}`, `|>`, `)`) goes on its own line, indented to the
same column as the opening head. Never end a multi-line form with `...]`
on the last expression's line.

```wolfram
(* GOOD *)
Module[{x, y, z},
	body1;
	body2
]

(* BAD *)
Module[{x, y, z},
	body1;
	body2]
```

## Pure functions

Pure functions are valuable, but reach for them only when they earn
their keep.

### Don't use a pure function where a named operator does the job

```wolfram
(* BAD *)
(#1 + #2) & @@ {1, 2}

(* GOOD *)
Plus @@ {1, 2}
```

### Prefer the full `Function[{x, ...}, ...]` form for anything non-trivial

Slot (`#`/`&`) syntax is fine for something small and obvious like
`Times[#, 5] & /@ Range[5]`. Past that, named arguments read far better
and make precedence explicit.

```wolfram
(* BAD: opaque slot soup *)
(#1 + (#2^#3 - #1)/#1) &[1, 2, 3]

(* GOOD *)
Function[{x, y, z},
	x + (y^z - x)/x
][1, 2, 3]
```

### Don't nest pure functions

Nested `&` functions are a notorious source of precedence bugs and are
hard to read after the fact. Lift the inner one out into a named helper
or a `Function[var, ...]`.

```wolfram
(* BAD: which # belongs to which &? *)
(# + 1 & /@ #^2) &[Range[4]]

(* GOOD *)
addOne[ex_] := ex + 1
(addOne /@ Sqrt[#]) &[Range[4]]
```

## Composition

### `@` chain for unary right-application

For chains of unary calls, prefer `f @ g @ h[x]` over `f[g[h[x]]]`. Less
bracket nesting, reads top-down. Use `[]` only where you need multiple
args.

```wolfram
(* GOOD *)
DeleteDuplicates @ Catenate @ Map[fn, xs]

(* BAD: ceremonial nesting *)
DeleteDuplicates[Catenate[Map[fn, xs]]]
```

Reserve `@` for a single symbol head applied to a single argument (or a
chain of them). Never apply `@` to a parenthesized compound expression
- `f@(multipleBitsOfCode)` is hard to read and invites precedence
surprises. Use full `f[...]` application there.

```wolfram
(* BAD: never do this *)
f@(multipleBitsOfCode)

(* GOOD *)
f[multipleBitsOfCode]
```

### `Lookup` is vectorized; prefer it over `Map[Lookup, ...]`

`Lookup[assoc, listOfKeys, default]` looks up every key at once and
returns the values in the order of the keys, so mapping it is redundant.

```wolfram
labels = <|"a" -> "start", "b" -> "end"|>;

(* BAD *)
Map[Lookup[labels, #, ""] &, {"a", "b", "z"}]

(* GOOD *)
Lookup[labels, {"a", "b", "z"}, ""]

(* both give {"start", "end", ""} *)
```

### Don't name single-use intermediates

If a value is read exactly once, inline it. Exception: name it when the
expression is long enough that the named form reads better, or when the
name carries domain meaning the inline expression doesn't.

### No postfix `//`

Postfix application reads fine in casual scratch work but is confusing
in committed code and carries surprising precedence. Use prefix or full
application.

```wolfram
(* BAD *)
codeToEvaluate // fnc

(* GOOD *)
fnc[codeToEvaluate]
```

### No infix `~f~` for prefix functions

`{a} ~Join~ {b}` evaluates correctly but makes precedence hard to
track. Write the ordinary prefix call.

```wolfram
(* BAD *)
{a} ~Join~ {b}

(* GOOD *)
Join[{a}, {b}]
```

### Parenthesize where precedence is ambiguous

When the reader (or you) would have to recall the precedence table, add
parentheses. This is especially important around `PatternTest` (`?`),
where `a_?f[x]` is genuinely ambiguous:

```wolfram
(* unclear: is the test f, or f[x]? *)
a_?f[x]

(* spell out what you mean *)
a_?(f[x])    (* PatternTest against f[x] *)
(a_?f)[x]    (* a pattern a_?f, applied to [x] *)
```

Naming a pattern inside `Alternatives` is another precedence trap: the `:`
binds more loosely than `|`, so the name captures the whole alternation
only with explicit grouping.

```wolfram
a : {__} | b : {{_, _}..}        (* head is Optional - probably not intended *)
(a : {__}) | (b : {{_, _}..})    (* head is Alternatives - intended *)
```

`Repeated` (`..`) next to a literal `0` misparses, because `0.` is itself
a valid number. Group the operand:

```wolfram
(* BAD: reads 0. then a stray . *)
0..

(* GOOD *)
(0)..
```

### Modularize repeated computation

When the same sub-expression appears in several definitions, factor it
into a well-named helper. The logic flows more clearly and a later change
happens in one place instead of many.

```wolfram
(* BAD: the quadratic formula is copied into each definition *)
fnc1[a_, b_, c_] := (-b + Sqrt[b^2 - 4 a c])/(2 a)
fnc2[d_, e_, f_, x_] := x - (-e + Sqrt[e^2 - 4 d f])/(2 d)

(* GOOD: one helper, reused *)
quadraticRoot[a_, b_, c_] := (-b + Sqrt[b^2 - 4 a c])/(2 a)

fnc1[a_, b_, c_] := quadraticRoot[a, b, c]
fnc2[d_, e_, f_, x_] := x - quadraticRoot[d, e, f]
```

## Data structures

When a function takes a data structure of a particular shape, describe
that shape explicitly - in the usage message, or in a comment / text
cell just before the code. A later developer should not have to infer
the structure from the implementation.

## Paclet structure (StructuredPackageFormat)

New paclets use the **StructuredPackageFormat** (new in Mathematica 15;
installable in 12.1+). It is built on four ``` System` ``` directives:
`PackageInitialize`, `PackageExported`, `PackageScoped`, `PackageImport`.

The paclet then is organized around a single context
for the entire paclet (e.g. `` Author`MyPaclet` ``).  Loading this loads
all of the code in the paclet and there is no need for any sub-contexts.

### Layout

The structured paclet format comprises a single file containing the
PackageInitialize call for the paclet's context and any number of
additional .wl files containing the paclet's codebase. These .wl files can
exist in a directory structure that is at most 3 levels deep. Often one
only goes a one or two  levels deeper than the top level file containing
the PackageInitialize call. Those one-level directories will typically
be named according to specific  topic or conceptual areas, thus providing
clear organization to the  intent of the codebase.

```
MyPaclet/
  PacletInfo.wl
  Kernel/
    MyPaclet.wl              umbrella: PackageInitialize[...] defines the paclet's Context
    TopicArea1/
      TopicArea1Subtopic1.wl             feature file: PackageExported[...] declarations
      TopicArea1Subtopic2.wl             feature file: PackageExported[...] declarations
    TopicArea2/
      TopicArea2Subtopic1.wl             feature file: PackageExported[...] declarations
      TopicArea2Subtopic2.wl             feature file: PackageExported[...] declarations
  Tests/
    Core/
      Widgets.wlt            tests mirror the Kernel layout
  Documentation/English/
```

The call to `PackageInitialize`  collects all `PackageExported`
/ `PackageScoped` symbols into the paclet's context. Feature
files are anonymous contributors; the split is for human
organization. (PackageInitialize only reaches into its own directory and
into directories up to 3 levels deep for code files to process.)

### PacletInfo.wl

```wolfram
PacletObject[<|
	"Name" -> "Author/MyPaclet",
	"PublisherID" -> "Author",
	"Version" -> "1.0.0",
	"WolframVersion" -> "15.0+",
	"PrimaryContext" -> "Author`MyPaclet`",
	"Extensions" -> {
		{
			"Kernel",
			"Root" -> "Kernel",
			(* The umbrella plus one {context, file} pair per component. *)
			"Context" -> {
				{"Author`MyPaclet`"}
			}
		},
		{"Documentation", "Root" -> "Documentation", "Language" -> "English"},
		{"Test", "Root" -> "Tests", "Method" -> "Experimental-v1"}
	}
|>]
```

**Loading and `"Symbols"`.** By default a paclet's `"Loading"`
is `Manual`: it loads only on explicit `Needs`/`Get`. To make it
*autoload* (load on first use of a symbol, no explicit `Needs`), set
`"Loading" -> Automatic` on the Kernel extension and list the trigger
symbols in `"Symbols"`. Crucially, **`"Symbols"` does nothing unless
`"Loading" -> Automatic` is also set** - the PacletManager only turns
`"Symbols"` into autoload triggers under the `Automatic` branch. So a bare
`"Symbols"` list with default (manual) loading has no effect; either add
`"Loading" -> Automatic` or just `Needs` the paclet. (The example above
uses manual loading and omits `"Symbols"`.)

### The umbrella loader

The umbrella is a **single-file** StructuredPackageFormat package
containing a call to `PackageInitialize`: it defines the paclet-wide
symbols. `` Needs["Author`MyPaclet`"] `` then loads the full codebase.

### The component loader

If you enable autoload (`"Loading" -> Automatic` plus a `"Symbols"`
list) for a component, its `PackageInitialize` call also needs
`"SymbolsToProtect" -> Automatic`, which clears the autoload *stub*
definitions before the real ones are read. Without it the stubs shadow
the real defs and the symbols load with no down-values - a sharp edge
to check if symbols load but "don't work". With plain manual loading (no
`"Symbols"`), no `SymbolsToProtect` is needed.

### Feature files

A feature file is just declarations plus definitions. It declares its
public symbols with `PackageExported`, its cross-file internals with
`PackageScoped`, and the other contexts it uses with `PackageImport`;
everything else is automatically private to the file:

```wolfram
(* Author`MyPaclet` :: Core :: Widgets *)

PackageExported[MakeWidget]        (* public: lands in the component context *)
PackageScoped[widgetHelper]        (* shared across the component's files, not public *)
PackageImport["GeneralUtilities`"] (* import another paclet/context *)

MakeWidget::usage = "MakeWidget[spec] builds a widget from spec."
MakeWidget[spec_] := Enclose[buildFrom @ ConfirmBy[spec, AssociationQ, "MakeWidget expects an association."]]
```

- `PackageExported[sym]` - public symbol.
- `PackageScoped[sym]` - shared across the paclets's files but not exported.
- `` PackageImport["Other`Context`"] `` - bring in another paclet/context;
  can import specific names with `` PackageImport["Ctx`", {sym1, sym2}] ``.
  The ``"Other`Context`"`` symbols are only available within the .wl file 
  within which PackageImport is called.
- To provide access to an external context to the full paclet make use of 
  the second argument to `PackageInitialize` in the loader file. 
- Any symbol you neither export nor scope is automatically private to its
  file.

Put `PackageExported`/`PackageScoped` declarations and usage messages
near the top of the file, then the definitions.

### Referencing symbols: load the context, don't qualify

Don't write fully-qualified `` Author`MyPaclet`MakeWidget `` in code or
tests. `Needs` the context you want (which puts it on `$ContextPath`)
and use the short name; load contexts explicitly rather than reaching
across them by full path.

```wolfram
Needs["Author`MyPaclet`"]
MakeWidget[<|"kind" -> "button"|>]
```

The exception is a `PackageScoped` symbol. Its context,
`` WolframInstitute`PureMath`PackageScope` ``, is not an importable package (#116):
offering scoped names for import is not how StructuredPackageFormat is meant to be
used. Code outside the paclet, tests included, calls a scoped symbol by its full name,
`` WolframInstitute`PureMath`PackageScope`gapSession[] ``.

## Tests

Use `VerificationTest`. Test specs live in `.wlt` files mirroring the
`Kernel` directory layout, run via `TestReport`.

```wolfram
VerificationTest[
	expression,
	expectedOutput,
	TestID -> "human-readable id"
]
```

Test the scope boundary, and test its two outcomes *distinctly*. Input
the function does not match is **returned unevaluated** - assert its head
is intact:

```wolfram
VerificationTest[
	Head @ safeInverse[5],
	safeInverse,
	TestID -> "safeInverse-nonmatching-left-unevaluated"
]
```

An evaluation that started and could not finish returns a `Failure`
(see *Invalid input and failure*) - assert that with `FailureQ`:

```wolfram
VerificationTest[
	FailureQ @ safeInverse[{{1, 1}, {1, 1}}],
	True,
	TestID -> "safeInverse-singular-returns-Failure"
]
```

Don't put `Print` inside test bodies; the runner reports
outcomes via `TestReport`. Make a `.wlt` runnable standalone by
`PacletDirectoryLoad[Directory[]]` at the top (run tests from a
directory the paclet sits under), then `Needs` the context under
test. (`Directory[]`, the working directory, is set during `TestReport`;
`$InputFileName` is not, so don't rely on it in a `.wlt`.)

Run the whole suite from the shell with a `.wls` runner
(e.g. `scripts/run_tests.wls`) that loops over the `.wlt` files, reports
each via `TestReport`, prints a stdout summary, and exits non-zero if
anything failed (so it drops into CI).

## Documentation

Usage messages and comments serve developers, and a usage message also
gives a user of the function its quick description - and gives a language
model working with the paclet its notion of the function's role and scope. 
Every exported function additionally needs user-visible documentation.

We **author documentation as literate markdown** and build the notebooks
with **PacletPage** (https://github.com/WolframInstitute/PacletPage, through
`scripts/docs.wls build`), rather than hand-editing notebook cells in the
DocumentationTools palette. The author writes YAML frontmatter and
`## section` headings in a `.md` file; the converter chooses every cell style
and fills the official authoring/definition notebook. Two authoring skills are available now (they
live in `.agent-skills/`, alongside the code skill below):

### Usage messages

Write a usage message for every function and parameter, public or not,
and write it *early* - often before the implementation, since drafting it
forces you to settle the argument forms and output shape. The temptation
to "write the usage message later" reliably produces missing or poor
messages. Keep messages in sync with the patterns as the code evolves;
the usage message is part of the code.

Format (this is what gives you Complete Selection and template insertion
for free): the template for each argument form starts the line, followed
by a short description; one form per line.

```wolfram
(* GOOD *)
foo::usage = "foo[string] gives the length of the string.\n\
foo[integer] gives the number of digits in the integer.\n\
foo[{integer1, integer2, ...}] gives a list of the number of digits in each.";

(* BAD *)
foo::usage = "" (* empty string *)
foo::usage = "foo" (* no message *)
foo::usage = "foo[string]"` (* no message *)
foo::usage = "gives the length of the string" (* no template at the start *)
```

If the function takes options, describe them briefly in the usage message.

You can use ```GeneralUtilities`SetUsage``` to format usage messages
consistently with built-in symbols (```Needs["GeneralUtilities`"]```). Note
the new structured package format will offer additional ways to
do this. This would be enabled by using the second argument to the
PackageInitialize function that the structured package format uses to
declare the paclet's Context.

### Comments

Wolfram code reads as a vertical narrative, so too many inline comments
between lines disrupt it (unlike languages where comments sit off to the
right). Prefer:

- A `Text`-style cell (in a notebook) or a comment block *before* a
  function's definition, describing what it does.
- A short comment at a genuinely subtle point in the code, to alert the
  next developer before they change it.
- Comment non-obvious behavior, quirks, or external format constraints
  (LibraryLink calling conventions, paclet layout expectations, etc.).
- Don't narrate obvious code. Prefer one short section comment over many
  tiny inline comments.
- Put spaces around the text inside a comment: `(* note *)`, not
  `(*note*)`.

**Example cells live only as long as the built page keeps them.** A page's `wl`
cells evaluate in one kernel in document order, but the built page resets that
state as it goes: a `---` thematic break and *any* heading are reset boundaries,
and **every boundary clears every binding the page has made**. The one thing the
converter protects is a *setup section* - a heading reading exactly `Definition`,
`Content` or `Initialization` - whose bindings survive once that section ends. A
house-style symbol page has no such section, so on it **nothing carries across a
heading or a `---`**: not a binding made under `## Basic Examples`, not anything.
(An earlier converter armed a protection snapshot at the first canonical example
heading and kept Basic-Examples bindings for the whole page; the converter's
release of 2026-09-02 replaced that rule, and 729 pages written to it shipped
cells that echoed their own input.) On a house-style symbol page that comes to
three authoring rules:

## Theme-aware colors in visual output

Always design WL output for both light and dark Wolfram themes from
the start. This applies wherever code emits visual output: a symbol's
own formatting (`MakeBoxes`) and graphics in kernel code, and the `wl`
example cells in the docs alike.

- Use **Standard color names** (`StandardBlue`, `StandardRed`,
  `StandardGreen`, `StandardOrange`, `StandardYellow`,
  `StandardPurple`, `StandardGray`) instead of `RGBColor[...]` or
  `Darker[Blue, 0.4]`. They read correctly on light and dark
  backgrounds. A curated multi-hue palette may use explicit colors,
  but verify each color works and reads well on both backgrounds.
- Use `LightDarkSwitched[lightValue, darkValue]` when a value
  (color, opacity, thickness) genuinely needs to differ between
  modes. Avoid hard-coded `White`/`Black` for `Background`,
  `FaceForm`, etc.; either let the theme drive it, or wrap in
  `LightDarkSwitched`.
- Don't unconditionally pin `Background -> White` on a Graph or
  Graphics. If a static PNG export needs an explicit background,
  set it on the Export call, not on the Graph.

Math in doc prose renders through `LaTeXMathParse` of the **`Wolfram/Parser`
paclet**, which handles standard LaTeX well (`\mathbb`, `\mathfrak`, `\sqrt`,
scripts, fractions - and Unicode letters like `ℚ ℤ ℝ` equally well). Two
authoring rules: **backslash Greek letters** (a bare `alpha_1` renders
letter-by-letter), and leave **no stray backslash before a Unicode letter**
(`$\ℚ$` renders the backslash visibly - the scar of a botched `\mathbb{Q}` ->
`ℚ` rewrite; write `$ℚ$`). Both `ℚ ℤ ℝ ℂ ℕ 𝔽` and `\mathbb{...}` render, and
the repo is written in Unicode - house style, not a rendering fix. The
converter silently degrades to a weak TeX fallback when
that paclet is missing, so the build loads it from the clone `scripts/fetch_deps.sh` makes.
**`\mathfrak` takes a single letter only.** It returns one box per glyph, so a
two-or-more-letter name inside it sets spaced - "𝔰 𝔲 (3)" rather than 𝔰𝔲(3).
Write those as raw Unicode fraktur inside `\mathrm{...}` - `$\mathrm{𝔰𝔲}(3)$`,
`$\mathrm{𝔰𝔬}(10)$`, `$\mathrm{𝔤𝔩}(d)$` - which passes the argument through as
one `StyleBox` and closes the gaps; bare Unicode fraktur outside `\mathrm` is
worse still (the parser splits it at the surrogate halves). A single letter is
already one box, so `$\mathfrak{g}$`, `$\mathfrak{e}_8$` stay as they are.
Bare `v_1` / `v1` / camelCase argument names still show as literal text instead
of a subscript or clean argument. Details and probe evidence:
[docs/notes/doc-math-rendering.md](docs/notes/doc-math-rendering.md) and
[docs/notes/doc-arg-naming.md](docs/notes/doc-arg-naming.md).

**A word never sits raw in inline math.** `$topology$` is a product of eight
italic letters, so the built page reads *t o p o l o g y*, not the word. Two
forms replace it. An **argument placeholder** takes the markdown italic form -
`*rule*`, `*point*`, `*cond*` - in the usage signature, in Details bullets and
in prose alike, so one name looks the same everywhere it appears; a span made of
nothing but names leaves math altogether, `(*pts*, *blocks*)` rather than
`$(pts, blocks)$`. A **word inside a real formula** - an operator name, a label
in a script, a unit, an argument name an equation genuinely needs - is wrapped
in `\text{...}`, or written with the macro that already exists for it (`\max`,
`\gcd`, `\deg`, `\mathrm{d}x`): `$\text{point} - \text{rate} \cdot \nabla f$`,
`$\{x \in ℝ : \text{cond}\}$`, `$n_{\text{kmax}}$`. Upright is right there -
it is how a multi-letter identifier is set in mathematics, and it keeps the name
distinct from the single-letter variables around it.

Two argument spellings stay in math, because the italic form cannot carry them:
a **subscripted** name (`$v_1$`, `$struct_1$` - a literal underscore inside
`*...*` leaks onto the page as text) and a **Greek** name (`$α_1$` in a
signature, `$\alpha_1$` in prose). A subscripted name whose base is a *word*
needs one more step in prose: `$struct_1$` is a word raw in math like any other,
so it sets as *s t r u c t*₁ there. Give the base a macro - `$\mathit{struct}_1$`
(italic, matching how the same name sets in the signature) or `$\text{cond}_i$`
where upright is wanted. In the signature itself `$struct_1$` is already correct
and must stay bare, for the reason in the next paragraph. Three things that look
like words are not:
a run of index letters (`$R_{abcd}$`), a word over an alphabet (`$abab$` in a
rewriting system), and a single letter - all three are mathematics and stay as
they are. A word that is really a symbol name is neither placeholder nor prose:
link it as <code>[Ideal]()</code>, or set it as `` `PrimeIdeal` ``.

`scripts/lint_docs.wls` **enforces** this rule, in prose math and in a signature
slot alike, so a word left in math fails CI instead of shipping. It reads a word
as three or more letters in a row that are lowercase after the first, which is
what separates a word from the juxtaposed symbols around it: `$ab$`, `$dx$`,
`$xy$` and `$BC$` are products and `$NkT$`, `$gMr$`, `$hZZ$` and `$SU$` are
symbol runs, so none of them fires. Silent as well are math already wrapped
(`\text{...}`, `\mathit{...}`, `\mathrm{...}`, `\operatorname{...}`), a single
letter, Greek in either spelling, the base of a subscripted name (`$struct_1$`),
a fenced block and an inline code span. The genuine multi-letter cases - the
index runs (`$R_{abcd}$`, `$f_{ijk}$`, `$R^r{}_{smn}$`), the words over an
alphabet (`$abab$`), the monomials (`$xyz$`, `$e^{ikx}$`) - are named one by one
in `mathWordAllowlist` in that script, grouped by the mathematics they are. A
new one is welcome there with a comment saying which mathematics it is; a run
that has no such reason is the defect the rule is looking for. The prose/slot
asymmetry carries into scripts, matching the paragraph below: a slot's plain
subscript stays bare (`$v_{min}$`), while in prose a word inside a script takes
its macro or its wrapper (`$q_{\max}$`, `$Z_{\text{Ising}}$`).

One place the wrapping rule reverses: **inside a `<code>` usage signature a
`$...$` is a template-argument slot, not a LaTeX span**, and any backslash macro
in it leaks onto the page as raw source - `$\text{rate}$`, `$q_{\max}$`,
`$\alpha$` and `$\dots$` all leak there, though every one of them renders in
prose. A signature therefore carries only markdown italic names (`*point*`,
`*eqn*`), plain subscripted names (`$v_1$`, `$v_{min}$`) and Unicode Greek
(`$α_1$`). Write the same quantity with `\text{...}` when it reappears in the
prose formula below the signature.

The slot understands a name and a plain subscript, and passes a Unicode letter
through; four further constructs need the same treatment as a macro. An
**ellipsis** is the bare character next to the slots, `{$x_1$, …}` - a `$…$`
leaks its dollars even with the character inside. A **superscript** takes the
Unicode digit, `$d⁰$`, `$d¹$`; where the exponent is an expression the formula
belongs in prose math beside the span (`dimensions $\{2^n\}$`, not
`<code>{$2^n$}</code>`), which is also where a `+ m^2 φ` term goes when a
signature would otherwise carry arithmetic. That digit does not compose with a
subscript - a slot carries one script only, so `$m_0^2$` has no slot spelling at
all: name the argument `$m_0$` and let the prose say the arguments are squared
masses. A **subscript that is an
expression** sets its operator outside the script, so `$a_{k-1}$` reads as
*a*ₖ − 1; index the list plainly in the signature (`{$a_0$, $a_1$, …}`) and let
the prose state the bound. **Two tokens in one slot** leak as well - a product
is `$a$ $b$` and a difference `$r$ - 1`, each name in a slot of its own.
`scripts/lint_docs.wls` fails on every one of these inside a `<code>` span, so
none of them ships.

**Escape context backticks inside `<code>`**: write
`` <code>Needs["WolframInstitute\`PureMath\`"]</code> ``, not the bare form. A
markdown renderer reads the unescaped backticks as a nested code span, so
`` Needs["WolframInstitute`PureMath`"] `` renders as `Needs["WolframInstitutePureMath"]`
on GitHub and the docs site - the context silently disappears. The docs build
gets it right either way (verified: both forms convert to the same notebook
string), so the built notebook never shows the bug and only the markdown view
does.

**Verify rendering, not source, for anything typographic.** The two rules
just above are both correct-in-source, wrong-on-delivery: a backtick inside a
single-backtick code span silently eats a context name, and a multi-letter
`\mathfrak` argument sets as spaced letters because the parser returns one
box per glyph. Neither is visible to a review of the markdown. Argument
subscripts and cell heights fail the same way. If a change is about how
something looks, build it and look at the built result.

Kernel code is authored with the **`implement-wolfram-functions`** skill
(guide page -> `PureMath/Kernel/<Category>/<Field>.wl` + tests); it reads this
style guide as its contract. `<Category>` is one of the 11 shared by the kernel,
test, guide and reference-page trees, and a kernel file takes the category of the
guide that chips its exported symbols. See CONTRIBUTING's "Architecture" for that
taxonomy and "Adding a field" for how the guide, implementation, and symbol-page
stages fit together as a pipeline.

Tutorials and tech notes are authored with the **`wolfram-tech-note`** skill
([.agent-skills/wolfram-tech-note/](.agent-skills/wolfram-tech-note/SKILL.md)) -
free-flowing prose interleaved with runnable examples, with this repo's
typography, output-showcasing, cheap-cell and verification rules folded in.

Planned, not yet built (do not assume these exist): **`wolfram-paclet`** (the
paclet's `ResourceDefinition.nb` for Paclet Repository submission), and the
sibling **`wolfram-function-resource`** / **`wolfram-example-repository`**
skills.

## Things to check from time to time

- Every localized symbol in a `Module`/`Block` is actually listed in its
  binding list (and used).
- Every function's usage message is up to date with its patterns.
- Every predicate (`...Q`) has a `[___] := False` fall-through **for ill-typed or
  out-of-scope input**. The exception: a predicate whose truth is genuinely
  *undecidable* for some otherwise-valid inputs guards its `False` on bad input
  only (e.g. `predQ[a_, b_] := False /; ! (validQ[a] && validQ[b])`) and leaves the
  undecidable cases **unevaluated** rather than answering `False` - as
  `CardinalLessEqualQ` does for ZFC-independent comparisons and
  `ConstructibleNumberQ` for numbers whose constructibility it cannot settle. A
  robust way to build such a predicate is to decide each direction only where it is
  *sound* (a clause that yields `True` only when provably true, a clause that
  yields `False` only when provably false) and let everything else stay symbolic.
  Other public functions deliberately have **no** catch-all clause - input matching
  no pattern returns unevaluated, never funneled into a `Failure`.
- No leftover internal/`Private` long-name references
  (`` SomeContext`Private`helper ``) or undocumented internal System functions
  (see *Avoid depending on `` System`Private` `` internals*).
- No `Return[...]` in a definition - restructure so the value falls out, or use
  `Catch`/`Throw` or `Enclose`/`Confirm` (see Bulletproofing).
