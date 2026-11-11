# Machine reals

The 64-bit reals of the compiler's typed code in the type theory: what the model is, what it assumes, what was
checked against the machine, and the plan for the second slice. The library is
`TypeTheory/Kernel/Library/MachineReals.wl`; the reading of typed code is in
`TypeTheory/Kernel/Elaboration/CompiledDefinitions.wl`.

## The model (0.40.0)

A machine real is a rational that binary64 represents, m 2^e with |m| < 2^53 and -1074 <= e <= 971. `"Real64"` is that
subtype of the rationals, so a machine real has an exact value, `x["rational"]`, and its order and equality are those
of its value. NaN and the infinities are no values: a typed entry leaves before it holds one, and the model's
operations give `A | Failure` with the leave as the failure. The sign of zero is not kept.

`TypeTheoryEnvironment["MachineReals"]` is the rationals with the declarations of `"Machine"` and the reals:
`"Machine"` stays on the integers, and `TypeTheoryFormalize[f, "Machine"]` takes the reals' environment where the
typed code of `f` has a real.

Each operation is the rounding of an exact rational result:

| Operation | Value | Leaves |
|---|---|---|
| `"real64Plus"`, `"real64Subtract"` | the result of the exact sum or difference | `"NotFinite"` past the largest real |
| `"real64Times"` | the result of the exact product | `"NotFinite"`; `"Underflow"` where the product is not 0 and its result is below 2^-1022 |
| `"real64Reciprocal"` | the result of 1/y; x / y is x times it, two roundings | those of a product; `"NotFinite"` by 0 |
| `"real64OfInteger"` | the result of an integer, taken before an operation with a real | none in the range of 64 bits |
| `"real64Floor"`, `"real64Ceiling"`, `"real64Round"`, `"real64IntegerPart"` | the machine integer of the whole number, `Round` half to even | `"IntegerOverflow"` from 9*10^18 on |
| `"real64Sqrt"` | the correctly rounded square root | `"Domain"` below 0 |
| an order of an integer and a real | the order of the two values | `"Range"` for an integer past 2^53 |
| `"real64EqualQ"` | the same, or apart by no more than 2^-46 of the larger | none |

## What is assumed

Three constants are axioms with an `"Implementation"`, which the Wolfram Language computes and the kernel never does:
`"real64Result"`, the rounding to the nearest real with ties to even; `"rationalFloor"`; and `"real64SqrtResult"`.
A fourth axiom is a proposition, `"real64ResultNearest"`, the specification of the rounding (below).
Everything else is a definition over a Boolean order of the rationals. A theorem about real code names the axioms
it uses in its closure: `"real64Plus"[x, y] == "real64Result"[x + y]` has
`<|"quotientSoundness" -> "Proposition", "real64Result" -> "Signature"|>`.

`NormalForm[term, "Implementations" -> True]` is a calculator. It replaces an implemented axiom applied to values by
the value the Wolfram Language computes, and what it gives is no proof: the kernel does not find the two sides equal
by computation, and refuses reflexivity as the proof of their equation (the test
"A-value-an-implementation-computed-is-no-proof").

## What was checked against the machine

`scripts/machine_real_checks.wl` runs 47 rows of real arithmetic as compiled code against the evaluator and compares
the results as text. On arm64 (macOS) and on x86-64 (Linux, a release build of the WolframKernel project with its
JIT on) the 47 rows give the same text. The rows cover each operation, each leave and the mixed integer and real
cases. They test that the model reads the code as the machine runs it; they are no proof of the arithmetic, which
rests on the three axioms.

## The second slice

The slice is in two parts. The first is in the library: the specification of the rounding as an axiom, the two
theorems of commutativity, the implementation by integers, and the Boolean of nearness with its grid. The second is
to come: the order of the rationals as far as the proofs need it, the spacing of the machine reals, the three
properties of the rounding and the lemma that turns the Boolean into an equation.

### Theorems with content

`"real64PlusCommutativity"`, `"real64Plus"[x, y] == "real64Plus"[y, x]`, and `"real64TimesCommutativity"`, the same
for `"real64Times"`, each by the commutativity of the rationals under the rounding. They use the rounding only as a
function, so their closure is that of the theorem above,
`<|"quotientSoundness" -> "Proposition", "real64Result" -> "Signature"|>`, and they are the first statements about
real code that are not true by unfolding.

### The properties of the rounding

Three properties are wanted, each a statement over the rationals:

- **Identity on the representable.** If q is representable, the rounding of q is q.
- **Monotone.** If q <= q' and both roundings are values, the rounding of q is at most that of q'.
- **The half-ulp bound.** The rounding of q is within half a unit in the last place of q: |r - q| <= 2^(e - 1) for
  the exponent e of r, and at most 2^-1075 in the subnormal range.

They follow from one further axiom, not three: the specification of the rounding. With B = 2^1024 - 2^970, the middle
of the largest real and 2^1024:

```wl
TypeTheoryAxiom["real64ResultNearest",
	ForAll[{Typed[q, Rationals]},
		And[
			Implies[Typed[B, Rationals] <= "rationalAbsolute"[q],
				"real64Result"[q] == Typed["right"[Failure["NotFinite", <||>]], "Real64" | Failure]],
			Implies["rationalAbsolute"[q] < Typed[B, Rationals],
				Exists[{Typed[r, "Real64"]},
					And[
						"real64Result"[q] == Typed["left"[r], "Real64" | Failure],
						And[
							ForAll[{Typed[s, "Real64"]},
								"rationalAbsolute"[q - r[["rational"]]] <= "rationalAbsolute"[q - s[["rational"]]]],
							ForAll[{Typed[s, "Real64"]},
								Implies[s[["rational"]] != r[["rational"]],
									Implies["rationalAbsolute"[q - s[["rational"]]] == "rationalAbsolute"[q - r[["rational"]]],
										Exists[{Typed[n, Integers]},
											r[["rational"]] == 2 "rationalOfInteger"[n] (s[["rational"]] - r[["rational"]])]]]]
						]
					]
				]
			]
		]
	]
]
```

In words: from B on, the leave; below B, a machine real r that no machine real is nearer to q than, and where another
machine real s is as near, r is an even multiple of their distance. The tie clause says "even" without a significand:
m 2^e is not unique, 2 being 1 * 2^1 and 2 * 2^0, but two machine reals as near to q as each other are neighbours, and
neighbours are consecutive multiples of their distance. A theorem that uses the axiom has it in its closure, kind
`"Proposition"`.

Such a function exists and is the only one:

1. The machine reals are finitely many, |m| < 2^53 with two bounded exponents, so some r is nearest to q, and at
   most two are, one on each side of q.
2. Two that are nearest, r < s, have no machine real between them, and then r = j u and s = (j + 1) u for u = s - r:
   within a binade both are multiples of its spacing u, and at a binade's upper end 2^k the spacing below is u and
   2^k is 2^53 u. Exactly one of j and j + 1 is even, so exactly one of the two satisfies the tie clause.
3. From B on the first clause gives the leave and the second says nothing; below B it is the other way round. The
   function is the roundTiesToEven of IEEE 754 with the leave for its infinities: IEEE overflows from B on, the
   tie at B going to the infinity because 2^1024 would be the even neighbour.

The cases where a statement of "even" could go wrong, checked by hand against the tie clause and each a row of the
grid test below, u being the spacing at the tie:

| q, an exact tie | The two nearest | r / (s - r) for each | The rounding |
|---|---|---|---|
| 2^-1075 | 0 and 2^-1074 | 0 and -1 | 0 |
| 3 * 2^-1075 | 2^-1074 and 2 * 2^-1074 | 1 and -2 | 2 * 2^-1074 |
| (2^53 - 1/2) u, below a power of two | (2^53 - 1) u and 2^53 u | 2^53 - 1 and -2^53 | 2^53 u |
| (2^53 + 1) u, above it, where the spacing is 2u | 2^53 u and 2^53 u + 2u | 2^52 and -(2^52 + 1) | 2^53 u |
| 2^53 + 1 | 2^53 and 2^53 + 2 | 2^52 and -(2^52 + 1) | 2^53 |
| the negatives of these | the negatives | the same | the negatives |
| 2^1024 - 2^970 | no tie: from here on the leave | | the leave |
| 2^1024 - 2^970 less any positive amount | the largest real, 2^1024 - 2^971, alone | | the largest real |

The three properties are then theorems, by arithmetic of the rationals and this uniqueness; they are the second
part of the slice, and need more of the order of the rationals than the library has, which proves it reflexive and
no more.

### The Boolean of nearness

The same specification gives certified values. `"real64NearestQ"[q, m, a, b]` is a Boolean that the kernel computes
for literals: whether the machine real m 2^a / 2^b is the rounding of the rational q. It asks that

- the real is in the range of a machine real, |m| < 2^53, a <= 971 and b <= 1074, and in its form of the largest m:
  |m| >= 2^52, or the exponent is the lowest, a = 0 and b = 1074. That form fixes the spacing: above |r| it is
  u = 2^a / 2^b, and below |r| it is u, or u / 2 where |m| = 2^52 and the exponent is not the lowest;
- q is within half the spacing of r on each side;
- where q is exactly half way, m is even. An odd m takes q strictly within half, and at |m| = 2^52 the half-way
  point toward 0 goes to r, 2^53 half-spacings being even.

The largest real has an odd m, so the check refuses 2^1024 - 2^970 for it, and with it everything from the bound on.
A lemma is to turn the check into `"real64Result"[q] == r`, the second part of the slice. Its proof needs one fact
about the predicate, the spacing of the machine reals around m 2^e in that form, proved once. A value the Wolfram
Language computed then enters a proof once the kernel has checked its certificate, where today it cannot enter one
at all.

The `"Implementation"` of the rounding is trusted for nothing. It computes by exact integer arithmetic, the
exponent from the bit lengths of the numerator and the denominator and the significand by an integer quotient with
its remainder compared to a half, and not by `N` of a rational. Whatever it computes, a wrong value only fails to
certify: the kernel's nearness check refuses it, and no equation comes of it.

`scripts/real64_nearest_grid.wl` holds the check itself to the machine, on 453 rows: the ties and bounds of the table
above and their negatives; 60 products, 60 sums and 40 reciprocals of machine reals, whose exact results IEEE 754
has the machine round to the nearest, the value expected being the machine's own; 40 exact ties (2 m + 1) 2^e, the
sum of two neighbouring reals; 20 ties among the subnormal reals; and 200 rationals whose numerator and denominator
are past 2^64. On every row the value the integers give is the one expected, the check accepts it, and the check
refuses the machine real next to it on each side; from the bound on the check refuses the largest real. The rows
come from a generator written out in the script, the same on every kernel. Run on Wolfram 15.0 and on the
WolframKernel project's kernel (cb26279f), arm64: no row fails on either.

`N` is not what the grid measures against, and for a reason it found. On Wolfram 15.0, `N` of a rational whose
numerator and denominator are past 2^64 is not the nearest machine real for a third of them: of 2000, a last place
off for 663 and two for 7. The WolframKernel project's `N` gives the nearest for all 2000, and `N` of an integer is
the nearest on both.

The alternative, defining the rounding by its algorithm and proving the specification, removes the axiom and is the
later stage: it needs the floor defined from the integers' quotient, which needs laws of `Quotient` the integers'
library does not have yet, and a search for the exponent. The specification axiom states exactly what that stage
would prove, so the theorems above it do not change when the axiom becomes a theorem.

`"rationalFloor"` and `"real64SqrtResult"` stay axioms in this slice. The square root gets the same kind of
specification when a theorem needs it: r >= 0 representable with no representable nearer to the root, stated by
squares.

### Power and the functions of the mathematical library

The model fixes a value only where every conforming machine computes the same value:

| Functions | What the model states | On what evidence |
|---|---|---|
| sum, difference, product, reciprocal, square root, the conversions and the whole-number functions | the value | IEEE 754 requires correct rounding; the 47 rows on two platforms |
| `Power` with an integer exponent | no value yet, only its leaves | typed code computes it by the compiler's built-in power, a chain of products in the order of the exponent's binary digits; Wolfram 15's own power is another rule, a last place off the chain at 6, 7, 10 and 15 on some bases and further at 1000. The WolframKernel project is to put its evaluator and typed code on Wolfram 15's rule; the model takes the rule from it then. The rows of `scripts/machine_real_checks.wl`, a variable and a constant exponent each, are the regression test, and whatever value the model gives will be tied to that kernel's C compiler and runtime library |
| `Exp`, `Log`, `Sin`, `Cos`, `Tan`, `ArcTan`, `Power` with a real exponent, and the rest of the library | no value: a constant per function with its domain and its leaves, and nothing about its last bit | these are not correctly rounded, and two libraries may differ in the last place; one witness per function, a point where arm64 and x86-64 differ, is to be found by a grid run on both |

A function of the last row is an axiom whose `"Implementation"` is the library of the machine it runs on, so a
normal form computed with it is not portable; the lemma that certifies a value covers the rounding and the square
root only. `NormalForm` with
implementations computes with it and the result holds for this machine; a theorem that mentions the function says
so in its closure, by the function's name, and can use nothing about it but that it is a function. A bound in units
of the last place against the exact function is not stated: the library has no real analysis to state the exact
function in.
