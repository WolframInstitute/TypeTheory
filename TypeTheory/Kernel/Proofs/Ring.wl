(* ::Package:: *)

(*
Ring: proofs of equations of natural numbers that hold in every commutative semiring.

A term of natural numbers is normalized to a polynomial in its atoms, the subterms that are not sums,
products, powers by a literal or literals. The normal form comes with a proof that the term equals
it, built from the prelude's laws of addition and multiplication, as Mathlib's ring builds its proofs:
congruence carries the proofs of the parts to the whole, and a sum or product of normal forms is put
in order step by step, by associativity and commutativity, its like terms combined by distributivity
and the laws of powers. Two terms with the same normal form are equal, by the two proofs. Nothing here
is trusted: the kernel checks the proof, so a mistake makes it fail to check.

	monomial      {c, {{atom, e}, ...}}, a coefficient c >= 1 and the atoms in canonical order, each
	              with an exponent e >= 1
	polynomial    a list of monomials in canonical order, none two with the same atoms; {} is 0
	equation      {left, right, proof}, proof a core term of type left == right

A polynomial's term is the right-nested sum of its monomials' terms, and a monomial's term the
right-nested product c * x^e * ..., without the coefficient when it is 1 and the exponent when it is 1.
An equation whose sides are equal by computation, as 2 + 3 and 5, has a proof by reflexivity, which the
kernel checks where the equation is used.
*)


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[ringNormalForm]
PackageScoped[ringEquationProof]


(* ::Section:: *)
(*Usage Messages*)


ringNormalForm::usage = "ringNormalForm[term] gives {polynomial, {term, normal, proof}} for a core term of natural numbers: its normal form as a polynomial in its atoms, \
the term normal of that polynomial, and a proof of term == normal from the laws of the prelude."
ringEquationProof::usage = "ringEquationProof[left, right] gives a proof of left == right for core terms of natural numbers with the same normal form, or None."


(* ::Section:: *)
(*Function Definitions*)


ringEquationProof[left_, right_] := With[{leftForm = ringNormalForm[left], rightForm = ringNormalForm[right]},
	If[ First[leftForm] === First[rightForm],
		Last @ transitive[Last[leftForm], symmetric[Last[rightForm]]],
		None
	]
]


(* ::Subsection:: *)
(*Terms*)


$naturals = constantReference[HoldComplete[NonNegativeIntegers], {}]

literal[n_Integer] := naturalLiteral[n]
plus[a_, b_] := application[application[constantReference[HoldComplete[Plus], {}], a], b]
times[a_, b_] := application[application[constantReference[HoldComplete[Times], {}], a], b]
power[a_, b_] := application[application[constantReference[HoldComplete[Power], {}], a], b]

factorTerm[{atom_, 1}] := atom
factorTerm[{atom_, exponent_Integer}] := power[atom, literal[exponent]]

productTerm[{factor_}] := factorTerm[factor]
productTerm[{factor_, rest__}] := times[factorTerm[factor], productTerm[{rest}]]

monomialTerm[{coefficient_Integer, {}}] := literal[coefficient]
monomialTerm[{1, factors_List}] := productTerm[factors]
monomialTerm[{coefficient_Integer, factors_List}] := times[literal[coefficient], productTerm[factors]]

polynomialTerm[{}] := literal[0]
polynomialTerm[{monomial_}] := monomialTerm[monomial]
polynomialTerm[{monomial_, rest__}] := plus[monomialTerm[monomial], polynomialTerm[{rest}]]

(* the canonical order of expressions orders the atoms, and the lists of factors of the monomials *)
atomBeforeQ[a_, b_] := Order[a, b] === 1
monomialBeforeQ[{_, factors_}, {_, otherFactors_}] := Order[factors, otherFactors] === 1


(* ::Subsection:: *)
(*Equations*)


reflexivityProof[term_] := makeApplication[constantReference[HoldComplete[EqualityReflexivity], {1}], {$naturals, term}]

reflexivityProofQ[proof_] := MatchQ[proof, application[application[constantReference[HoldComplete[EqualityReflexivity], _], _], _]]

reflexive[term_] := {term, term, reflexivityProof[term]}

(* left and right are equal by computation *)
computed[left_, right_] := {left, right, reflexivityProof[right]}

symmetric[{left_, right_, proof_}] /; reflexivityProofQ[proof] := computed[right, left]
symmetric[{left_, right_, proof_}] := {right, left, makeApplication[constantReference[HoldComplete[EqualitySymmetry], {1}], {$naturals, left, right, proof}]}

(* a step by reflexivity is left out: the kernel checks the computation where the other proof is used *)
transitive[{left_, _, proof_}, {_, right_, otherProof_}] /; reflexivityProofQ[proof] := {left, right, otherProof}
transitive[{left_, _, proof_}, {_, right_, otherProof_}] /; reflexivityProofQ[otherProof] := {left, right, proof}
transitive[{left_, middle_, proof_}, {_, right_, otherProof_}] :=
	{left, right, makeApplication[constantReference[HoldComplete[EqualityTransitivity], {1}], {$naturals, left, middle, right, proof, otherProof}]}

chain[first_, rest___] := Fold[transitive, first, {rest}]

(* context[left] == context[right], for a context of one hole, a function of terms that puts no binder
   around the hole *)
congruent[context_, {left_, right_, proof_}] /; reflexivityProofQ[proof] := computed[context[left], context[right]]
congruent[context_, {left_, right_, proof_}] := {
	context[left],
	context[right],
	makeApplication[
		constantReference[HoldComplete[EqualityCongruence], {1, 1}],
		{$naturals, $naturals, left, right, lambdaAbstraction[HoldComplete[x], $naturals, context[boundVariable[0]], "Explicit"], proof}
	]
}

(* operation[a, b] == operation[a', b'] from a == a' and b == b' *)
congruentBoth[operation_, first : {_, firstRight_, _}, second : {secondLeft_, _, _}] :=
	transitive[congruent[Function[hole, operation[hole, secondLeft]], first], congruent[Function[hole, operation[firstRight, hole]], second]]

law[name_, arguments_List, left_, right_] := {left, right, makeApplication[constantReference[HoldComplete[name], {}], arguments]}

additionAssociativity[a_, b_, c_] := law[AdditionAssociativity, {a, b, c}, plus[plus[a, b], c], plus[a, plus[b, c]]]
additionCommutativity[a_, b_] := law[AdditionCommutativity, {a, b}, plus[a, b], plus[b, a]]
additionZeroLeft[n_] := law[AdditionZeroLeft, {n}, plus[literal[0], n], n]
additionZeroRight[n_] := law[AdditionZeroRight, {n}, plus[n, literal[0]], n]
multiplicationAssociativity[a_, b_, c_] := law[MultiplicationAssociativity, {a, b, c}, times[times[a, b], c], times[a, times[b, c]]]
multiplicationCommutativity[a_, b_] := law[MultiplicationCommutativity, {a, b}, times[a, b], times[b, a]]
multiplicationZeroLeft[n_] := law[MultiplicationZeroLeft, {n}, times[literal[0], n], literal[0]]
multiplicationZeroRight[n_] := law[MultiplicationZeroRight, {n}, times[n, literal[0]], literal[0]]
multiplicationOneLeft[n_] := law[MultiplicationOneLeft, {n}, times[literal[1], n], n]
distributivityLeft[a_, b_, c_] := law[MultiplicationDistributivityLeft, {a, b, c}, times[a, plus[b, c]], plus[times[a, b], times[a, c]]]
distributivityRight[a_, b_, c_] := law[MultiplicationDistributivityRight, {a, b, c}, times[plus[a, b], c], plus[times[a, c], times[b, c]]]
powerZero[m_] := law[PowerZero, {m}, power[m, literal[0]], literal[1]]
powerOne[m_] := law[PowerOne, {m}, power[m, literal[1]], m]
powerSuccessor[m_, n_] := law[PowerSuccessor, {m, n}, power[m, plus[n, literal[1]]], times[power[m, n], m]]
powerAddition[m_, a_, b_] := law[PowerAddition, {m, a, b}, power[m, plus[a, b]], times[power[m, a], power[m, b]]]

(* x op (y op z) == y op (x op z), from associativity and commutativity *)
leftCommutativity[operation_, associativity_, commutativity_, x_, y_, z_] := chain[
	symmetric[associativity[x, y, z]],
	congruent[Function[hole, operation[hole, z]], commutativity[x, y]],
	associativity[y, x, z]
]


(* ::Subsection:: *)
(*Normal forms*)


(* a successor is a sum with 1, and NaturalNumberZero is 0, by computation; Subtract, which stops at 0,
   is no operation of a semiring, so a difference is an atom, and so is a power by a large exponent of
   anything but an atom *)
ringNormalForm[term_] := Replace[term, {
	naturalLiteral[0] :> {{}, reflexive[term]},
	naturalLiteral[n_Integer] :> {{{n, {}}}, reflexive[term]},
	constantReference[HoldComplete[NaturalNumberZero], _] :> {{}, computed[term, literal[0]]},
	application[constantReference[HoldComplete[NaturalNumberSuccessor], _], argument_] :> With[{sum = ringNormalForm[plus[argument, literal[1]]]},
		{First[sum], Replace[Last[sum], {_, right_, proof_} :> {term, right, proof}]}
	],
	application[application[constantReference[HoldComplete[Plus], {}], a_], b_] :> sumNormalForm[a, b],
	application[application[constantReference[HoldComplete[Times], {}], a_], b_] :> productNormalForm[a, b],
	application[application[constantReference[HoldComplete[Power], {}], naturalLiteral[m_Integer]], naturalLiteral[k_Integer]] /; k <= $largestRingExponent :>
		With[{value = If[k == 0, 1, m^k]}, {If[value == 0, {}, {{value, {}}}], computed[term, literal[value]]}],
	application[application[constantReference[HoldComplete[Power], {}], a_], naturalLiteral[k_Integer]] /; k <= $largestRingExponent :> powerNormalForm[a, k],
	_ :> {{{1, {{term, 1}}}}, reflexive[term]}
}]

sumNormalForm[a_, b_] := With[{first = ringNormalForm[a], second = ringNormalForm[b]},
	{sum = polynomialSum[First[first], First[second]]},
	{First[sum], transitive[congruentBoth[plus, Last[first], Last[second]], Last[sum]]}
]

productNormalForm[a_, b_] := With[{first = ringNormalForm[a], second = ringNormalForm[b]},
	{product = polynomialProduct[First[first], First[second]]},
	{First[product], transitive[congruentBoth[times, Last[first], Last[second]], Last[product]]}
]

$largestRingExponent = 4096

(* an atom to a power is a monomial; any other power is a product, by at most 32 multiplications *)
powerNormalForm[a_, 0] := {{{1, {}}}, powerZero[a]}
powerNormalForm[a_, k_Integer] := With[{base = ringNormalForm[a]},
	Replace[First[base], {
		{{1, {{atom_, 1}}}} /; k == 1 :> {{{1, {{atom, 1}}}}, transitive[congruent[Function[hole, power[hole, literal[1]]], Last[base]], powerOne[atom]]},
		{{1, {{atom_, 1}}}} :> {{{1, {{atom, k}}}}, congruent[Function[hole, power[hole, literal[k]]], Last[base]]},
		_ /; k > 32 :> With[{term = power[a, literal[k]]}, {{{1, {{term, 1}}}}, reflexive[term]}],
		polynomial_ :> With[{raised = polynomialPower[polynomial, k]},
			{First[raised], transitive[congruent[Function[hole, power[hole, literal[k]]], Last[base]], Last[raised]]}
		]
	}]
]

(* {polynomial, term[A]^k == term[polynomial]}, by k - 1 multiplications *)
polynomialPower[polynomial_List, 1] := {polynomial, powerOne[polynomialTerm[polynomial]]}
polynomialPower[polynomial_List, k_Integer] := With[{lower = polynomialPower[polynomial, k - 1]},
	{product = polynomialProduct[First[lower], polynomial]},
	{First[product], chain[
		powerSuccessor[polynomialTerm[polynomial], literal[k - 1]],
		congruent[Function[hole, times[hole, polynomialTerm[polynomial]]], Last[lower]],
		Last[product]
	]}
]


(* ::Subsection:: *)
(*Sums*)


(* {C, term[A] + term[B] == term[C]}: the monomials of A inserted into B one at a time, the last first *)
polynomialSum[{}, second_List] := {second, additionZeroLeft[polynomialTerm[second]]}
polynomialSum[first_List, {}] := {first, additionZeroRight[polynomialTerm[first]]}
polynomialSum[{monomial_}, second_List] := monomialInsertion[monomial, second]
polynomialSum[{monomial_, rest__}, second_List] := With[{inner = polynomialSum[{rest}, second]},
	{outer = monomialInsertion[monomial, First[inner]]},
	{First[outer], chain[
		additionAssociativity[monomialTerm[monomial], polynomialTerm[{rest}], polynomialTerm[second]],
		congruent[Function[hole, plus[monomialTerm[monomial], hole]], Last[inner]],
		Last[outer]
	]}
]

(* {D, term[m] + term[C] == term[D]} *)
monomialInsertion[monomial_, {}] := {{monomial}, additionZeroRight[monomialTerm[monomial]]}
monomialInsertion[monomial_, {next_, rest___}] := Which[
	Last[monomial] === Last[next],
		With[{merged = likeMonomialSum[monomial, next]},
			If[ {rest} === {},
				{{First[merged]}, Last[merged]},
				{{First[merged], rest}, transitive[
					symmetric[additionAssociativity[monomialTerm[monomial], monomialTerm[next], polynomialTerm[{rest}]]],
					congruent[Function[hole, plus[hole, polynomialTerm[{rest}]]], Last[merged]]
				]}
			]
		],
	monomialBeforeQ[monomial, next],
		{{monomial, next, rest}, reflexive[plus[monomialTerm[monomial], polynomialTerm[{next, rest}]]]},
	{rest} === {},
		{{next, monomial}, additionCommutativity[monomialTerm[monomial], monomialTerm[next]]},
	True,
		With[{inner = monomialInsertion[monomial, {rest}]},
			{Prepend[First[inner], next], transitive[
				leftCommutativity[plus, additionAssociativity, additionCommutativity, monomialTerm[monomial], monomialTerm[next], polynomialTerm[{rest}]],
				congruent[Function[hole, plus[monomialTerm[next], hole]], Last[inner]]
			]}
		]
]

(* c1 x... + c2 x... == (c1 + c2) x..., by distributivity, with the coefficient 1 shown first *)
likeMonomialSum[{first_Integer, {}}, {second_Integer, {}}] := {{first + second, {}}, computed[plus[literal[first], literal[second]], literal[first + second]]}
likeMonomialSum[{first_Integer, factors : {__}}, {second_Integer, factors : {__}}] := With[{product = productTerm[factors]},
	{{first + second, factors}, chain[
		congruentBoth[plus, coefficientShown[first, product], coefficientShown[second, product]],
		symmetric[distributivityRight[literal[first], literal[second], product]],
		computed[times[plus[literal[first], literal[second]], product], times[literal[first + second], product]]
	]}
]

(* the monomial's term == c * product *)
coefficientShown[1, product_] := symmetric[multiplicationOneLeft[product]]
coefficientShown[coefficient_Integer, product_] := reflexive[times[literal[coefficient], product]]


(* ::Subsection:: *)
(*Products*)


(* {C, term[A] * term[B] == term[C]}, by distributivity *)
polynomialProduct[{}, second_List] := {{}, multiplicationZeroLeft[polynomialTerm[second]]}
polynomialProduct[first_List, {}] := {{}, multiplicationZeroRight[polynomialTerm[first]]}
polynomialProduct[{monomial_}, {other_}] := With[{product = monomialProduct[monomial, other]}, {{First[product]}, Last[product]}]
polynomialProduct[{monomial_}, {other_, rest__}] := With[
	{left = polynomialProduct[{monomial}, {other}], right = polynomialProduct[{monomial}, {rest}]},
	{sum = polynomialSum[First[left], First[right]]},
	{First[sum], chain[
		distributivityLeft[monomialTerm[monomial], monomialTerm[other], polynomialTerm[{rest}]],
		congruentBoth[plus, Last[left], Last[right]],
		Last[sum]
	]}
]
polynomialProduct[{monomial_, rest__}, second_List] := With[
	{left = polynomialProduct[{monomial}, second], right = polynomialProduct[{rest}, second]},
	{sum = polynomialSum[First[left], First[right]]},
	{First[sum], chain[
		distributivityRight[monomialTerm[monomial], polynomialTerm[{rest}], polynomialTerm[second]],
		congruentBoth[plus, Last[left], Last[right]],
		Last[sum]
	]}
]

(* {m, term[m1] * term[m2] == term[m]}: the coefficients multiplied in front, the factors merged *)
monomialProduct[{first_Integer, {}}, {second_Integer, {}}] := {{first second, {}}, computed[times[literal[first], literal[second]], literal[first second]]}
monomialProduct[{1, factors : {__}}, {1, otherFactors : {__}}] := With[{merged = factorProduct[factors, otherFactors]},
	{{1, First[merged]}, Last[merged]}
]
monomialProduct[{first_Integer, factors : {__}}, {second_Integer, {}}] := With[{swapped = monomialProduct[{second, {}}, {first, factors}]},
	{First[swapped], transitive[multiplicationCommutativity[monomialTerm[{first, factors}], literal[second]], Last[swapped]]}
]
monomialProduct[{first_Integer, {}}, {second_Integer, factors : {__}}] := With[{product = productTerm[factors]},
	{{first second, factors}, chain[
		congruent[Function[hole, times[literal[first], hole]], coefficientShown[second, product]],
		symmetric[multiplicationAssociativity[literal[first], literal[second], product]],
		computed[times[times[literal[first], literal[second]], product], times[literal[first second], product]],
		coefficientHidden[first second, product]
	]}
]
monomialProduct[{first_Integer, factors : {__}}, {second_Integer, otherFactors : {__}}] := With[
	{product = productTerm[factors], otherProduct = productTerm[otherFactors], merged = factorProduct[factors, otherFactors]},
	{{first second, First[merged]}, chain[
		congruentBoth[times, coefficientShown[first, product], coefficientShown[second, otherProduct]],
		multiplicationAssociativity[literal[first], product, times[literal[second], otherProduct]],
		congruent[
			Function[hole, times[literal[first], hole]],
			leftCommutativity[times, multiplicationAssociativity, multiplicationCommutativity, product, literal[second], otherProduct]
		],
		symmetric[multiplicationAssociativity[literal[first], literal[second], times[product, otherProduct]]],
		computed[times[times[literal[first], literal[second]], times[product, otherProduct]], times[literal[first second], times[product, otherProduct]]],
		congruent[Function[hole, times[literal[first second], hole]], Last[merged]],
		coefficientHidden[first second, productTerm[First[merged]]]
	]}
]

(* c * product == the monomial's term, the coefficient 1 left out *)
coefficientHidden[1, product_] := multiplicationOneLeft[product]
coefficientHidden[coefficient_Integer, product_] := reflexive[times[literal[coefficient], product]]

(* {F, term[F1] * term[F2] == term[F]} for lists of factors: the factors of F1 inserted into F2 one at a
   time, the last first, the powers of an atom combined *)
factorProduct[{factor_}, second_List] := factorInsertion[factor, second]
factorProduct[{factor_, rest__}, second_List] := With[{inner = factorProduct[{rest}, second]},
	{outer = factorInsertion[factor, First[inner]]},
	{First[outer], chain[
		multiplicationAssociativity[factorTerm[factor], productTerm[{rest}], productTerm[second]],
		congruent[Function[hole, times[factorTerm[factor], hole]], Last[inner]],
		Last[outer]
	]}
]

factorInsertion[factor_, {next_, rest___}] := Which[
	First[factor] === First[next],
		With[{merged = likeFactorProduct[factor, next]},
			If[ {rest} === {},
				{{First[merged]}, Last[merged]},
				{{First[merged], rest}, transitive[
					symmetric[multiplicationAssociativity[factorTerm[factor], factorTerm[next], productTerm[{rest}]]],
					congruent[Function[hole, times[hole, productTerm[{rest}]]], Last[merged]]
				]}
			]
		],
	atomBeforeQ[First[factor], First[next]],
		{{factor, next, rest}, reflexive[times[factorTerm[factor], productTerm[{next, rest}]]]},
	{rest} === {},
		{{next, factor}, multiplicationCommutativity[factorTerm[factor], factorTerm[next]]},
	True,
		With[{inner = factorInsertion[factor, {rest}]},
			{Prepend[First[inner], next], transitive[
				leftCommutativity[times, multiplicationAssociativity, multiplicationCommutativity, factorTerm[factor], factorTerm[next], productTerm[{rest}]],
				congruent[Function[hole, times[factorTerm[next], hole]], Last[inner]]
			]}
		]
]

(* x^a * x^b == x^(a + b), with the exponent 1 shown first *)
likeFactorProduct[{atom_, first_Integer}, {atom_, second_Integer}] := {{atom, first + second}, chain[
	congruentBoth[times, exponentShown[atom, first], exponentShown[atom, second]],
	symmetric[powerAddition[atom, literal[first], literal[second]]],
	computed[power[atom, plus[literal[first], literal[second]]], power[atom, literal[first + second]]]
]}

exponentShown[atom_, 1] := symmetric[powerOne[atom]]
exponentShown[atom_, exponent_Integer] := reflexive[power[atom, literal[exponent]]]
