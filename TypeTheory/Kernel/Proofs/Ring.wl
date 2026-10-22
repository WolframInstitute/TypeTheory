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

The same normal forms are built for the integers of TypeTheoryEnvironment["Integers"], from their laws,
with $ring the integers: a coefficient is a nonzero integer, -3 x the product of the negation of the
integer of 3 and x, and like monomials can cancel. Two literals of the same sign add by computation; of
opposite signs they are two pairs, equal by a lemma. A negation is the product with -1, a difference
the sum with the negation, and the integer of a natural number is pushed into the natural number's
sums, products and powers. The exponents are natural numbers.

A polynomial combination proves l == r from hypotheses a1 == b1, ...: Wolfram finds cofactors ci with
d (l - r) = c1 (a1 - b1) + ..., d a positive integer and each ci a polynomial with integer coefficients,
the difference pi - qi of two with natural coefficients. PolynomialReduce finds them when the
hypotheses reduce the goal, and otherwise linear algebra over the rationals finds cofactors of each
degree up to the goal's, d clearing their denominators. Then d l + X == d r + X' holds in every
commutative semiring, with X the sum of the pi bi and qi ai, and X' that of the pi ai and qi bi; the
hypotheses make X' equal to X, taking X from both sides leaves d l == d r, and MultiplicationCancellation
leaves l == r.

Linear arithmetic proves l <= r from hypotheses a1 <= b1, ..., each monomial of the atoms counted as a
variable. LessEqualTotality gives l <= r or r < l, and the second is refuted: Wolfram's FindInstance
finds natural multipliers yi of r + 1 <= l and the hypotheses with y1 (a1 - b1) + ... a positive
constant c. The inequalities, multiplied by MultiplicationMonotonicity and added by AdditionMonotonicity,
give A <= B, where B + c == A holds in every commutative semiring, so B + c <= B, which is
(B + (c - 1)) + 1 <= B + (c - 1) after B <= B + (c - 1), and LessIrreflexivity refutes it.
*)


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[ringNormalForm]
PackageScoped[ringEquationProof]
PackageScoped[ringCombinationProof]
PackageScoped[ringLinearProof]
PackageScoped[ringContradictionProof]
PackageScoped[ringEquationInequalities]
PackageScoped[integerRingEquationProof]
PackageScoped[integerRingAvailableQ]


(* ::Section:: *)
(*Usage Messages*)


ringNormalForm::usage = "ringNormalForm[term] gives {polynomial, {term, normal, proof}} for a core term of natural numbers: its normal form as a polynomial in its atoms, \
the term normal of that polynomial, and a proof of term == normal from the laws of the prelude."
ringEquationProof::usage = "ringEquationProof[left, right] gives a proof of left == right for core terms of natural numbers with the same normal form, or None."
ringCombinationProof::usage = "ringCombinationProof[left, right, {{a, b, proof}, ...}] gives a proof of left == right from proofs of equations a == b of natural numbers, \
by a polynomial combination of them that Wolfram's PolynomialReduce finds, or None."
ringLinearProof::usage = "ringLinearProof[left, right, {{a, b, proof}, ...}] gives a proof of left <= right from proofs of inequalities a <= b of natural numbers that \
imply it linearly, or None."
ringContradictionProof::usage = "ringContradictionProof[{{a, b, proof}, ...}] gives a proof of False from proofs of inequalities a <= b of natural numbers that contradict \
each other linearly, or None."
integerRingEquationProof::usage = "integerRingEquationProof[left, right] gives a proof of left == right for core terms of the integers of TypeTheoryEnvironment[\"Integers\"] \
with the same normal form, from the integers' laws, or None."
integerRingAvailableQ::usage = "integerRingAvailableQ[environment] gives True if environment declares the integers and the laws their normal forms are built from."
ringEquationInequalities::usage = "ringEquationInequalities[a, b, proof] gives {{a, b, proof1}, {b, a, proof2}}, the inequalities a <= b and b <= a, from a proof of a == b."


(* ::Section:: *)
(*Function Definitions*)


ringEquationProof[left_, right_] := Replace[ringEquation[left, right], equation_List :> Last[equation]]

integerRingEquationProof[left_, right_] := Block[{$ring = $integerRing}, ringEquationProof[left, right]]

integerRingAvailableQ[environment_] := AllTrue[
	Join[Values[$integerRing["Laws"]], Values[$integerRing["Operations"]], $integerNormalFormConstants],
	Function[name, constantDeclaredQ[environment, name]]
]

(* left == right as an equation, or None *)
ringEquation[left_, right_] := With[{leftForm = ringNormalForm[left], rightForm = ringNormalForm[right]},
	If[First[leftForm] === First[rightForm], transitive[Last[leftForm], symmetric[Last[rightForm]]], None]
]


(* ::Subsection:: *)
(*Polynomial combinations*)


ringCombinationProof[left_, right_, hypotheses_List] := Replace[combinationEquation[left, right, hypotheses], equation_List :> Last[equation]]

(* None where no cofactors are found; a hypothesis whose sides have the same normal form says nothing,
   and is left out *)
combinationEquation[left_, right_, hypotheses_List] := Module[{forms, atoms, variables, difference, useful, cofactors, scale},
	forms = Function[pair, Function[term, First @ ringNormalForm[term]] /@ pair] /@ Prepend[Function[hypothesis, Most[hypothesis]] /@ hypotheses, {left, right}];
	atoms = DeleteDuplicates @ Catenate[Function[monomial, First /@ Last[monomial]] /@ Catenate[Catenate[forms]]];
	variables = Table[Subscript[\[FormalX], k], {k, Length[atoms]}];
	difference = Function[pair, Expand[Subtract @@ (Function[polynomial, wolframPolynomial[polynomial, AssociationThread[atoms, variables]]] /@ pair)]];
	useful = Select[Transpose[{hypotheses, difference /@ Rest[forms]}], Function[pair, Last[pair] =!= 0]];
	cofactors = foundCofactors[difference[First[forms]], Last /@ useful, variables];
	If[ cofactors === None,
		None,
		scale = LCM @@ Denominator[Catenate[Function[cofactor, Last /@ CoefficientRules[cofactor, variables]] /@ cofactors]];
		combination[left, right, scale, MapThread[
			Function[{hypothesis, cofactor}, Prepend[signedParts[scale * cofactor, variables, atoms], hypothesis]],
			{First /@ useful, cofactors}
		]]
	]
]

(* the cofactors c with target = c . divisors, from PolynomialReduce, or else from linear algebra for
   cofactors of degree 0, 1, ... up to the target's, at least 2; None if there are none *)
foundCofactors[target_, divisors_List, variables_List] := With[{reduced = Quiet @ PolynomialReduce[target, divisors, variables]},
	If[ Expand[Last[reduced]] === 0,
		First[reduced],
		linearCofactors[target, divisors, variables, 0, Max[2, Total /@ Keys[CoefficientRules[target, variables]]]]
	]
]

linearCofactors[_, _, _, degree_Integer, limit_] /; degree > limit := None
linearCofactors[target_, divisors_List, variables_List, degree_Integer, limit_] := Module[{monomials, unknowns, cofactors, solution},
	monomials = Times @@@ (Function[exponents, variables^exponents] /@ Select[Tuples[Range[0, degree], Length[variables]], Function[exponents, Total[exponents] <= degree]]);
	unknowns = Table[\[FormalU][i, j], {i, Length[divisors]}, {j, Length[monomials]}];
	cofactors = unknowns . monomials;
	solution = Quiet @ Solve[Thread[Last /@ CoefficientRules[Expand[target - cofactors . divisors], variables] == 0], Flatten[unknowns]];
	If[ MatchQ[solution, {{___Rule}, ___}],
		Expand[cofactors /. First[solution] /. \[FormalU][___] -> 0],
		linearCofactors[target, divisors, variables, degree + 1, limit]
	]
]

(* the polynomial as a Wolfram expression in the variables standing for its atoms *)
wolframPolynomial[polynomial_List, variableOf_Association] := Total[Function[monomial,
	First[monomial] * Times @@ (Function[factor, variableOf[First[factor]]^Last[factor]] /@ Last[monomial])
] /@ polynomial]

(* {p, q}: the cofactor's terms of positive coefficient, and its terms of negative coefficient negated,
   as polynomials in the atoms *)
signedParts[cofactor_, variables_List, atoms_List] := With[{rules = CoefficientRules[Expand[cofactor], variables]},
	Function[sign,
		Function[rule, {sign * Last[rule], Select[Transpose[{atoms, First[rule]}], Function[factor, Last[factor] > 0]]}] /@
			Select[rules, Function[rule, sign * Last[rule] > 0]]
	] /@ {1, -1}
]

(* each hypothesis a == b with its parts p and q gives p a == p b and q b == q a; their sums are X' == X *)
combination[left_, right_, scale_Integer, parts_List] := With[
	{
		summands = Catenate @ Replace[parts, {hypothesis_, p_, q_} :> Join[
			If[p === {}, {}, {congruent[Function[hole, times[polynomialTerm[p], hole]], hypothesis]}],
			If[q === {}, {}, {congruent[Function[hole, times[polynomialTerm[q], hole]], symmetric[hypothesis]]}]
		], {1}]
	},
	Replace[
		If[ summands === {},
			ringEquation[scaled[left, scale], scaled[right, scale]],
			cancelled[scaled[left, scale], scaled[right, scale], Fold[Function[{accumulated, summand}, congruentBoth[plus, summand, accumulated]], Last[summands], Reverse[Most[summands]]]]
		],
		{
			None -> None,
			equation_ /; scale == 1 :> equation,
			{_, _, proof_} :> law[MultiplicationCancellation, {literal[scale - 1], left, right, proof}, left, right]
		}
	]
]

scaled[term_, 1] := term
scaled[term_, scale_Integer] := times[literal[scale], term]

(* left == right from left + X == right + X', by the normal forms, and difference, a proof of X' == X *)
cancelled[left_, right_, difference : {primed_, unprimed_, _}] := Replace[ringEquation[plus[left, unprimed], plus[right, primed]], {
	None -> None,
	identity_ :> chain[
		symmetric[additionSubtractionCancellation[left, unprimed]],
		congruent[Function[hole, subtract[hole, unprimed]], transitive[identity, congruent[Function[hole, plus[right, hole]], difference]]],
		additionSubtractionCancellation[right, unprimed]
	]
}]


(* ::Subsection:: *)
(*Linear arithmetic*)


ringLinearProof[left_, right_, inequalities_List] := With[{id = freshFreeVariable[]},
	Replace[ringContradictionProof[Prepend[inequalities, {plus[right, literal[1]], left, freeVariable[id]}]], {
		None -> None,
		contradiction_ :> makeApplication[constantReference[recursorName[HoldComplete[Or]], {}], {
			lessEqual[left, right],
			less[right, left],
			lambdaAbstraction[HoldComplete[t], or[lessEqual[left, right], less[right, left]], lessEqual[left, right], "Explicit"],
			lambdaAbstraction[HoldComplete[h], lessEqual[left, right], boundVariable[0], "Explicit"],
			lambdaAbstraction[
				HoldComplete[g],
				less[right, left],
				makeApplication[constantReference[HoldComplete[FalseElimination], {}], {lessEqual[left, right], abstractFreeVariable[contradiction, id]}],
				"Explicit"
			],
			makeApplication[constantReference[HoldComplete[LessEqualTotality], {}], {left, right}]
		}]
	}]
]

(* every natural number is at least 0, so each monomial m of the inequalities adds 0 <= m *)
ringContradictionProof[given_List] := Module[{inequalities, forms, atoms, variables, differences, multipliers},
	inequalities = Join[given, nonnegativity[Function[inequality, Function[term, First @ ringNormalForm[term]] /@ Most[inequality]] /@ given]];
	forms = Function[inequality, Function[term, First @ ringNormalForm[term]] /@ Most[inequality]] /@ inequalities;
	atoms = DeleteDuplicates @ Catenate[Function[monomial, First /@ Last[monomial]] /@ Catenate[Catenate[forms]]];
	variables = Table[Subscript[\[FormalX], k], {k, Length[atoms]}];
	differences = Function[pair, Expand[Subtract @@ (Function[polynomial, wolframPolynomial[polynomial, AssociationThread[atoms, variables]]] /@ pair)]] /@ forms;
	multipliers = contradictionMultipliers[differences, variables];
	If[multipliers === None, None, contradiction[inequalities, multipliers, Expand[multipliers . differences]]]
]

nonnegativity[forms_List] := Function[factors, With[{term = productTerm[factors]},
	{literal[0], term, makeApplication[constantReference[HoldComplete[LessEqualZero], {}], {term}]}
]] /@ DeleteCases[DeleteDuplicates[Last /@ Catenate[Catenate[forms]]], {}]

(* natural numbers y with y . differences a positive constant, or None *)
contradictionMultipliers[differences_List, variables_List] := With[{multipliers = Table[\[FormalY][i], {i, Length[differences]}]},
	{rules = CoefficientRules[Expand[multipliers . differences], variables]},
	Replace[
		TimeConstrained[
			Quiet @ FindInstance[
				And @@ Join[
					Thread[(Last /@ Select[rules, Function[rule, Total[First[rule]] > 0]]) == 0],
					{Total[Last /@ Select[rules, Function[rule, Total[First[rule]] == 0]]] >= 1},
					Thread[multipliers >= 0]
				],
				multipliers,
				Integers
			],
			10,
			$Aborted
		],
		{
			{solution_List, ___} :> ReplaceAll[multipliers, solution],
			_ :> None
		}
	]
]

(* the inequalities multiplied and added give A <= B, and B + c == A *)
contradiction[inequalities_List, multipliers_List, constant_Integer] := With[
	{scaled = DeleteCases[MapThread[scaledInequality, {inequalities, multipliers}], None]},
	{sum = Fold[Function[{accumulated, inequality}, addedInequalities[inequality, accumulated]], Last[scaled], Reverse[Most[scaled]]]},
	Replace[sum, {small_, large_, proof_} :> Replace[ringEquation[plus[large, literal[constant]], small], {
		None -> None,
		identity_ :> irreflexivityContradiction[large, constant, makeApplication[constantReference[HoldComplete[EqualitySubstitution], {1}], {
			$naturals,
			lambdaAbstraction[HoldComplete[t], $naturals, lessEqual[boundVariable[0], large], "Explicit"],
			small,
			plus[large, literal[constant]],
			Last[symmetric[identity]],
			proof
		}]]
	}]]
]

scaledInequality[_, 0] := None
scaledInequality[inequality_List, 1] := inequality
scaledInequality[{a_, b_, proof_}, multiplier_Integer] :=
	{times[a, literal[multiplier]], times[b, literal[multiplier]], makeApplication[constantReference[HoldComplete[MultiplicationMonotonicity], {}], {a, b, literal[multiplier], proof}]}

addedInequalities[{a_, b_, proof_}, {c_, d_, otherProof_}] :=
	{plus[a, c], plus[b, d], makeApplication[constantReference[HoldComplete[AdditionMonotonicity], {}], {a, b, c, d, proof, otherProof}]}

(* False from a proof of B + c <= B, c >= 1: it is (B + (c - 1)) + 1 <= B + (c - 1) after B <= B + (c - 1) *)
irreflexivityContradiction[large_, constant_Integer, proof_] := application[
	makeApplication[constantReference[HoldComplete[LessIrreflexivity], {}], {plus[large, literal[constant - 1]]}],
	makeApplication[constantReference[HoldComplete[LessEqualTransitivity], {}], {
		plus[large, literal[constant]],
		large,
		plus[large, literal[constant - 1]],
		proof,
		makeApplication[constantReference[HoldComplete[LessEqualAddition], {}], {large, literal[constant - 1]}]
	}]
]

(* a <= b and b <= a, each from a <= a carried along a == b *)
ringEquationInequalities[a_, b_, proof_] := {
	{a, b, carriedReflexivity[a, b, proof, Function[side, lessEqual[a, side]]]},
	{b, a, carriedReflexivity[a, b, proof, Function[side, lessEqual[side, a]]]}
}

(* predicate[b] from predicate[a], which is a <= a *)
carriedReflexivity[a_, b_, proof_, predicate_] := makeApplication[constantReference[HoldComplete[EqualitySubstitution], {1}], {
	$naturals,
	lambdaAbstraction[HoldComplete[t], $naturals, predicate[boundVariable[0]], "Explicit"],
	a,
	b,
	proof,
	application[constantReference[HoldComplete[LessEqualReflexivity], {}], a]
}]


(* ::Subsection:: *)
(*Terms*)


$naturals = constantReference[HoldComplete[NonNegativeIntegers], {}]

(* The ring the normal forms are in: the natural numbers, or the integers of
   TypeTheoryEnvironment["Integers"], whose coefficients have signs. Its literals are the coefficients;
   exponents are natural numbers in either. *)
$naturalNumberRing = <|
	"Type" -> $naturals,
	"Operations" -> <|"Plus" -> HoldComplete[Plus], "Times" -> HoldComplete[Times], "Power" -> HoldComplete[Power]|>,
	"Literal" -> naturalLiteral,
	"NormalForm" -> naturalNormalForm,
	"LiteralSum" -> computedLiteralSum,
	"Laws" -> <|
		"AdditionAssociativity" -> HoldComplete[AdditionAssociativity],
		"AdditionCommutativity" -> HoldComplete[AdditionCommutativity],
		"AdditionZeroLeft" -> HoldComplete[AdditionZeroLeft],
		"AdditionZeroRight" -> HoldComplete[AdditionZeroRight],
		"MultiplicationAssociativity" -> HoldComplete[MultiplicationAssociativity],
		"MultiplicationCommutativity" -> HoldComplete[MultiplicationCommutativity],
		"MultiplicationZeroLeft" -> HoldComplete[MultiplicationZeroLeft],
		"MultiplicationZeroRight" -> HoldComplete[MultiplicationZeroRight],
		"MultiplicationOneLeft" -> HoldComplete[MultiplicationOneLeft],
		"MultiplicationDistributivityLeft" -> HoldComplete[MultiplicationDistributivityLeft],
		"MultiplicationDistributivityRight" -> HoldComplete[MultiplicationDistributivityRight],
		"PowerZero" -> HoldComplete[PowerZero],
		"PowerOne" -> HoldComplete[PowerOne],
		"PowerSuccessor" -> HoldComplete[PowerSuccessor],
		"PowerAddition" -> HoldComplete[PowerAddition]
	|>
|>

$integerRing = <|
	"Type" -> constantReference[HoldComplete[Integers], {}],
	"Operations" -> <|"Plus" -> HoldComplete["integerAddition"], "Times" -> HoldComplete["integerMultiplication"], "Power" -> HoldComplete["integerPower"]|>,
	"Literal" -> integerLiteral,
	"NormalForm" -> integerNormalForm,
	"LiteralSum" -> integerLiteralSum,
	"Laws" -> <|
		"AdditionAssociativity" -> HoldComplete[IntegerAdditionAssociativity],
		"AdditionCommutativity" -> HoldComplete[IntegerAdditionCommutativity],
		"AdditionZeroLeft" -> HoldComplete["integerAdditionZeroLeft"],
		"AdditionZeroRight" -> HoldComplete[IntegerAdditionZero],
		"MultiplicationAssociativity" -> HoldComplete[IntegerMultiplicationAssociativity],
		"MultiplicationCommutativity" -> HoldComplete[IntegerMultiplicationCommutativity],
		"MultiplicationZeroLeft" -> HoldComplete["integerMultiplicationZeroLeft"],
		"MultiplicationZeroRight" -> HoldComplete["integerMultiplicationZeroRight"],
		"MultiplicationOneLeft" -> HoldComplete["integerMultiplicationOneLeft"],
		"MultiplicationDistributivityLeft" -> HoldComplete[IntegerDistributivity],
		"MultiplicationDistributivityRight" -> HoldComplete["integerDistributivityRight"],
		"PowerZero" -> HoldComplete["integerPowerZero"],
		"PowerOne" -> HoldComplete["integerPowerOne"],
		"PowerSuccessor" -> HoldComplete["integerPowerSuccessor"],
		"PowerAddition" -> HoldComplete["integerPowerAddition"]
	|>
|>

$ring = $naturalNumberRing

(* the constants the integers' normal forms are built from, beside the ring's laws and operations *)
$integerNormalFormConstants = HoldComplete /@ Unevaluated[{
	Integers, "integerOfNatural", "integerNegation", "integerSubtraction", "integerNegationProduct", "integerLiteralDifferenceNonnegative",
	"integerLiteralDifferenceNegative", IntegerOfNaturalAddition, IntegerOfNaturalMultiplication, "integerOfNaturalPower",
	EqualityReflexivity, EqualitySymmetry, EqualityTransitivity, EqualityCongruence
}]

literal[n_Integer] := $ring["Literal"][n]
plus[a_, b_] := ringOperation["Plus", a, b]
times[a_, b_] := ringOperation["Times", a, b]
power[a_, b_] := ringOperation["Power", a, b]
ringOperation[name_String, a_, b_] := application[application[constantReference[$ring["Operations"][name], {}], a], b]
subtract[a_, b_] := application[application[constantReference[HoldComplete[Subtract], {}], a], b]

(* an exponent and a sum of exponents, natural numbers in either ring *)
exponent[n_Integer] := naturalLiteral[n]
exponentSum[a_, b_] := application[application[constantReference[HoldComplete[Plus], {}], a], b]

(* the integers' literals: n is the integer of the natural number n, and -n its negation *)
integerLiteral[n_Integer?NonNegative] := integerOfNatural[naturalLiteral[n]]
integerLiteral[n_Integer] := negation[integerLiteral[-n]]
integerOfNatural[term_] := application[constantReference[HoldComplete["integerOfNatural"], {}], term]
negation[term_] := application[constantReference[HoldComplete["integerNegation"], {}], term]
lessEqual[a_, b_] := application[application[constantReference[HoldComplete[LessEqual], {}], a], b]
less[a_, b_] := application[application[constantReference[HoldComplete[Less], {}], a], b]
or[p_, q_] := application[application[constantReference[HoldComplete[Or], {}], p], q]

factorTerm[{atom_, 1}] := atom
factorTerm[{atom_, k_Integer}] := power[atom, exponent[k]]

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


reflexivityProof[term_] := makeApplication[constantReference[HoldComplete[EqualityReflexivity], {1}], {$ring["Type"], term}]

reflexivityProofQ[proof_] := MatchQ[proof, application[application[constantReference[HoldComplete[EqualityReflexivity], _], _], _]]

reflexive[term_] := {term, term, reflexivityProof[term]}

(* left and right are equal by computation *)
computed[left_, right_] := {left, right, reflexivityProof[right]}

symmetric[{left_, right_, proof_}] /; reflexivityProofQ[proof] := computed[right, left]
symmetric[{left_, right_, proof_}] := {right, left, makeApplication[constantReference[HoldComplete[EqualitySymmetry], {1}], {$ring["Type"], left, right, proof}]}

(* a step by reflexivity is left out: the kernel checks the computation where the other proof is used *)
transitive[{left_, _, proof_}, {_, right_, otherProof_}] /; reflexivityProofQ[proof] := {left, right, otherProof}
transitive[{left_, _, proof_}, {_, right_, otherProof_}] /; reflexivityProofQ[otherProof] := {left, right, proof}
transitive[{left_, middle_, proof_}, {_, right_, otherProof_}] :=
	{left, right, makeApplication[constantReference[HoldComplete[EqualityTransitivity], {1}], {$ring["Type"], left, middle, right, proof, otherProof}]}

chain[first_, rest___] := Fold[transitive, first, {rest}]

(* context[left] == context[right], for a context of one hole, a function of terms that puts no binder
   around the hole *)
congruent[context_, {left_, right_, proof_}] /; reflexivityProofQ[proof] := computed[context[left], context[right]]
congruent[context_, {left_, right_, proof_}] := {
	context[left],
	context[right],
	makeApplication[
		constantReference[HoldComplete[EqualityCongruence], {1, 1}],
		{$ring["Type"], $ring["Type"], left, right, lambdaAbstraction[HoldComplete[x], $ring["Type"], context[boundVariable[0]], "Explicit"], proof}
	]
}

(* operation[a, b] == operation[a', b'] from a == a' and b == b' *)
congruentBoth[operation_, first : {_, firstRight_, _}, second : {secondLeft_, _, _}] :=
	transitive[congruent[Function[hole, operation[hole, secondLeft]], first], congruent[Function[hole, operation[firstRight, hole]], second]]

law[name_, arguments_List, left_, right_] := {left, right, makeApplication[constantReference[HoldComplete[name], {}], arguments]}

(* a law of the ring, by the name of the natural numbers' *)
ringLaw[name_String, arguments_List, left_, right_] := {left, right, makeApplication[constantReference[$ring["Laws"][name], {}], arguments]}

additionAssociativity[a_, b_, c_] := ringLaw["AdditionAssociativity", {a, b, c}, plus[plus[a, b], c], plus[a, plus[b, c]]]
additionCommutativity[a_, b_] := ringLaw["AdditionCommutativity", {a, b}, plus[a, b], plus[b, a]]
additionZeroLeft[n_] := ringLaw["AdditionZeroLeft", {n}, plus[literal[0], n], n]
additionZeroRight[n_] := ringLaw["AdditionZeroRight", {n}, plus[n, literal[0]], n]
multiplicationAssociativity[a_, b_, c_] := ringLaw["MultiplicationAssociativity", {a, b, c}, times[times[a, b], c], times[a, times[b, c]]]
multiplicationCommutativity[a_, b_] := ringLaw["MultiplicationCommutativity", {a, b}, times[a, b], times[b, a]]
multiplicationZeroLeft[n_] := ringLaw["MultiplicationZeroLeft", {n}, times[literal[0], n], literal[0]]
multiplicationZeroRight[n_] := ringLaw["MultiplicationZeroRight", {n}, times[n, literal[0]], literal[0]]
multiplicationOneLeft[n_] := ringLaw["MultiplicationOneLeft", {n}, times[literal[1], n], n]
distributivityLeft[a_, b_, c_] := ringLaw["MultiplicationDistributivityLeft", {a, b, c}, times[a, plus[b, c]], plus[times[a, b], times[a, c]]]
distributivityRight[a_, b_, c_] := ringLaw["MultiplicationDistributivityRight", {a, b, c}, times[plus[a, b], c], plus[times[a, c], times[b, c]]]
powerZero[m_] := ringLaw["PowerZero", {m}, power[m, exponent[0]], literal[1]]
powerOne[m_] := ringLaw["PowerOne", {m}, power[m, exponent[1]], m]
powerSuccessor[m_, n_] := ringLaw["PowerSuccessor", {m, n}, power[m, exponentSum[n, exponent[1]]], times[power[m, n], m]]
powerAddition[m_, a_, b_] := ringLaw["PowerAddition", {m, a, b}, power[m, exponentSum[a, b]], times[power[m, a], power[m, b]]]
additionSubtractionCancellation[n_, m_] := law[AdditionSubtractionCancellation, {n, m}, subtract[plus[n, m], m], n]

(* literal[a] + literal[b] == literal[a + b]: by computation, but for integers of opposite signs, which
   are two pairs equal by a lemma; a negative one first is moved second *)
computedLiteralSum[a_Integer, b_Integer] := computed[plus[literal[a], literal[b]], literal[a + b]]

integerLiteralSum[a_Integer, b_Integer] /; a b >= 0 := computedLiteralSum[a, b]
integerLiteralSum[a_Integer?Negative, b_Integer] := transitive[additionCommutativity[literal[a], literal[b]], integerLiteralSum[b, a]]
integerLiteralSum[a_Integer, b_Integer] /; a + b >= 0 :=
	law["integerLiteralDifferenceNonnegative", {naturalLiteral[-b], naturalLiteral[a + b]}, plus[literal[a], literal[b]], literal[a + b]]
integerLiteralSum[a_Integer, b_Integer] :=
	law["integerLiteralDifferenceNegative", {naturalLiteral[a], naturalLiteral[-a - b]}, plus[literal[a], literal[b]], literal[a + b]]

(* x op (y op z) == y op (x op z), from associativity and commutativity *)
leftCommutativity[operation_, associativity_, commutativity_, x_, y_, z_] := chain[
	symmetric[associativity[x, y, z]],
	congruent[Function[hole, operation[hole, z]], commutativity[x, y]],
	associativity[y, x, z]
]


(* ::Subsection:: *)
(*Normal forms*)


ringNormalForm[term_] := $ring["NormalForm"][term]

(* a successor is a sum with 1, and NaturalNumberZero is 0, by computation; Subtract, which stops at 0,
   is no operation of a semiring, so a difference is an atom, and so is a power by a large exponent of
   anything but an atom *)
naturalNormalForm[term_] := Replace[term, {
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

(* A term of integers: a literal, the integer of a natural number literal or its negation, is a constant;
   sums, products and powers by literals carry over; a difference is the sum with the negation by
   computation, and a negation the product with -1; the integer of a sum, product, power or successor of
   natural numbers is that of the integers, and any other term is an atom. *)
integerNormalForm[term_] := Replace[term, {
	application[constantReference[HoldComplete["integerOfNatural"], _], naturalLiteral[0]] :> {{}, reflexive[term]},
	application[constantReference[HoldComplete["integerOfNatural"], _], naturalLiteral[n_Integer]] :> {{{n, {}}}, reflexive[term]},
	application[constantReference[HoldComplete["integerNegation"], _], application[constantReference[HoldComplete["integerOfNatural"], _], naturalLiteral[0]]] :>
		{{}, computed[term, literal[0]]},
	application[constantReference[HoldComplete["integerNegation"], _], application[constantReference[HoldComplete["integerOfNatural"], _], naturalLiteral[n_Integer]]] :>
		{{{-n, {}}}, reflexive[term]},
	application[application[constantReference[HoldComplete["integerAddition"], _], a_], b_] :> sumNormalForm[a, b],
	application[application[constantReference[HoldComplete["integerMultiplication"], _], a_], b_] :> productNormalForm[a, b],
	application[application[constantReference[HoldComplete["integerSubtraction"], _], a_], b_] :> With[{sum = sumNormalForm[a, negation[b]]},
		{First[sum], transitive[computed[term, plus[a, negation[b]]], Last[sum]]}
	],
	application[constantReference[HoldComplete["integerNegation"], _], a_] :> With[{product = productNormalForm[literal[-1], a]},
		{First[product], transitive[law["integerNegationProduct", {a}, term, times[literal[-1], a]], Last[product]]}
	],
	application[application[constantReference[HoldComplete["integerPower"], _], a_], naturalLiteral[k_Integer]] /; k <= $largestRingExponent :> powerNormalForm[a, k],
	application[constantReference[HoldComplete["integerOfNatural"], _], n_] :> castNormalForm[term, n],
	_ :> {{{1, {{term, 1}}}}, reflexive[term]}
}]

(* the integer term of the natural number n *)
castNormalForm[term_, n_] := Replace[n, {
	application[application[constantReference[HoldComplete[Plus], _], a_], b_] :> castThrough[term, law[IntegerOfNaturalAddition, {a, b}, term, plus[integerOfNatural[a], integerOfNatural[b]]]],
	application[application[constantReference[HoldComplete[Times], _], a_], b_] :> castThrough[term, law[IntegerOfNaturalMultiplication, {a, b}, term, times[integerOfNatural[a], integerOfNatural[b]]]],
	application[application[constantReference[HoldComplete[Power], _], a_], naturalLiteral[k_Integer]] /; k <= $largestRingExponent :>
		castThrough[term, law["integerOfNaturalPower", {a, naturalLiteral[k]}, term, power[integerOfNatural[a], naturalLiteral[k]]]],
	application[constantReference[HoldComplete[NaturalNumberSuccessor], _], a_] :>
		castThrough[term, law[IntegerOfNaturalAddition, {a, naturalLiteral[1]}, term, plus[integerOfNatural[a], literal[1]]]],
	constantReference[HoldComplete[NaturalNumberZero], _] :> {{}, computed[term, literal[0]]},
	_ :> {{{1, {{term, 1}}}}, reflexive[term]}
}]

(* the normal form of the right side of the equation, which the left side equals *)
castThrough[term_, equation : {_, right_, _}] := With[{form = ringNormalForm[right]},
	{First[form], transitive[equation, Last[form]]}
]

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
		{{1, {{atom_, 1}}}} /; k == 1 :> {{{1, {{atom, 1}}}}, transitive[congruent[Function[hole, power[hole, exponent[1]]], Last[base]], powerOne[atom]]},
		{{1, {{atom_, 1}}}} :> {{{1, {{atom, k}}}}, congruent[Function[hole, power[hole, exponent[k]]], Last[base]]},
		_ /; k > 32 :> With[{term = power[a, exponent[k]]}, {{{1, {{term, 1}}}}, reflexive[term]}],
		polynomial_ :> With[{raised = polynomialPower[polynomial, k]},
			{First[raised], transitive[congruent[Function[hole, power[hole, exponent[k]]], Last[base]], Last[raised]]}
		]
	}]
]

(* {polynomial, term[A]^k == term[polynomial]}, by k - 1 multiplications *)
polynomialPower[polynomial_List, 1] := {polynomial, powerOne[polynomialTerm[polynomial]]}
polynomialPower[polynomial_List, k_Integer] := With[{lower = polynomialPower[polynomial, k - 1]},
	{product = polynomialProduct[First[lower], polynomial]},
	{First[product], chain[
		powerSuccessor[polynomialTerm[polynomial], exponent[k - 1]],
		congruent[Function[hole, times[hole, polynomialTerm[polynomial]]], Last[lower]],
		Last[product]
	]}
]


(* ::Subsection:: *)
(*Sums*)


(* {C, term[A] + term[B] == term[C]}: A and B merged as two sorted lists are, the first monomial of either
   taken in turn, like monomials added; a step for each monomial, where inserting one at a time would
   take a step for each pair. Like monomials of the integers can cancel, leaving fewer monomials. *)
polynomialSum[{}, second_List] := {second, additionZeroLeft[polynomialTerm[second]]}
polynomialSum[first_List, {}] := {first, additionZeroRight[polynomialTerm[first]]}
polynomialSum[{monomial_}, second_List] := monomialInsertion[monomial, second]
polynomialSum[first_List, {other_}] := With[{inserted = monomialInsertion[other, first]},
	{First[inserted], transitive[additionCommutativity[polynomialTerm[first], monomialTerm[other]], Last[inserted]]}
]
polynomialSum[first : {monomial_, rest__}, second : {other_, others__}] := Which[
	(* (m + R) + (o + S) == (m + o) + (R + S) *)
	Last[monomial] === Last[other],
		With[{merged = likeMonomialSum[monomial, other], inner = polynomialSum[{rest}, {others}]},
			{joined = joinedMonomials[First[merged], First[inner]]},
			{First[joined], chain[
				additionAssociativity[monomialTerm[monomial], polynomialTerm[{rest}], polynomialTerm[second]],
				congruent[
					Function[hole, plus[monomialTerm[monomial], hole]],
					leftCommutativity[plus, additionAssociativity, additionCommutativity, polynomialTerm[{rest}], monomialTerm[other], polynomialTerm[{others}]]
				],
				symmetric[additionAssociativity[monomialTerm[monomial], monomialTerm[other], plus[polynomialTerm[{rest}], polynomialTerm[{others}]]]],
				congruentBoth[plus, Last[merged], Last[inner]],
				Last[joined]
			]}
		],
	(* (m + R) + B == m + (R + B) *)
	monomialBeforeQ[monomial, other],
		With[{inner = polynomialSum[{rest}, second]},
			{prepended = prependedMonomial[monomial, First[inner]]},
			{First[prepended], chain[
				additionAssociativity[monomialTerm[monomial], polynomialTerm[{rest}], polynomialTerm[second]],
				congruent[Function[hole, plus[monomialTerm[monomial], hole]], Last[inner]],
				Last[prepended]
			]}
		],
	(* A + (o + S) == o + (A + S) *)
	True,
		With[{inner = polynomialSum[first, {others}]},
			{prepended = prependedMonomial[other, First[inner]]},
			{First[prepended], chain[
				leftCommutativity[plus, additionAssociativity, additionCommutativity, polynomialTerm[first], monomialTerm[other], polynomialTerm[{others}]],
				congruent[Function[hole, plus[monomialTerm[other], hole]], Last[inner]],
				Last[prepended]
			]}
		]
]

(* {D, term[m] + term[C] == term[D]} *)
monomialInsertion[monomial_, {}] := {{monomial}, additionZeroRight[monomialTerm[monomial]]}
monomialInsertion[monomial_, {next_, rest___}] := Which[
	Last[monomial] === Last[next],
		With[{merged = likeMonomialSum[monomial, next]},
			If[ {rest} === {},
				merged,
				With[{joined = joinedMonomials[First[merged], {rest}]},
					{First[joined], chain[
						symmetric[additionAssociativity[monomialTerm[monomial], monomialTerm[next], polynomialTerm[{rest}]]],
						congruent[Function[hole, plus[hole, polynomialTerm[{rest}]]], Last[merged]],
						Last[joined]
					]}
				]
			]
		],
	monomialBeforeQ[monomial, next],
		{{monomial, next, rest}, reflexive[plus[monomialTerm[monomial], polynomialTerm[{next, rest}]]]},
	{rest} === {},
		{{next, monomial}, additionCommutativity[monomialTerm[monomial], monomialTerm[next]]},
	True,
		With[{inner = monomialInsertion[monomial, {rest}]},
			{prepended = prependedMonomial[next, First[inner]]},
			{First[prepended], chain[
				leftCommutativity[plus, additionAssociativity, additionCommutativity, monomialTerm[monomial], monomialTerm[next], polynomialTerm[{rest}]],
				congruent[Function[hole, plus[monomialTerm[next], hole]], Last[inner]],
				Last[prepended]
			]}
		]
]

(* {D, term[m] + term[C] == term[D]} for a monomial m before those of C: m alone where C is empty *)
prependedMonomial[monomial_, {}] := {{monomial}, additionZeroRight[monomialTerm[monomial]]}
prependedMonomial[monomial_, polynomial_List] := {Prepend[polynomial, monomial], reflexive[plus[monomialTerm[monomial], polynomialTerm[polynomial]]]}

(* {D, term[L] + term[C] == term[D]} for L no monomial or one before those of C *)
joinedMonomials[{}, polynomial_List] := {polynomial, additionZeroLeft[polynomialTerm[polynomial]]}
joinedMonomials[{monomial_}, polynomial_List] := prependedMonomial[monomial, polynomial]

(* {L, c1 x... + c2 x... == term[L]}, L the monomial (c1 + c2) x..., by distributivity, with the coefficient
   1 shown first; or no monomial, where the coefficients of the integers cancel *)
likeMonomialSum[{first_Integer, {}}, {second_Integer, {}}] := {If[first + second == 0, {}, {{first + second, {}}}], $ring["LiteralSum"][first, second]}
likeMonomialSum[{first_Integer, factors : {__}}, {second_Integer, factors : {__}}] := With[{product = productTerm[factors]},
	{If[first + second == 0, {}, {{first + second, factors}}], chain[
		congruentBoth[plus, coefficientShown[first, product], coefficientShown[second, product]],
		symmetric[distributivityRight[literal[first], literal[second], product]],
		congruent[Function[hole, times[hole, product]], $ring["LiteralSum"][first, second]],
		If[first + second == 0, multiplicationZeroLeft[product], coefficientHidden[first + second, product]]
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
	symmetric[powerAddition[atom, exponent[first], exponent[second]]],
	computed[power[atom, exponentSum[exponent[first], exponent[second]]], power[atom, exponent[first + second]]]
]}

exponentShown[atom_, 1] := symmetric[powerOne[atom]]
exponentShown[atom_, k_Integer] := reflexive[power[atom, exponent[k]]]
