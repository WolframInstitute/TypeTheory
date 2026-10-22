(* ::Package:: *)

(*
Sums of squares: certificates that a polynomial with integer coefficients is at least 0 for all values of
its variables.

A certificate of f is {d, {{c1, g1}, ...}}, with d f == c1 g1^2 + ..., d and the ci positive integers and
the gi polynomials with integer coefficients. Wolfram finds it as SOS tools do: f is m . Q . m for the
vector m of the monomials that can occur in the gi and a symmetric matrix Q, its Gram matrix, whose
entries add up to the coefficients of f, and f is a sum of squares when one such Q is positive
semidefinite. The monomials are those with half the exponents of f, in the box and the degrees they span,
less those whose squares f cannot have. The equations of the coefficients are solved exactly; where they
leave Q free, SemidefiniteOptimization finds a Q as far inside the positive semidefinite ones as it can,
which is rounded to rationals. An exact decomposition Q = L . D . Transpose[L], D diagonal and at least
0, gives f as the sum of the D[[k]] ((Transpose[L] . m)[[k]])^2, and d clears the denominators.

Nothing here is trusted: the tactic "SumOfSquares" proves d f == c1 g1^2 + ... by "Ring", and the kernel
checks the proof.
*)


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[sumOfSquaresCertificate]


(* ::Section:: *)
(*Usage Messages*)


sumOfSquaresCertificate::usage = "sumOfSquaresCertificate[f, {x1, x2, ...}] gives {d, {{c1, g1}, ...}} with d f == c1 g1^2 + ... for a polynomial f with integer \
coefficients in the variables, d and the ci positive integers and the gi polynomials with integer coefficients, or None if Wolfram finds no sum of squares."


(* ::Section:: *)
(*Function Definitions*)


(* a larger basis makes the semidefinite problem too large to solve in good time *)
$largestSquareBasis = 60

sumOfSquaresCertificate[f_, variables_List] := With[{polynomial = Expand[f]},
	Which[
		polynomial === 0,
			{1, {}},
		! PolynomialQ[polynomial, variables] || ! AllTrue[Last /@ CoefficientRules[polynomial, variables], IntegerQ],
			None,
		True,
			With[{basis = monomialBasis[Keys[CoefficientRules[polynomial, variables]]]},
				If[ basis === {} || Length[basis] > $largestSquareBasis,
					None,
					Replace[gramMatrix[polynomial, variables, basis], matrix_List :> certificateOfGramMatrix[polynomial, variables, basis, matrix]]
				]
			]
	]
]


(* ::Subsection:: *)
(*Monomials*)


(* the exponents of the monomials that can occur in the squares: half those of f, in their box and in the
   total degrees they span *)
monomialBasis[support_List] := With[{degrees = Total /@ support},
	prunedBasis[
		Select[
			Tuples[MapThread[Range, {Ceiling[Min /@ Transpose[support] / 2], Floor[Max /@ Transpose[support] / 2]}]],
			Function[exponents, Ceiling[Min[degrees] / 2] <= Total[exponents] <= Floor[Max[degrees] / 2]]
		],
		support
	]
]

(* a monomial whose square f lacks, and that is no product of two others of the basis, has 0 on the
   diagonal, so 0 in its row of a positive semidefinite Q: it is left out, until no other is *)
prunedBasis[basis_List, support_List] := With[
	{
		kept = Select[basis, Function[exponents, Or[
			MemberQ[support, 2 exponents],
			AnyTrue[basis, Function[other, other =!= exponents && MemberQ[basis, 2 exponents - other]]]
		]]]
	},
	If[kept === basis, basis, prunedBasis[kept, support]]
]


(* ::Subsection:: *)
(*Gram matrices*)


(* the positions on and above the diagonal of an n by n matrix, row by row *)
upperEntries[n_Integer] := Catenate[Table[{i, j}, {i, n}, {j, i, n}]]

symmetricMatrix[values_List, n_Integer] := With[{index = AssociationThread[upperEntries[n], values]},
	Table[index[Sort[{i, j}]], {i, n}, {j, n}]
]

(* a positive semidefinite Gram matrix of rationals, or None: the entries on and above the diagonal are
   the unknowns, and the coefficient of each product of two monomials is an equation, an entry off the
   diagonal counting twice *)
gramMatrix[polynomial_, variables_List, basis_List] := Module[{entries, monomialOf, exponents, coefficients, products, equationOf, equations, particular},
	entries = upperEntries[Length[basis]];
	monomialOf = AssociationThread[Range[Length[basis]], basis];
	exponents = Function[entry, Total[Lookup[monomialOf, entry]]] /@ entries;
	coefficients = Association[CoefficientRules[polynomial, variables]];
	products = DeleteDuplicates[Join[Keys[coefficients], exponents]];
	equationOf = AssociationThread[products, Range[Length[products]]];
	equations = SparseArray[
		MapThread[
			Function[{entry, product, unknown}, {equationOf[product], unknown} -> If[First[entry] == Last[entry], 1, 2]],
			{entries, exponents, Range[Length[entries]]}
		],
		{Length[products], Length[entries]}
	];
	particular = Quiet[LinearSolve[equations, Lookup[coefficients, Key /@ products, 0]], {LinearSolve::nosol}];
	If[VectorQ[particular], semidefiniteMember[Normal[particular], Normal /@ NullSpace[equations], Length[basis]], None]
]

(* a positive semidefinite matrix of particular + t . nullSpace for rationals t, or None *)
semidefiniteMember[particular_List, {}, n_Integer] := With[{matrix = symmetricMatrix[particular, n]},
	If[squareDecomposition[matrix] === None, None, matrix]
]
semidefiniteMember[particular_List, nullSpace_List, n_Integer] := With[{atZero = symmetricMatrix[particular, n]},
	If[ squareDecomposition[atZero] =!= None,
		atZero,
		roundedMember[particular, nullSpace, n, interiorParameters[particular, nullSpace, n]]
	]
]

(* {t, lambda}: parameters t with the matrix of particular + t . nullSpace, less lambda times the
   identity, positive semidefinite, lambda as large as SemidefiniteOptimization finds and at most 1; or
   None. The last block of each matrix bounds lambda. *)
interiorParameters[particular_List, nullSpace_List, n_Integer] := With[
	{
		block = Function[{matrix, corner}, ArrayFlatten[{{matrix, 0}, {0, {{corner}}}}]],
		parameterCount = Length[nullSpace]
	},
	Replace[
		Quiet @ TimeConstrained[
			SemidefiniteOptimization[
				Append[ConstantArray[0, parameterCount], -1],
				Join[
					{N @ block[symmetricMatrix[particular, n], 1]},
					Function[vector, N @ block[symmetricMatrix[vector, n], 0]] /@ nullSpace,
					{N @ block[-IdentityMatrix[n], -1]}
				]
			],
			30
		],
		{
			solution_List /; VectorQ[solution, NumericQ] && Length[solution] == parameterCount + 1 :> solution,
			_ :> None
		}
	]
]

(* the parameters rounded to rationals, each more closely than the last, until the matrix is positive
   semidefinite *)
roundedMember[_, _, _, None] := None
roundedMember[particular_List, nullSpace_List, n_Integer, solution_List] := FirstCase[
	10. ^ -Range[2, 12],
	tolerance_ :> With[{matrix = symmetricMatrix[particular + Rationalize[Most[solution], tolerance] . nullSpace, n]},
		matrix /; squareDecomposition[matrix] =!= None
	],
	None
]


(* ::Subsection:: *)
(*Squares*)


(* {{p1, l1}, ...}, each p > 0 and l a vector of rationals, with the matrix the sum of the p l l^T: the
   LDL^T decomposition, for a positive semidefinite matrix of rationals, or None if it is not one. Each
   step takes out the first row, whose first entry is the pivot, and goes on with the rest of the matrix
   less the part of that row; a pivot of 0 must have a row of 0s. The offset counts the rows taken out. *)
squareDecomposition[matrix_List] := decompositionSteps[matrix, 0, {}]

decompositionSteps[{}, _Integer, factors_List] := factors
decompositionSteps[matrix_List, offset_Integer, factors_List] := With[{row = First[matrix]},
	Which[
		First[row] < 0,
			None,
		First[row] == 0,
			If[AllTrue[row, Function[entry, entry == 0]], decompositionSteps[Rest /@ Rest[matrix], offset + 1, factors], None],
		True,
			decompositionSteps[
				Rest /@ Rest[matrix - Outer[Times, row, row] / First[row]],
				offset + 1,
				Append[factors, {First[row], Join[ConstantArray[0, offset], row / First[row]]}]
			]
	]
]

(* each p (l . m)^2 is w g^2 for g with coprime integer coefficients, and d the denominators of the w
   cleared; the sum is checked before it is given *)
certificateOfGramMatrix[polynomial_, variables_List, basis_List, matrix_List] := Module[{monomials, weighted, scale, squares},
	monomials = Function[exponents, Times @@ (variables ^ exponents)] /@ basis;
	weighted = Function[factor, With[{denominator = LCM @@ Denominator[Last[factor]]},
		{content = GCD @@ (denominator Last[factor])},
		{First[factor] content ^ 2 / denominator ^ 2, Expand[(denominator / content) Last[factor] . monomials]}
	]] /@ squareDecomposition[matrix];
	scale = LCM @@ Denominator[First /@ weighted];
	squares = Function[pair, {scale First[pair], Last[pair]}] /@ weighted;
	If[Expand[scale polynomial - Total[Function[pair, First[pair] Last[pair] ^ 2] /@ squares]] === 0, {scale, squares}, None]
]
