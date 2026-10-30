(* ::Package:: *)

(*
The compiled kernel: the type checking, reduction and definitional equality of TypeChecking.wl, compiled with
FunctionCompile over terms interned as integers. TypeTheoryCheck checks an environment with it about a hundred
times faster than with the kernel of TypeChecking.wl; it is the same algorithm, one function for each of its
functions, in the same order of cases, so the two accept the same declarations.

A term is an id into one FixedArray, the memory, which holds:

	nodes                 six cells each: a tag, three fields, the loose bound range and flags (free variables,
	                      universe parameters), interned in an open-addressing table, so that structurally equal
	                      terms are one id and comparing terms is comparing ids
	universe levels       four cells each, interned in their canonical form (CoreTerms.wl's normalizeLevel), so
	                      that equivalent levels are one id
	constants             a row each: kind, type, value, universe parameters, height, hint, and the counts and
	                      tables of inductive types, constructors and recursors
	caches                weak head normal forms with and without unfolding, and types inferred with and without
	                      checking, each indexed by id; a union-find of the definitional equalities found, and a
	                      table of the ones refuted
	the memo              of substitution, lifting, abstraction and universe instantiation, so that each walks
	                      every distinct subterm once a call
	the local context     the type, and the value of a local definition, of every free variable
	the stack             spines and level components

Every function takes the memory first and integers after, and gives an integer: an id, 1 or 0 for a question, and
0 for failure, after setting the memory's status to the reason. Recursion is counted, so a term too deep to check
in compiled code is refused rather than overflowing the stack, and no arithmetic can overflow, which would leave
compiled code.

What it checks: that the type of every axiom, definition, theorem, hole and quotient constant is a type, that the
value of every definition and theorem has its type, that a theorem's statement is a proposition, that every
universe parameter a declaration mentions is one of its own, that every constant it mentions is declared before
it, and that a definition's height and hint are the ones its value gives. Inductive types, with the constructors
and recursors they generate, and the quotient types' declaration are checked by the kernel of InductiveTypes.wl
and Quotients.wl, afterwards (TypeTheoryCheck in Queries.wl).

What it handles: environments under rules with Prop and without rewrite rules, quantities or cubical type theory,
whose natural number literals are below 2^62 and whose terms are not too deep. For any other, compiledKernelCheck
gives None and TypeTheoryCheck replays the environment with the kernel of TypeChecking.wl.

The library is compiled once for each platform and version of the Wolfram Language by scripts/compile_kernel.wls,
which writes LibraryResources/<$SystemID>/TypeTheoryKernel with the hash of the program beside it; release.wls
builds it for the archive. Without a library whose hash is the program's, TypeTheoryCheck uses the kernel of
TypeChecking.wl.
*)


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[compiledKernelCheck]
PackageScoped[compiledKernelAvailableQ]
PackageScoped[compileKernelLibrary]


(* ::Section:: *)
(*Usage Messages*)


compiledKernelCheck::usage = "compiledKernelCheck[environment] or compiledKernelCheck[environment, trusted], its first trusted constants taken as they are, checks the declarations of environment with the compiled kernel, all but inductive types, \
their constructors and recursors, and quotient types, and gives a Success, the Failure of the first declaration that does not check, whose \"Position\" \
is that declaration's, or None where the compiled kernel does not handle the environment or no library is available."
compiledKernelAvailableQ::usage = "compiledKernelAvailableQ[] gives True if the compiled kernel's library for this platform and version is available."
compileKernelLibrary::usage = "compileKernelLibrary[] compiles the kernel's library into LibraryResources/<$SystemID> of the paclet and gives its File."


(* ::Section:: *)
(*Function Definitions*)


(* ::Subsection:: *)
(*The program*)


(* the layout of the memory, the tags of terms and levels, the kinds of constants, the columns of a constant's
   row, the reasons for failure, put into the program before it is compiled *)
$codeConstants = {
	hCap -> 1, hNodes -> 2, hNodeBase -> 3, hTableBase -> 4, hTableMask -> 5,
	hLevelBase -> 6, hLevels -> 7, hLevelCap -> 8, hLevelTableBase -> 9, hLevelTableMask -> 10,
	hConstBase -> 11, hConsts -> 12,
	hWhnfBase -> 13, hCoreBase -> 14, hInferBase -> 15, hInferOnlyBase -> 16, hParentBase -> 17,
	hFailBase -> 18, hFailMask -> 19,
	hMemoBase -> 20, hMemoMask -> 21, hGen -> 22,
	hLctxBase -> 23, hLctx -> 24, hLctxCap -> 25,
	hStackBase -> 26, hStackTop -> 27, hStackCap -> 28,
	hStatus -> 29, hDetail -> 30,
	hFlatBase -> 31, hFlatCount -> 32,
	hNatType -> 33, hNatZero -> 34, hNatSucc -> 35, hZeroNode -> 36, hSuccNode -> 37, hNatNode -> 38,
	hDepth -> 39, hDepthLimit -> 40,
	hUnivBase -> 41, hUnivMask -> 42,
	hLevelZero -> 43, hLevelNil -> 44, hLevelOne -> 45,
	hMaxDepth -> 46, hMaxStack -> 47, hDefeqCalls -> 48, hWhnfCalls -> 49, hInferCalls -> 50,
	hMarkBase -> 51, hMarkGen -> 52, hCurrent -> 53, hLazyX -> 54, hLazyY -> 55, hFailA -> 56, hFailB -> 57, hFailTerm -> 58,
	hHeaderSize -> 64,
	tBVar -> 1, tSort -> 2, tConst -> 3, tApp -> 4, tLam -> 5, tPi -> 6, tLet -> 7, tLit -> 8, tProj -> 9, tFVar -> 10,
	lConst -> 1, lParam -> 2, lSucc -> 3, lMax -> 4, lIMax -> 5, lCons -> 6, lNil -> 7,
	kAxiom -> 1, kDefinition -> 2, kTheorem -> 3, kOpaque -> 4, kInductive -> 5, kConstructor -> 6, kRecursor -> 7, kQuotient -> 8, kHole -> 9,
	cWidth -> 20, cKind -> 1, cType -> 2, cValue -> 3, cParams -> 4, cNumParams -> 5, cHeight -> 6, cHint -> 7,
	cA -> 8, cB -> 9, cC -> 10, cD -> 11, cE -> 12, cF -> 13, cG -> 14, cH -> 15, cI -> 16, cNatRole -> 17, cBoolFalse -> 18, cBoolTrue -> 19, cDeclared -> 20,
	eMismatch -> 1, eNotType -> 2, eNotFunction -> 3, eNotProp -> 4, eLooseBVar -> 5, eArity -> 6, eUnknownConstant -> 7, eProjType -> 8, eProjIndex -> 9,
	eProjProof -> 10, eUndeclaredParam -> 11, eIllFormed -> 12, eDeclarationMismatch -> 13,
	eUnsupported -> 20, eDepth -> 21, eCapacity -> 22, eStack -> 23, eLevelCapacity -> 24, eLctxCapacity -> 25, eLiteralOverflow -> 26,
	mask40 -> 1099511627775, litLimit -> 4611686018427387904
}

SetAttributes[kfn, HoldAll]

$program = Hold[{

	(* ::Subsection:: *)
	(* Memory, status, depth and stack *)

	kfn[arenaFail, Function[{m, code}, If[m["Part", hStatus] == 0, m["SetPart", hStatus, code]]; 0]],
	kfn[arenaFailed, Function[{m}, If[m["Part", hStatus] != 0, 1, 0]]],
	kfn[arenaEnter, Function[{m}, Module[{d = m["Part", hDepth] + 1},
		m["SetPart", hDepth, d];
		If[d > m["Part", hMaxDepth], m["SetPart", hMaxDepth, d]];
		If[d > m["Part", hDepthLimit], arenaFail[m, eDepth]; 0, 1]
	]]],
	kfn[arenaLeave, Function[{m, result}, m["SetPart", hDepth, m["Part", hDepth] - 1]; result]],
	kfn[arenaStackGet, Function[{m, i}, m["Part", m["Part", hStackBase] + 1 + i]]],
	kfn[arenaStackSet, Function[{m, i, v}, m["SetPart", m["Part", hStackBase] + 1 + i, v]; v]],
	kfn[arenaReserve, Function[{m, n}, Module[{top = m["Part", hStackTop]},
		If[top + n > m["Part", hStackCap], Return[arenaFail[m, eStack] - 1]];
		m["SetPart", hStackTop, top + n];
		If[top + n > m["Part", hMaxStack], m["SetPart", hMaxStack, top + n]];
		top
	]]],
	kfn[arenaRestore, Function[{m, top}, m["SetPart", hStackTop, top]; top]],

	(* ::Subsection:: *)
	(* Nodes *)

	kfn[arenaNodeAt, Function[{m, id, j}, m["Part", m["Part", hNodeBase] + 6 id - 6 + j]]],
	kfn[arenaTagOf, Function[{m, id}, If[id < 1, 0, arenaNodeAt[m, id, 1]]]],
	kfn[arenaF1Of, Function[{m, id}, If[id < 1, 0, arenaNodeAt[m, id, 2]]]],
	kfn[arenaF2Of, Function[{m, id}, If[id < 1, 0, arenaNodeAt[m, id, 3]]]],
	kfn[arenaF3Of, Function[{m, id}, If[id < 1, 0, arenaNodeAt[m, id, 4]]]],
	kfn[arenaRangeOf, Function[{m, id}, If[id < 1, 0, arenaNodeAt[m, id, 5]]]],
	kfn[arenaFlagsOf, Function[{m, id}, If[id < 1, 0, arenaNodeAt[m, id, 6]]]],
	kfn[arenaMkNode, Function[{m, tag, a, b, c}, Module[
		{mask = m["Part", hTableMask], base = m["Part", hTableBase], h = 0, id = 0, n = 0, range = 0, flags = 0, cell = 0},
		h = BitAnd[tag * 1000003 + BitAnd[a, mask40], mask40];
		h = BitAnd[h * 1000003 + BitAnd[b, mask40], mask40];
		h = BitAnd[h * 1000003 + BitAnd[c, mask40], mask40];
		h = BitAnd[BitXor[h, BitShiftRight[h, 17]], mask];
		While[True,
			id = m["Part", base + 1 + h];
			If[id == 0, Break[]];
			If[arenaNodeAt[m, id, 1] == tag && arenaNodeAt[m, id, 2] == a && arenaNodeAt[m, id, 3] == b && arenaNodeAt[m, id, 4] == c, Return[id]];
			h = BitAnd[h + 1, mask]
		];
		n = m["Part", hNodes] + 1;
		If[n > m["Part", hCap], Return[arenaFail[m, eCapacity]]];
		Which[
			tag == tBVar, range = a + 1; flags = 0,
			tag == tSort, range = 0; flags = If[BitAnd[arenaLevelFlags[m, a], 1] == 1, 2, 0],
			tag == tConst, range = 0; flags = If[BitAnd[arenaLevelFlags[m, b], 1] == 1, 2, 0],
			tag == tApp, range = Max[arenaRangeOf[m, a], arenaRangeOf[m, b]]; flags = BitOr[arenaFlagsOf[m, a], arenaFlagsOf[m, b]],
			tag == tLam || tag == tPi, range = Max[arenaRangeOf[m, a], arenaRangeOf[m, b] - 1, 0]; flags = BitOr[arenaFlagsOf[m, a], arenaFlagsOf[m, b]],
			tag == tLet, range = Max[arenaRangeOf[m, a], arenaRangeOf[m, b], arenaRangeOf[m, c] - 1, 0]; flags = BitOr[BitOr[arenaFlagsOf[m, a], arenaFlagsOf[m, b]], arenaFlagsOf[m, c]],
			tag == tProj, range = arenaRangeOf[m, c]; flags = arenaFlagsOf[m, c],
			tag == tFVar, range = 0; flags = 1,
			True, range = 0; flags = 0
		];
		cell = m["Part", hNodeBase] + 6 n - 6;
		m["SetPart", cell + 1, tag];
		m["SetPart", cell + 2, a];
		m["SetPart", cell + 3, b];
		m["SetPart", cell + 4, c];
		m["SetPart", cell + 5, range];
		m["SetPart", cell + 6, flags];
		m["SetPart", base + 1 + h, n];
		m["SetPart", hNodes, n];
		n
	]]],
	kfn[arenaMkApp, Function[{m, f, a}, If[f < 1 || a < 1, 0, arenaMkNode[m, tApp, f, a, 0]]]],
	kfn[arenaMkBinder, Function[{m, tag, d, b}, If[d < 1 || b < 1, 0, arenaMkNode[m, tag, d, b, 0]]]],
	kfn[arenaMkLet, Function[{m, t, v, b}, If[t < 1 || v < 1 || b < 1, 0, arenaMkNode[m, tLet, t, v, b]]]],
	kfn[arenaMkProj, Function[{m, s, i, t}, If[t < 1, 0, arenaMkNode[m, tProj, s, i, t]]]],
	kfn[arenaMkConst, Function[{m, c, ls}, If[ls < 1, 0, arenaMkNode[m, tConst, c, ls, 0]]]],

	(* ::Subsection:: *)
	(* Universe levels, canonical: a component, or a maximum of components sorted by base, as TypeTheory's normalizeLevel *)

	kfn[arenaLevelAt, Function[{m, l, j}, m["Part", m["Part", hLevelBase] + 4 l - 4 + j]]],
	kfn[arenaLtagOf, Function[{m, l}, If[l < 1, 0, arenaLevelAt[m, l, 1]]]],
	kfn[arenaLa, Function[{m, l}, If[l < 1, 0, arenaLevelAt[m, l, 2]]]],
	kfn[arenaLb, Function[{m, l}, If[l < 1, 0, arenaLevelAt[m, l, 3]]]],
	kfn[arenaLevelFlags, Function[{m, l}, If[l < 1, 0, arenaLevelAt[m, l, 4]]]],
	kfn[arenaMkLevel, Function[{m, tag, a, b}, Module[
		{mask = m["Part", hLevelTableMask], base = m["Part", hLevelTableBase], h = 0, id = 0, n = 0, flags = 0, cell = 0},
		h = BitAnd[tag * 1000003 + BitAnd[a, mask40], mask40];
		h = BitAnd[h * 1000003 + BitAnd[b, mask40], mask40];
		h = BitAnd[BitXor[h, BitShiftRight[h, 17]], mask];
		While[True,
			id = m["Part", base + 1 + h];
			If[id == 0, Break[]];
			If[arenaLevelAt[m, id, 1] == tag && arenaLevelAt[m, id, 2] == a && arenaLevelAt[m, id, 3] == b, Return[id]];
			h = BitAnd[h + 1, mask]
		];
		n = m["Part", hLevels] + 1;
		If[n > m["Part", hLevelCap], Return[arenaFail[m, eLevelCapacity]]];
		flags = Which[
			tag == lParam, 1,
			tag == lSucc, arenaLevelFlags[m, a],
			tag == lMax || tag == lIMax || tag == lCons, BitOr[arenaLevelFlags[m, a], arenaLevelFlags[m, b]],
			True, 0
		];
		cell = m["Part", hLevelBase] + 4 n - 4;
		m["SetPart", cell + 1, tag];
		m["SetPart", cell + 2, a];
		m["SetPart", cell + 3, b];
		m["SetPart", cell + 4, flags];
		m["SetPart", base + 1 + h, n];
		m["SetPart", hLevels, n];
		n
	]]],
	(* the components of canonical l, each {base, offset} with base 0 for a constant, extra added to each offset, pushed on the stack *)
	kfn[arenaPushComponents, Function[{m, l, extra}, Module[{t = arenaLtagOf[m, l], s = 0},
		Which[
			t == lMax, arenaPushComponents[m, arenaLa[m, l], extra] + arenaPushComponents[m, arenaLb[m, l], extra],
			t == lConst || t == lParam || t == lIMax || t == lSucc,
				s = arenaReserve[m, 2];
				If[s < 0, Return[0]];
				Which[
					t == lConst, arenaStackSet[m, s, 0]; arenaStackSet[m, s + 1, arenaLa[m, l] + extra],
					t == lSucc, arenaStackSet[m, s, arenaLa[m, l]]; arenaStackSet[m, s + 1, arenaLb[m, l] + extra],
					True, arenaStackSet[m, s, l]; arenaStackSet[m, s + 1, extra]
				];
				1,
			True, 0
		]
	]]],
	(* the canonical level of the count components on the stack from start, as CoreTerms.wl's mergeComponents and fromComponents *)
	kfn[arenaFromComponents, Function[{m, start, count}, Module[{constant = 0, i = 0, j = 0, q = 0, kept = 0, b = 0, o = 0, keepConstant = 1, result = 0, k = 0},
		Do[If[arenaStackGet[m, start + 2 i] == 0, constant = Max[constant, arenaStackGet[m, start + 2 i + 1]]], {i, 0, count - 1}];
		Do[
			b = arenaStackGet[m, start + 2 i];
			o = arenaStackGet[m, start + 2 i + 1];
			If[b != 0,
				j = 0;
				While[j < kept && arenaStackGet[m, start + 2 j] < b, j++];
				If[j < kept && arenaStackGet[m, start + 2 j] == b,
					If[o > arenaStackGet[m, start + 2 j + 1], arenaStackSet[m, start + 2 j + 1, o]],
					Do[arenaStackSet[m, start + 2 q, arenaStackGet[m, start + 2 q - 2]]; arenaStackSet[m, start + 2 q + 1, arenaStackGet[m, start + 2 q - 1]], {q, kept, j + 1, -1}];
					arenaStackSet[m, start + 2 j, b];
					arenaStackSet[m, start + 2 j + 1, o];
					kept++
				]
			],
			{i, 0, count - 1}
		];
		Do[If[arenaStackGet[m, start + 2 i + 1] >= constant, keepConstant = 0], {i, 0, kept - 1}];
		Do[
			b = arenaStackGet[m, start + 2 i];
			o = arenaStackGet[m, start + 2 i + 1];
			k = If[o == 0, b, arenaMkLevel[m, lSucc, b, o]];
			result = If[result == 0, k, arenaMkLevel[m, lMax, k, result]],
			{i, kept - 1, 0, -1}
		];
		If[keepConstant == 1,
			k = arenaMkLevel[m, lConst, constant, 0];
			result = If[result == 0, k, arenaMkLevel[m, lMax, k, result]]
		];
		result
	]]],
	kfn[arenaLevelSucc, Function[{m, l, k}, Module[{top = m["Part", hStackTop], count = 0, r = 0},
		If[k == 0, Return[l]];
		count = arenaPushComponents[m, l, k];
		r = arenaFromComponents[m, top, count];
		arenaRestore[m, top];
		r
	]]],
	kfn[arenaLevelMax, Function[{m, a, b}, Module[{top = m["Part", hStackTop], count = 0, r = 0},
		If[a == b, Return[a]];
		count = arenaPushComponents[m, a, 0];
		count = count + arenaPushComponents[m, b, 0];
		r = arenaFromComponents[m, top, count];
		arenaRestore[m, top];
		r
	]]],
	kfn[arenaLevelNeverZero, Function[{m, l}, Module[{t = arenaLtagOf[m, l]},
		Which[
			t == lConst, If[arenaLa[m, l] > 0, 1, 0],
			t == lSucc, If[arenaLb[m, l] > 0, 1, 0],
			t == lMax, If[arenaLevelNeverZero[m, arenaLa[m, l]] == 1, 1, arenaLevelNeverZero[m, arenaLb[m, l]]],
			True, 0
		]
	]]],
	(* the largest constant or offset among the components of b *)
	kfn[arenaLevelFloor, Function[{m, b}, Module[{t = arenaLtagOf[m, b]},
		Which[
			t == lConst, arenaLa[m, b],
			t == lSucc, arenaLb[m, b],
			t == lMax, Max[arenaLevelFloor[m, arenaLa[m, b]], arenaLevelFloor[m, arenaLb[m, b]]],
			True, 0
		]
	]]],
	kfn[arenaHasComponent, Function[{m, b, base, offset}, Module[{t = arenaLtagOf[m, b]},
		Which[
			t == lParam || t == lIMax, If[b == base && offset <= 0, 1, 0],
			t == lSucc, If[arenaLa[m, b] == base && arenaLb[m, b] >= offset, 1, 0],
			t == lMax, If[arenaHasComponent[m, arenaLa[m, b], base, offset] == 1, 1, arenaHasComponent[m, arenaLb[m, b], base, offset]],
			True, 0
		]
	]]],
	kfn[arenaComponentLessEqual, Function[{m, base, offset, b},
		Which[
			base == 0, If[offset <= arenaLevelFloor[m, b], 1, 0],
			arenaHasComponent[m, b, base, offset] == 1, 1,
			arenaLtagOf[m, base] == lIMax,
				If[arenaLevelLessEqual[m, arenaLevelSucc[m, arenaLa[m, base], offset], b] == 1, arenaLevelLessEqual[m, arenaLevelSucc[m, arenaLb[m, base], offset], b], 0],
			True, 0
		]
	]],
	kfn[arenaLevelLessEqual, Function[{m, a, b}, Module[{t = arenaLtagOf[m, a]},
		Which[
			t == lConst, arenaComponentLessEqual[m, 0, arenaLa[m, a], b],
			t == lParam || t == lIMax, arenaComponentLessEqual[m, a, 0, b],
			t == lSucc, arenaComponentLessEqual[m, arenaLa[m, a], arenaLb[m, a], b],
			t == lMax, If[arenaLevelLessEqual[m, arenaLa[m, a], b] == 1, arenaLevelLessEqual[m, arenaLb[m, a], b], 0],
			True, 0
		]
	]]],
	kfn[arenaLevelIMax, Function[{m, a, b},
		Which[
			arenaLtagOf[m, b] == lConst && arenaLa[m, b] == 0, b,
			arenaLevelNeverZero[m, b] == 1, arenaLevelMax[m, a, b],
			arenaLevelLessEqual[m, a, arenaLevelMax[m, b, m["Part", hLevelOne]]] == 1, b,
			True, arenaMkLevel[m, lIMax, a, b]
		]
	]],
	kfn[arenaParamValue, Function[{m, p, params, levels}, Module[{ps = params, ls = levels},
		While[arenaLtagOf[m, ps] == lCons,
			If[arenaLa[m, ps] == p, Return[If[arenaLtagOf[m, ls] == lCons, arenaLa[m, ls], p]]];
			ps = arenaLb[m, ps];
			ls = arenaLb[m, ls]
		];
		p
	]]],
	kfn[arenaInstLevel, Function[{m, l, params, levels}, Module[{t = arenaLtagOf[m, l]},
		If[BitAnd[arenaLevelFlags[m, l], 1] == 0, Return[l]];
		Which[
			t == lParam, arenaParamValue[m, l, params, levels],
			t == lSucc, arenaLevelSucc[m, arenaInstLevel[m, arenaLa[m, l], params, levels], arenaLb[m, l]],
			t == lIMax, arenaLevelIMax[m, arenaInstLevel[m, arenaLa[m, l], params, levels], arenaInstLevel[m, arenaLb[m, l], params, levels]],
			t == lMax, arenaLevelMax[m, arenaInstLevel[m, arenaLa[m, l], params, levels], arenaInstLevel[m, arenaLb[m, l], params, levels]],
			t == lCons, arenaMkLevel[m, lCons, arenaInstLevel[m, arenaLa[m, l], params, levels], arenaInstLevel[m, arenaLb[m, l], params, levels]],
			True, l
		]
	]]],
	kfn[arenaLevelListLength, Function[{m, ls}, Module[{x = ls, k = 0}, While[arenaLtagOf[m, x] == lCons, k++; x = arenaLb[m, x]]; k]]],

	(* ::Subsection:: *)
	(* Memo of the walks, by generation; the universe instantiation cache; the failure table; union-find *)

	kfn[arenaNewGen, Function[{m}, Module[{g = m["Part", hGen] + 1}, m["SetPart", hGen, g]; g]]],
	(* the slot holding the keys in generation gen as 1 + h, or the free slot for them as -1 - h, or 0 *)
	kfn[arenaMemoSlot, Function[{m, k1, k2, gen}, Module[{mask = m["Part", hMemoMask], base = m["Part", hMemoBase], h = 0, cell = 0},
		h = BitAnd[BitAnd[k1, mask40] * 1000003 + BitAnd[k2, mask40], mask40];
		h = BitAnd[BitXor[h, BitShiftRight[h, 15]], mask];
		Do[
			cell = base + 4 h;
			If[m["Part", cell + 3] != gen, Return[-1 - h]];
			If[m["Part", cell + 1] == k1 && m["Part", cell + 2] == k2, Return[1 + h]];
			h = BitAnd[h + 1, mask],
			{64}
		];
		0
	]]],
	kfn[arenaMemoValue, Function[{m, slot}, m["Part", m["Part", hMemoBase] + 4 (slot - 1) + 4]]],
	kfn[arenaMemoStore, Function[{m, slot, k1, k2, gen, v}, Module[{cell = 0},
		If[slot < 0,
			cell = m["Part", hMemoBase] + 4 (-1 - slot);
			m["SetPart", cell + 1, k1];
			m["SetPart", cell + 2, k2];
			m["SetPart", cell + 3, gen];
			m["SetPart", cell + 4, v]
		];
		v
	]]],
	kfn[arenaUnivSlot, Function[{m, k1, k2, k3}, Module[{mask = m["Part", hUnivMask], base = m["Part", hUnivBase], h = 0, cell = 0},
		h = BitAnd[BitAnd[k1, mask40] * 1000003 + BitAnd[k2, mask40], mask40];
		h = BitAnd[h * 1000003 + BitAnd[k3, mask40], mask40];
		h = BitAnd[BitXor[h, BitShiftRight[h, 15]], mask];
		Do[
			cell = base + 4 h;
			If[m["Part", cell + 1] == 0, Return[-1 - h]];
			If[m["Part", cell + 1] == k1 && m["Part", cell + 2] == k2 && m["Part", cell + 3] == k3, Return[1 + h]];
			h = BitAnd[h + 1, mask],
			{64}
		];
		0
	]]],
	kfn[arenaUnivValue, Function[{m, slot}, m["Part", m["Part", hUnivBase] + 4 (slot - 1) + 4]]],
	kfn[arenaUnivStore, Function[{m, slot, k1, k2, k3, v}, Module[{cell = 0},
		If[slot < 0 && v > 0,
			cell = m["Part", hUnivBase] + 4 (-1 - slot);
			m["SetPart", cell + 1, k1];
			m["SetPart", cell + 2, k2];
			m["SetPart", cell + 3, k3];
			m["SetPart", cell + 4, v]
		];
		v
	]]],
	kfn[arenaFailSlot, Function[{m, x, y}, Module[{mask = m["Part", hFailMask], base = m["Part", hFailBase], h = 0, cell = 0},
		h = BitAnd[BitAnd[x, mask40] * 1000003 + BitAnd[y, mask40], mask40];
		h = BitAnd[BitXor[h, BitShiftRight[h, 15]], mask];
		Do[
			cell = base + 2 h;
			If[m["Part", cell + 1] == 0, Return[-1 - h]];
			If[m["Part", cell + 1] == x && m["Part", cell + 2] == y, Return[1 + h]];
			h = BitAnd[h + 1, mask],
			{64}
		];
		0
	]]],
	kfn[arenaFailInsert, Function[{m, x, y}, Module[{slot = arenaFailSlot[m, x, y], cell = 0},
		If[slot < 0,
			cell = m["Part", hFailBase] + 2 (-1 - slot);
			m["SetPart", cell + 1, x];
			m["SetPart", cell + 2, y]
		];
		0
	]]],
	kfn[arenaFindRoot, Function[{m, a}, Module[{base = m["Part", hParentBase], x = a, p = 0, g = 0},
		While[True,
			p = m["Part", base + x];
			If[p == 0, Return[x]];
			g = m["Part", base + p];
			If[g == 0, Return[p]];
			m["SetPart", base + x, g];
			x = g
		];
		x
	]]],
	kfn[arenaUnite, Function[{m, a, b}, Module[{ra = arenaFindRoot[m, a], rb = arenaFindRoot[m, b]},
		If[ra != rb, m["SetPart", m["Part", hParentBase] + ra, rb]];
		1
	]]],

	(* ::Subsection:: *)
	(* The local context *)

	kfn[arenaNewFVar, Function[{m, type, value}, Module[{k = m["Part", hLctx] + 1, cell = 0},
		If[type < 1, Return[0]];
		If[k > m["Part", hLctxCap], Return[arenaFail[m, eLctxCapacity]]];
		m["SetPart", hLctx, k];
		cell = m["Part", hLctxBase] + 2 k - 2;
		m["SetPart", cell + 1, type];
		m["SetPart", cell + 2, value];
		arenaMkNode[m, tFVar, k, 0, 0]
	]]],
	kfn[arenaFvarType, Function[{m, k}, m["Part", m["Part", hLctxBase] + 2 k - 1]]],
	kfn[arenaFvarValue, Function[{m, k}, m["Part", m["Part", hLctxBase] + 2 k]]],

	(* ::Subsection:: *)
	(* Walks: substitution, lifting, abstraction, occurrence, universe instantiation; each distinct subterm once per call *)

	(* the loose bound variables depth, depth + 1, ... of e replaced by the k values on the stack from vs, the last for depth *)
	kfn[arenaInst, Function[{m, e, depth, vs, k, gen}, Module[{t = 0, slot = 0, r = 0, i = 0, v = 0},
		If[arenaRangeOf[m, e] <= depth, Return[e]];
		If[arenaEnter[m] == 0, Return[arenaLeave[m, 0]]];
		slot = arenaMemoSlot[m, e, depth, gen];
		If[slot > 0, Return[arenaLeave[m, arenaMemoValue[m, slot]]]];
		t = arenaTagOf[m, e];
		r = Which[
			t == tBVar,
				i = arenaF1Of[m, e];
				If[i < depth + k,
					v = arenaStackGet[m, vs + k - 1 - (i - depth)];
					If[depth == 0 || arenaRangeOf[m, v] == 0, v, arenaLiftLoose[m, v, depth]],
					arenaMkNode[m, tBVar, i - k, 0, 0]
				],
			t == tApp, arenaMkApp[m, arenaInst[m, arenaF1Of[m, e], depth, vs, k, gen], arenaInst[m, arenaF2Of[m, e], depth, vs, k, gen]],
			t == tLam || t == tPi, arenaMkBinder[m, t, arenaInst[m, arenaF1Of[m, e], depth, vs, k, gen], arenaInst[m, arenaF2Of[m, e], depth + 1, vs, k, gen]],
			t == tLet, arenaMkLet[m, arenaInst[m, arenaF1Of[m, e], depth, vs, k, gen], arenaInst[m, arenaF2Of[m, e], depth, vs, k, gen], arenaInst[m, arenaF3Of[m, e], depth + 1, vs, k, gen]],
			t == tProj, arenaMkProj[m, arenaF1Of[m, e], arenaF2Of[m, e], arenaInst[m, arenaF3Of[m, e], depth, vs, k, gen]],
			True, e
		];
		slot = arenaMemoSlot[m, e, depth, gen];
		arenaMemoStore[m, slot, e, depth, gen, r];
		arenaLeave[m, r]
	]]],
	kfn[arenaLift, Function[{m, e, amount, cutoff, gen}, Module[{t = 0, slot = 0, r = 0, i = 0},
		If[arenaRangeOf[m, e] <= cutoff, Return[e]];
		If[arenaEnter[m] == 0, Return[arenaLeave[m, 0]]];
		slot = arenaMemoSlot[m, e, cutoff, gen];
		If[slot > 0, Return[arenaLeave[m, arenaMemoValue[m, slot]]]];
		t = arenaTagOf[m, e];
		r = Which[
			t == tBVar, i = arenaF1Of[m, e]; arenaMkNode[m, tBVar, If[i >= cutoff, i + amount, i], 0, 0],
			t == tApp, arenaMkApp[m, arenaLift[m, arenaF1Of[m, e], amount, cutoff, gen], arenaLift[m, arenaF2Of[m, e], amount, cutoff, gen]],
			t == tLam || t == tPi, arenaMkBinder[m, t, arenaLift[m, arenaF1Of[m, e], amount, cutoff, gen], arenaLift[m, arenaF2Of[m, e], amount, cutoff + 1, gen]],
			t == tLet, arenaMkLet[m, arenaLift[m, arenaF1Of[m, e], amount, cutoff, gen], arenaLift[m, arenaF2Of[m, e], amount, cutoff, gen], arenaLift[m, arenaF3Of[m, e], amount, cutoff + 1, gen]],
			t == tProj, arenaMkProj[m, arenaF1Of[m, e], arenaF2Of[m, e], arenaLift[m, arenaF3Of[m, e], amount, cutoff, gen]],
			True, e
		];
		slot = arenaMemoSlot[m, e, cutoff, gen];
		arenaMemoStore[m, slot, e, cutoff, gen, r];
		arenaLeave[m, r]
	]]],
	kfn[arenaLiftLoose, Function[{m, e, amount}, If[amount == 0 || arenaRangeOf[m, e] == 0, e, arenaLift[m, e, amount, 0, arenaNewGen[m]]]]],
	kfn[arenaInstantiateValues, Function[{m, e, vs, k}, If[k == 0 || arenaRangeOf[m, e] == 0, e, arenaInst[m, e, 0, vs, k, arenaNewGen[m]]]]],
	kfn[arenaInstantiate1, Function[{m, e, v}, Module[{s = 0, r = 0},
		If[arenaRangeOf[m, e] == 0, Return[e]];
		If[v < 1, Return[0]];
		s = arenaReserve[m, 1];
		If[s < 0, Return[0]];
		arenaStackSet[m, s, v];
		r = arenaInst[m, e, 0, s, 1, arenaNewGen[m]];
		arenaRestore[m, s];
		r
	]]],
	kfn[arenaAbst, Function[{m, e, fv, depth, gen}, Module[{t = 0, slot = 0, r = 0},
		If[BitAnd[arenaFlagsOf[m, e], 1] == 0, Return[e]];
		If[arenaEnter[m] == 0, Return[arenaLeave[m, 0]]];
		slot = arenaMemoSlot[m, e, depth, gen];
		If[slot > 0, Return[arenaLeave[m, arenaMemoValue[m, slot]]]];
		t = arenaTagOf[m, e];
		r = Which[
			t == tFVar, If[arenaF1Of[m, e] == fv, arenaMkNode[m, tBVar, depth, 0, 0], e],
			t == tApp, arenaMkApp[m, arenaAbst[m, arenaF1Of[m, e], fv, depth, gen], arenaAbst[m, arenaF2Of[m, e], fv, depth, gen]],
			t == tLam || t == tPi, arenaMkBinder[m, t, arenaAbst[m, arenaF1Of[m, e], fv, depth, gen], arenaAbst[m, arenaF2Of[m, e], fv, depth + 1, gen]],
			t == tLet, arenaMkLet[m, arenaAbst[m, arenaF1Of[m, e], fv, depth, gen], arenaAbst[m, arenaF2Of[m, e], fv, depth, gen], arenaAbst[m, arenaF3Of[m, e], fv, depth + 1, gen]],
			t == tProj, arenaMkProj[m, arenaF1Of[m, e], arenaF2Of[m, e], arenaAbst[m, arenaF3Of[m, e], fv, depth, gen]],
			True, e
		];
		slot = arenaMemoSlot[m, e, depth, gen];
		arenaMemoStore[m, slot, e, depth, gen, r];
		arenaLeave[m, r]
	]]],
	kfn[arenaAbstractFVar, Function[{m, e, fvNode}, If[e < 1, 0, arenaAbst[m, e, arenaF1Of[m, fvNode], 0, arenaNewGen[m]]]]],
	kfn[arenaOcc, Function[{m, e, target, gen}, Module[{t = 0, slot = 0, r = 0},
		If[arenaRangeOf[m, e] <= target, Return[0]];
		If[arenaEnter[m] == 0, Return[arenaLeave[m, 0]]];
		slot = arenaMemoSlot[m, e, target, gen];
		If[slot > 0, Return[arenaLeave[m, arenaMemoValue[m, slot]]]];
		t = arenaTagOf[m, e];
		r = Which[
			t == tBVar, If[arenaF1Of[m, e] == target, 1, 0],
			t == tApp, If[arenaOcc[m, arenaF1Of[m, e], target, gen] == 1, 1, arenaOcc[m, arenaF2Of[m, e], target, gen]],
			t == tLam || t == tPi, If[arenaOcc[m, arenaF1Of[m, e], target, gen] == 1, 1, arenaOcc[m, arenaF2Of[m, e], target + 1, gen]],
			t == tLet, Which[arenaOcc[m, arenaF1Of[m, e], target, gen] == 1, 1, arenaOcc[m, arenaF2Of[m, e], target, gen] == 1, 1, True, arenaOcc[m, arenaF3Of[m, e], target + 1, gen]],
			t == tProj, arenaOcc[m, arenaF3Of[m, e], target, gen],
			True, 0
		];
		slot = arenaMemoSlot[m, e, target, gen];
		arenaMemoStore[m, slot, e, target, gen, r];
		arenaLeave[m, r]
	]]],
	kfn[arenaOccursBVar, Function[{m, e, target}, arenaOcc[m, e, target, arenaNewGen[m]]]],
	kfn[arenaInstUniv, Function[{m, e, params, levels}, Module[{t = 0, slot = 0, r = 0},
		If[BitAnd[arenaFlagsOf[m, e], 2] == 0, Return[e]];
		If[arenaEnter[m] == 0, Return[arenaLeave[m, 0]]];
		slot = arenaUnivSlot[m, e, levels, params];
		If[slot > 0, Return[arenaLeave[m, arenaUnivValue[m, slot]]]];
		t = arenaTagOf[m, e];
		r = Which[
			t == tSort, arenaMkNode[m, tSort, arenaInstLevel[m, arenaF1Of[m, e], params, levels], 0, 0],
			t == tConst, arenaMkConst[m, arenaF1Of[m, e], arenaInstLevel[m, arenaF2Of[m, e], params, levels]],
			t == tApp, arenaMkApp[m, arenaInstUniv[m, arenaF1Of[m, e], params, levels], arenaInstUniv[m, arenaF2Of[m, e], params, levels]],
			t == tLam || t == tPi, arenaMkBinder[m, t, arenaInstUniv[m, arenaF1Of[m, e], params, levels], arenaInstUniv[m, arenaF2Of[m, e], params, levels]],
			t == tLet, arenaMkLet[m, arenaInstUniv[m, arenaF1Of[m, e], params, levels], arenaInstUniv[m, arenaF2Of[m, e], params, levels], arenaInstUniv[m, arenaF3Of[m, e], params, levels]],
			t == tProj, arenaMkProj[m, arenaF1Of[m, e], arenaF2Of[m, e], arenaInstUniv[m, arenaF3Of[m, e], params, levels]],
			True, e
		];
		slot = arenaUnivSlot[m, e, levels, params];
		arenaUnivStore[m, slot, e, levels, params, r];
		arenaLeave[m, r]
	]]],

	(* ::Subsection:: *)
	(* Spines and constants *)

	kfn[arenaSpineCount, Function[{m, e}, Module[{x = e, n = 0}, While[arenaTagOf[m, x] == tApp, n++; x = arenaF1Of[m, x]]; n]]],
	kfn[arenaSpineHead, Function[{m, e}, Module[{x = e}, While[arenaTagOf[m, x] == tApp, x = arenaF1Of[m, x]]; x]]],
	(* the n arguments of e's spine pushed on the stack, outermost first; their start *)
	kfn[arenaPushSpine, Function[{m, e, n}, Module[{s = arenaReserve[m, n], x = e, j = 0},
		If[s < 0, Return[-1]];
		Do[arenaStackSet[m, s + j, arenaF2Of[m, x]]; x = arenaF1Of[m, x], {j, n - 1, 0, -1}];
		s
	]]],
	kfn[arenaApplyArgs, Function[{m, f, s, count}, Module[{r = f, j = 0},
		Do[r = arenaMkApp[m, r, arenaStackGet[m, s + j]], {j, 0, count - 1}];
		r
	]]],
	kfn[arenaConstCell, Function[{m, c, col}, m["Part", m["Part", hConstBase] + cWidth (c - 1) + col]]],
	kfn[arenaFlatAt, Function[{m, i}, m["Part", m["Part", hFlatBase] + i]]],

	(* ::Subsection:: *)
	(* Reduction *)

	kfn[arenaToConstructorForm, Function[{m, e},
		If[arenaTagOf[m, e] != tLit || m["Part", hNatType] == 0,
			e,
			If[arenaF1Of[m, e] == 0, m["Part", hZeroNode], arenaMkApp[m, m["Part", hSuccNode], arenaMkNode[m, tLit, arenaF1Of[m, e] - 1, 0, 0]]]
		]
	]],
	kfn[arenaWhnfStep, Function[{m, e, unfold}, Module[{n = arenaSpineCount[m, e], h = arenaSpineHead[m, e], s = 0, t = 0, r = e, c = 0, b = 0, v = 0, top = m["Part", hStackTop]},
		t = arenaTagOf[m, h];
		If[n == 0 && (t == tSort || t == tPi || t == tLam || t == tLit || t == tBVar), Return[e]];
		s = arenaPushSpine[m, e, n];
		If[s < 0, Return[0]];
		r = Which[
			t == tLam,
				c = 0;
				b = h;
				While[c < n && arenaTagOf[m, b] == tLam, b = arenaF2Of[m, b]; c++];
				arenaApplyArgs[m, arenaInstantiateValues[m, b, s, c], s + c, n - c],
			t == tLet, arenaApplyArgs[m, arenaInstantiate1[m, arenaF3Of[m, h], arenaF2Of[m, h]], s, n],
			t == tConst, arenaReduceConstant[m, e, h, s, n, unfold],
			t == tProj, arenaReduceProjection[m, e, h, s, n],
			t == tFVar, v = arenaFvarValue[m, arenaF1Of[m, h]]; If[v != 0, arenaApplyArgs[m, v, s, n], e],
			True, e
		];
		arenaRestore[m, top];
		r
	]]],
	kfn[arenaWhnfCore, Function[{m, e, unfold}, Module[{cacheBase = 0, cached = 0, r = e, next = 0},
		If[e < 1, Return[0]];
		cacheBase = If[unfold == 1, m["Part", hWhnfBase], m["Part", hCoreBase]];
		cached = m["Part", cacheBase + e];
		If[cached != 0, Return[cached]];
		If[arenaEnter[m] == 0, Return[arenaLeave[m, 0]]];
		m["SetPart", hWhnfCalls, m["Part", hWhnfCalls] + 1];
		While[True,
			next = arenaWhnfStep[m, r, unfold];
			If[next == r || next == 0, Break[]];
			r = next
		];
		If[next == 0 || arenaFailed[m] == 1, Return[arenaLeave[m, 0]]];
		m["SetPart", cacheBase + e, r];
		arenaLeave[m, r]
	]]],
	kfn[arenaWhnf, Function[{m, e}, arenaWhnfCore[m, e, 1]]],
	kfn[arenaReduceConstant, Function[{m, e, h, s, n, unfold}, Module[{c = arenaF1Of[m, h], ls = arenaF2Of[m, h], role = 0, kind = 0, lit = 0},
		role = arenaConstCell[m, c, cNatRole];
		If[role != 0,
			lit = arenaLiteralOperation[m, c, role, s, n];
			If[lit != 0, Return[lit]];
			If[arenaFailed[m] == 1, Return[0]]
		];
		kind = arenaConstCell[m, c, cKind];
		Which[
			kind == kDefinition, If[unfold == 1, arenaApplyArgs[m, arenaInstUniv[m, arenaConstCell[m, c, cValue], arenaConstCell[m, c, cParams], ls], s, n], e],
			kind == kRecursor, arenaReduceRecursor[m, e, c, ls, s, n],
			kind == kQuotient, arenaReduceQuotient[m, e, c, s, n],
			True, e
		]
	]]],
	kfn[arenaLiteralValue, Function[{m, a}, Module[{t = arenaWhnf[m, a], succs = 0, succNode = m["Part", hSuccNode]},
		While[arenaTagOf[m, t] == tApp && arenaF1Of[m, t] == succNode,
			succs++;
			t = arenaWhnf[m, arenaF2Of[m, t]]
		];
		Which[
			arenaTagOf[m, t] == tLit, arenaF1Of[m, t] + succs,
			t == m["Part", hZeroNode] && t != 0, succs,
			True, -1
		]
	]]],
	kfn[arenaLiteralPower, Function[{m, x, y}, Module[{r = 1, b = x, e = y},
		If[x <= 1, Return[x]];
		While[e > 0,
			If[BitAnd[e, 1] == 1, If[r > Quotient[litLimit, b], Return[-2]]; r = r b];
			e = BitShiftRight[e, 1];
			If[e > 0, If[b > Quotient[litLimit, b], Return[-2]]; b = b b]
		];
		r
	]]],
	kfn[arenaLiteralGCD, Function[{m, x, y}, Module[{a = x, b = y, t = 0}, While[b != 0, t = Mod[a, b]; a = b; b = t]; a]]],
	kfn[arenaLiteralLog2, Function[{m, x}, Module[{a = x, k = -1}, While[a > 0, a = BitShiftRight[a, 1]; k++]; k]]],
	(* an operation registered for the natural numbers on literal arguments: 0 where it does not compute, which unfolds it *)
	kfn[arenaLiteralOperation, Function[{m, c, role, s, n}, Module[{arity = If[role == 8, 1, 2], x = 0, y = 0, r = 0},
		If[n != arity, Return[0]];
		x = arenaLiteralValue[m, arenaStackGet[m, s]];
		If[x < 0, Return[0]];
		If[arity == 2, y = arenaLiteralValue[m, arenaStackGet[m, s + 1]]; If[y < 0, Return[0]]];
		r = Which[
			role == 1, If[x > litLimit - y, -2, x + y],
			role == 2, Max[x - y, 0],
			role == 3, If[x != 0 && y > Quotient[litLimit, x], -2, x y],
			role == 4, Which[y == 0, 1, y >= 16777216, -1, True, arenaLiteralPower[m, x, y]],
			role == 5, If[y == 0, 0, Quotient[x, y]],
			role == 6, If[y == 0, x, Mod[x, y]],
			role == 7, arenaLiteralGCD[m, x, y],
			role == 8, If[x == 0, 0, arenaLiteralLog2[m, x]],
			role == 9, BitAnd[x, y],
			role == 10, BitOr[x, y],
			role == 11, BitXor[x, y],
			role == 12, Which[y >= 16777216, -1, x == 0, 0, y >= 62, -2, x >= BitShiftLeft[1, 62 - y], -2, True, BitShiftLeft[x, y]],
			role == 13, If[y >= 63, 0, BitShiftRight[x, y]],
			role == 14, If[x == y, -10, -11],
			role == 15, If[x <= y, -10, -11],
			True, -1
		];
		Which[
			r == -1, 0,
			r == -2, arenaFail[m, eLiteralOverflow],
			r == -10, arenaMkConst[m, arenaConstCell[m, c, cBoolTrue], m["Part", hLevelNil]],
			r == -11, arenaMkConst[m, arenaConstCell[m, c, cBoolFalse], m["Part", hLevelNil]],
			True, arenaMkNode[m, tLit, r, 0, 0]
		]
	]]],
	(* the rule of recursor c for constructor ctor: the index of its four cells in the flat table, or 0 *)
	kfn[arenaRecursorRule, Function[{m, c, ctor}, Module[{base = arenaConstCell[m, c, cI], count = arenaConstCell[m, c, cH], j = 0},
		Do[If[arenaFlatAt[m, base + 4 j] == ctor, Return[base + 4 j]], {j, 0, count - 1}];
		0
	]]],
	kfn[arenaReduceRecursor, Function[{m, e, c, ls, s, n}, Module[
		{np = arenaConstCell[m, c, cB], nmot = arenaConstCell[m, c, cC], nmin = arenaConstCell[m, c, cD], nidx = arenaConstCell[m, c, cE], majorIndex = 0, major = 0, mw = 0, n2 = 0, h2 = 0, s2 = 0, rule = 0, r = 0, top = m["Part", hStackTop]},
		majorIndex = np + nmot + nmin + nidx;
		If[n < majorIndex + 1, Return[e]];
		major = arenaStackGet[m, s + majorIndex];
		mw = arenaToConstructorForm[m, arenaWhnf[m, major]];
		If[mw == 0, Return[0]];
		h2 = arenaSpineHead[m, mw];
		If[arenaTagOf[m, h2] == tConst,
			rule = arenaRecursorRule[m, c, arenaF1Of[m, h2]];
			If[rule > 0,
				n2 = arenaSpineCount[m, mw];
				If[n2 == arenaFlatAt[m, rule + 1] + arenaFlatAt[m, rule + 2],
					s2 = arenaPushSpine[m, mw, n2];
					If[s2 < 0, Return[0]];
					r = arenaApplyArgs[m, arenaInstUniv[m, arenaFlatAt[m, rule + 3], arenaConstCell[m, c, cParams], ls], s, np + nmot + nmin];
					r = arenaApplyArgs[m, r, s2 + arenaFlatAt[m, rule + 1], arenaFlatAt[m, rule + 2]];
					r = arenaApplyArgs[m, r, s + majorIndex + 1, n - majorIndex - 1];
					arenaRestore[m, top];
					Return[r]
				]
			]
		];
		If[arenaConstCell[m, c, cF] == 1, Return[arenaReduceKLike[m, e, c, ls, s, n, major]]];
		arenaStructureReduct[m, e, c, ls, s, n, major]
	]]],
	kfn[arenaReduceKLike, Function[{m, e, c, ls, s, n, major}, Module[
		{rule = arenaConstCell[m, c, cI], levels = ls, ctorApp = 0, np = arenaConstCell[m, c, cB], nmot = arenaConstCell[m, c, cC], nmin = arenaConstCell[m, c, cD], majorIndex = 0, r = 0},
		majorIndex = np + nmot + nmin + arenaConstCell[m, c, cE];
		If[arenaConstCell[m, c, cG] == 1, levels = arenaLb[m, ls]];
		ctorApp = arenaApplyArgs[m, arenaMkConst[m, arenaFlatAt[m, rule], levels], s, np];
		If[arenaIsDefEq[m, arenaInferType[m, major, 1], arenaInferType[m, ctorApp, 1]] == 1,
			r = arenaApplyArgs[m, arenaInstUniv[m, arenaFlatAt[m, rule + 3], arenaConstCell[m, c, cParams], ls], s, np + nmot + nmin];
			arenaApplyArgs[m, r, s + majorIndex + 1, n - majorIndex - 1],
			e
		]
	]]],
	kfn[arenaStructureReduct, Function[{m, e, c, ls, s, n, major}, Module[
		{ind = arenaConstCell[m, c, cA], majorType = 0, hd = 0, rule = arenaConstCell[m, c, cI], nf = 0, j = 0, s3 = 0, r = 0, np = arenaConstCell[m, c, cB], nmot = arenaConstCell[m, c, cC], nmin = arenaConstCell[m, c, cD], majorIndex = 0, top = m["Part", hStackTop]},
		majorIndex = np + nmot + nmin + arenaConstCell[m, c, cE];
		If[arenaConstCell[m, ind, cF] != 1, Return[e]];
		majorType = arenaWhnf[m, arenaInferType[m, major, 1]];
		hd = arenaSpineHead[m, majorType];
		If[arenaTagOf[m, hd] != tConst || arenaF1Of[m, hd] != ind, Return[e]];
		If[arenaPropositionQ[m, majorType] == 1, Return[e]];
		nf = arenaFlatAt[m, rule + 2];
		s3 = arenaReserve[m, nf];
		If[s3 < 0, Return[0]];
		Do[arenaStackSet[m, s3 + j, arenaMkProj[m, ind, j, major]], {j, 0, nf - 1}];
		r = arenaApplyArgs[m, arenaInstUniv[m, arenaFlatAt[m, rule + 3], arenaConstCell[m, c, cParams], ls], s, np + nmot + nmin];
		r = arenaApplyArgs[m, r, s3, nf];
		r = arenaApplyArgs[m, r, s + majorIndex + 1, n - majorIndex - 1];
		arenaRestore[m, top];
		r
	]]],
	kfn[arenaReduceProjection, Function[{m, e, h, s, n}, Module[{struct = arenaF1Of[m, h], idx = arenaF2Of[m, h], w = 0, hw = 0, ctor = 0, nw = 0, np = 0, sw = 0, r = 0, top = m["Part", hStackTop]},
		w = arenaWhnf[m, arenaF3Of[m, h]];
		hw = arenaSpineHead[m, w];
		If[arenaTagOf[m, hw] != tConst, Return[e]];
		ctor = arenaF1Of[m, hw];
		If[arenaConstCell[m, struct, cKind] != kInductive || arenaConstCell[m, struct, cC] != 1 || arenaFlatAt[m, arenaConstCell[m, struct, cD]] != ctor, Return[e]];
		np = arenaConstCell[m, struct, cA];
		nw = arenaSpineCount[m, w];
		If[nw != np + arenaConstCell[m, ctor, cD], Return[e]];
		sw = arenaPushSpine[m, w, nw];
		If[sw < 0, Return[0]];
		r = arenaApplyArgs[m, arenaStackGet[m, sw + np + idx], s, n];
		arenaRestore[m, top];
		r
	]]],
	kfn[arenaReduceQuotient, Function[{m, e, c, s, n}, Module[{role = arenaConstCell[m, c, cA], f = 0, major = 0, restStart = 0, w = 0, hw = 0},
		Which[
			role == 3 && n >= 6, f = arenaStackGet[m, s + 3]; major = arenaStackGet[m, s + 5]; restStart = 6,
			role == 4 && n >= 5, f = arenaStackGet[m, s + 3]; major = arenaStackGet[m, s + 4]; restStart = 5,
			True, Return[e]
		];
		w = arenaWhnf[m, major];
		hw = arenaSpineHead[m, w];
		If[arenaTagOf[m, hw] != tConst || arenaF1Of[m, hw] != arenaConstCell[m, c, cB] || arenaSpineCount[m, w] != 3, Return[e]];
		arenaApplyArgs[m, arenaMkApp[m, f, arenaF2Of[m, w]], s + restStart, n - restStart]
	]]],

	(* ::Subsection:: *)
	(* Type inference *)

	kfn[arenaInferType, Function[{m, e, inferOnly}, Module[{cached = 0, r = 0},
		If[e < 1, Return[0]];
		cached = m["Part", m["Part", hInferBase] + e];
		If[cached != 0, Return[cached]];
		If[inferOnly == 1, cached = m["Part", m["Part", hInferOnlyBase] + e]; If[cached != 0, Return[cached]]];
		If[arenaEnter[m] == 0, Return[arenaLeave[m, 0]]];
		m["SetPart", hInferCalls, m["Part", hInferCalls] + 1];
		r = arenaInferTypeOf[m, e, inferOnly];
		If[r == 0 || arenaFailed[m] == 1, Return[arenaLeave[m, 0]]];
		m["SetPart", If[inferOnly == 1, m["Part", hInferOnlyBase], m["Part", hInferBase]] + e, r];
		arenaLeave[m, r]
	]]],
	kfn[arenaInferTypeOf, Function[{m, e, inferOnly}, Module[{t = arenaTagOf[m, e]},
		Which[
			t == tBVar, arenaFail[m, eLooseBVar],
			t == tFVar, arenaFvarType[m, arenaF1Of[m, e]],
			t == tSort, arenaMkNode[m, tSort, arenaLevelSucc[m, arenaF1Of[m, e], 1], 0, 0],
			t == tConst, arenaConstantType[m, arenaF1Of[m, e], arenaF2Of[m, e]],
			t == tLit, If[m["Part", hNatNode] == 0, arenaFail[m, eUnsupported], m["Part", hNatNode]],
			t == tApp, arenaSpineType[m, e, inferOnly],
			t == tLam, arenaLambdaType[m, e, inferOnly],
			t == tPi, arenaFunctionTypeSort[m, e, inferOnly],
			t == tLet, arenaLocalDefinitionType[m, e, inferOnly],
			t == tProj, arenaProjectionType[m, e, inferOnly],
			True, arenaFail[m, eIllFormed]
		]
	]]],
	kfn[arenaConstantType, Function[{m, c, ls},
		Which[
			c < 1 || c > m["Part", hConsts], arenaFail[m, eUnknownConstant],
			arenaConstCell[m, c, cDeclared] == 0, arenaFail[m, eUnknownConstant],
			arenaLevelListLength[m, ls] != arenaConstCell[m, c, cNumParams], arenaFail[m, eArity],
			True, arenaInstUniv[m, arenaConstCell[m, c, cType], arenaConstCell[m, c, cParams], ls]
		]
	]],
	kfn[arenaSpineType, Function[{m, e, inferOnly}, Module[{n = arenaSpineCount[m, e], h = arenaSpineHead[m, e], s = 0, type = 0, i = 0, p = 0, w = 0, r = 0, top = m["Part", hStackTop]},
		s = arenaPushSpine[m, e, n];
		If[s < 0, Return[0]];
		type = arenaInferType[m, h, inferOnly];
		If[type == 0, arenaRestore[m, top]; Return[0]];
		While[i < n,
			If[arenaTagOf[m, type] == tPi,
				If[inferOnly == 0,
					If[arenaCheckHasType[m, arenaStackGet[m, s + i], arenaInstantiateValues[m, arenaF1Of[m, type], s + p, i - p]] == 0, arenaRestore[m, top]; Return[0]]
				];
				type = arenaF2Of[m, type];
				i++,
				w = arenaWhnf[m, arenaInstantiateValues[m, type, s + p, i - p]];
				If[arenaTagOf[m, w] != tPi, arenaRestore[m, top]; Return[arenaFail[m, eNotFunction]]];
				type = w;
				p = i
			]
		];
		r = arenaInstantiateValues[m, type, s + p, n - p];
		arenaRestore[m, top];
		r
	]]],
	kfn[arenaCheckHasType, Function[{m, e, expected}, Module[{actual = arenaInferType[m, e, 0]},
		If[actual == 0 || expected == 0, Return[0]];
		If[arenaIsDefEq[m, actual, expected] == 1, 1, If[m["Part", hStatus] == 0, m["SetPart", hFailA, actual]; m["SetPart", hFailB, expected]; m["SetPart", hFailTerm, e]]; arenaFail[m, eMismatch]]
	]]],
	kfn[arenaSortLevel, Function[{m, t, inferOnly}, Module[{s = arenaInferType[m, t, inferOnly]},
		If[s == 0, Return[0]];
		s = arenaWhnf[m, s];
		If[arenaTagOf[m, s] == tSort, arenaF1Of[m, s], arenaFail[m, eNotType]]
	]]],
	kfn[arenaLambdaType, Function[{m, e, inferOnly}, Module[{d = arenaF1Of[m, e], fv = 0, bt = 0},
		If[inferOnly == 0, If[arenaSortLevel[m, d, 0] == 0, Return[0]]];
		fv = arenaNewFVar[m, d, 0];
		bt = arenaInferType[m, arenaInstantiate1[m, arenaF2Of[m, e], fv], inferOnly];
		If[bt == 0, Return[0]];
		arenaMkBinder[m, tPi, d, arenaAbstractFVar[m, bt, fv]]
	]]],
	kfn[arenaFunctionTypeSort, Function[{m, e, inferOnly}, Module[{l1 = 0, l2 = 0, fv = 0},
		l1 = arenaSortLevel[m, arenaF1Of[m, e], inferOnly];
		If[l1 == 0, Return[0]];
		fv = arenaNewFVar[m, arenaF1Of[m, e], 0];
		l2 = arenaSortLevel[m, arenaInstantiate1[m, arenaF2Of[m, e], fv], inferOnly];
		If[l2 == 0, Return[0]];
		arenaMkNode[m, tSort, arenaLevelIMax[m, l1, l2], 0, 0]
	]]],
	kfn[arenaLocalDefinitionType, Function[{m, e, inferOnly}, Module[{t = arenaF1Of[m, e], v = arenaF2Of[m, e], fv = 0, bt = 0},
		If[inferOnly == 0,
			If[arenaSortLevel[m, t, 0] == 0, Return[0]];
			If[arenaCheckHasType[m, v, t] == 0, Return[0]]
		];
		fv = arenaNewFVar[m, t, v];
		bt = arenaInferType[m, arenaInstantiate1[m, arenaF3Of[m, e], fv], inferOnly];
		If[bt == 0, Return[0]];
		arenaInstantiate1[m, arenaAbstractFVar[m, bt, fv], v]
	]]],
	kfn[arenaProjectionType, Function[{m, e, inferOnly}, Module[
		{struct = arenaF1Of[m, e], idx = arenaF2Of[m, e], term = arenaF3Of[m, e], pt = 0, hd = 0, np = 0, sp = 0, ctor = 0, ft = 0, j = 0, w = 0, fromProof = 0, l = 0, top = m["Part", hStackTop]},
		pt = arenaInferType[m, term, inferOnly];
		If[pt == 0, Return[0]];
		pt = arenaWhnf[m, pt];
		hd = arenaSpineHead[m, pt];
		If[arenaTagOf[m, hd] != tConst || arenaF1Of[m, hd] != struct || arenaConstCell[m, struct, cKind] != kInductive || arenaConstCell[m, struct, cF] != 1, Return[arenaFail[m, eProjType]]];
		np = arenaSpineCount[m, pt];
		sp = arenaPushSpine[m, pt, np];
		If[sp < 0, Return[0]];
		ctor = arenaFlatAt[m, arenaConstCell[m, struct, cD]];
		ft = arenaInstUniv[m, arenaConstCell[m, ctor, cType], arenaConstCell[m, struct, cParams], arenaF2Of[m, hd]];
		Do[
			w = arenaWhnf[m, ft];
			If[arenaTagOf[m, w] != tPi, arenaRestore[m, top]; Return[arenaFail[m, eNotFunction]]];
			ft = arenaInstantiate1[m, arenaF2Of[m, w], arenaStackGet[m, sp + j]],
			{j, 0, np - 1}
		];
		l = arenaSortLevel[m, pt, inferOnly];
		If[l == 0, arenaRestore[m, top]; Return[0]];
		fromProof = If[l == m["Part", hLevelZero], 1, 0];
		Do[
			w = arenaWhnf[m, ft];
			If[arenaTagOf[m, w] != tPi, arenaRestore[m, top]; Return[arenaFail[m, eNotFunction]]];
			If[fromProof == 1 && arenaOccursBVar[m, arenaF2Of[m, w], 0] == 1,
				l = arenaSortLevel[m, arenaF1Of[m, w], inferOnly];
				If[l != m["Part", hLevelZero], arenaRestore[m, top]; Return[arenaFail[m, eProjProof]]]
			];
			ft = arenaInstantiate1[m, arenaF2Of[m, w], arenaMkProj[m, struct, j, term]],
			{j, 0, idx - 1}
		];
		w = arenaWhnf[m, ft];
		If[arenaTagOf[m, w] != tPi, arenaRestore[m, top]; Return[arenaFail[m, eProjIndex]]];
		If[fromProof == 1,
			l = arenaSortLevel[m, arenaF1Of[m, w], inferOnly];
			If[l != m["Part", hLevelZero], arenaRestore[m, top]; Return[arenaFail[m, eProjProof]]]
		];
		arenaRestore[m, top];
		arenaF1Of[m, w]
	]]],

	(* ::Subsection:: *)
	(* Definitional equality *)

	kfn[arenaIsDefEq, Function[{m, a, b}, Module[{r = 0, x = 0, y = 0},
		If[a == b, Return[1]];
		If[a < 1 || b < 1, Return[0]];
		If[arenaFindRoot[m, a] == arenaFindRoot[m, b], Return[1]];
		If[a < b, x = a; y = b, x = b; y = a];
		If[arenaFailSlot[m, x, y] > 0, Return[0]];
		If[arenaEnter[m] == 0, Return[arenaLeave[m, 0]]];
		m["SetPart", hDefeqCalls, m["Part", hDefeqCalls] + 1];
		r = arenaDefEqCases[m, a, b];
		If[arenaFailed[m] == 1, Return[arenaLeave[m, 0]]];
		If[r == 1, arenaUnite[m, a, b], arenaFailInsert[m, x, y]];
		arenaLeave[m, r]
	]]],
	kfn[arenaDefEqCases, Function[{m, a, b}, Module[{ta = arenaTagOf[m, a], tb = arenaTagOf[m, b], fv = 0},
		Which[
			ta == tSort && tb == tSort, If[arenaF1Of[m, a] == arenaF1Of[m, b], 1, 0],
			ta == tLit && tb == tLit, If[arenaF1Of[m, a] == arenaF1Of[m, b], 1, 0],
			(ta == tLam || ta == tPi) && ta == tb,
				If[arenaIsDefEq[m, arenaF1Of[m, a], arenaF1Of[m, b]] == 0, Return[0]];
				fv = arenaNewFVar[m, arenaF1Of[m, a], 0];
				arenaIsDefEq[m, arenaInstantiate1[m, arenaF2Of[m, a], fv], arenaInstantiate1[m, arenaF2Of[m, b], fv]],
			True, arenaReducedEqual[m, a, b]
		]
	]]],
	kfn[arenaReducedEqual, Function[{m, a, b}, Module[{ca = arenaWhnfCore[m, a, 0], cb = arenaWhnfCore[m, b, 0], pi = 0},
		If[ca == 0 || cb == 0, Return[0]];
		If[ca != a || cb != b, Return[arenaIsDefEq[m, ca, cb]]];
		pi = arenaProofIrrelevance[m, a, b];
		If[pi >= 0, Return[pi]];
		arenaLazyDelta[m, a, b]
	]]],
	kfn[arenaPropositionQ, Function[{m, type}, Module[{s = arenaInferType[m, type, 1]},
		If[s == 0, Return[0]];
		s = arenaWhnf[m, s];
		If[arenaTagOf[m, s] == tSort && arenaF1Of[m, s] == m["Part", hLevelZero], 1, 0]
	]]],
	kfn[arenaProofIrrelevance, Function[{m, a, b}, Module[{t = arenaTagOf[m, a], ta = 0},
		If[t == tSort || t == tPi || t == tLit, Return[-1]];
		ta = arenaInferType[m, a, 1];
		If[ta == 0, Return[0]];
		If[arenaPropositionQ[m, ta] == 1, arenaIsDefEq[m, ta, arenaInferType[m, b, 1]], -1]
	]]],
	kfn[arenaLazyDelta, Function[{m, a, b}, Module[{x = a, y = b, step = 0, moved = 0},
		While[True,
			step = arenaLazyDeltaStep[m, x, y];
			If[arenaFailed[m] == 1, Return[0]];
			If[step != 2, Break[]];
			If[m["Part", hLazyX] == m["Part", hLazyY], step = 1; Break[]];
			x = m["Part", hLazyX];
			y = m["Part", hLazyY];
			moved = 1
		];
		Which[
			step == 1, 1,
			moved == 0, arenaNormalFormsEqual[m, a, b],
			True, arenaIsDefEq[m, x, y]
		]
	]]],
	kfn[arenaHeadDefinition, Function[{m, t}, Module[{h = arenaSpineHead[m, t], c = 0},
		If[arenaTagOf[m, h] != tConst, Return[0]];
		c = arenaF1Of[m, h];
		If[arenaConstCell[m, c, cKind] != kDefinition, Return[0]];
		1 + 2 arenaConstCell[m, c, cHeight] + arenaConstCell[m, c, cHint]
	]]],
	kfn[arenaUnfoldedHead, Function[{m, t}, Module[{h = arenaSpineHead[m, t], n = arenaSpineCount[m, t], s = 0, r = 0, top = m["Part", hStackTop]},
		s = arenaPushSpine[m, t, n];
		If[s < 0, Return[0]];
		r = arenaApplyArgs[m, arenaInstUniv[m, arenaConstCell[m, arenaF1Of[m, h], cValue], arenaConstCell[m, arenaF1Of[m, h], cParams], arenaF2Of[m, h]], s, n];
		arenaRestore[m, top];
		arenaWhnfCore[m, r, 0]
	]]],
	(* 0 for neither side unfolding, 1 for one definition at both heads applied to equal arguments, 2 for the next pair in hLazyX, hLazyY *)
	kfn[arenaLazyDeltaStep, Function[{m, a, b}, Module[{da = arenaHeadDefinition[m, a], db = arenaHeadDefinition[m, b], ha = 0, hb = 0, aa = 0, ab = 0, x = a, y = b},
		If[da == 0 && db == 0, Return[0]];
		If[da != 0, ha = BitShiftRight[da - 1, 1]; aa = BitAnd[da - 1, 1]];
		If[db != 0, hb = BitShiftRight[db - 1, 1]; ab = BitAnd[db - 1, 1]];
		Which[
			db == 0, x = arenaUnfoldedHead[m, a],
			da == 0, y = arenaUnfoldedHead[m, b],
			aa == 1 && ab == 1, x = arenaUnfoldedHead[m, a]; y = arenaUnfoldedHead[m, b],
			aa == 1, x = arenaUnfoldedHead[m, a],
			ab == 1, y = arenaUnfoldedHead[m, b],
			ha > hb, x = arenaUnfoldedHead[m, a],
			ha < hb, y = arenaUnfoldedHead[m, b],
			arenaSameHeadArgumentsEqual[m, a, b] == 1, Return[1],
			True, x = arenaUnfoldedHead[m, a]; y = arenaUnfoldedHead[m, b]
		];
		If[x == 0 || y == 0, Return[0]];
		m["SetPart", hLazyX, x];
		m["SetPart", hLazyY, y];
		2
	]]],
	kfn[arenaHeadsEqual, Function[{m, ha, hb}, Module[{t = arenaTagOf[m, ha]},
		Which[
			t != arenaTagOf[m, hb], 0,
			t == tConst, If[arenaF1Of[m, ha] == arenaF1Of[m, hb] && arenaF2Of[m, ha] == arenaF2Of[m, hb], 1, 0],
			t == tFVar, If[arenaF1Of[m, ha] == arenaF1Of[m, hb], 1, 0],
			t == tProj, If[arenaF1Of[m, ha] == arenaF1Of[m, hb] && arenaF2Of[m, ha] == arenaF2Of[m, hb], arenaIsDefEq[m, arenaF3Of[m, ha], arenaF3Of[m, hb]], 0],
			True, 0
		]
	]]],
	kfn[arenaArgumentsEqual, Function[{m, a, b, n}, Module[{sa = 0, sb = 0, j = 0, r = 1, top = m["Part", hStackTop]},
		sa = arenaPushSpine[m, a, n];
		sb = arenaPushSpine[m, b, n];
		If[sa < 0 || sb < 0, arenaRestore[m, top]; Return[0]];
		Do[If[arenaIsDefEq[m, arenaStackGet[m, sa + j], arenaStackGet[m, sb + j]] == 0, r = 0; Break[]], {j, 0, n - 1}];
		arenaRestore[m, top];
		r
	]]],
	kfn[arenaSameHeadArgumentsEqual, Function[{m, a, b}, Module[{ha = arenaSpineHead[m, a], na = arenaSpineCount[m, a]},
		Which[
			arenaTagOf[m, ha] != tConst || na == 0 || na != arenaSpineCount[m, b], 0,
			arenaHeadsEqual[m, ha, arenaSpineHead[m, b]] == 0, 0,
			True, arenaArgumentsEqual[m, a, b, na]
		]
	]]],
	kfn[arenaSpinesEqual, Function[{m, a, b}, Module[{na = arenaSpineCount[m, a]},
		Which[
			na != arenaSpineCount[m, b], 0,
			arenaHeadsEqual[m, arenaSpineHead[m, a], arenaSpineHead[m, b]] == 0, 0,
			True, arenaArgumentsEqual[m, a, b, na]
		]
	]]],
	kfn[arenaEtaEqual, Function[{m, lam, other}, Module[{fv = arenaNewFVar[m, arenaF1Of[m, lam], 0]},
		arenaIsDefEq[m, arenaInstantiate1[m, arenaF2Of[m, lam], fv], arenaMkApp[m, other, fv]]
	]]],
	kfn[arenaLiteralEqual, Function[{m, a, b}, Module[{fa = arenaToConstructorForm[m, a], fb = arenaToConstructorForm[m, b]},
		If[fa != a || fb != b, arenaIsDefEq[m, fa, fb], 0]
	]]],
	kfn[arenaStructureEta, Function[{m, x, other}, Module[{h = arenaSpineHead[m, x], n = arenaSpineCount[m, x], ctor = 0, ind = 0, np = 0, nf = 0, s = 0, j = 0, r = 1, top = m["Part", hStackTop]},
		If[arenaTagOf[m, h] != tConst, Return[0]];
		ctor = arenaF1Of[m, h];
		If[arenaConstCell[m, ctor, cKind] != kConstructor, Return[0]];
		ind = arenaConstCell[m, ctor, cA];
		If[arenaConstCell[m, ind, cF] != 1, Return[0]];
		np = arenaConstCell[m, ctor, cC];
		nf = arenaConstCell[m, ctor, cD];
		If[n != np + nf, Return[0]];
		If[arenaIsDefEq[m, arenaInferType[m, x, 1], arenaInferType[m, other, 1]] == 0, Return[0]];
		s = arenaPushSpine[m, x, n];
		If[s < 0, Return[0]];
		Do[If[arenaIsDefEq[m, arenaStackGet[m, s + np + j], arenaMkProj[m, ind, j, other]] == 0, r = 0; Break[]], {j, 0, nf - 1}];
		arenaRestore[m, top];
		r
	]]],
	kfn[arenaUnitEqual, Function[{m, a, b}, Module[{t = arenaTagOf[m, a], type = 0, h = 0, s = 0},
		If[t == tSort || t == tPi, Return[0]];
		type = arenaWhnf[m, arenaInferType[m, a, 1]];
		h = arenaSpineHead[m, type];
		If[arenaTagOf[m, h] != tConst, Return[0]];
		s = arenaF1Of[m, h];
		If[arenaConstCell[m, s, cKind] != kInductive || arenaConstCell[m, s, cF] != 1, Return[0]];
		If[arenaConstCell[m, arenaFlatAt[m, arenaConstCell[m, s, cD]], cD] != 0, Return[0]];
		arenaIsDefEq[m, type, arenaInferType[m, b, 1]]
	]]],
	kfn[arenaNormalFormsEqual, Function[{m, a, b}, Module[{ta = arenaTagOf[m, a], tb = arenaTagOf[m, b]},
		Which[
			ta == tLam, arenaEtaEqual[m, a, b],
			tb == tLam, arenaEtaEqual[m, b, a],
			ta == tLit || tb == tLit, arenaLiteralEqual[m, a, b],
			arenaSpinesEqual[m, a, b] == 1, 1,
			arenaStructureEta[m, a, b] == 1, 1,
			arenaStructureEta[m, b, a] == 1, 1,
			True, arenaUnitEqual[m, a, b]
		]
	]]],

	(* ::Subsection:: *)
	(* Declarations *)

	kfn[arenaLevelParamsIn, Function[{m, l, params}, Module[{t = arenaLtagOf[m, l], ps = params},
		If[BitAnd[arenaLevelFlags[m, l], 1] == 0, Return[1]];
		Which[
			t == lParam,
				While[arenaLtagOf[m, ps] == lCons, If[arenaLa[m, ps] == l, Return[1]]; ps = arenaLb[m, ps]];
				0,
			t == lSucc, arenaLevelParamsIn[m, arenaLa[m, l], params],
			True, If[arenaLevelParamsIn[m, arenaLa[m, l], params] == 1, arenaLevelParamsIn[m, arenaLb[m, l], params], 0]
		]
	]]],
	kfn[arenaParamsWalk, Function[{m, e, params, gen}, Module[{t = 0, cell = 0},
		If[BitAnd[arenaFlagsOf[m, e], 2] == 0, Return[1]];
		cell = m["Part", hMarkBase] + e;
		If[m["Part", cell] == gen, Return[1]];
		m["SetPart", cell, gen];
		If[arenaEnter[m] == 0, Return[arenaLeave[m, 0]]];
		t = arenaTagOf[m, e];
		arenaLeave[m, Which[
			t == tSort, arenaLevelParamsIn[m, arenaF1Of[m, e], params],
			t == tConst, arenaLevelParamsIn[m, arenaF2Of[m, e], params],
			t == tApp || t == tLam || t == tPi, If[arenaParamsWalk[m, arenaF1Of[m, e], params, gen] == 1, arenaParamsWalk[m, arenaF2Of[m, e], params, gen], 0],
			t == tLet, Which[arenaParamsWalk[m, arenaF1Of[m, e], params, gen] == 0, 0, arenaParamsWalk[m, arenaF2Of[m, e], params, gen] == 0, 0, True, arenaParamsWalk[m, arenaF3Of[m, e], params, gen]],
			t == tProj, arenaParamsWalk[m, arenaF3Of[m, e], params, gen],
			True, 1
		]]
	]]],
	kfn[arenaParamsDeclared, Function[{m, c}, Module[{gen = m["Part", hMarkGen] + 1, params = arenaConstCell[m, c, cParams]},
		m["SetPart", hMarkGen, gen];
		If[arenaParamsWalk[m, arenaConstCell[m, c, cType], params, gen] == 0, Return[0]];
		If[arenaConstCell[m, c, cValue] > 0, arenaParamsWalk[m, arenaConstCell[m, c, cValue], params, gen], 1]
	]]],
	(* the greatest height of the definitions e mentions, each distinct subterm once in the walk gen *)
	kfn[arenaHeightWalk, Function[{m, e, gen}, Module[{t = 0, cell = 0, c = 0, h = 0},
		If[e < 1, Return[0]];
		cell = m["Part", hMarkBase] + e;
		If[m["Part", cell] == gen, Return[0]];
		m["SetPart", cell, gen];
		If[arenaEnter[m] == 0, Return[arenaLeave[m, 0]]];
		t = arenaTagOf[m, e];
		h = Which[
			t == tConst, c = arenaF1Of[m, e]; If[arenaConstCell[m, c, cKind] == kDefinition, arenaConstCell[m, c, cHeight], 0],
			t == tApp || t == tLam || t == tPi, Max[arenaHeightWalk[m, arenaF1Of[m, e], gen], arenaHeightWalk[m, arenaF2Of[m, e], gen]],
			t == tLet, Max[arenaHeightWalk[m, arenaF1Of[m, e], gen], arenaHeightWalk[m, arenaF2Of[m, e], gen], arenaHeightWalk[m, arenaF3Of[m, e], gen]],
			t == tProj, arenaHeightWalk[m, arenaF3Of[m, e], gen],
			True, 0
		];
		arenaLeave[m, h]
	]]],
	(* a value that takes arguments and projects a field out of the last, as TypeChecking.wl's projectionFunctionQ *)
	kfn[arenaProjectionFunctionQ, Function[{m, v}, Module[{x = v},
		If[arenaTagOf[m, x] != tLam, Return[0]];
		While[arenaTagOf[m, x] == tLam, x = arenaF2Of[m, x]];
		If[arenaTagOf[m, x] == tProj && arenaTagOf[m, arenaF3Of[m, x]] == tBVar && arenaF1Of[m, arenaF3Of[m, x]] == 0, 1, 0]
	]]],
	(* a definition's height and hint, which its record carries, are the ones its value gives, as declareDefinition gives them *)
	kfn[arenaDefinitionRecordQ, Function[{m, c}, Module[{gen = m["Part", hMarkGen] + 1, value = arenaConstCell[m, c, cValue]},
		m["SetPart", hMarkGen, gen];
		If[1 + arenaHeightWalk[m, value, gen] == arenaConstCell[m, c, cHeight] && arenaProjectionFunctionQ[m, value] == arenaConstCell[m, c, cHint], 1, 0]
	]]],
	kfn[arenaCheckDeclaration, Function[{m, c}, Module[{kind = arenaConstCell[m, c, cKind], type = arenaConstCell[m, c, cType], value = arenaConstCell[m, c, cValue], l = 0},
		m["SetPart", hCurrent, c];
		If[arenaParamsDeclared[m, c] == 0, Return[arenaFail[m, eUndeclaredParam]]];
		Which[
			kind == kAxiom || kind == kHole || kind == kQuotient,
				If[arenaSortLevel[m, type, 0] == 0, Return[0]],
			kind == kDefinition || kind == kOpaque,
				If[arenaSortLevel[m, type, 0] == 0, Return[0]];
				If[arenaCheckHasType[m, value, type] == 0, Return[0]];
				If[kind == kDefinition && arenaDefinitionRecordQ[m, c] == 0, Return[arenaFail[m, eDeclarationMismatch]]],
			kind == kTheorem,
				l = arenaSortLevel[m, type, 0];
				If[l == 0, Return[0]];
				If[l != m["Part", hLevelZero], Return[arenaFail[m, eNotProp]]];
				If[arenaCheckHasType[m, value, type] == 0, Return[0]],
			True, Return[arenaFail[m, eUnsupported]]
		];
		1
	]]]
},

	(* the entry: loads the inputs into a fresh memory and checks the declarations in order *)
	Function[
		{
			Typed[nodes, "PackedArray"::["MachineInteger", 2]],
			Typed[levels, "PackedArray"::["MachineInteger", 2]],
			Typed[consts, "PackedArray"::["MachineInteger", 2]],
			Typed[flat, "PackedArray"::["MachineInteger", 1]],
			Typed[order, "PackedArray"::["MachineInteger", 1]],
			Typed[settings, "PackedArray"::["MachineInteger", 1]]
		},
		Module[
			{
				cap = settings[[1]], levelCap = settings[[2]], tableSize = 2, levelTableSize = 2, memoSize = BitShiftLeft[1, settings[[7]]], univSize = BitShiftLeft[1, settings[[8]]],
				failSize = BitShiftLeft[1, settings[[9]]], stackCap = settings[[10]], lctxCap = settings[[11]], numNodes = Length[nodes], numLevels = Length[levels],
				numConsts = Length[consts], numFlat = Length[flat], total = 0
			},
			While[tableSize < 2 cap, tableSize = 2 tableSize];
			While[levelTableSize < 2 levelCap, levelTableSize = 2 levelTableSize];
			total = hHeaderSize + 6 cap + tableSize + 4 levelCap + levelTableSize + cWidth numConsts + 4 cap + cap + 2 failSize + 4 memoSize + 2 lctxCap + stackCap + numFlat + 4 univSize + cap + 16;
		Module[
			{
				m = CreateDataStructure["FixedArray"::["MachineInteger"], total], offset = hHeaderSize, i = 0, j = 0, tag = 0, a = 0, b = 0, c = 0, x = 0, cell = 0, processed = 0,
				nodeMap = ConstantArray[0, numNodes], levelMap = ConstantArray[0, numLevels], result = ConstantArray[0, 12]
			},
			m["SetPart", hCap, cap];
			m["SetPart", hNodeBase, offset]; offset = offset + 6 cap;
			m["SetPart", hTableBase, offset]; m["SetPart", hTableMask, tableSize - 1]; offset = offset + tableSize;
			m["SetPart", hLevelCap, levelCap];
			m["SetPart", hLevelBase, offset]; offset = offset + 4 levelCap;
			m["SetPart", hLevelTableBase, offset]; m["SetPart", hLevelTableMask, levelTableSize - 1]; offset = offset + levelTableSize;
			m["SetPart", hConstBase, offset]; m["SetPart", hConsts, numConsts]; offset = offset + cWidth numConsts;
			m["SetPart", hWhnfBase, offset]; offset = offset + cap;
			m["SetPart", hCoreBase, offset]; offset = offset + cap;
			m["SetPart", hInferBase, offset]; offset = offset + cap;
			m["SetPart", hInferOnlyBase, offset]; offset = offset + cap;
			m["SetPart", hParentBase, offset]; offset = offset + cap;
			m["SetPart", hFailBase, offset]; m["SetPart", hFailMask, failSize - 1]; offset = offset + 2 failSize;
			m["SetPart", hMemoBase, offset]; m["SetPart", hMemoMask, memoSize - 1]; offset = offset + 4 memoSize;
			m["SetPart", hLctxBase, offset]; m["SetPart", hLctxCap, lctxCap]; offset = offset + 2 lctxCap;
			m["SetPart", hStackBase, offset]; m["SetPart", hStackCap, stackCap]; offset = offset + stackCap;
			m["SetPart", hFlatBase, offset]; m["SetPart", hFlatCount, numFlat]; offset = offset + numFlat;
			m["SetPart", hUnivBase, offset]; m["SetPart", hUnivMask, univSize - 1]; offset = offset + 4 univSize;
			m["SetPart", hMarkBase, offset]; offset = offset + cap;
			m["SetPart", hDepthLimit, settings[[3]]];
			m["SetPart", hGen, 1];
			(* levels: each input row to its canonical level *)
			m["SetPart", hLevelNil, arenaMkLevel[m, lNil, 0, 0]];
			m["SetPart", hLevelZero, arenaMkLevel[m, lConst, 0, 0]];
			m["SetPart", hLevelOne, arenaMkLevel[m, lConst, 1, 0]];
			Do[
				tag = levels[[i, 1]]; a = levels[[i, 2]]; b = levels[[i, 3]];
				levelMap[[i]] = Which[
					tag == lConst, arenaMkLevel[m, lConst, a, 0],
					tag == lParam, arenaMkLevel[m, lParam, a, 0],
					tag == lSucc, arenaLevelSucc[m, levelMap[[a]], b],
					tag == lMax, arenaLevelMax[m, levelMap[[a]], levelMap[[b]]],
					tag == lIMax, arenaLevelIMax[m, levelMap[[a]], levelMap[[b]]],
					tag == lCons, arenaMkLevel[m, lCons, levelMap[[a]], levelMap[[b]]],
					True, m["Part", hLevelNil]
				],
				{i, numLevels}
			];
			(* nodes: each input row to its id, its parts rows before it *)
			Do[
				tag = nodes[[i, 1]]; a = nodes[[i, 2]]; b = nodes[[i, 3]]; c = nodes[[i, 4]];
				nodeMap[[i]] = Which[
					tag == tBVar || tag == tLit, arenaMkNode[m, tag, a, 0, 0],
					tag == tSort, arenaMkNode[m, tSort, levelMap[[a]], 0, 0],
					tag == tConst, arenaMkNode[m, tConst, a, levelMap[[b]], 0],
					tag == tApp || tag == tLam || tag == tPi, arenaMkNode[m, tag, nodeMap[[a]], nodeMap[[b]], 0],
					tag == tLet, arenaMkNode[m, tLet, nodeMap[[a]], nodeMap[[b]], nodeMap[[c]]],
					tag == tProj, arenaMkNode[m, tProj, a, b, nodeMap[[c]]],
					True, 0
				],
				{i, numNodes}
			];
			(* constants: type, value and universe parameters mapped to the memory's ids *)
			Do[
				cell = m["Part", hConstBase] + cWidth (i - 1);
				Do[m["SetPart", cell + j, consts[[i, j]]], {j, cWidth}];
				If[consts[[i, cType]] > 0, m["SetPart", cell + cType, nodeMap[[consts[[i, cType]]]]]];
				If[consts[[i, cValue]] > 0, m["SetPart", cell + cValue, nodeMap[[consts[[i, cValue]]]]]];
				m["SetPart", cell + cParams, levelMap[[consts[[i, cParams]]]]];
				m["SetPart", cell + cDeclared, 0],
				{i, numConsts}
			];
			(* the flat table: a negative entry is minus a node row *)
			Do[x = flat[[i]]; m["SetPart", m["Part", hFlatBase] + i, If[x < 0, nodeMap[[-x]], x]], {i, numFlat}];
			m["SetPart", hNatType, settings[[4]]];
			m["SetPart", hNatZero, settings[[5]]];
			m["SetPart", hNatSucc, settings[[6]]];
			If[settings[[4]] > 0,
				m["SetPart", hNatNode, arenaMkConst[m, settings[[4]], m["Part", hLevelNil]]];
				m["SetPart", hZeroNode, arenaMkConst[m, settings[[5]], m["Part", hLevelNil]]];
				m["SetPart", hSuccNode, arenaMkConst[m, settings[[6]], m["Part", hLevelNil]]]
			];
			(* the declarations in order: a positive entry is checked, a negative one declared as it is *)
			Do[
				x = order[[i]];
				If[m["Part", hStatus] != 0, Break[]];
				If[x > 0, arenaCheckDeclaration[m, x]];
				If[m["Part", hStatus] == 0,
					m["SetPart", m["Part", hConstBase] + cWidth (Abs[x] - 1) + cDeclared, 1];
					processed++
				],
				{i, Length[order]}
			];
			result[[1]] = m["Part", hStatus];
			result[[2]] = m["Part", hCurrent];
			result[[3]] = m["Part", hNodes];
			result[[4]] = m["Part", hLevels];
			result[[5]] = m["Part", hMaxDepth];
			result[[6]] = m["Part", hMaxStack];
			result[[7]] = m["Part", hDefeqCalls];
			result[[8]] = m["Part", hWhnfCalls];
			result[[9]] = m["Part", hInferCalls];
			result[[10]] = m["Part", hLctx];
			result[[11]] = processed;
			result[[12]] = total;
			If[settings[[12]] == 1,
				Module[{dump = ConstantArray[0, 15 + 4 m["Part", hNodes] + 3 m["Part", hLevels]], k = 0},
					Do[dump[[k]] = result[[k]], {k, 12}];
					dump[[13]] = m["Part", hFailA];
					dump[[14]] = m["Part", hFailB];
					dump[[15]] = m["Part", hFailTerm];
					Do[
						dump[[15 + 4 k - 3]] = arenaTagOf[m, k];
						dump[[15 + 4 k - 2]] = arenaF1Of[m, k];
						dump[[15 + 4 k - 1]] = arenaF2Of[m, k];
						dump[[15 + 4 k]] = arenaF3Of[m, k],
						{k, m["Part", hNodes]}
					];
					Do[
						dump[[15 + 4 m["Part", hNodes] + 3 k - 2]] = arenaLtagOf[m, k];
						dump[[15 + 4 m["Part", hNodes] + 3 k - 1]] = arenaLa[m, k];
						dump[[15 + 4 m["Part", hNodes] + 3 k]] = arenaLb[m, k],
						{k, m["Part", hLevels]}
					];
					dump
				],
				result
			]
		]
		]
	]
]


$memoryType = "FixedArray"::["MachineInteger"]

(* each kfn becomes a FunctionDeclaration: its first argument the memory, the others and its value machine integers *)
compiledKernelProgram[] := compiledKernelProgram[] = ReplaceAll[$program, $codeConstants] /. kfn[name_Symbol, Function[{arguments__}, body_]] :> With[
	{types = Prepend[ConstantArray["MachineInteger", Length[{arguments}] - 1], $memoryType]},
	FunctionDeclaration[name, Typed[types -> "MachineInteger"][Function[{arguments}, body]]] /; True
]

(* the program written with every symbol in full, so the same in every session *)
compiledKernelHash[] := compiledKernelHash[] = Block[{$Context = "TypeTheoryKernelHash`", $ContextPath = {"System`"}},
	Hash[ToString[compiledKernelProgram[], InputForm], "SHA256", "HexString"]
]


(* ::Subsection:: *)
(*The library*)


$libraryDirectory = FileNameJoin[{ParentDirectory[DirectoryName[$InputFileName], 2], "LibraryResources", $SystemID}]

$wolframVersion = ToString[$VersionNumber] <> "." <> ToString[$ReleaseNumber]

(* None until looked for, then the compiled function, or False without a library for this program and version *)
$compiledKernel = None

compiledKernelFunction[] := Replace[$compiledKernel, None :> ($compiledKernel = loadCompiledKernel[])]

loadCompiledKernel[] := Quiet @ Block[{metadata = Import[FileNameJoin[{$libraryDirectory, "TypeTheoryKernel.json"}], "RawJSON"]},
	If[ AssociationQ[metadata] && metadata["Hash"] === compiledKernelHash[] && metadata["WolframVersion"] === $wolframVersion && FileExistsQ[FileNameJoin[{$libraryDirectory, metadata["Library"]}]],
		Replace[LibraryFunctionLoad[FileNameJoin[{$libraryDirectory, metadata["Library"]}]], Except[_CompiledCodeFunction] -> False],
		False
	]
]

compiledKernelAvailableQ[] := MatchQ[compiledKernelFunction[], _CompiledCodeFunction]

(* about five minutes and six gigabytes on an M3 Max with Wolfram 15.1 *)
(* the compiler recurses deeper than the default limit on a program this size *)
compileKernelLibrary[] := Block[{library, $RecursionLimit = 100000},
	If[! DirectoryQ[$libraryDirectory], CreateDirectory[$libraryDirectory, CreateIntermediateDirectories -> True]];
	library = Replace[compiledKernelProgram[], Hold[declarations_, entry_] :> FunctionCompileExportLibrary[FileNameJoin[{$libraryDirectory, "TypeTheoryKernel"}], declarations, entry]];
	If[ ! StringQ[library],
		Failure["CompiledKernelNotBuilt", <|"MessageTemplate" -> "The compiled kernel's library was not built: `1`.", "MessageParameters" -> {library}|>],
		Export[
			FileNameJoin[{$libraryDirectory, "TypeTheoryKernel.json"}],
			<|"Hash" -> compiledKernelHash[], "Library" -> FileNameTake[library], "WolframVersion" -> $wolframVersion, "SystemID" -> $SystemID|>,
			"RawJSON"
		];
		$compiledKernel = None;
		File[library]
	]
]


(* ::Subsection:: *)
(*The input*)


(* The contents of an environment as Export writes them (SavedEnvironments.wl), as packed integer arrays: the node
   table, its leaves first, so that a row names only rows before it; the universe levels, likewise; a row for each
   constant; a flat table of the constructors of inductive types and the rules of recursors, where a negative entry
   is minus a node row; the declarations in order, an inductive type, constructor or recursor negated, as they are
   taken as they are; and the settings. *)

$kindCodes = <|"Axiom" -> 1, "Definition" -> 2, "Theorem" -> 3, "Opaque" -> 4, "InductiveType" -> 5, "Constructor" -> 6, "Recursor" -> 7, "Quotient" -> 8, "Hole" -> 9|>

$roleCodes = <|
	"Addition" -> 1, "Subtraction" -> 2, "Multiplication" -> 3, "Power" -> 4, "Quotient" -> 5, "Remainder" -> 6, "GCD" -> 7, "Log2" -> 8,
	"BitAnd" -> 9, "BitOr" -> 10, "BitXor" -> 11, "ShiftLeft" -> 12, "ShiftRight" -> 13, "Equal" -> 14, "LessEqual" -> 15
|>

$quotientRoleCodes = <|"Type" -> 1, "Introduction" -> 2, "Lift" -> 3, "Induction" -> 4|>

notHandled[] := Throw[None, compiledKernelInput]

levelRow[level_] := Lookup[$levelIndex, Key[level], addLevelRow[level, levelRowOf[level]]]
addLevelRow[key_, row_] := ($levelRows[++$levelCount] = row; $levelIndex[key] = $levelCount)

levelRowOf[n_Integer?NonNegative] := {1, n, 0}
levelRowOf[levelParameter[name_]] := {2, Lookup[$parameterIndex, Key[name], $parameterIndex[name] = Length[$parameterIndex] + 1], 0}
levelRowOf[levelSuccessor[level_, k_Integer?Positive]] := {3, levelRow[level], k}
levelRowOf[levelMaximum[level_]] := {4, levelRow[level], levelRow[level]}
levelRowOf[levelMaximum[first_, rest__]] := {4, levelRow[first], levelRow[levelMaximum[rest]]}
levelRowOf[levelImpredicativeMaximum[a_, b_]] := {5, levelRow[a], levelRow[b]}
levelRowOf[_] := notHandled[]

levelListRow[{}] := $nilRow
levelListRow[{first_, rest___}] := Lookup[$levelIndex, Key[{"List", first, rest}], addLevelRow[{"List", first, rest}, {6, levelRow[first], levelListRow[{rest}]}]]

leafRow[leaf_] := Lookup[$leafIndex, Key[leaf], ($leafRows[++$leafCount] = leafRowOf[leaf]; $leafIndex[leaf] = $leafCount)]

leafRowOf[boundVariable[index_Integer?NonNegative]] := {1, index, 0, 0}
leafRowOf[universeSort[level_]] := {2, levelRow[level], 0, 0}
leafRowOf[constantReference[name_, levels_List]] := {3, Lookup[$constantIndex, Key[name], notHandled[]], levelListRow[levels], 0}
leafRowOf[naturalLiteral[n_Integer]] /; 0 <= n < 2^62 := {8, n, 0, 0}
leafRowOf[_] := notHandled[]

(* a part of a row or record: a leaf's row, or minus the composite row k of termRef[k] until the leaves are counted *)
partRow[termRef[k_Integer]] := -k
partRow[leaf_] := leafRow[leaf]

compositeRow[{"a", function_, argument_}] := {4, partRow[function], partRow[argument], 0}
compositeRow[{"l", _, domain_, body_, _String}] := {5, partRow[domain], partRow[body], 0}
compositeRow[{"p", _, domain_, body_, _String}] := {6, partRow[domain], partRow[body], 0}
compositeRow[{"d", _, type_, value_, body_}] := {7, partRow[type], partRow[value], partRow[body]}
compositeRow[{"j", structure_, index_Integer, term_}] := {9, Lookup[$constantIndex, Key[structure], notHandled[]], index, partRow[term]}
compositeRow[_] := notHandled[]

flatAppend[values_List] := With[{start = Length[$flat] + 1}, $flat = Join[$flat, values]; start]

constantRow[record_] := Block[{row = ConstantArray[0, 20]},
	row[[1]] = Lookup[$kindCodes, record["Kind"], notHandled[]];
	row[[2]] = partRow[record["Type"]];
	row[[3]] = If[KeyExistsQ[record, "Value"], partRow[record["Value"]], 0];
	row[[4]] = levelListRow[levelParameter /@ record["UniverseParameters"]];
	row[[5]] = Length[record["UniverseParameters"]];
	row[[6]] = Lookup[record, "Height", 0];
	row[[7]] = Boole[Lookup[record, "Hint", None] === "Abbreviation"];
	Switch[record["Kind"],
		"InductiveType",
			row[[8 ;; 13]] = {
				record["NumberOfParameters"],
				record["NumberOfIndices"],
				Length[record["Constructors"]],
				flatAppend[Lookup[$constantIndex, record["Constructors"]]],
				Boole[TrueQ[record["Recursive"]]],
				Boole[Length[record["Constructors"]] == 1 && record["NumberOfIndices"] == 0 && ! TrueQ[record["Recursive"]]]
			},
		"Constructor",
			row[[8 ;; 11]] = {$constantIndex[record["InductiveType"]], record["ConstructorIndex"], record["NumberOfParameters"], record["NumberOfFields"]},
		"Recursor",
			row[[8 ;; 16]] = {
				$constantIndex[record["InductiveType"]],
				record["NumberOfParameters"],
				record["NumberOfMotives"],
				record["NumberOfMinors"],
				record["NumberOfIndices"],
				Boole[TrueQ[record["KLike"]]],
				Boole[TrueQ[record["EliminationUniverse"]]],
				Length[record["Rules"]],
				flatAppend[Catenate[KeyValueMap[
					Function[{constructor, rule}, {$constantIndex[constructor], rule["NumberOfParameters"], rule["NumberOfFields"], {"Row", partRow[rule["RightHandSide"]]}}],
					record["Rules"]
				]]]
			},
		"Quotient",
			row[[8 ;; 9]] = {$quotientRoleCodes[record["QuotientRole"]], $constantIndex[record["Introduction"]]}
	];
	row
]

(* the constructors false and true of the Booleans a comparison of natural numbers gives *)
booleanConstructors[records_, type_] := Replace[functionBody[functionBody[type]], {
	constantReference[booleans_, {}] :> Lookup[$constantIndex, records[booleans]["Constructors"]],
	_ :> notHandled[]
}]

functionBody[termRef[k_Integer]] := functionBody[$rows[[k]]]
functionBody[{"p", _, _, body_, _}] := body
functionBody[dependentFunctionType[_, _, body_, _]] := body
functionBody[other_] := other

(* the leaves are rows 1 to leaves, so the composite row k is row leaves + k *)
shiftedRows[rows_, leaves_] := Replace[rows, k_Integer?Negative :> leaves - k, {2}]

kernelInput[contents_Association, trusted_Integer, capacityFactor_] := Catch[Block[
	{
		$constantIndex, $levelIndex = <||>, $levelRows = <||>, $levelCount = 0, $parameterIndex = <||>, $nilRow, $leafIndex = <||>, $leafRows = <||>, $leafCount = 0,
		$flat = {}, $rows = contents["Nodes"], names = contents["Names"], records = contents["Records"], natural = contents["NaturalNumbers"],
		composites, constants, leaves, nodes, capacity
	},
	If[ ! MatchQ[contents["Rules"], TypeTheoryRules[KeyValuePattern[{"Prop" -> True, "RewriteRules" -> False, "Quantities" -> False, "Cubical" -> False}]]] || contents["RewriteRuleIndex"] =!= <||>,
		notHandled[]
	];
	$constantIndex = AssociationThread[names -> Range[Length[names]]];
	$nilRow = addLevelRow["Nil", {7, 0, 0}];
	composites = compositeRow /@ $rows;
	constants = Function[name, constantRow[records[name]]] /@ names;
	If[ AssociationQ[natural],
		KeyValueMap[
			Function[{operation, role}, With[{c = $constantIndex[operation]},
				constants[[c, 17]] = $roleCodes[role];
				If[MemberQ[{"Equal", "LessEqual"}, role], constants[[c, 18 ;; 19]] = booleanConstructors[records, records[operation]["Type"]]]
			]],
			natural["Roles"]
		]
	];
	leaves = $leafCount;
	nodes = Join[Values[$leafRows], composites];
	nodes[[All, 2 ;; 4]] = shiftedRows[nodes[[All, 2 ;; 4]], leaves];
	constants[[All, 2 ;; 3]] = shiftedRows[constants[[All, 2 ;; 3]], leaves];
	capacity = capacityFactor Max[2^20, 8 Length[nodes]];
	<|
		"Nodes" -> Developer`ToPackedArray[nodes],
		"Levels" -> Developer`ToPackedArray[Values[$levelRows]],
		"Constants" -> Developer`ToPackedArray[constants],
		"Flat" -> Developer`ToPackedArray[Append[Replace[$flat, {"Row", row_} :> -If[row < 0, leaves - row, row], {1}], 0]],
		"Order" -> Developer`ToPackedArray[MapThread[Function[{index, kind}, If[5 <= kind <= 7 || index <= trusted, -index, index]], {Range[Length[names]], constants[[All, 1]]}]],
		"Settings" -> Developer`ToPackedArray[{
			capacity, 65536, 20000,
			If[AssociationQ[natural], $constantIndex[natural["Type"]], 0],
			If[AssociationQ[natural], $constantIndex[natural["Zero"]], 0],
			If[AssociationQ[natural], $constantIndex[natural["Successor"]], 0],
			20, 20, 18, 2^20, capacity, 0
		}],
		"Names" -> names
	|>
], compiledKernelInput]


(* ::Subsection:: *)
(*Checking*)


$failureMessages = <|
	1 -> {"TypeMismatch", "a term does not have the type expected there"},
	2 -> {"TypeExpected", "a term that must be a type is not one"},
	3 -> {"FunctionExpected", "a term whose type is not a function type is applied to an argument"},
	4 -> {"PropositionExpected", "the statement of the theorem is not a proposition"},
	5 -> {"LooseBoundVariable", "a bound variable occurs outside its binder"},
	6 -> {"UniverseArity", "a constant is given another number of universe levels than it takes"},
	7 -> {"UnknownConstant", "it mentions a constant that is not declared before it"},
	8 -> {"ProjectionType", "a projection is of a term whose type is not its structure"},
	9 -> {"ProjectionIndex", "a projection is of a field its structure does not have"},
	10 -> {"ProjectionFromProof", "a projection takes data out of a proof"},
	11 -> {"UndeclaredUniverseParameter", "it mentions a universe parameter that it does not declare"},
	12 -> {"IllFormedTerm", "a part of it is not a term"},
	13 -> {"DeclarationMismatch", "its record does not match the record that checking its declaration gives"}
|>

(* the reasons the compiled kernel cannot finish: capacity, for which it runs again with four times the memory,
   and terms it does not handle, for which TypeChecking.wl's kernel checks the environment *)
$capacityStatuses = {22, 23, 24, 25}

compiledKernelCheck[environment_] := compiledKernelCheck[environment, 0]

(* the first trusted constants are taken as they are, as those of the environment a list of declarations extends *)
compiledKernelCheck[environment_, trusted_Integer] := Block[{function = compiledKernelFunction[], contents, duplicate},
	If[! MatchQ[function, _CompiledCodeFunction], Return[None]];
	contents = environmentContents[environment, None];
	duplicate = FirstPosition[contents["Names"], name_ /; ! DuplicateFreeQ[contents["Records"][name]["UniverseParameters"]], None, {1}, Heads -> False];
	If[ duplicate =!= None,
		Return[Failure["DuplicateUniverseParameter", <|
			"MessageTemplate" -> "The universe parameters of `1` must be distinct.",
			"MessageParameters" -> {HoldForm @@ contents["Names"][[First[duplicate]]]},
			"Position" -> First[duplicate]
		|>]]
	];
	compiledCheckWith[function, contents, trusted, 1]
]

compiledCheckWith[function_, contents_, trusted_, capacityFactor_] := Block[{input = kernelInput[contents, trusted, capacityFactor], result},
	If[input === None, Return[None]];
	result = function[input["Nodes"], input["Levels"], input["Constants"], input["Flat"], input["Order"], input["Settings"]];
	Which[
		! VectorQ[result, IntegerQ],
			None,
		result[[1]] == 0,
			Success["EnvironmentChecked", <|
				"MessageTemplate" -> "All `1` constants of the environment check again from their declarations.",
				"MessageParameters" -> {Length[input["Names"]]},
				"Constants" -> Length[input["Names"]]
			|>],
		MemberQ[$capacityStatuses, result[[1]]] && capacityFactor < 16,
			compiledCheckWith[function, contents, trusted, 4 capacityFactor],
		KeyExistsQ[$failureMessages, result[[1]]],
			Failure[First[$failureMessages[result[[1]]]], <|
				"MessageTemplate" -> "`1` does not check: `2`.",
				"MessageParameters" -> {HoldForm @@ input["Names"][[result[[2]]]], Last[$failureMessages[result[[1]]]]},
				"Position" -> result[[2]]
			|>],
		True,
			None
	]
]
