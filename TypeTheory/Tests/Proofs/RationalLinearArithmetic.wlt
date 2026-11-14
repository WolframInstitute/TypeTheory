(* ::Package:: *)

(* Tests for "LinearArithmetic" over the rationals (Proofs/Ring.wl, rationalLinearBoundProof): goals l <= r, l < r,
   l == r and False of Rationals, from inequalities, strict inequalities and equations among the hypotheses, by
   multipliers Wolfram finds and a certificate the kernel checks; a false inequality refused, and certificates made
   from forged multipliers refused. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

rationals = TypeTheoryEnvironment["Rationals"]

closedQ[proof_] := ! FailureQ[proof] && proof["Goals"] === {}

VerificationTest[
	Map[closedQ, {
		TypeTheoryProof[ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, Implies[x <= y, 2 x <= x + y]], rationals, {"Introduce"[x, y, h], "LinearArithmetic"}],
		TypeTheoryProof[ForAll[{Typed[x, Rationals], Typed[y, Rationals], Typed[z, Rationals]}, Implies[x <= y, Implies[y <= z, x <= z]]], rationals, {"Introduce"[x, y, z, h1, h2], "LinearArithmetic"}],
		TypeTheoryProof[ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, Implies[0 <= x, Implies[x <= 3, Implies[y <= 2 x, y <= 6]]]], rationals, {"Introduce"[x, y, h1, h2, h3], "LinearArithmetic"}],
		TypeTheoryProof[ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, Implies[x == y + 1, y <= x]], rationals, {"Introduce"[x, y, e], "LinearArithmetic"}],
		TypeTheoryProof[ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, Implies[x <= y, Implies[y <= x, x == y]]], rationals, {"Introduce"[x, y, h1, h2], "LinearArithmetic"}],
		TypeTheoryProof[ForAll[{Typed[x, Rationals]}, Implies[x + 1 <= x, Typed[False, TypeUniverse[0]]]], rationals, {"Introduce"[x, h], "LinearArithmetic"}]
	}],
	{True, True, True, True, True, True},
	TestID -> "Linear-arithmetic-proves-inequalities-equations-and-False-of-rationals"
]

(* a strict hypothesis with a positive multiplier, or a positive constant, makes a strict conclusion *)
VerificationTest[
	Map[closedQ, {
		TypeTheoryProof[ForAll[{Typed[x, Rationals], Typed[y, Rationals], Typed[z, Rationals]}, Implies[x < y, Implies[y <= z, x < z]]], rationals, {"Introduce"[x, y, z, h1, h2], "LinearArithmetic"}],
		TypeTheoryProof[ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, Implies[x <= y, x < y + 1]], rationals, {"Introduce"[x, y, h], "LinearArithmetic"}],
		TypeTheoryProof[ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, Implies[x < y, Implies[y < x, Typed[False, TypeUniverse[0]]]]], rationals, {"Introduce"[x, y, h1, h2], "LinearArithmetic"}],
		TypeTheoryProof[ForAll[{Typed[x, Rationals], Typed[y, Rationals], Typed[z, Rationals]}, Implies[x < y, Implies[y < z, x + y < 2 z]]], rationals, {"Introduce"[x, y, z, h1, h2], "LinearArithmetic"}]
	}],
	{True, True, True, True},
	TestID -> "Strict-and-non-strict-hypotheses-mix-in-a-strict-conclusion"
]

(* a goal that does not follow is refused, a strict one from non-strict hypotheses too *)
VerificationTest[
	{
		First[TypeTheoryProof[ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, Implies[x <= y, y <= x]], rationals, {"Introduce"[x, y, h], "LinearArithmetic"}]],
		First[TypeTheoryProof[ForAll[{Typed[x, Rationals], Typed[y, Rationals]}, Implies[x <= y, x < y]], rationals, {"Introduce"[x, y, h], "LinearArithmetic"}]]
	},
	{"NoLinearCombination", "NoLinearCombination"},
	TestID -> "A-false-inequality-of-rationals-is-refused"
]

(* the certificate of forged multipliers: for x <= y from h : x <= y, 1 (y - x) == 1 (y - x) is the true one; a
   negative multiplier has no proof that it is at least 0, and 2 (y - x) is not y - x, so neither gives a proof *)
VerificationTest[
	Module[{environment = rationals, x, y, h, context, xs, ys, hs, rationalsType},
		rationalsType = WolframInstitute`TypeTheory`PackageScope`constantReference[HoldComplete[Rationals], {}];
		context = <|
			9101 -> <|"Name" -> HoldComplete["x"], "Type" -> rationalsType, "Binder" -> "Explicit"|>,
			9102 -> <|"Name" -> HoldComplete["y"], "Type" -> rationalsType, "Binder" -> "Explicit"|>,
			9103 -> <|"Name" -> HoldComplete["h"], "Type" -> WolframInstitute`TypeTheory`PackageScope`rationalLessEqualTerm[WolframInstitute`TypeTheory`PackageScope`freeVariable[9101], WolframInstitute`TypeTheory`PackageScope`freeVariable[9102]], "Binder" -> "Explicit"|>
		|>;
		xs = WolframInstitute`TypeTheory`PackageScope`freeVariable[9101];
		ys = WolframInstitute`TypeTheory`PackageScope`freeVariable[9102];
		hs = {{xs, ys, WolframInstitute`TypeTheory`PackageScope`freeVariable[9103], False}};
		{
			WolframInstitute`TypeTheory`PackageScope`rationalLinearCertificate[environment, context, xs, ys, hs, 1, {1}, 0] =!= None,
			WolframInstitute`TypeTheory`PackageScope`rationalLinearCertificate[environment, context, xs, ys, hs, 1, {-1}, 0],
			WolframInstitute`TypeTheory`PackageScope`rationalLinearCertificate[environment, context, xs, ys, hs, 1, {2}, 0],
			WolframInstitute`TypeTheory`PackageScope`rationalLinearCertificate[environment, context, xs, ys, hs, 1, {1}, 3]
		}
	],
	{True, None, None, None},
	TestID -> "Forged-multipliers-give-no-certificate-of-rationals"
]

(* the naturals' linear arithmetic is as it was *)
VerificationTest[
	closedQ[TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers], Typed[m, NonNegativeIntegers]}, Implies[n <= m, n <= m + 1]], rationals, {"Introduce"[n, m, h], "LinearArithmetic"}]],
	True,
	TestID -> "The-naturals-linear-arithmetic-is-unchanged"
]
