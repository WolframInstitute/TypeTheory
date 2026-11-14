(* ::Package:: *)

(* Tests for Library/MachineRealsSpacing.wl: the certificate of the rounding and the standard model rest on the
   specification of the rounding alone, and a check that the kernel computes names the result of a literal.
   Run with: TestReport["TypeTheory/Tests/Library/MachineRealsSpacing.wlt"] from the repository root. *)

PacletDirectoryLoad[Directory[]]

Needs["WolframInstitute`TypeTheory`"]

reals = TypeTheoryEnvironment["MachineReals"]

VerificationTest[
	Map[
		Function[name, TypeTheoryAxiomClosure[TypeTheoryTerm[name, reals]]],
		{"real64ResultOfNearestQ", "real64StandardModel", "real64PlusStandardModel", "real64TimesStandardModel"}
	],
	ConstantArray[<|"quotientSoundness" -> "Proposition", "real64Result" -> "Signature", "real64ResultNearest" -> "Proposition"|>, 4],
	TestID -> "The-certificate-and-the-standard-model-rest-on-the-specification-of-the-rounding-alone"
]

(* 1/10 rounds to 7205759403792794 2^-56, the machine real 0.1: its check computes to "true" and names the result;
   the significand next to it fails the check *)
certificate[m_] := TypeTheoryProof[
	Exists[{Typed[r, "Real64"]}, And[
		"real64Result"[Typed[1/10, Rationals]] == Typed["left"[r], "Real64" | Failure],
		r[["rational"]] "rationalOfInteger"["integerOfNatural"[2^56]] == "rationalOfInteger"[Typed[m, Integers] "integerOfNatural"[2^0]]
	]],
	reals,
	{"Apply"["real64ResultOfNearestQ"], "Decide"}
]

VerificationTest[
	{certificate[7205759403792794]["Goals"], With[{wrong = certificate[7205759403792795]}, FailureQ[wrong] || wrong["Goals"] =!= {}]},
	{{}, True},
	TestID -> "A-literal-rounding-enters-a-proof-by-its-check-and-the-next-significand-is-refused"
]
