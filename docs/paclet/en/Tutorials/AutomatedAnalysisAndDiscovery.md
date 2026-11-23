---
Template: TechNote
Name: AutomatedAnalysisAndDiscovery
Title: Automated Analysis and Discovery
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/tutorial/AutomatedAnalysisAndDiscovery
Keywords: [TypeTheoryDetermine, TypeTheoryAssumptions, TypeTheoryConsequences, TypeTheoryTermination, automated theorem proving, counterexamples, independence, finite models, abduction, forward chaining, termination, ranking functions, Farkas, polynomial interpretation, LLMFunction, verification]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TypeTheoryIntroduction, ProgramsAndProofs, PatternsAndRewriting, TheWolframLanguage]
---

[TypeTheoryProof]() and [TypeTheoryTactic]() build proofs step by step. On top of them sit four high-level analysis and discovery superfunctions: [TypeTheoryDetermine]() decides whether a proposition is provable, refutable, independent, or undetermined; [TypeTheoryAssumptions]() discovers missing hypotheses that make an unprovable statement true; [TypeTheoryConsequences]() derives non-trivial consequences from a statement assumed true; and [TypeTheoryTermination]() certifies termination, conditional termination, or divergence of formalized Wolfram Language programs and rewrite systems.

This tutorial explains how each superfunction works under the hood, why every result remains strictly outside the kernel trust boundary, and walks through a wide gallery of examples ranging from arithmetic and finite models to rewrite systems, integer loops, and live [LLMFunction]() synthesis.

## Architecture and the Trust Boundary

TypeTheory keeps its trusted kernel small. Only the core checking files listed in `` WolframInstitute`TypeTheory`PackageScope`$trustedSources `` decide whether a term is well typed and whether a proof term inhabits its statement. All four superfunctions live in untrusted code (`Proofs/Superfunctions.wl`), alongside tactics and elaboration:

```wl
FreeQ[WolframInstitute`TypeTheory`PackageScope`$trustedSources, s_String /; StringContainsQ[s, "Superfunctions"]]
```

<!-- => True -->

Because the search engines are untrusted, they are free to combine aggressive heuristics: Wolfram Language symbolic solvers ([Reduce](), [FindInstance](), [FindEquationalProof]()), finite model search, Farkas linear programming, polynomial weight synthesis, and even [LLMFunction]() calls. Before any superfunction returns a verified result, however, it hands the constructed proof term back to the trusted kernel with term-checking caches cleared, verifying that the proof has no open goals and its term truly checks against the statement's core type. Every returned [TypeTheoryProof]() can be passed directly to [TypeTheoryTheorem]() or [TypeTheoryCheck]().

## Deciding, Proving, and Refuting with TypeTheoryDetermine

### How TypeTheoryDetermine Works Under the Hood

Given a held proposition *P* in an environment *env*, [TypeTheoryDetermine]() first checks whether a [Decidable]() instance synthesizes for *P* and records that fact orthogonally in `"ComputationallyDecidable"`. It then executes a staged pipeline, stopping as soon as one stage produces a kernel-checked certificate:

1. **Closed decision fast-path (`"Decide"`):** if *P* is closed (not a universal quantifier) and computationally decidable, it runs `"Decide"` on both *P* and <code>[Not]()[*P*]</code> via `"decideSoundness"`.
2. **Quick counterexample probe (`"Counterexample"`):** for universal statements, it tries the counterexample oracle first so false conjectures fail fast with a concrete witness and a kernel-checked proof of <code>[Not]()[*P*]</code>.
3. **Positive proof portfolio (`"Portfolio"`):** runs <code>[TypeTheoryTactic]()[[Automatic]()]</code> together with untrusted heuristics for structural induction on natural numbers, natural-number subtraction and multiplicative cancellation, Farkas-based integer linear arithmetic, and Boolean case splitting. For existentials, it extracts the concrete `"Witness"` from the finished proof term.
4. **Negative proof portfolio (`"NegationPortfolio"`):** runs the same portfolio on <code>[Not]()[*P*]</code>.
5. **Certified model independence (`"CertifiedModelIndependence"`):** when *P* mentions opaque axioms (such as an uninterpreted function or carrier), it searches for two concrete instantiations (concrete functions over the natural numbers or finite carriers up to `"MaxModelSize"`) and builds two kernel-checked proofs: `"TrueModel"` proving the instantiated *P*, and `"FalseModel"` proving its negation.
6. **Optional LLM tactic synthesis (`"LLMVerified"`):** strictly disabled under the default `Method -> Automatic`; enabled only when [Method]() is `"LLM"` or `{"Heuristic", "LLM"}`.
7. **Axiom-sensitivity gap check and honest `"Undetermined"`:** if *env* lacks classical axioms (such as `"Constructive"`), it checks whether *P* becomes provable in the prelude and records `"ClassicallyProvable"`, `"RequiredAxioms"`, and `"ClassicalProof"` under `"Details"`.

### Closed Decisions and Kernel Theorems

A closed true equation is decided by computation, with `"ComputationallyDecidable" -> True`:

```wl
decidedTrue = TypeTheoryDetermine[2 + 2 == 4]
```

<!-- => <|"Status" -> "Proved", "Statement" -> 2 + 2 == 4, "Proof" -> Proof complete, "Counterexample" -> None, "Witness" -> None, "Models" -> None, "ComputationallyDecidable" -> True, "Method" -> "Decide", "Details" -> <||>|> -->

The proof inside `"Proof"` is checked again by the kernel when declared with [TypeTheoryTheorem]():

```wl
TypeTheoryEnvironment[TypeTheoryTheorem[TwoPlusTwo, decidedTrue["Proof"]]][TwoPlusTwo]
```

<!-- => theorem TwoPlusTwo : 2 + 2 == 4 -->

A closed false equation is equally decidable (`"ComputationallyDecidable" -> True`), and its proof proves the negation:

```wl
decidedFalse = TypeTheoryDetermine[2 + 2 == 5]
```

<!-- => <|"Status" -> "Refuted", "Statement" -> 2 + 2 == 5, "Proof" -> Proof complete, "Counterexample" -> None, "Witness" -> None, "Models" -> None, "ComputationallyDecidable" -> True, "Method" -> "Decide", "Details" -> <||>|> -->

Verify the refutation proof directly against <code>[Not]()[2 + 2 == 5]</code>:

```wl
TypeTheoryCheck[decidedFalse["Proof"]["Term"], TypeTheoryTerm[Not[2 + 2 == 5]]]
```

<!-- => Success["TypeChecked", ...] -->

### Induction, Algebra, Witnesses, and Counterexamples

Left-identity of addition is not true by computation alone, so the portfolio proves it by induction on `n`:

```wl
TypeTheoryDetermine[ForAll[{n}, 0 + n == n]]
```

<!-- => <|"Status" -> "Proved", "Statement" -> ∀_n∶ℕ 0 + n == n, "Proof" -> Proof complete, "Counterexample" -> None, "Witness" -> None, "Models" -> None, "ComputationallyDecidable" -> False, "Method" -> "Portfolio", "Details" -> <||>|> -->

Commutativity of addition and polynomial identities close through the ring and induction heuristics:

```wl
TypeTheoryDetermine[ForAll[{a, b}, a + b == b + a]]
```

<!-- => <|"Status" -> "Proved", "Statement" -> ∀_a∶ℕ ∀_b∶ℕ a + b == b + a, "Proof" -> Proof complete, "Counterexample" -> None, "Witness" -> None, "Models" -> None, "ComputationallyDecidable" -> False, "Method" -> "Portfolio", "Details" -> <||>|> -->

```wl
TypeTheoryDetermine[ForAll[{a, b}, (a + b)^2 == a^2 + 2 a b + b^2]]
```

<!-- => <|"Status" -> "Proved", "Statement" -> ∀_a∶ℕ ∀_b∶ℕ (a + b)^2 == a^2 + 2 a b + b^2, "Proof" -> Proof complete, "Counterexample" -> None, "Witness" -> None, "Models" -> None, "ComputationallyDecidable" -> False, "Method" -> "Portfolio", "Details" -> <||>|> -->

For an existential statement, [TypeTheoryDetermine]() proves existence and extracts the concrete `"Witness"` from the proof term:

```wl
TypeTheoryDetermine[Exists[{x, y}, x^2 + y^2 == 25 && 0 < x && x < y]]
```

<!-- => <|"Status" -> "Proved", "Statement" -> ∃_x∶ℕ ∃_y∶ℕ x^2 + y^2 == 25 ∧ 0 < x ∧ x < y, "Proof" -> Proof complete, "Counterexample" -> None, "Witness" -> <|"x" -> 3, "y" -> 4|>, "Models" -> None, "ComputationallyDecidable" -> False, "Method" -> "Portfolio", "Details" -> <||>|> -->

False universal conjectures are refuted with an explicit `"Counterexample"` and a kernel-checked proof of their negation:

```wl
TypeTheoryDetermine[ForAll[{n}, n^2 <= 2^n]]
```

<!-- => <|"Status" -> "Refuted", "Statement" -> ∀_n∶ℕ n^2 <= 2^n, "Proof" -> Proof complete, "Counterexample" -> <|"n" -> 3|>, "Witness" -> None, "Models" -> None, "ComputationallyDecidable" -> False, "Method" -> "Counterexample", "Details" -> <||>|> -->

```wl
TypeTheoryDetermine[ForAll[{n}, n < 2 n]]
```

<!-- => <|"Status" -> "Refuted", "Statement" -> ∀_n∶ℕ n < 2 n, "Proof" -> Proof complete, "Counterexample" -> <|"n" -> 0|>, "Witness" -> None, "Models" -> None, "ComputationallyDecidable" -> False, "Method" -> "Counterexample", "Details" -> <||>|> -->

### Integers and Constructive Axiom Gaps

Naming `"Integers"` switches into the quotient integer environment, where integer ring identities and linear inequalities are proved by the integer arithmetic heuristics:

```wl
TypeTheoryDetermine[ForAll[{Typed[x, Integers], Typed[y, Integers]}, Implies[x <= y, x <= y + 1]], "Integers"]
```

<!-- => <|"Status" -> "Proved", "Statement" -> ∀_x∶ℤ ∀_y∶ℤ x <= y ⇒ x <= y + 1, "Proof" -> Proof complete, "Counterexample" -> None, "Witness" -> None, "Models" -> None, "ComputationallyDecidable" -> False, "Method" -> "Portfolio", "Details" -> <||>|> -->

```wl
TypeTheoryDetermine[ForAll[{Typed[x, Integers], Typed[y, Integers]}, (x - y) (x + y) == x^2 - y^2], "Integers"]
```

<!-- => <|"Status" -> "Proved", "Statement" -> ∀_x∶ℤ ∀_y∶ℤ (x - y) (x + y) == x^2 - y^2, "Proof" -> Proof complete, "Counterexample" -> None, "Witness" -> None, "Models" -> None, "ComputationallyDecidable" -> False, "Method" -> "Portfolio", "Details" -> <||>|> -->

In `"Constructive"`, classical tautologies such as double-negation elimination and Peirce's law are unprovable. [TypeTheoryDetermine]() reports `"Undetermined"` and diagnoses the exact classical axioms from the prelude that close the gap:

```wl
TypeTheoryDetermine[ForAll[{Typed[p, TypeUniverse[0]]}, Implies[Not[Not[p]], p]], "Constructive"]
```

<!-- => <|"Status" -> "Undetermined", "Statement" -> ∀_p∶Prop ¬¬p ⇒ p, "Proof" -> None, "Counterexample" -> None, "Witness" -> None, "Models" -> None, "ComputationallyDecidable" -> False, "Method" -> "SearchExhausted", "Details" -> <|"ClassicallyProvable" -> True, "RequiredAxioms" -> <|"choice" -> "Signature", "quotientSoundness" -> "Proposition", "propositionalExtensionality" -> "Proposition"|>, "ClassicalProof" -> Proof complete|>|> -->

```wl
TypeTheoryDetermine[ForAll[{Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]]}, Implies[Implies[Implies[p, q], p], p]], "Constructive"]
```

<!-- => <|"Status" -> "Undetermined", "Statement" -> ∀_p∶Prop ∀_q∶Prop ((p ⇒ q) ⇒ p) ⇒ p, "Proof" -> None, ..., "Details" -> <|"ClassicallyProvable" -> True, "RequiredAxioms" -> ..., "ClassicalProof" -> Proof complete|>|> -->

### Certified Independence via Concrete and Finite Models

When a proposition mentions opaque axioms, neither the statement nor its negation may be provable. Rather than merely giving up, [TypeTheoryDetermine]() tries to exhibit two concrete interpretations of the opaque symbols, one that satisfies the statement and one that satisfies its negation, and proves both in the kernel.

Declare an opaque unary function on the natural numbers:

```wl
opaqueEnv = TypeTheoryEnvironment[{TypeTheoryAxiom[opaqueInv, Naturals -> Naturals]}]
```

<!-- => TypeTheoryEnvironment summary box: 276 constants -->

Being an involution is independent of the signature `opaqueInv : ℕ → ℕ`: the identity function satisfies it while the successor function refutes it:

```wl
TypeTheoryDetermine[ForAll[{x}, opaqueInv[opaqueInv[x]] == x], opaqueEnv]
```

<!-- => <|"Status" -> "Independent", "Statement" -> ∀_x∶ℕ opaqueInv[opaqueInv[x]] == x, "Proof" -> None, "Counterexample" -> None, "Witness" -> None, "Models" -> <|"TrueModel" -> <|"Assignment" -> ..., "Proof" -> Proof complete|>, "FalseModel" -> <|"Assignment" -> ..., "Proof" -> Proof complete|>|>, "ComputationallyDecidable" -> False, "Method" -> "CertifiedModelIndependence", "Details" -> <||>|> -->

Now declare an abstract magma, an opaque carrier type with an opaque binary operation:

```wl
magma = TypeTheoryEnvironment[{
    TypeTheoryAxiom[magmaCarrier, TypeUniverse[1]],
    TypeTheoryAxiom[magmaOp, magmaCarrier -> magmaCarrier -> magmaCarrier]
}]
```

<!-- => TypeTheoryEnvironment summary box: 277 constants -->

Both commutativity and associativity are certified independent via finite carrier models (such as 1-element and 2-element models over [Booleans]() or bounded naturals):

```wl
TypeTheoryDetermine[ForAll[{Typed[x, magmaCarrier], Typed[y, magmaCarrier]}, magmaOp[x, y] == magmaOp[y, x]], magma]
```

<!-- => <|"Status" -> "Independent", "Statement" -> ∀_x∶magmaCarrier ∀_y∶magmaCarrier magmaOp[x, y] == magmaOp[y, x], ..., "Method" -> "CertifiedModelIndependence", "Details" -> <||>|> -->

```wl
TypeTheoryDetermine[ForAll[{Typed[x, magmaCarrier], Typed[y, magmaCarrier], Typed[z, magmaCarrier]}, magmaOp[magmaOp[x, y], z] == magmaOp[x, magmaOp[y, z]]], magma]
```

<!-- => <|"Status" -> "Independent", "Statement" -> ∀_x∶magmaCarrier ∀_y∶magmaCarrier ∀_z∶magmaCarrier magmaOp[magmaOp[x, y], z] == magmaOp[x, magmaOp[y, z]], ..., "Method" -> "CertifiedModelIndependence", "Details" -> <||>|> -->

## Finding Missing Assumptions with TypeTheoryAssumptions

### How TypeTheoryAssumptions Works Under the Hood

When a proposition *P* is unprovable, finding *any* assumption *A* such that `A ⇒ P` is trivial if you allow cheating (`A = False` or `A = P`). [TypeTheoryAssumptions]() prevents trivial answers through a five-engine candidate generator followed by three strict verification gates and subsumption pruning:

1. **Candidate generation:**
   - **Symbolic domain abduction (`"SymbolicDomain"`):** translates arithmetic formulas into Wolfram Language expressions, solves the truth region with [Reduce]() (over `Integers` with a `Reals` fallback), strips redundant domain guards, and extracts atomic inequality conjuncts.
   - **Tactic-residual lemma abduction:** introduces binders and inspects partial tactic goals for missing side conditions.
   - **Axiom diff (`"AxiomDiff"`):** checks whether an environment without classical logic (like `"Constructive"`) needs the law of excluded middle.
   - **Counterexample-guided refinement (`"CounterexampleRefinement"`):** finds concrete counterexamples `x == c` and proposes the exact exclusion guard `x != c`.
   - **Algebraic property catalog (`"AlgebraicCatalog"`):** inspects opaque unary and binary operations in *P* and tests standard structural laws (identity, involution, commutativity, associativity, and their combinations).
   - **Open-proof goal abstraction (`"OpenGoalAbstraction"`):** when given an unfinished [TypeTheoryProof](), restricts each open goal to its actually referenced context variables and abstracts it into a closed goal-closing assumption.
2. **Three quality gates:**
   - **Kernel proof gate:** constructs and kernel-verifies a complete proof of `A ⇒ P` (wrapped inside universal binders for `"Local"` guards, or outside for `"Global"` hypotheses).
   - **Non-vacuity gate:** rejects contradictory assumptions by finding a satisfying witness (recorded in `"Witness"`) or proving `A` is not refutable.
   - **Non-triviality gate:** rejects assumptions identical to the target, equivalent assumptions that are not strictly simpler, and assumptions that prove the consequent of an implication while ignoring its existing premises.
3. **Subsumption pruning and ranking:** removes stronger candidates implied by weaker verified ones and ranks the survivors by simplicity and generality.

### Arithmetic Domain Guards and Counterexample Refinement

Recall that `n^2 <= 2^n` failed only at `n == 3`. [TypeTheoryAssumptions]() discovers both the symbolic tail bound `4 <= n` and the exact counterexample exclusion `n != 3`:

```wl
boundAssumptions = TypeTheoryAssumptions[ForAll[{n}, n^2 <= 2^n]]
```

<!-- => {<|"Assumption" -> 4 <= n, "Statement" -> ∀_n∶ℕ 4 <= n ⇒ n^2 <= 2^n, "Proof" -> Proof complete, "Scope" -> "Local", "Method" -> "SymbolicDomain", "Witness" -> <|"n" -> 4|>, "Verified" -> True|>, <|"Assumption" -> n != 3, "Statement" -> ∀_n∶ℕ n != 3 ⇒ n^2 <= 2^n, "Proof" -> Proof complete, "Scope" -> "Local", "Method" -> "CounterexampleRefinement", "Witness" -> <|"n" -> 0|>, "Verified" -> True|>} -->

The first repaired statement is immediately declarable as a kernel-checked theorem:

```wl
TypeTheoryEnvironment[TypeTheoryTheorem[QuadraticBelowExponential, First[boundAssumptions]["Proof"]]][QuadraticBelowExponential]
```

<!-- => theorem QuadraticBelowExponential : ∀_n∶ℕ 4 <= n ⇒ n^2 <= 2^n -->

Similarly, `n < 2 n` needs `1 <= n`, natural-number subtraction cancellation needs `b <= a`, and multiplicative cancellation needs `1 <= c` (while the non-triviality gate filters out the useless assumption `a == b`):

```wl
TypeTheoryAssumptions[ForAll[{n}, n < 2 n]]
```

<!-- => {<|"Assumption" -> 1 <= n, "Statement" -> ∀_n∶ℕ 1 <= n ⇒ n < 2 n, "Proof" -> Proof complete, "Scope" -> "Local", "Method" -> "SymbolicDomain", "Witness" -> <|"n" -> 1|>, "Verified" -> True|>} -->

```wl
TypeTheoryAssumptions[ForAll[{a, b}, Subtract[a, b] + b == a]]
```

<!-- => {<|"Assumption" -> b <= a, "Statement" -> ∀_a∶ℕ ∀_b∶ℕ b <= a ⇒ (a - b) + b == a, "Proof" -> Proof complete, "Scope" -> "Local", "Method" -> "SymbolicDomain", "Witness" -> <|"a" -> 0, "b" -> 0|>, "Verified" -> True|>} -->

```wl
TypeTheoryAssumptions[ForAll[{a, b, c}, Implies[a c == b c, a == b]]]
```

<!-- => {<|"Assumption" -> 1 <= c, "Statement" -> ∀_a∶ℕ ∀_b∶ℕ ∀_c∶ℕ 1 <= c ⇒ a c == b c ⇒ a == b, "Proof" -> Proof complete, "Scope" -> "Local", ...|>} -->

### Missing Axioms, Algebraic Properties, and Open Proofs

In `"Constructive"`, both double-negation elimination and Peirce's law elicit the law of excluded middle via `"AxiomDiff"`:

```wl
TypeTheoryAssumptions[ForAll[{Typed[p, TypeUniverse[0]]}, Implies[Not[Not[p]], p]], "Constructive"]
```

<!-- => {<|"Assumption" -> ∀_p∶Prop p ∨ ¬p, "Statement" -> (∀_p∶Prop p ∨ ¬p) ⇒ ∀_p∶Prop ¬¬p ⇒ p, "Proof" -> Proof complete, "Scope" -> "Global", "Method" -> "AxiomDiff", "Witness" -> None, "Verified" -> True, "AxiomName" -> "excludedMiddle"|>} -->

```wl
TypeTheoryAssumptions[ForAll[{Typed[p, TypeUniverse[0]], Typed[q, TypeUniverse[0]]}, Implies[Implies[Implies[p, q], p], p]], "Constructive"]
```

<!-- => {<|"Assumption" -> ∀_p∶Prop p ∨ ¬p, "Statement" -> (∀_p∶Prop p ∨ ¬p) ⇒ ∀_p∶Prop ∀_q∶Prop ((p ⇒ q) ⇒ p) ⇒ p, "Proof" -> Proof complete, "Scope" -> "Global", "Method" -> "AxiomDiff", "Witness" -> None, "Verified" -> True, "AxiomName" -> "excludedMiddle"|>} -->

Over `magma`, the algebraic catalog discovers that commutativity and associativity together make `magmaOp[magmaOp[x, y], z] == magmaOp[x, magmaOp[z, y]]` provable:

```wl
TypeTheoryAssumptions[ForAll[{Typed[x, magmaCarrier], Typed[y, magmaCarrier], Typed[z, magmaCarrier]}, magmaOp[magmaOp[x, y], z] == magmaOp[x, magmaOp[z, y]]], magma]
```

<!-- => {<|"Assumption" -> (∀_x∶magmaCarrier ∀_y∶magmaCarrier magmaOp[x, y] == magmaOp[y, x]) ∧ (∀_x∶magmaCarrier ∀_y∶magmaCarrier ∀_z∶magmaCarrier magmaOp[magmaOp[x, y], z] == magmaOp[x, magmaOp[y, z]]), ..., "Method" -> "AlgebraicCatalog", "Verified" -> True|>} -->

Over `opaqueEnv`, the algebraic catalog finds that `opaqueInv[x] == x` implies injectivity:

```wl
TypeTheoryAssumptions[ForAll[{x, y}, Implies[opaqueInv[x] == opaqueInv[y], x == y]], opaqueEnv]
```

<!-- => {<|"Assumption" -> ∀_x∶ℕ opaqueInv[x] == x, ..., "Scope" -> "Global", "Method" -> "AlgebraicCatalog", "Verified" -> True|>} -->

When given an unfinished [TypeTheoryProof](), [TypeTheoryAssumptions]() abstracts each open goal into the assumption needed to close it:

```wl
openProof = TypeTheoryProof[ForAll[{n}, n == 0], {"Introduce"[n]}]
```

<!-- => Proof, 1 goal: n ∶ ℕ ⊢ n == 0 -->

```wl
TypeTheoryAssumptions[openProof]
```

<!-- => {<|"Assumption" -> ∀_n∶ℕ n == 0, "Statement" -> (∀_n∶ℕ n == 0) ⇒ ∀_n∶ℕ n == 0, "Proof" -> Proof complete, "Scope" -> "GoalHole", "Witness" -> None, "Method" -> "OpenGoalAbstraction", "Verified" -> True|>} -->

An already provable theorem needs no extra assumptions and returns `{}`:

```wl
TypeTheoryAssumptions[ForAll[{n}, n + 0 == n]]
```

<!-- => {} -->

## Discovering Non-Trivial Consequences with TypeTheoryConsequences

### How TypeTheoryConsequences Works Under the Hood

From a proposition *P* assumed true, infinitely many trivial statements follow ([True](), `P ∨ Q`, background theorems of arithmetic, or everything at all when *P* is false). [TypeTheoryConsequences]() filters out every form of noise:

1. **Inconsistency short-circuit (`"InconsistencyShortCircuit"`):** first checks whether <code>[Not]()[*P*]</code> is provable. If so, it immediately stops and returns [False]() tagged `"Inconsistent" -> True` with the refutation proof.
2. **Candidate generation:**
   - **Structural elimination & specialization (`"CanonicalSpecialization"`, `"DiagonalSpecialization"`):** unpacks conjunctions and existentials, instantiates universal hypotheses at canonical values (`0`, `1`), and forms diagonal specializations.
   - **Forward chaining (`"ForwardChaining"`):** matches hypothesis heads against environment lemmas such as `"lessEqualAntisymmetry"`.
   - **Symbolic projection (`"SymbolicProjection"`):** projects arithmetic equations and inequalities onto single variables with [Reduce]() to discover tight upper and lower bounds.
   - **Equational and algebraic discovery (`"EquationalDiscovery"`):** checks classic consequences of equational hypotheses (injectivity, surjectivity, iterated identities) and classical logic principles (double-negation elimination, Peirce's law, contraposition).
3. **Four quality gates:**
   - **Kernel proof gate:** builds and kernel-verifies a proof of `P ⇒ C`.
   - **Exact proof-term relevance gate:** opens the normalized proof term `(h : P) ↦ body` and verifies that the hypothesis variable `h` genuinely occurs free in `body`, guaranteeing *P* was actually used.
   - **Non-background novelty gate:** rejects any *C* that is already provable without *P*.
   - **Non-triviality and subsumption gate:** rejects [True](), *P* itself, equivalents (unless `"IncludeEquivalents" -> True`), and consequences implied by stronger discovered consequences.

### Equational, Arithmetic, Order, and Classical Consequences

Assuming `opaqueInv` in `opaqueEnv` is an involution yields canonical instances, surjectivity, injectivity, and the third-iterate identity:

```wl
invConsequences = TypeTheoryConsequences[ForAll[{x}, opaqueInv[opaqueInv[x]] == x], opaqueEnv]
```

<!-- => {<|"Consequence" -> opaqueInv[opaqueInv[0]] == 0, ..., "Method" -> "CanonicalSpecialization", "Inconsistent" -> False, "Verified" -> True|>, ..., <|"Consequence" -> ∀_y∶ℕ ∃_x∶ℕ opaqueInv[x] == y, ..., "Method" -> "EquationalDiscovery", "Inconsistent" -> False, "Verified" -> True|>, ...} -->

Every consequence proof is declarable as a theorem:

```wl
TypeTheoryEnvironment[opaqueEnv, {TypeTheoryTheorem[InvolutionInstance, First[invConsequences]["Proof"]]}][InvolutionInstance]
```

<!-- => theorem InvolutionInstance : (∀_x∶ℕ opaqueInv[opaqueInv[x]] == x) ⇒ opaqueInv[opaqueInv[0]] == 0 -->

Declare constants for symbolic projection and order forward chaining:

```wl
varsEnv = TypeTheoryEnvironment[{
    TypeTheoryAxiom[xCircle, Naturals],
    TypeTheoryAxiom[yCircle, Naturals],
    TypeTheoryAxiom[aSum, Naturals],
    TypeTheoryAxiom[bSum, Naturals],
    TypeTheoryAxiom[aOrd, Naturals],
    TypeTheoryAxiom[bOrd, Naturals]
}]
```

<!-- => TypeTheoryEnvironment summary box: 281 constants -->

From polynomial and linear equations over the natural numbers, symbolic projection derives tight coordinate bounds:

```wl
TypeTheoryConsequences[xCircle^2 + yCircle^2 == 25, varsEnv]
```

<!-- => {<|"Consequence" -> xCircle <= 5, "Statement" -> xCircle^2 + yCircle^2 == 25 ⇒ xCircle <= 5, "Proof" -> Proof complete, "Method" -> "SymbolicProjection", "Inconsistent" -> False, "Verified" -> True|>, <|"Consequence" -> yCircle <= 5, "Statement" -> xCircle^2 + yCircle^2 == 25 ⇒ yCircle <= 5, "Proof" -> Proof complete, "Method" -> "SymbolicProjection", "Inconsistent" -> False, "Verified" -> True|>} -->

```wl
TypeTheoryConsequences[aSum + bSum == 4, varsEnv]
```

<!-- => {<|"Consequence" -> aSum <= 4, "Statement" -> aSum + bSum == 4 ⇒ aSum <= 4, "Proof" -> Proof complete, "Method" -> "SymbolicProjection", "Inconsistent" -> False, "Verified" -> True|>, <|"Consequence" -> bSum <= 4, "Statement" -> aSum + bSum == 4 ⇒ bSum <= 4, "Proof" -> Proof complete, "Method" -> "SymbolicProjection", "Inconsistent" -> False, "Verified" -> True|>} -->

From a conjunction of inequalities, forward chaining applies `"lessEqualAntisymmetry"` to derive equality:

```wl
orderConsequences = TypeTheoryConsequences[And[aOrd <= bOrd, bOrd <= aOrd], varsEnv]
```

<!-- => {<|"Consequence" -> aOrd == bOrd, "Statement" -> aOrd <= bOrd ∧ bOrd <= aOrd ⇒ aOrd == bOrd, "Proof" -> Proof complete, "Method" -> "ForwardChaining", "Inconsistent" -> False, "Verified" -> True|>} -->

Check the proof term directly with [TypeTheoryCheck]():

```wl
TypeTheoryCheck[First[orderConsequences]["Proof"]["Term"], First[orderConsequences]["Statement"]]
```

<!-- => Success["TypeChecked", ...] -->

Assuming excluded middle in `"Constructive"` yields double-negation elimination, Peirce's law, and contraposition:

```wl
TypeTheoryConsequences[ForAll[{Typed[p, TypeUniverse[0]]}, Or[p, Not[p]]], "Constructive"]
```

<!-- => {<|"Consequence" -> ∀_p∶Prop ¬¬p ⇒ p, ..., "Verified" -> True|>, <|"Consequence" -> ∀_p∶Prop ∀_q∶Prop ((p ⇒ q) ⇒ p) ⇒ p, ..., "Verified" -> True|>, <|"Consequence" -> ∀_p∶Prop ∀_q∶Prop (¬q ⇒ ¬p) ⇒ p ⇒ q, ..., "Verified" -> True|>} -->

Finally, an inconsistent assumption short-circuits immediately to [False]() rather than flooding the output with ex-falso consequences:

```wl
TypeTheoryConsequences[ForAll[{n}, n^2 <= 2^n]]
```

<!-- => {<|"Consequence" -> False, "Statement" -> (∀_n∶ℕ n^2 <= 2^n) ⇒ False, "Proof" -> Proof complete, "Method" -> "InconsistencyShortCircuit", "Inconsistent" -> True, "Verified" -> True|>} -->

```wl
TypeTheoryConsequences[2 + 2 == 5]
```

<!-- => {<|"Consequence" -> False, "Statement" -> 2 + 2 == 5 ⇒ False, "Proof" -> Proof complete, "Method" -> "InconsistencyShortCircuit", "Inconsistent" -> True, "Verified" -> True|>} -->

## Crossing the Heuristic Barrier with LLMFunction

### How the LLM Layer Works Under the Hood

By default (`Method -> Automatic`), all four superfunctions run strictly offline. When [Method]() includes `"LLM"`, the untrusted LLM layer constructs a compact prompt containing:

- the proposition formatted via [TypeTheoryExpression]() (never internal kernel terms);
- the relevant user-declared constants from the environment, marking definitions as unfoldable with `"RewriteRepeated"`;
- the exact TypeTheory tactic or surface syntax rules.

It invokes [LLMFunction]() using Wolfram AI's default model (`"LLMEvaluator" -> Automatic`) or a user-provided [LLMConfiguration]() (such as custom `"Prompts"` guidance), parses the reply strictly into held [HoldComplete]() expressions so nothing can evaluate arbitrarily, and submits every candidate to the exact same [TypeTheoryProof]() execution, quality gates, and trusted kernel verification. An LLM hallucination is rejected silently; only kernel-verified theorems can ever be returned.

### Proving Recursive Definitions Where Heuristics Stop

Formalize Gauss's triangular numbers and list summation via [TypeTheoryFormalize]():

```wl
triangular[0] = 0;
triangular[n_Integer] := n + triangular[n - 1];
total[{}] = 0;
total[{x_, rest___}] := x + total[{rest}];
programs = TypeTheoryEnvironment[Join[TypeTheoryFormalize[triangular], TypeTheoryFormalize[total]]]
```

<!-- => TypeTheoryEnvironment summary box: 277 constants -->

The offline heuristic portfolio does not unfold user-defined recursive definitions during induction, so [TypeTheoryDetermine]() honestly reports `"Undetermined"` on Gauss's formula:

```wl
TypeTheoryDetermine[ForAll[{n}, 2 triangular[n] == n (n + 1)], programs]
```

<!-- => <|"Status" -> "Undetermined", "Statement" -> ∀_n∶ℕ 2 triangular[n] == n (n + 1), "Proof" -> None, "Counterexample" -> None, "Witness" -> None, "Models" -> None, "ComputationallyDecidable" -> False, "Method" -> "SearchExhausted", "Details" -> <||>|> -->

Enabling `"LLM"` queries Wolfram AI's default model with no custom prompt; it proposes induction on `n` with `"RewriteRepeated"[triangular]` and `"PolynomialReduce"`, and the kernel verifies the proof:

```wl
gaussLLM = TypeTheoryDetermine[
    ForAll[{n}, 2 triangular[n] == n (n + 1)],
    programs,
    Method -> {"Heuristic", "LLM"},
    TimeConstraint -> 45
]
```

<!-- => <|"Status" -> "Proved", "Statement" -> ∀_n∶ℕ 2 triangular[n] == n (n + 1), "Proof" -> Proof complete, ..., "Method" -> "LLMVerified", "Details" -> <|"Tactics" -> ...|>|> -->

Declare Gauss's formula as a kernel-checked theorem:

```wl
TypeTheoryEnvironment[programs, {TypeTheoryTheorem[GaussFormula, gaussLLM["Proof"]]}][GaussFormula]
```

<!-- => theorem GaussFormula : ∀_n∶ℕ 2 triangular[n] == n (n + 1) -->

List summation over [Join]() also stops offline heuristics at `"Undetermined"`:

```wl
TypeTheoryDetermine[ForAll[{a, b}, total[Join[a, b]] == total[a] + total[b]], programs]
```

<!-- => <|"Status" -> "Undetermined", "Statement" -> ∀_a∶{ℕ} ∀_b∶{ℕ} total[Join[a, b]] == total[a] + total[b], "Proof" -> None, ..., "Method" -> "SearchExhausted", "Details" -> <||>|> -->

Passing prompt guidance through [LLMConfiguration]() steers Wolfram AI's default model to the exact structural-induction and rewriting proof, which the kernel checks:

```wl
TypeTheoryDetermine[
    ForAll[{a, b}, total[Join[a, b]] == total[a] + total[b]],
    programs,
    Method -> {"Heuristic", "LLM"},
    "LLMEvaluator" -> LLMConfiguration[<|"Prompts" -> "To prove statements about total[Join[a, b]], introduce a and b, do Induction on a, use RewriteRepeated[total, Join] then Ring on the base case, then Introduce[x, rest, ih], RewriteRepeated[total, Join, ih], and Ring."|>],
    TimeConstraint -> 45
]
```

<!-- => <|"Status" -> "Proved", "Statement" -> ∀_a∶{ℕ} ∀_b∶{ℕ} total[Join[a, b]] == total[a] + total[b], "Proof" -> Proof complete, ..., "Method" -> "LLMVerified", "Details" -> <|"Tactics" -> ...|>|> -->

### Cross-Function Assumptions and Functional-Equation Consequences via LLMFunction

Declare two opaque functions `leftInverse` and `fnG`, plus an additive function `additiveF`:

```wl
fnEnv = TypeTheoryEnvironment[{
    TypeTheoryAxiom[leftInverse, Naturals -> Naturals],
    TypeTheoryAxiom[fnG, Naturals -> Naturals],
    TypeTheoryAxiom[additiveF, Naturals -> Naturals]
}]
```

<!-- => TypeTheoryEnvironment summary box: 278 constants -->

Offline heuristics inspect only single-function laws (`fnG[x] == x`, `fnG[fnG[x]] == x`) and never synthesize a cross-function hypothesis relating `leftInverse` and `fnG`. With `Method -> "LLM"` and prompt guidance, [TypeTheoryAssumptions]() discovers that a left inverse implies injectivity and verifies the proof in the kernel:

```wl
TypeTheoryAssumptions[
    ForAll[{x, y}, Implies[fnG[x] == fnG[y], x == y]],
    fnEnv,
    Method -> "LLM",
    "LLMEvaluator" -> LLMConfiguration[<|"Prompts" -> "Suggest an assumption relating leftInverse and fnG (such as leftInverse being a left inverse of fnG) that implies fnG is injective."|>],
    TimeConstraint -> 45
]
```

<!-- => {<|"Assumption" -> ∀_n∶ℕ leftInverse[fnG[n]] == n, ..., "Scope" -> "Global", "Method" -> "LLM", "Witness" -> None, "Verified" -> True|>} -->

Similarly, from the Cauchy additivity law `additiveF[x + y] == additiveF[x] + additiveF[y]`, `Method -> "LLM"` proposes the doubling identity `additiveF[x + x] == additiveF[x] + additiveF[x]`, which passes both kernel verification and exact proof-term relevance checking:

```wl
TypeTheoryConsequences[
    ForAll[{x, y}, additiveF[x + y] == additiveF[x] + additiveF[y]],
    fnEnv,
    Method -> "LLM",
    TimeConstraint -> 45
]
```

<!-- => {<|"Consequence" -> ∀_x∶ℕ additiveF[x + x] == additiveF[x] + additiveF[x], ..., "Method" -> "LLM", "Inconsistent" -> False, "Verified" -> True|>} -->

## Certifying Termination and Divergence with TypeTheoryTermination

### How TypeTheoryTermination Works Under the Hood

[TypeTheoryTermination]() dispatches across six specialized analyzers depending on whether the target is a pointwise expression, a global rewrite system, an integer loop or recursive function, or a total definition:

1. **Pointwise rewrite execution (`"ConcreteExecution"`):** encodes the rules into an environment over [Expressions]() using `"Meaning" -> "Rules"`, defines an iteration combinator `iterateReplaceAll`, computes up to `"MaxSteps"`, and produces a kernel proof that step `k` reaches a fixed point.
2. **Global rewrite termination (`"PolynomialWeightInterpretation"`):** assigns positive polynomial head weights via [FindInstance]() (with a bounded grid search fallback for nonlinear constraints), defines `expressionWeight : Expressions -> ℕ` in an extended environment, and proves `expressionWeight[rhs] < expressionWeight[lhs]` for every rule in the kernel.
3. **Pointwise lasso cycle induction (`"LassoCycleInduction"`):** detects a repeated expression state `(PrefixLength, Period, States)` under `iterateDownValues` and proves by induction on the step count `n` that the iterate remains on the cycle and never equals `"none"`.
4. **Unbounded self-embedding divergence (`"SelfEmbeddingDivergenceInvariant"`):** detects self-embedding rules such as `growFn[x_] := growFn[x + 1]` and proves by induction that `Exists[x, iterateDownValues[n, growFn[0]] == some[growFn[x]]]`, hence never `"none"`.
5. **Farkas affine ranking functions and conditional termination (`"FarkasAffineRankingFunction"`, `"ConditionalFarkasAndDivergence"`):** extracts `(Init, Guard, Step)` from integer [While]() loops and recursive [If]() functions, solves Farkas constraints for an affine measure `μ(n, i)`, and proves `guard ⇒ 0 <= μ ∧ μ(step) < μ` in `"Integers"`. When some inputs terminate and others diverge, it synthesizes both the termination precondition with `"TerminationProof"` and a concrete `"NonTerminationWitness"` with an inductive `"NonTerminationProof"`.
6. **Structural recursion totality (`"StructuralRecursor"`):** when [TypeTheoryFormalize]() translates a symbol directly into a kernel-checked [TypeTheoryDefinition]() over an inductive recursor, every input terminates by strong normalization of the type theory.

### Pointwise and Global Rewrite Termination

One-step and two-step pointwise termination under a commuting rewrite rule:

```wl
TypeTheoryTermination[rwA[rwB[0]], {rwA[rwB[x_]] :> rwB[rwA[x]]}]
```

<!-- => <|"Status" -> "Terminating", "Target" -> rwA[rwB[0]], "Steps" -> 1, "NormalForm" -> rwB[rwA[0]], "Statement" -> ..., "Proof" -> Proof complete, "Method" -> "ConcreteExecution", "Verified" -> True|> -->

```wl
TypeTheoryTermination[rwA[rwB[rwB[0]]], {rwA[rwB[x_]] :> rwB[rwA[x]]}]
```

<!-- => <|"Status" -> "Terminating", "Target" -> rwA[rwB[rwB[0]]], "Steps" -> 2, "NormalForm" -> rwB[rwB[rwA[0]]], "Statement" -> ..., "Proof" -> Proof complete, "Method" -> "ConcreteExecution", "Verified" -> True|> -->

Global termination of two different rewrite systems certified via polynomial weight interpretations:

```wl
TypeTheoryTermination[{rwA[rwB[x_]] :> rwB[rwA[x]]}]
```

<!-- => <|"Status" -> "Terminating", "Target" -> {rwA[rwB[x_]] :> rwB[rwA[x]]}, "Measure" -> ..., "Statement" -> ..., "Proof" -> Proof complete, "Method" -> "PolynomialWeightInterpretation", "Verified" -> True|> -->

```wl
TypeTheoryTermination[{nest[nest[x_]] :> nest[x]}]
```

<!-- => <|"Status" -> "Terminating", "Target" -> {nest[nest[x_]] :> nest[x]}, "Measure" -> ..., "Statement" -> ..., "Proof" -> Proof complete, "Method" -> "PolynomialWeightInterpretation", "Verified" -> True|> -->

### Certified Non-Termination: Lassos and Unbounded Growth

A period-1 fixed cycle and a period-2 alternating cycle are both certified `"NonTerminating"` by lasso cycle induction:

```wl
lassoFn[x_] := lassoFn[x];
TypeTheoryTermination[lassoFn[0]]
```

<!-- => <|"Status" -> "NonTerminating", "Target" -> lassoFn[0], "Cycle" -> <|"PrefixLength" -> 0, "Period" -> 1, "States" -> {lassoFn[0]}|>, "Statement" -> ..., "Proof" -> Proof complete, "Method" -> "LassoCycleInduction", "Verified" -> True|> -->

```wl
toggle[0] := toggle[1];
toggle[1] := toggle[0];
TypeTheoryTermination[toggle[0]]
```

<!-- => <|"Status" -> "NonTerminating", "Target" -> toggle[0], "Cycle" -> <|"PrefixLength" -> 0, "Period" -> 2, "States" -> {toggle[0], toggle[1]}|>, "Statement" -> ..., "Proof" -> Proof complete, "Method" -> "LassoCycleInduction", "Verified" -> True|> -->

An unbounded diverging rewrite rule never repeats a state, so [TypeTheoryTermination]() switches to a self-embedding divergence invariant:

```wl
growFn[x_] := growFn[x + 1];
TypeTheoryTermination[growFn, "Meaning" -> "Rules"]
```

<!-- => <|"Status" -> "NonTerminating", "Target" -> growFn, "Statement" -> ..., "Proof" -> Proof complete, "Method" -> "SelfEmbeddingDivergenceInvariant", "Verified" -> True|> -->

### Integer Loops, Conditional Termination, and Structural Recursion

Both a countdown [While]() loop (measure `i`) and a count-up [While]() loop (measure `n - i`) receive Farkas affine ranking functions proved in `"Integers"`:

```wl
sumLoop[n_Integer] := Module[{i = n, s = 0}, While[i > 0, s += i; i--]; s];
sumLoopRes = TypeTheoryTermination[sumLoop]
```

<!-- => <|"Status" -> "Terminating", "Target" -> sumLoop, "Measure" -> "i", "FuelBound" -> Max[0, n] + 1, "Statement" -> ..., "Proof" -> Proof complete, "Method" -> "FarkasAffineRankingFunction", "Verified" -> True|> -->

Declare the descent proof as a kernel theorem in `"Integers"`:

```wl
TypeTheoryEnvironment["Integers", {TypeTheoryTheorem[SumLoopTerminates, sumLoopRes["Proof"]]}][SumLoopTerminates]
```

<!-- => theorem SumLoopTerminates : ℤ → ∀_i∶ℤ 0 < i ⇒ 0 <= i ∧ i - 1 < i -->

A count-up loop synthesizes the relative measure `n - i`:

```wl
countUp[n_Integer] := Module[{i = 0, s = 0}, While[i < n, s += i; i++]; s];
TypeTheoryTermination[countUp]
```

<!-- => <|"Status" -> "Terminating", "Target" -> countUp, "Measure" -> -i + n, "FuelBound" -> Max[0, n] + 1, "Statement" -> ..., "Proof" -> Proof complete, "Method" -> "FarkasAffineRankingFunction", "Verified" -> True|> -->

An integer factorial with base case `n == 0` terminates on non-negative inputs and diverges on negative inputs. [TypeTheoryTermination]() certifies both sides simultaneously:

```wl
factFn[n_Integer] := If[n == 0, 1, n * factFn[n - 1]];
factRes = TypeTheoryTermination[factFn]
```

<!-- => <|"Status" -> "ConditionallyTerminating", "Target" -> factFn, "Precondition" -> "0 <= n", "Measure" -> "n", "TerminationProof" -> Proof complete, "NonTerminationWitness" -> <|"n" -> -1|>, "NonTerminationProof" -> Proof complete, "Method" -> "ConditionalFarkasAndDivergence", "Verified" -> True|> -->

Finally, functions formalized directly as definitions over inductive recursors, both simple definitions and structural recursions like `triangular`, are total by construction:

```wl
doubleInt[n_Integer] := 2 n;
TypeTheoryTermination[doubleInt, "Meaning" -> "Function"]
```

<!-- => <|"Status" -> "Terminating", "Target" -> doubleInt, "Method" -> "StructuralRecursor", "Verified" -> True, ...|> -->

```wl
TypeTheoryTermination[triangular, "Meaning" -> "Function"]
```

<!-- => <|"Status" -> "Terminating", "Target" -> triangular, "Method" -> "StructuralRecursor", "Verified" -> True, ...|> -->

## Putting All Four Together

In practice the four superfunctions form a single exploratory loop:

1. Test a conjecture with [TypeTheoryDetermine](): either get a kernel-checked theorem, a concrete counterexample, certified independence models, or an honest `"Undetermined"` (optionally escalating to `Method -> {"Heuristic", "LLM"}`).
2. When a conjecture fails or is independent, ask [TypeTheoryAssumptions]() for the missing domain guards, axioms, or algebraic laws that repair it into a theorem.
3. When exploring what a hypothesis buys, ask [TypeTheoryConsequences]() for its non-trivial, genuinely dependent consequences (or an immediate inconsistency diagnosis).
4. Whenever the statement involves a Wolfram Language program or rewrite rule formalized with [TypeTheoryFormalize](), ask [TypeTheoryTermination]() to certify totality, loop ranking functions, preconditions, or divergence witnesses.
