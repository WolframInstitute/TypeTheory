---
Template: TechNote
Name: Wolfram23Universality
Title: The Universality of Wolfram's (2,3) Turing Machine
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/tutorial/Wolfram23Universality
Keywords: [Turing machine, universality, Wolfram 2-3 machine, Alex Smith, forward simulation, 2-tag system, cyclic tag system, Cocke-Minsky, Cook, lookahead machine, proof]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TypeTheoryIntroduction, ThePrelude, ProgramsAndProofs, WolframLanguageTheorems]
---

The goal of this formalization is Alex Smith's theorem that Wolfram's 2-state, 3-color Turing machine is universal: for any well-formed binary Turing machine, any valid starting configuration and any finite run of `n` steps, there exist a starting configuration of Wolfram's (2,3) machine in state A, decoding parameters, a strictly increasing sequence of step times and a final time `T` such that the run stays on its tape through time `T`, decodes at each scheduled time to the binary machine's corresponding configuration (up to trailing blanks), and exits cleanly to the right at time `T + 1`. Smith's proof reaches the machine through a chain of emulations, six rungs from binary Turing machines down to the (2,3) machine, each a forward simulation between step systems, and a seventh that composes them.

All definitions and theorems of the formalization live in <code>[TypeTheoryEnvironment]()["Wolfram23"]</code>, checked by TypeTheory's kernel. The environment extends the prelude, axioms included; each theorem's [TypeTheoryAxiomClosure]() shows what it rests on, and every theorem shown here rests on the kernel alone.

| Rung | Emulation | Target steps per source step | Status |
|---|---|---|---|
| Framework | Partial step systems, `"forwardSimulation"`, lifting and composition | | Proved |
| 1 | Binary Turing machine to 2-tag system (Cocke and Minsky) | 3 tag rounds per right move, 5 per left move | Proved |
| 2 | 2-tag system to cyclic tag system (Cook) | `k + k` cyclic tag steps (one full cycle of `2 k` appendants) | Proved |
| Glue (1 and 2) | Binary Turing machine to cyclic tag system (`"machineToCyclicTag"`) | Composition of rungs 1 and 2 over `84 S + 1` symbols | Proved |
| 3 | Cyclic tag system to System 5 | `x + 1` or `x + 2` (two doubled steps per source step) | Planned |
| 4 | System 5 to System 4 | Existential, for parameter `f` large enough | Planned |
| 5 | System 4 to System 3 (parity blocks of width `2^w`) | At least 1 | Planned |
| 6 | System 3 to Wolfram's (2,3) machine (Systems 3 to 0 and tape extension) | 1 or 3 | Proved |
| 7 | Composition, decoders, confinement and exit | Composition of rungs 1 to 6 | Planned |

This draft covers the rungs proved so far: the simulation framework, rung 6 (System 3 to Wolfram's (2,3) machine), rung 2 (2-tag systems to cyclic tag systems), rung 1 (binary Turing machines to 2-tag systems), and the glue that joins rungs 1 and 2 into `"machineToCyclicTag"`.

Load the environment:

```wl
wolfram23 = TypeTheoryEnvironment["Wolfram23"]
```

<!-- => TypeTheoryEnvironment summary box: 468 constants -->

[Information]() shows the constants it declares on top of the prelude, by kind:

```wl
Information[wolfram23, "Kinds"]
```

<!-- => <|"InductiveType" -> 38, "Constructor" -> 79, "Recursor" -> 39, "Definition" -> 153, "Quotient" -> 4, "Theorem" -> 151, "Axiom" -> 4|> -->

## The Framework

Every machine and rewriting system along the ladder is a single partial step function `step : S -> Option[S]` on a type `S` of configurations. A step that succeeds gives `"some"[s']`; a halting state or a head leaving a finite tape gives `"none"`. Iterating `step` for `n` steps threads the optional configuration through `"optionBind"`:

```wl
wolfram23["steps"]
```

<!-- => definition steps : ∀_{S ∶ Type} (S → Option[S]) → ℕ → S → Option[S] := {S ∶ Type} (step ∶ S → Option[S]) (n ∶ ℕ) (s ∶ S) ↦ ℕ_rec[(k ∶ ℕ) ↦ Option[S], some[s], (k ∶ ℕ) (previous ∶ Option[S]) ↦ optionBind[previous, step], n] -->

Iteration obeys the additive law `"stepsAdd"`: taking `m + n` steps is taking `m` steps and then `n` more from whatever configuration they reach:

```wl
wolfram23["stepsAdd"]
```

<!-- => theorem stepsAdd : ∀_S∶Type ∀_step∶S → Option[S] ∀_m∶ℕ ∀_n∶ℕ ∀_s∶S steps[step, m + n, s] == optionBind[steps[step, m, s], (y ∶ S) ↦ steps[step, n, y]] -->

Each rung is stated as a `"forwardSimulation"` along a binary relation `R : S -> T -> Prop`. Whenever `R[s, t]` holds and the source system `f` steps from `s` to `s2`, the target system `g` takes `k >= 1` steps from `t` to some `t2` with `R[s2, t2]`. Relations are needed for two reasons: Wolfram's (2,3) machine has no periodic orbits, so no time-independent function can follow a cyclic tag system step for step; and for finite runs the remaining step budgets live inside `R`:

```wl
wolfram23["forwardSimulation"]
```

<!-- => definition forwardSimulation : ∀_{S ∶ Type} ∀_{T ∶ Type} (S → Option[S]) → (T → Option[T]) → (S → T → Prop) → Prop := {S ∶ Type} {T ∶ Type} (f ∶ S → Option[S]) (g ∶ T → Option[T]) (R ∶ S → T → Prop) ↦ ∀_s∶S ∀_t∶T ∀_s2∶S R[s, t] ⇒ f[s] == some[s2] ⇒ ∃_k∶ℕ (1 ≤ k ∧ ∃_t2∶T (steps[g, k, t] == some[t2] ∧ R[s2, t2])) -->

By induction on `n`, `"forwardSimulationSteps"` lifts a single-step simulation to multi-step runs: `n` steps of `f` are matched by `j >= n` steps of `g`:

```wl
wolfram23["forwardSimulationSteps"]
```

<!-- => theorem forwardSimulationSteps : ∀_S∶Type ∀_T∶Type ∀_f∶S → Option[S] ∀_g∶T → Option[T] ∀_R∶S → T → Prop forwardSimulation[f, g, R] ⇒ ∀_n∶ℕ ∀_s∶S ∀_t∶T ∀_s2∶S R[s, t] ⇒ steps[f, n, s] == some[s2] ⇒ ∃_j∶ℕ (n ≤ j ∧ ∃_t2∶T (steps[g, j, t] == some[t2] ∧ R[s2, t2])) -->

Two simulations compose through `"forwardSimulationCompose"` along the relational composition `∃_t∶T (R[s, t] ∧ R2[t, u])`: a step of `f` gives `k >= 1` steps of `g`, and `"forwardSimulationSteps"` lifts those `k` steps to `j >= k >= 1` steps of `h`:

```wl
wolfram23["forwardSimulationCompose"]
```

<!-- => theorem forwardSimulationCompose : ∀_S∶Type ∀_T∶Type ∀_U∶Type ∀_f∶S → Option[S] ∀_g∶T → Option[T] ∀_h∶U → Option[U] ∀_R∶S → T → Prop ∀_R2∶T → U → Prop forwardSimulation[f, g, R] ⇒ forwardSimulation[g, h, R2] ⇒ forwardSimulation[f, h, (s ∶ S) (u ∶ U) ↦ ∃_t∶T (R[s, t] ∧ R2[t, u])] -->

Two recurring special cases construct simulations in one line. First, a map `phi : S -> T` that commutes with `f` and `g` induces a one-step simulation along `d == phi[c]`:

```wl
wolfram23["relabelingSimulation"]
```

<!-- => theorem relabelingSimulation : ∀_S∶Type ∀_T∶Type ∀_f∶S → Option[S] ∀_g∶T → Option[T] ∀_phi∶S → T (∀_c∶S g[phi[c]] == optionMap[phi, f[c]]) ⇒ forwardSimulation[f, g, (c ∶ S) (d ∶ T) ↦ d == phi[c]] -->

Second, a step function `g` that agrees with `f` wherever `f` is defined (stated as `g[c] == orElse[f[c], g[c]]`, so cases where `f[c]` is `"none"` reduce to `g[c] == g[c]`) simulates `f` along equality:

```wl
wolfram23["agreementSimulation"]
```

<!-- => theorem agreementSimulation : ∀_S∶Type ∀_f∶S → Option[S] ∀_g∶S → Option[S] (∀_c∶S g[c] == orElse[f[c], g[c]]) ⇒ forwardSimulation[f, g, (c ∶ S) (d ∶ S) ↦ d == c] -->

## Rung 6: System 3 to Wolfram's (2,3) Machine

Rung 6 sits at the bottom of the ladder. It connects System 3, a 3-state lookahead machine whose state-A and state-B scans leave the tape clean, to Wolfram's 2-state, 3-color Turing machine through two intermediate lookahead machines, Systems 2 and 1, and then bridges the finite-tape lookahead semantics to the standard tape-growing Turing machine.

### The Two Systems

Systems 3, 2, 1 and 0 all share one configuration type, `"LookaheadConfiguration"`: a zipper holding the cells left of the head (nearest first), the head cell, the cells right of the head (nearest first), and the state (`"stateA"`, `"stateB"`, or `"stateC"`), over the three colors `"color0"`, `"color1"`, `"color2"`:

```wl
wolfram23["LookaheadConfiguration"]
```

<!-- => inductive LookaheadConfiguration : Type | lookaheadConfiguration : {Color} → Color → {Color} → LookaheadState → LookaheadConfiguration -->

A rule of `"LookaheadRule"` either rewrites the head alone (`"oneCell"`) or inspects and rewrites the head together with its immediate right neighbor (`"twoCells"`). System 0 is Wolfram's (2,3) machine (with `"stateC"` unused): `A0 -> B1R`, `A1 -> A2L`, `A2 -> A1L`, `B0 -> A2L`, `B1 -> B2R`, `B2 -> A0R`. System 3 has rules `A0 -> B2R`, `A1 -> A1L`, `A2 -> A2L`, `B0 -> A2L`, `B1 -> B1R`, `B20 -> A00R`, `B21 -> C21R`, `B22 -> C22R`, `C0 -> A2L`, `C10 -> A00R`, `C11 -> C21R`, `C12 -> C22R`, and `C2 -> B1R`. Under `"lookaheadStep"`, moving past either end of the zipper gives `"none"`.

Take a System 3 configuration in state B reading color 2 with right neighbor 1:

```wl
start3 = TypeTheoryTerm["lookaheadConfiguration"[{"color1"}, "color2", {"color1", "color0"}, "stateB"], wolfram23]
```

<!-- => lookaheadConfiguration[{color1}, color2, {color1, color0}, stateB] -->

One step of System 3 fires the two-cell rule `B21 -> C21R`, leaving color 2 on the left, moving right onto color 1, and entering state C:

```wl
NormalForm[TypeTheoryTerm["lookaheadStep"["system3", start3], wolfram23]]
```

<!-- => some[lookaheadConfiguration[{color2, color1}, color1, {color0}, stateC]] -->

Applying the two relabelings `"phi3"` (which swaps colors 1 and 2 on every cell left of the head, and on the head in state A) and `"phi2"` (which turns state C into state B with the head swapped) sends `start3` to a System 0 configuration:

```wl
start0 = NormalForm[TypeTheoryTerm["phi2"["phi3"[start3]], wolfram23]]
```

<!-- => lookaheadConfiguration[{color2}, color2, {color1, color0}, stateB] -->

From `start0`, System 0 takes three steps (`B2 -> A0R`, `A1 -> A2L`, `A0 -> B1R`):

```wl
NormalForm[TypeTheoryTerm["steps"["lookaheadStep"["system0"], 3, start0], wolfram23]]
```

<!-- => some[lookaheadConfiguration[{color1, color2}, color2, {color0}, stateB]] -->

That configuration is the exact `"phi2"`-after-`"phi3"` image of System 3's successor:

```wl
NormalForm[TypeTheoryTerm["phi2"["phi3"["lookaheadConfiguration"[{"color2", "color1"}, "color1", {"color0"}, "stateC"]]], wolfram23]]
```

<!-- => lookaheadConfiguration[{color1, color2}, color2, {color0}, stateB] -->

At the edge of the tape, `"lookaheadStep"` stops with `"none"`:

```wl
NormalForm[TypeTheoryTerm["lookaheadStep"["system0", "lookaheadConfiguration"[{"color2"}, "color0", {}, "stateA"]], wolfram23]]
```

<!-- => none ∶ Option[LookaheadConfiguration] -->

The standard Turing machine step `"turingMachineStep"` instead extends the tape by a blank `"color0"`:

```wl
NormalForm[TypeTheoryTerm["turingMachineStep"["system0", "lookaheadConfiguration"[{"color2"}, "color0", {}, "stateA"]], wolfram23]]
```

<!-- => some[lookaheadConfiguration[{color1, color2}, color0, {}, stateB]] -->

### The Relation and the Theorem

Composing the two relabelings `"phi3"` (System 3 to System 2) and `"phi2"` (System 2 to System 1) with equality (System 1 to System 0) gives `"system0Simulates3"`:

```wl
wolfram23["system0Simulates3"]
```

<!-- => theorem system0Simulates3 : forwardSimulation[lookaheadStep[system3], lookaheadStep[system0], (c ∶ LookaheadConfiguration) (e ∶ LookaheadConfiguration) ↦ ∃_d1∶LookaheadConfiguration ((∃_d2∶LookaheadConfiguration (d2 == phi3[c] ∧ d1 == phi2[d2])) ∧ e == d1)] -->

Composing once more with the bridge from `"lookaheadStep"["system0"]` to `"turingMachineStep"["system0"]` yields `"wolfram23Simulates3"`:

```wl
wolfram23["wolfram23Simulates3"]
```

<!-- => theorem wolfram23Simulates3 : forwardSimulation[lookaheadStep[system3], turingMachineStep[system0], (c ∶ LookaheadConfiguration) (g ∶ LookaheadConfiguration) ↦ ∃_e∶LookaheadConfiguration ((∃_d1∶LookaheadConfiguration ((∃_d2∶LookaheadConfiguration (d2 == phi3[c] ∧ d1 == phi2[d2])) ∧ e == d1)) ∧ g == e)] -->

Its axiom closure is empty; the theorem rests on the kernel alone:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm["wolfram23Simulates3", wolfram23]]
```

<!-- => <||> -->

### The Proof

Because `"phi3"` swaps every cell to the left of the head, moving left brings a swapped cell under the head. Proving the two relabeling equations therefore splits the entire zipper (state, head, right half and its first cell, and left half), after which every leaf computes by `"Reflexivity"`. For `"phi3"`:

```wl
wolfram23["phi3Step"]
```

<!-- => theorem phi3Step : ∀_c∶LookaheadConfiguration lookaheadStep[system2, phi3[c]] == optionMap[phi3, lookaheadStep[system3, c]] -->

And for `"phi2"`:

```wl
wolfram23["phi2Step"]
```

<!-- => theorem phi2Step : ∀_c∶LookaheadConfiguration lookaheadStep[system1, phi2[c]] == optionMap[phi2, lookaheadStep[system2, c]] -->

Between System 1 and System 0, `"system0Steps"[c]` is 3 on `B21` and `B22` and 1 otherwise. Stating agreement via `"orElse"` turns every case where System 1 stops into a reflexivity equation, so a single case tree (also splitting the cell beyond the neighbor in `B21` and `B22`) proves `"system0FollowsSystem1"`:

```wl
wolfram23["system0FollowsSystem1"]
```

<!-- => theorem system0FollowsSystem1 : ∀_c∶LookaheadConfiguration steps[lookaheadStep[system0], system0Steps[c], c] == orElse[lookaheadStep[system1, c], steps[lookaheadStep[system0], system0Steps[c], c]] -->

`"Decide"` on each branch proves that the step count is always at least 1:

```wl
wolfram23["system0StepsPositive"]
```

<!-- => theorem system0StepsPositive : ∀_c∶LookaheadConfiguration 1 ≤ system0Steps[c] -->

Together they prove `"system0Simulates1"`:

```wl
wolfram23["system0Simulates1"]
```

<!-- => theorem system0Simulates1 : forwardSimulation[lookaheadStep[system1], lookaheadStep[system0], (c ∶ LookaheadConfiguration) (d ∶ LookaheadConfiguration) ↦ d == c] -->

One more zipper split proves that the standard machine agrees with `"lookaheadStep"["system0"]` wherever the head stays on the tape:

```wl
wolfram23["turingMachineFollowsSystem0"]
```

<!-- => theorem turingMachineFollowsSystem0 : ∀_c∶LookaheadConfiguration turingMachineStep[system0, c] == orElse[lookaheadStep[system0, c], turingMachineStep[system0, c]] -->

The proof term of `"system0Simulates1"` builds the existential witness `"system0Steps"[s]` directly from `"system0StepsPositive"` and `"system0FollowsSystem1"`:

```wl
wolfram23["system0Simulates1"]["Term"]
```

<!-- => (s ∶ LookaheadConfiguration) (t ∶ LookaheadConfiguration) (s2 ∶ LookaheadConfiguration) (related ∶ t == s) (stepped ∶ lookaheadStep[system1, s] == some[s2]) ↦ existsIntroduction[system0Steps[s], andIntroduction[system0StepsPositive[s], existsIntroduction[s2, andIntroduction[equalityTransitivity[equalityTransitivity[equalityCongruence[(x ∶ LookaheadConfiguration) ↦ steps[lookaheadStep[system0], system0Steps[s], x], related], system0FollowsSystem1[s]], equalityCongruence[(o ∶ Option[LookaheadConfiguration]) ↦ orElse[o, steps[lookaheadStep[system0], system0Steps[s], s]], stepped]], equalityReflexivity[s2]]]]] ∶ forwardSimulation[lookaheadStep[system1], lookaheadStep[system0], (c ∶ LookaheadConfiguration) (d ∶ LookaheadConfiguration) ↦ d == c] -->

And [TypeTheoryProofTree]() draws the derivation of `"system0Simulates3"`: `"phi3Step"` and `"phi2Step"` each pass through `"relabelingSimulation"`, join by `"forwardSimulationCompose"`, and compose with `"system0Simulates1"`:

```wl
TypeTheoryProofTree[wolfram23["system0Simulates3"]["Term"]]
```

<!-- => derivation of system0Simulates3 by forwardSimulationCompose from forwardSimulationCompose (of relabelingSimulation[phi3Step] and relabelingSimulation[phi2Step]) and system0Simulates1 -->

## Rung 2: 2-Tag Systems to Cyclic Tag Systems

Rung 2 formalizes Cook's emulation of any 2-tag system over `{0, ..., k - 1}` by a cyclic tag system with `2 k` appendants.

### The Two Systems

A 2-tag system is polymorphic over its symbol type `S`: `"tagStep"[productions, w]` drops the first two symbols `a` and `b` of `w` and appends `productions[a]`, returning `"none"` when `w` has fewer than two symbols:

```wl
TypeTheoryType["tagStep", wolfram23]
```

<!-- => ∀_{S ∶ Type} (S → {S}) → {S} → Option[{S}] -->

A cyclic tag configuration holds a bit list `data` and a list of bit-list `appendants`. Each step of `"cyclicTagStep"` removes the first bit `b` of `data`, appends the first appendant `a` when `b` is `"true"` (and nothing when `"false"`), and rotates `a` to the back of `appendants`. Carrying the rotated appendants inside the configuration eliminates any phase counter:

```wl
wolfram23["CyclicTagConfiguration"]
```

<!-- => inductive CyclicTagConfiguration : Type | cyclicTagConfiguration : {𝔹} → {{𝔹}} → CyclicTagConfiguration -->

Take the two-symbol 2-tag system `0 -> {1}`, `1 -> {0, 0}`:

```wl
tagProductions = TypeTheoryTerm[Function[{Typed[i, Naturals]}, InductiveRecursor[Naturals][Function[{Typed[q, Naturals]}, {Naturals}], {1}, Function[{Typed[j, Naturals], Typed[r, {Naturals}]}, {0, 0}], i]], wolfram23]
```

<!-- => (i ∶ ℕ) ↦ ℕ_rec[(q ∶ ℕ) ↦ {ℕ}, {1}, (j ∶ ℕ) (r ∶ {ℕ}) ↦ {0, 0}, i] -->

One step of the 2-tag system on `{0, 1, 1}` deletes `0` and `1` and appends `{1}`:

```wl
NormalForm[TypeTheoryTerm["tagStep"[tagProductions, {0, 1, 1}], wolfram23]]
```

<!-- => some[{1, 1}] -->

On a standalone cyclic tag configuration with data `{true, false}` and appendants `{{true}, {false, false}}`, two steps append `{true}` under the first bit, nothing under the second, and rotate the appendants back to their starting order:

```wl
NormalForm[TypeTheoryTerm["steps"["cyclicTagStep", 2, "cyclicTagConfiguration"[{"true", "false"}, {{"true"}, {"false", "false"}}]], wolfram23]]
```

<!-- => some[cyclicTagConfiguration[{true}, {{true}, {false, false}}]] -->

In Cook's construction (`"cookConfiguration"`), each symbol `i < k` becomes a one-hot block `"oneHot"[k, i]` of `k` bits, and the `2 k` appendants consist of the `k` encoded productions followed by `k` empty appendants. Stepping the encoding of `{0, 1, 1}` for `2 + 2 = 4` cyclic tag steps gives:

```wl
NormalForm[TypeTheoryTerm["steps"["cyclicTagStep", 4, "cookConfiguration"[2, tagProductions, {0, 1, 1}]], wolfram23]]
```

<!-- => some[cyclicTagConfiguration[{false, true, false, true}, {{false, true}, {true, false, true, false}, {}, {}}]] -->

That matches the encoding of `{1, 1}` directly:

```wl
NormalForm[TypeTheoryTerm["cookConfiguration"[2, tagProductions, {1, 1}], wolfram23]]
```

<!-- => cyclicTagConfiguration[{false, true, false, true}, {{false, true}, {true, false, true, false}, {}, {}}] -->

### The Relation and the Theorem

A tag word `w` over natural numbers relates to a cyclic tag configuration `c` when `c == "cookConfiguration"[k, productions, w]` and `"allBelow"[k, w]` holds (every symbol `a` in `w` satisfies `a + 1 <= k`). Under the hypothesis that every production of a symbol below `k` stays below `k`, `"cookSimulation"` establishes the forward simulation:

```wl
wolfram23["cookSimulation"]
```

<!-- => theorem cookSimulation : ∀_k∶ℕ ∀_productions∶ℕ → {ℕ} (∀_i∶ℕ i + 1 ≤ k ⇒ allBelow[k, productions[i]]) ⇒ forwardSimulation[tagStep[productions], cyclicTagStep, (w ∶ {ℕ}) (c ∶ CyclicTagConfiguration) ↦ (c == cookConfiguration[k, productions, w] ∧ allBelow[k, w])] -->

It uses no axioms:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm["cookSimulation", wolfram23]]
```

<!-- => <||> -->

### The Proof

The workhorse of rung 2 is the block lemma `"cyclicTagBlock"`: stepping a cyclic tag system through a prefix `bits` of the data that matches a prefix `as` of the appendants in length consumes `bits`, appends `"selected"[bits, as]` (the appendants under the `"true"` bits, in order), and rotates `as` behind the remaining appendants `q`:

```wl
wolfram23["cyclicTagBlock"]
```

<!-- => theorem cyclicTagBlock : ∀_bits∶{𝔹} ∀_as∶{{𝔹}} ∀_r∶{𝔹} ∀_q∶{{𝔹}} Length[as] == Length[bits] ⇒ steps[cyclicTagStep, Length[bits], cyclicTagConfiguration[Join[bits, r], Join[as, q]]] == some[cyclicTagConfiguration[Join[r, selected[bits, as]], Join[q, as]]] -->

Two selection lemmas evaluate `"selected"` on the two halves of a cycle. A one-hot block at `i < k` selects `f[i]` from `"appendantsFrom"[f, k]`:

```wl
wolfram23["selectedOneHot"]
```

<!-- => theorem selectedOneHot : ∀_k∶ℕ ∀_i∶ℕ ∀_f∶ℕ → {𝔹} i + 1 ≤ k ⇒ selected[oneHot[k, i], appendantsFrom[f, k]] == f[i] -->

And any block against `"emptyAppendants"[k]` selects nothing:

```wl
wolfram23["selectedEmptyAppendants"]
```

<!-- => theorem selectedEmptyAppendants : ∀_k∶ℕ ∀_blocks∶{𝔹} selected[blocks, emptyAppendants[k]] == {} -->

Word encoding distributes over [Join]():

```wl
wolfram23["encodeWordJoin"]
```

<!-- => theorem encodeWordJoin : ∀_k∶ℕ ∀_u∶{ℕ} ∀_v∶{ℕ} encodeWord[k, Join[u, v]] == Join[encodeWord[k, u], encodeWord[k, v]] -->

Applying `"cyclicTagBlock"` twice (first `k` steps on `"oneHot"[k, a]` against the encoded productions, then `k` steps on `"oneHot"[k, b]` against the empty appendants) proves `"cookStep"`:

```wl
wolfram23["cookStep"]
```

<!-- => theorem cookStep : ∀_k∶ℕ ∀_productions∶ℕ → {ℕ} ∀_a∶ℕ ∀_b∶ℕ ∀_rest∶{ℕ} a + 1 ≤ k ⇒ b + 1 ≤ k ⇒ steps[cyclicTagStep, k + k, cookConfiguration[k, productions, Prepend•a•(Prepend•b•rest)]] == some[cookConfiguration[k, productions, Join[rest, productions[a]]]] -->

And `"allBelowJoin"` preserves the symbol bound across [Join]():

```wl
wolfram23["allBelowJoin"]
```

<!-- => theorem allBelowJoin : ∀_k∶ℕ ∀_u∶{ℕ} ∀_v∶{ℕ} allBelow[k, u] ⇒ allBelow[k, v] ⇒ allBelow[k, Join[u, v]] -->

To apply `"cyclicTagBlock"` with an explicit step count `n` (such as `k`), `"cyclicTagBlockSteps"` rewrites `n` to `Length[blocks]` using the recursor of [Equal](). Here is its proof term:

```wl
wolfram23["cyclicTagBlockSteps"]["Term"]
```

<!-- => (n ∶ ℕ) (blocks ∶ {𝔹}) (as ∶ {{𝔹}}) (r ∶ {𝔹}) (q ∶ {{𝔹}}) (blockLength ∶ Length[blocks] == n) (appendantsLength ∶ Length[as] == n) ↦ Equal_rec[ℕ, n, (y ∶ ℕ) (t ∶ n == y) ↦ (steps[cyclicTagStep, y, cyclicTagConfiguration[Join[blocks, r], Join[as, q]]] == some[cyclicTagConfiguration[Join[r, selected[blocks, as]], Join[q, as]]] ⇒ steps[cyclicTagStep, n, cyclicTagConfiguration[Join[blocks, r], Join[as, q]]] == some[cyclicTagConfiguration[Join[r, selected[blocks, as]], Join[q, as]]]), (p ∶ steps[cyclicTagStep, n, cyclicTagConfiguration[Join[blocks, r], Join[as, q]]] == some[cyclicTagConfiguration[Join[r, selected[blocks, as]], Join[q, as]]]) ↦ p, Length[blocks], equalitySymmetry[blockLength], cyclicTagBlock[blocks, as, r, q, equalityTransitivity[appendantsLength, equalitySymmetry[blockLength]]]] ∶ ∀_n∶ℕ ∀_blocks∶{𝔹} ∀_as∶{{𝔹}} ∀_r∶{𝔹} ∀_q∶{{𝔹}} Length[blocks] == n ⇒ Length[as] == n ⇒ steps[cyclicTagStep, n, cyclicTagConfiguration[Join[blocks, r], Join[as, q]]] == some[cyclicTagConfiguration[Join[r, selected[blocks, as]], Join[q, as]]] -->

And its derivation via [TypeTheoryProofTree]():

```wl
TypeTheoryProofTree[wolfram23["cyclicTagBlockSteps"]["Term"]]
```

<!-- => derivation of cyclicTagBlockSteps by ∀I and →I from Equal_rec over equalitySymmetry[blockLength] and cyclicTagBlock applied to equalityTransitivity[appendantsLength, equalitySymmetry[blockLength]] -->

## Rung 1: Binary Turing Machines to 2-Tag Systems

Rung 1 formalizes Cocke and Minsky's emulation of any binary Turing machine by a 2-tag system, where one step of the machine takes three rounds of the tag system for a move right and five rounds for a move left.

### The Two Systems

A binary Turing machine configuration (`"BinaryConfiguration"`) carries a natural-number state `q` (`0` halts with `"none"`), a left half-tape `left` (nearest cell first), a head bit `head`, and a right half-tape `right` (nearest cell first). A machine is a transition function `tm : ℕ -> 𝔹 -> MachineTransition` giving the next state, written bit, and move direction (`"moveLeft"` or `"moveRight"`). Moving past the end of an empty half-tape reads `"false"`:

```wl
wolfram23["BinaryConfiguration"]
```

<!-- => inductive BinaryConfiguration : Type | binaryConfiguration : ℕ → {𝔹} → 𝔹 → {𝔹} → BinaryConfiguration -->

The target is a 2-tag system over the 22-constructor inductive type `"MinskySymbol"`: `"pad"` plus 21 symbol kinds carrying the state `q`, and where needed the scanned bit `h` and the left-tape parity bit `b`. Using an inductive type of symbols lets `"minskyProductions"[tm]` compute directly on symbolic states and machines. Each half-tape is read as a natural number with its nearest cell least significant (`"tapeValue"`), so a configuration `(q, left, head, right)` encodes as `"binaryWord"[c] = "minskyWord"[q, m, 2 n + h]`, where `m = tapeValue[left]`, `n = tapeValue[right]`, and `h = bitValue[head]`: the word `A_q pad (alpha_q pad)^m B_q pad (beta_q pad)^(2 n + h)`.

Consider a machine that writes `"true"`, moves right, and halts in state 0:

```wl
tmRight = TypeTheoryTerm[Function[{Typed[q, Naturals], Typed[h, Booleans]}, "machineTransition"[0, "true", "moveRight"]], wolfram23]
```

<!-- => (q ∶ ℕ) (h ∶ 𝔹) ↦ machineTransition[0, true, moveRight] -->

Start it in state 1 on a blank tape:

```wl
startBinary = TypeTheoryTerm["binaryConfiguration"[1, Typed[{}, {Booleans}], "false", Typed[{}, {Booleans}]], wolfram23]
```

<!-- => binaryConfiguration[1, {} ∶ {𝔹}, false, {} ∶ {𝔹}] -->

One step of `"binaryStep"` writes `"true"` onto the left half-tape and enters state 0:

```wl
NormalForm[TypeTheoryTerm["binaryStep"[tmRight, startBinary], wolfram23]]
```

<!-- => some[binaryConfiguration[0, {true}, false, {}]] -->

The starting word in Cocke and Minsky's 2-tag system has `m = 0` and `2 n + h = 0`:

```wl
NormalForm[TypeTheoryTerm["binaryWord"[startBinary], wolfram23]]
```

<!-- => {symbolA[1], pad, symbolB[1], pad} -->

Three rounds of `"tagStep"["minskyProductions"[tmRight]]` (2 + 2 + 2 = 6 tag steps) advance that word (a move left with a 1 on the left takes five rounds, 3 + 3 + 3 + 2 + 2 = 13 tag steps):

```wl
NormalForm[TypeTheoryTerm["steps"["tagStep"["minskyProductions"[tmRight]], 6, "binaryWord"[startBinary]], wolfram23]]
```

<!-- => some[{symbolA[0], pad, symbolAlpha[0], pad, symbolB[0], pad}] -->

The result matches `"binaryWord"` of the next machine configuration:

```wl
NormalForm[TypeTheoryTerm["binaryWord"["binaryConfiguration"[0, {"true"}, "false", Typed[{}, {Booleans}]]], wolfram23]]
```

<!-- => {symbolA[0], pad, symbolAlpha[0], pad, symbolB[0], pad} -->

### The Relation and the Theorem

A binary configuration `c` relates to a tag word `w` by `w == "binaryWord"[c]`. For every binary machine `tm`, `"minskySimulation"` proves that the 2-tag system follows `tm`:

```wl
wolfram23["minskySimulation"]
```

<!-- => theorem minskySimulation : ∀_tm∶ℕ → 𝔹 → MachineTransition forwardSimulation[binaryStep[tm], tagStep[minskyProductions[tm]], (c ∶ BinaryConfiguration) (w ∶ {MinskySymbol}) ↦ w == binaryWord[c]] -->

It rests on no axioms:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm["minskySimulation", wolfram23]]
```

<!-- => <||> -->

### The Proof

Rather than stepping symbol by symbol through every transition, the proof abstracts one full pass over a word as `"passOutFrom"[productions, w, read]`, a structural recursion that collects the productions of every other symbol of `w` (starting from the first when `read` is `"true"`, and from the second when `"false"`). Over repeated pairs, `"passOutAlignedPairs"` (and its shifted twin `"passOutShiftedPairs"`) pulls out repeated productions:

```wl
wolfram23["passOutAlignedPairs"]
```

<!-- => theorem passOutAlignedPairs : ∀_S∶Type ∀_productions∶S → {S} ∀_a∶S ∀_b∶S ∀_m∶ℕ ∀_l∶{S} passOutFrom[productions, Join[pairs[a, b, m], l], true] == Join[repeated[productions[a], m], passOutFrom[productions, l, true]] -->

Two round theorems connect `"steps"` to `"passOutFrom"`. On a word of even length `2 n`, `n` tag steps yield `"passOutFrom"[productions, u, "true"]`:

```wl
wolfram23["tagRoundEvenWhole"]
```

<!-- => theorem tagRoundEvenWhole : ∀_S∶Type ∀_productions∶S → {S} ∀_n∶ℕ ∀_u∶{S} Length[u] == 2 n ⇒ steps[tagStep[productions], n, u] == some[passOutFrom[productions, u, true]] -->

On an odd word `a :: l` where `Length[l] == 2 n + 2` and `productions[a] == c :: d`, the last symbol of `l` takes `c` as its partner, so `n + 2` tag steps drop `c` and leave `Join[d, "passOutFrom"[productions, l, "false"]]`:

```wl
wolfram23["tagRoundOddHead"]
```

<!-- => theorem tagRoundOddHead : ∀_S∶Type ∀_productions∶S → {S} ∀_n∶ℕ ∀_a∶S ∀_l∶{S} ∀_c∶S ∀_d∶S Length[l] == 2 n + 2 ⇒ productions[a] == Prepend•c•d ⇒ steps[tagStep[productions], n + 2, Prepend•a•l] == some[Join[d, passOutFrom[productions, l, false]]] -->

Each round of Cocke and Minsky's machine step is one theorem. Round 1 rewrites `"minskyWord"[q, m, n]` into `"afterRound1"[q, m, n]`:

```wl
wolfram23["minskyRound1"]
```

<!-- => theorem minskyRound1 : ∀_tm∶ℕ → 𝔹 → MachineTransition ∀_q∶ℕ ∀_m∶ℕ ∀_n∶ℕ steps[tagStep[minskyProductions[tm]], (m + n) + 2, minskyWord[q, m, n]] == some[afterRound1[q, m, n]] -->

Round 2 halves the right number `2 n + h`. The bit `h` decides whether the word it reads has even or odd length, and over an odd word the last symbol takes the first symbol of the next production as its partner (`"tagRoundOddHead"`), which shifts the reading frame of round 3:

```wl
wolfram23["minskyRound2"]
```

<!-- => theorem minskyRound2 : ∀_tm∶ℕ → 𝔹 → MachineTransition ∀_q∶ℕ ∀_m∶ℕ ∀_h∶𝔹 ∀_n∶ℕ steps[tagStep[minskyProductions[tm]], (m + n) + 2, afterRound1[q, m, 2 n + bitValue[h]]] == some[afterRound2[q, h, m, n]] -->

In round 3, a right move doubles `m`, adds the written bit, restores the frame with `"padUnless"[h]`, and lands directly on the next configuration's `"minskyWord"`:

```wl
wolfram23["minskyRound3Right"]
```

<!-- => theorem minskyRound3Right : ∀_tm∶ℕ → 𝔹 → MachineTransition ∀_q∶ℕ ∀_h∶𝔹 ∀_m∶ℕ ∀_n∶ℕ tm[q, h]〚direction〛 == moveRight ⇒ steps[tagStep[minskyProductions[tm]], (m + n) + 2, afterRound2[q, h, m, n]] == some[minskyWord[tm[q, h]〚next〛, 2 m + bitValue[tm[q, h]〚write〛], n]] -->

A left move instead doubles `n` into `2 n` pairs of `K` in round 3:

```wl
wolfram23["minskyRound3Left"]
```

<!-- => theorem minskyRound3Left : ∀_tm∶ℕ → 𝔹 → MachineTransition ∀_q∶ℕ ∀_h∶𝔹 ∀_m∶ℕ ∀_n∶ℕ tm[q, h]〚direction〛 == moveLeft ⇒ steps[tagStep[minskyProductions[tm]], (m + n) + 2, afterRound2[q, h, m, n]] == some[afterRound3[q, h, m, n]] -->

Round 4 halves the left number `2 i + b` by the same parity trick:

```wl
wolfram23["minskyRound4"]
```

<!-- => theorem minskyRound4 : ∀_tm∶ℕ → 𝔹 → MachineTransition ∀_q∶ℕ ∀_h∶𝔹 ∀_b∶𝔹 ∀_i∶ℕ ∀_n∶ℕ steps[tagStep[minskyProductions[tm]], (i + 2 n) + 2, afterRound3[q, h, 2 i + bitValue[b], n]] == some[afterRound4[q, h, b, i, n]] -->

And round 5 shifts the written bit and `b` into the right number `2 (2 n + write) + b`:

```wl
wolfram23["minskyRound5"]
```

<!-- => theorem minskyRound5 : ∀_tm∶ℕ → 𝔹 → MachineTransition ∀_q∶ℕ ∀_h∶𝔹 ∀_b∶𝔹 ∀_i∶ℕ ∀_n∶ℕ steps[tagStep[minskyProductions[tm]], (i + 2 n) + 2, afterRound4[q, h, b, i, n]] == some[minskyWord[tm[q, h]〚next〛, i, 2 (2 n + bitValue[tm[q, h]〚write〛]) + bitValue[b]]] -->

Chaining those three or five rounds with `"stepsThen"` (after splitting `left` or `right` with `"tapeSplit"`) yields `"minskyStep"`:

```wl
wolfram23["minskyStep"]
```

<!-- => theorem minskyStep : ∀_tm∶ℕ → 𝔹 → MachineTransition ∀_c∶BinaryConfiguration ∀_c2∶BinaryConfiguration binaryStep[tm, c] == some[c2] ⇒ ∃_s∶ℕ (1 ≤ s ∧ steps[tagStep[minskyProductions[tm]], s, binaryWord[c]] == some[binaryWord[c2]]) -->

The proof term of `"tagRoundEvenWhole"` shows how the general even-round lemma `"tagRoundEven"` specializes to a whole word by appending `{}` via `"joinEmptyRight"`:

```wl
wolfram23["tagRoundEvenWhole"]["Term"]
```

<!-- => (S ∶ Type) (productions ∶ S → {S}) (n ∶ ℕ) (u ∶ {S}) (length ∶ Length[u] == 2 n) ↦ equalityTransitivity[equalityCongruence[(x ∶ {S}) ↦ steps[tagStep[productions], n, x], equalitySymmetry[joinEmptyRight[u]]], tagRoundEven[S, productions, n, u, {}, length]] ∶ ∀_S∶Type ∀_productions∶S → {S} ∀_n∶ℕ ∀_u∶{S} Length[u] == 2 n ⇒ steps[tagStep[productions], n, u] == some[passOutFrom[productions, u, true]] -->

Its derivation via [TypeTheoryProofTree]():

```wl
TypeTheoryProofTree[wolfram23["tagRoundEvenWhole"]["Term"]]
```

<!-- => derivation of tagRoundEvenWhole by ∀I and →I from equalityTransitivity over equalityCongruence[equalitySymmetry[joinEmptyRight]] and tagRoundEven -->

## Joining Rungs 1 and 2: Binary Machines to Cyclic Tag Systems

Rung 1 produces a 2-tag system over `"MinskySymbol"`, whereas rung 2 expects a 2-tag system over natural numbers below some bound `k`. Joining them numbers the symbols of states `0` to `S - 1` into `{0, ..., 84 S}`, builds the corresponding numerical 2-tag system `"minskyNumbers"[tm]`, proves that its productions stay below `84 S + 1`, and composes with `"cookSimulation"`.

### The Two Systems

The encoding `"minskyEncode"` maps `"pad"` to `0` and each non-pad symbol to `84 q + 4 kind + 2 h + b + 1` (reserving four slots per symbol kind, 84 slots per state `q`). Decoding `"minskyDecode"` maps `0` back to `"pad"` and `m + 1` through a structural-recursion division `"divideBy"[84, m]` (incrementing a `"QuotientRemainder"` pair one unit at a time with `"carryDigit"`) into an 84-entry table `"minskyTable"[q]`.

For `"symbolJ"[2, "true", "false"]` (state 2, kind offset 76, `h = true`, `b = false`), the code is `84 * 2 + 76 + 2 + 1 = 247`:

```wl
NormalForm[TypeTheoryTerm["minskyEncode"["symbolJ"[2, "true", "false"]], wolfram23]]
```

<!-- => 247 -->

Division by 84 computes directly in the kernel:

```wl
NormalForm[TypeTheoryTerm["divideBy"[84, 200], wolfram23]]
```

<!-- => quotientRemainder[2, 32] -->

And `"minskyDecode"` recovers the original symbol from `247`:

```wl
NormalForm[TypeTheoryTerm["minskyDecode"[247], wolfram23]]
```

<!-- => symbolJ[2, true, false] -->

The numerical 2-tag system `"minskyNumbers"[tm]` decodes a number, applies `"minskyProductions"[tm]`, and encodes the output word. Stepping the symbolic tag system once from `"binaryWord"[startBinary]`:

```wl
NormalForm[TypeTheoryTerm["tagStep"["minskyProductions"[tmRight], "binaryWord"[startBinary]], wolfram23]]
```

<!-- => some[{symbolB[1], pad, symbolP1[1], symbolP0[1]}] -->

Stepping the numerical tag system once from the encoded word gives the same result up to `"minskyEncode"` (`93`, `0`, `101`, `105` are the codes of `"symbolB"[1]`, `"pad"`, `"symbolP1"[1]`, `"symbolP0"[1]`):

```wl
NormalForm[TypeTheoryTerm["tagStep"["minskyNumbers"[tmRight], "minskyEncode" /@ "binaryWord"[startBinary]], wolfram23]]
```

<!-- => some[{93, 0, 101, 105}] -->

### The Relation and the Theorem

When a machine satisfies `"machineBelow"[tm, S]` (every transition from a state `q < S` enters a state below `S`), `"machineToCyclicTag"` composes rung 1, the numerical relabeling, and rung 2 into a single forward simulation from `"binaryStep"[tm]` directly to `"cyclicTagStep"` with alphabet size `84 S + 1`:

```wl
wolfram23["machineToCyclicTag"]
```

<!-- => theorem machineToCyclicTag : ∀_tm∶ℕ → 𝔹 → MachineTransition ∀_S∶ℕ machineBelow[tm, S] ⇒ forwardSimulation[binaryStep[tm], cyclicTagStep, (c ∶ BinaryConfiguration) (x ∶ CyclicTagConfiguration) ↦ ∃_v∶{ℕ} ((∃_w∶{MinskySymbol} (w == binaryWord[c] ∧ v == minskyEncode /@ w)) ∧ x == cookConfiguration[84 S + 1, minskyNumbers[tm], v] ∧ allBelow[84 S + 1, v])] -->

Its axiom closure is empty:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm["machineToCyclicTag", wolfram23]]
```

<!-- => <||> -->

### The Proof

Because `"divideBy"[84, 84 q + c]` reduces by `"divideAdd"` to `c` carries after `"divideBy"[84, 84 q]`, proving `"divideMultiple"` lets every literal offset `c` compute by `"Reflexivity"`:

```wl
wolfram23["divideMultiple"]
```

<!-- => theorem divideMultiple : ∀_q∶ℕ divideBy[84, 84 q] == quotientRemainder[q, 0] -->

That gives `"minskyDecodeEncode"` in 42 uniform cases:

```wl
wolfram23["minskyDecodeEncode"]
```

<!-- => theorem minskyDecodeEncode : ∀_s∶MinskySymbol minskyDecode[minskyEncode[s]] == s -->

That inverse law makes `"tagStep"["minskyNumbers"[tm]]` commute with `"minskyEncode"`:

```wl
wolfram23["minskyNumbersCommute"]
```

<!-- => theorem minskyNumbersCommute : ∀_tm∶ℕ → 𝔹 → MachineTransition ∀_w∶{MinskySymbol} tagStep[minskyNumbers[tm], minskyEncode /@ w] == optionMap[(v ∶ {MinskySymbol}) ↦ minskyEncode /@ v, tagStep[minskyProductions[tm], w]] -->

Applying `"relabelingSimulation"` immediately yields `"minskyNumbersSimulation"`:

```wl
wolfram23["minskyNumbersSimulation"]
```

<!-- => theorem minskyNumbersSimulation : ∀_tm∶ℕ → 𝔹 → MachineTransition forwardSimulation[tagStep[minskyProductions[tm]], tagStep[minskyNumbers[tm]], (w ∶ {MinskySymbol}) (v ∶ {ℕ}) ↦ v == minskyEncode /@ w] -->

To satisfy rung 2's hypothesis that every production keeps symbols below `84 S + 1`, `"divideSpecification"` proves the division invariant `84 q + r == m` and `r + 1 <= 84` (by induction, splitting on the decidability instance `"naturalNumberEqualityDecidable"[r + 1, 84]` inside `"carrySpecification"`):

```wl
wolfram23["divideSpecification"]
```

<!-- => theorem divideSpecification : ∀_m∶ℕ (84 divideBy[84, m]〚quotient〛 + divideBy[84, m]〚remainder〛 == m ∧ divideBy[84, m]〚remainder〛 + 1 ≤ 84) -->

From that bound, `"decodeBelow"`, `"productionsBelow"` and `"mapEncodeBelow"` combine into `"minskyNumbersBelow"`:

```wl
wolfram23["minskyNumbersBelow"]
```

<!-- => theorem minskyNumbersBelow : ∀_tm∶ℕ → 𝔹 → MachineTransition ∀_S∶ℕ machineBelow[tm, S] ⇒ ∀_i∶ℕ i + 1 ≤ 84 S + 1 ⇒ allBelow[84 S + 1, minskyNumbers[tm, i]] -->

The proof term of `"minskyNumbersBelow"` is a single three-step pipeline through `"decodeBelow"`, `"productionsBelow"` and `"mapEncodeBelow"`:

```wl
wolfram23["minskyNumbersBelow"]["Term"]
```

<!-- => (tm ∶ ℕ → 𝔹 → MachineTransition) (S ∶ ℕ) (machine ∶ machineBelow[tm, S]) (i ∶ ℕ) (bound ∶ i + 1 ≤ 84 S + 1) ↦ mapEncodeBelow[S, minskyProductions[tm, minskyDecode[i]], productionsBelow[tm, S, machine, minskyDecode[i], decodeBelow[S, i, bound]]] ∶ ∀_tm∶ℕ → 𝔹 → MachineTransition ∀_S∶ℕ machineBelow[tm, S] ⇒ ∀_i∶ℕ i + 1 ≤ 84 S + 1 ⇒ allBelow[84 S + 1, minskyNumbers[tm, i]] -->

Finally, [TypeTheoryProofTree]() displays the entire derivation of `"machineToCyclicTag"`: `"minskySimulation"` and `"minskyNumbersSimulation"` compose first, `"minskyNumbersBelow"` feeds `"cookSimulation"`, and a second `"forwardSimulationCompose"` joins the two halves:

```wl
TypeTheoryProofTree[wolfram23["machineToCyclicTag"]["Term"]]
```

<!-- => derivation of machineToCyclicTag by ∀I and →I from forwardSimulationCompose over forwardSimulationCompose[minskySimulation, minskyNumbersSimulation] and cookSimulation[minskyNumbersBelow] -->

## What Remains

Four rungs remain to close the gap between `"machineToCyclicTag"` and `"wolfram23Simulates3"` and complete the universality theorem:

- **Rung 3 (cyclic tag systems to System 5)**: encode a cyclic tag system into System 5's bag and rules with the doubling folded into the encoder, prove the two-doubled-step simulation lemma, and settle the representation of finite sets and their truncated-subtraction invariants.
- **Rung 4 (System 5 to System 4)**: emulate System 5 by System 4 for a finite run, choosing the parameter `f` large enough for the run's length and establishing System 5's terminal event and System 4's exit in state C.
- **Rung 5 (System 4 to System 3)**: encode System 4's sets as parity blocks of width `2^w`, prove the prefix-XOR scan and the rule-60 period-`2^w` identity by induction on `w`, and prove left confinement together with System 3's exit lemma.
- **Rung 7 (full composition and universality)**: compose rungs 1 through 6 into the existential finite universality theorem for Wolfram's (2,3) Turing machine, prove the decoding lemmas for the decoder of each layer, and combine confinement with the terminal exit configuration (followed later by the infinite form, one tape for all `n`).
