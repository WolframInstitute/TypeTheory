# TypeTheory documentation guide

How to write the TypeTheory documentation sources under `docs/paclet/en/`: the `Template: Symbol`
reference pages, the `Template: Guide` guide, the `Template: TechNote` tutorial and the resource
definition. They are literate-markdown files that [`build_docs.wls`](../../../build_docs.wls) turns
into evaluated notebooks with PacletPage's `BuildPacletDocumentation`, which runs MarkdownToNotebook
on each page. The notebooks land under `TypeTheory/Documentation/English/`, and
[`release.wls`](../../../release.wls) publishes them as the
[documentation site](https://www.wolframcloud.com/obj/wolframinstitute/TypeTheory). This follows
LeanLink's documentation guide, which has the reasons behind each rule.

## Build and read back, always

A page is done when it has been built and every output cell read back. Run the build with the `wl`
CLI, not `wolframscript`:

```
wl -f build_docs.wls
```

The `<!-- => ... -->` hint after a cell is for authors only: the converter strips it, so nothing
checks it against the real output. Probe each example against the paclet, then write the real result
into the hint. A page is converted again only when its source or the paclet's code changed;
`--no-cache` evaluates everything again.

The build fails on a page that does not convert, and on a section that reads a name only an earlier
section gave a value.

## Where state threads

- The **tutorial** runs in one context: `arithmetic`, `proof` and `proved`, defined once, are used
  section after section.
- Every other page runs each section, and each example between `---` delimiters, in a clean context,
  so each one defines what it uses: an environment other than the prelude is built in the example
  that needs it.

## TypeTheory's own rules

- **The prelude goes without saying.** A term, a proof or a list of declarations without an
  environment is in the prelude, so examples never write `TypeTheoryEnvironment["Prelude"]` where it
  could be left out: <code>[TypeTheoryTerm]()[2 + 3]</code>, <code>[TypeTheoryProof]()[*statement*, {...}]</code>,
  <code>[TypeTheoryEnvironment]()[{*declaration*}]</code>. Name an environment only when it is not the
  prelude, and build on <code>[TypeTheoryEnvironment]()[]</code> when the prelude must be left out, as
  for natural numbers of your own.
- **[TypeOf]() takes a term written out.** It holds its argument, so `TypeOf[statement]` with
  `statement` a variable does not reach TypeTheory and fails with a compiler message. Use
  <code>[TypeTheoryCheck]()[*statement*]</code> for a term in a variable.
- **Name constants with fresh symbols.** A declaration holds its name, but [Keys]() and
  <code>*env*[*name*]</code> evaluate it, and System symbols with values (`Red`, `Tree`, `Next`) do
  not stay names. Use descriptive names that are not System symbols, such as `BinaryTree` or
  `TwoPlusTwo`.
- **A symbol stands for a term only if its value is a [TypeTheoryTerm]() or a finished
  [TypeTheoryProof]().** A variable holding a bare [Function]() is not expanded inside a term.

## Hints for terms

Terms, declarations and proofs display in two dimensions. A hint writes the display on one line:

- a quantifier with its binder below it as `∀_n∶ℕ` (explicit) or `∀_{a ∶ Prop}` (implicit);
- the logical connectives as `∧`, `∨`, `¬`, and the natural numbers' constructors as `0` and `n + 1`;
- a function as `(n ∶ ℕ) ↦ body`, and a function type as `ℕ → ℕ`, or `a ⇒ b` between propositions;
- an equation as `2 + 2 == 4`;
- a declaration as `theorem TwoPlusTwo : 2 + 2 == 4`;
- a proof as `Proof, 2 goals: ⊢ True; ⊢ 1 + 1 == 2`, or `Proof complete`;
- an environment as `TypeTheoryEnvironment summary box: 32 constants`;
- a failure by its tag, `Failure["TypeMismatch", ...]`.

## Symbols are links

Every symbol, built-in or TypeTheory's, is a link written `[TypeTheoryTerm]()`. A call is code and a
link: <code>[TypeTheoryTactic]()["Introduce", *x*]</code>. Backticks are for what is not a symbol:
a term fragment (`n + 0 == n`), a tactic name (`"Induction"`), an option value. Argument names are in
*italics*. A page that links a TypeTheory symbol without a page of its own gets one in the same pass.

## Cells

- No `Needs`: the converter loads the paclet from the frontmatter `Context:`.
- One output per cell, with its own caption.
- Show the display, not the guts: a term, a declaration, a proof and an environment each display
  themselves.
- Wolfram Language source follows the house style: no em dashes, ASCII `->` in code.

## Page shape

- **Frontmatter**: `Template`, `Name`, `Context`, `Paclet`, `URI` (the basename matches the URI's
  tail), `Keywords`, and for a symbol page `SeeAlso` and `RelatedGuides`.
- **Symbol page**: `## Usage`, `## Details & Options`, then `## Basic Examples`, `## Scope`,
  `## Properties and Relations`, `## Possible Issues` as warranted. Model a function on
  [Symbols/TypeTheoryEnvironment.md](Symbols/TypeTheoryEnvironment.md) and a prelude constant on
  [Symbols/AndIntroduction.md](Symbols/AndIntroduction.md).
- **Guide**: an `## Abstract`, then `## Functions` as `[Symbol]() description` items under
  subheadings. See [Guides/TypeTheory.md](Guides/TypeTheory.md).
- **Tutorial**: one running story with real prose. See
  [Tutorials/TypeTheoryIntroduction.md](Tutorials/TypeTheoryIntroduction.md).
