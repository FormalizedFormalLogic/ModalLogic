# Contributing to ModalLogic

How to contribute to ModalLogic: the flow to `main`, PR/commit titles, pre-submission checks, and disclosure of AI involvement. For the coding conventions of the Lean sources, see [style.md](./style.md) and [refactoring.md](./refactoring.md); for the bibliography, see [references.md](./references.md).

Items marked 🤖 are especially directed at AI coding agents.

## Projects

This repository is a collection of independent formalization projects, one Lake library each. Syntax and semantics are deliberately not shared between them: how formulas are built, and which abbreviations are introduced, measurably changes how hard the inductions are, so each project defines what suits its own proofs.

| library | source |
| --- | --- |
| `Fin74` | "An Incomplete Logic Containing S4" [Fin74] |
| `SV26` | "Interpolation above S4" [SV26] |
| `CZ97Cp7` | "Modal Logic" [CZ97], Chapter 7 (algebraic semantics) |
| `ModalNeighborhood` | neighborhood semantics for the non-normal modal logics of the E family |
| `ModalLogicArchive` | material carried over from earlier work, not tied to a single paper |

## How changes land on `main`

All changes to `main` go through GitHub pull requests, developed on a topic branch. PRs are always squash-merged, so the PR title becomes the commit message on `main` — hence the title convention below.

## PR titles and commit convention

PR titles are in English, in the usual conventional-commit form:

```
<type>(scope): <subject>
```

`<type>` is one of the following (do not use `feat`):

| type | meaning |
| --- | --- |
| `add` | new results, definitions, theorems |
| `fix` | fixing something misformalized |
| `refactor` | renaming/organizing; existing facts essentially unchanged |
| `doc` | documents |
| `ci` | GitHub Actions |
| `chore` | other maintenance (e.g. version-up) |

`scope` is the project library the change belongs to (`Fin74`, `ModalLogicArchive`, …), narrowed to a module where that helps (`Fin74/Kripke`), following precedents in `git log --oneline`. Changes outside the libraries — build configuration, CI, contributor documentation — take no scope.

For `<subject>`, name one representative result of the PR; no verb phrases like "formalize the …" — write "Kripke incompleteness of the Fine logic", not "formalize the Kripke incompleteness of the Fine logic".

PRs (title and body) are written in English.

## Before submitting

- The affected modules build with `lake build`, with no errors or warnings (including remaining `sorry`).
- Run import-all to keep each library's root file up to date:
  ```shell
  just mk-all
  ```
- Remove unused imports and unnecessary `public`. `lake shake` needs a completed build, so run it after `lake build`, and build once more afterwards because it rewrites imports:
  ```shell
  just shake
  ```
  `lake shake --fix` mistakes a `meta import` for a duplicate of the corresponding `public import` and deletes it; write every such line as `meta import <Module> -- shake: keep`.
- If you added entries to `references.bib`, format it:
  ```shell
  just format-bib
  ```
- 🤖 No development-time artifacts survive in the code — plan references, issue numbers, step numbers, stale skeleton-era comments. See [style.md](./style.md#stale-comments-and-planning-artifacts).

## Disclosing AI involvement

🤖 Whenever an AI agent was involved in producing the changes — fully generated or merely assisted — this must be disclosed in the contribution itself:

- every commit created with an AI agent carries a co-author trailer, e.g.
  ```
  Co-Authored-By: Claude <noreply@anthropic.com>
  ```
- the PR states in natural language (in the body, or in the title if appropriate) that an AI agent was used.
