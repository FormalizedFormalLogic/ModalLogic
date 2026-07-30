# Contributing to ModalLogic

How changes land on `main`, the commit convention, the checks to run before merging, and disclosure of AI involvement. For the coding conventions of the Lean sources see [style.md](./style.md) and [refactoring.md](./refactoring.md); for the bibliography workflow see [references.md](./references.md).

Items marked 🤖 are especially directed at AI coding agents.

## Project layout

This repository is a collection of independent formalization projects, one Lake library each. The syntax of `Formula` and the semantics are deliberately *not* shared between them: the way formulas are built, and which abbreviations are introduced, measurably changes how hard the inductions are, so each project defines what suits its own proofs. Common infrastructure is factored out only when experience shows it pays off.

| library | source |
| --- | --- |
| `Fin74` | "An Incomplete Logic Containing S4" [Fin74] |
| `SV26` | "Interpolation above S4" [SV26] |
| `CZ97Cp7` | "Modal Logic" [CZ97], Chapter 7 (algebraic semantics) |
| `ModalLogicArchive` | material carried over from earlier work, not tied to a single paper |

## How changes land on `main`

Every change is developed on a topic branch in a git worktree and lands on `main` as a single squash merge, approved by the repository owner beforehand.

**Committing directly on `main` is not allowed.** The `PreToolUse` hook [`.claude/hooks/protect-main.sh`](../.claude/hooks/protect-main.sh) denies `git commit`/`add`/`merge`/`push`/… whenever the target repository is on `main`. The exceptions are maintenance edits to the repository's own configuration (`.claude/`, `contribute/`, `.gitignore`, `references.bib`, `Justfile`, CI and editor settings) and the approved squash merge itself; prefix the command with `ALLOW_MAIN_WRITE=1` to bypass the hook there.

```shell
git worktree add .claude/worktrees/<branch> -b <branch>
cp -al .lake .claude/worktrees/<branch>/.lake   # share the dependency build via hardlinks
rm -rf .claude/worktrees/<branch>/.lake/build   # keep this project's build products per-worktree
```

Only `.lake/packages/` — pinned by the manifest and immutable while the worktree is being worked on — may be hardlinked. Sharing `.lake/build` causes stale builds: an olean rewritten in place through a shared inode makes `lake build` report success without having recompiled.

## Commit convention

Commit messages are written in English — subject, body, and trailers alike.

Work belonging to one of the project libraries carries the project name as a subject prefix, without exception:

```
Fin74: Kripke incompleteness of the Fine logic
```

For the subject, name one representative result of the change; no verb phrases like "formalize the …" — write "Strict arithmetical hierarchy theorem", not "formalize the strict arithmetical hierarchy theorem". Changes outside the libraries (build configuration, CI, contributor documentation) need no prefix.

## Before merging

Run, in this order:

1. `lake build` — the affected modules build with no errors and no warnings, including remaining `sorry`.
2. `just mk-all` — regenerates each library's all-import root file, so a newly added file cannot be silently left out of the build.
3. `just shake` — removes unused imports and unnecessary `public`. It requires a completed build, hence the order.
4. `lake build` again — shake rewrites imports, so confirm the result still builds.

`lake shake --fix` mistakes a `meta import` for a duplicate of the corresponding `public import` and deletes it, breaking the build. Write every `meta import` with a keep annotation:

```lean
meta import <Module> -- shake: keep
```

If a build then fails with

```
Invalid `meta` definition … is not accessible here; consider adding `public meta import …`
```

restore the deleted line and annotate it.

When one logical task was split across several worktrees, run the `mk-all`/`shake` steps once on the integration branch after merging, not in each worktree.

If you added entries to `references.bib`, format it with `just format-bib`; see [references.md](./references.md).

🤖 No development-time artifacts survive in the code — plan references, issue numbers, step numbers, stale skeleton-era comments. See [style.md](./style.md#stale-comments-and-planning-artifacts).

## Disclosing AI involvement

🤖 Whenever an AI agent was involved in producing a change — fully generated or merely assisted — every commit carries a co-author trailer:

```
Co-Authored-By: Claude <noreply@anthropic.com>
```
