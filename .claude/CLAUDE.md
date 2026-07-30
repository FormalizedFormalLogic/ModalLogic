# ModalLogic Project Instructions

- Before committing or merging, read **`contribute/index.md`**.
- Before writing or refactoring proofs, read **`contribute/style.md`** and **`contribute/refactoring.md`**.
- Before touching `references.bib` or citing the literature, read **`contribute/references.md`**.

## Setup

Proof work in this repository uses the `lean4` plugin (marketplace `lean4-skills`, providing `/lean4:autoprove` etc.) and the `lean-lsp` MCP server (defined in `.mcp.json`; requires `uv` and `ripgrep`). Enable both after cloning:

```
/plugin marketplace add cameronfreer/lean4-skills
/plugin install lean4@lean4-skills
```

Bibliographic metadata is looked up through the Zotero MCP server (`mcp__zotero__*`), configured at user scope.

## Working in a worktree

Every task, not only proof work, is carried out on a branch in a worktree under `.claude/worktrees/<branch>`; `main` is never edited directly. See `contribute/index.md` for the exact `git worktree add` / `.lake` procedure and for the maintenance edits that are exempt.

Do not use `gwq`: its worktree paths conflict with the `EnterWorktree` tool. Enter a worktree by calling `EnterWorktree` with an absolute `path` (its `name` argument would skip the `.lake` setup), and leave with `ExitWorktree` in `keep` mode.

## Sharing progress via `.claude/docs/directions/`

`.claude/docs/directions/` is untracked and shared between sessions and agents. Worktrees live under the main repository, so address it from a worktree by its path in the main repository (`$(dirname $(git rev-parse --git-common-dir))/.claude/docs/directions/`).

Right after creating a worktree, and before starting the work itself:

1. Add a checklist item to `.claude/docs/directions/worktrees.md` (e.g. `- [ ] my-slug — proof of …`), and tick it once the work is done.
2. Create `.claude/docs/directions/YYYYMMDDHHMM_<slug>.md` describing what this worktree is for: the task, the approach, the current state. (`worktrees.md` itself takes no timestamp prefix.)

Update the slug file roughly once per commit, so that anyone reading `worktrees.md` sees the current state.

**Never delete anything under `.claude/docs/directions/`.** It is untracked, so a deletion cannot be recovered. Completed records stay; tick them off in `worktrees.md` or move them to a "done" section instead. This holds when cleaning up worktrees (`git worktree remove`) as well.

## Subagents and models

- **Plan proofs on paper with Fable first.** Before filling a new `sorry` or proving a new lemma, have a Fable subagent (`model: fable`) work out the mathematical strategy. Fable writes no Lean code. Ask the user for approval before launching it, even in auto-edit mode, presenting the scope and the estimate.
- **Record the plan on the integration branch**, in full: the original plan and the split into steps, committed as a file, so the user can review it and so the work can be resumed after a lost session. Revisions are appended, never overwritten. Where the work is split across worktrees, note which branch owns which step.
- **Have the plan split into small steps** — intermediate lemmas that can be stated separately, the individual cases of a case split.
- **Build the skeleton before the substance.** First state every lemma of the plan with `sorry` as its proof; then state the main theorem in terms of them (its own proof may stay `sorry`); only then fill the `sorry`s one at a time.
- **Delegate the implementation to `lean4-proof-writer`** (`.claude/agents/lean4-proof-writer.md`) rather than to `general-purpose`, one subagent per step, and instruct it explicitly to use `/lean4:autoprove`. Refactoring of proofs that already build goes to `lean4-proof-refactorer`.
- **The coordinator (main loop) never writes Lean proof code itself**, however trivial it looks.
- **Use the cheapest model that works**: Sonnet for implementation and refactoring, Opus (`model: opus`) only where Sonnet fails or the quality is insufficient; Sonnet or Haiku for routine investigation (reading neighbouring code, scanning a PDF). A bulk docstring cleanup that touches no proof code can be fanned out over several Haiku subagents, one per file.
- Commit after each `sorry` filled — not in batches — and confirm `lake build` plus clean LSP diagnostics before each commit.
- **Never merge into `main` on your own.** Report the branch name, the changes and the build result, and wait for the user's decision.
