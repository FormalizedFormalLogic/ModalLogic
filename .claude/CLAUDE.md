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

## Local workflow

How worktrees are created, how progress is shared between sessions, and which subagent and model handles which kind of work are machine-local conventions, described in `CLAUDE.local.md` (untracked). Do not copy them into the tracked documents.
