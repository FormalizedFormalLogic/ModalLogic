#!/usr/bin/env bash
# PreToolUse(Bash) hook: refuse git commands that write history or the index
# while the target repository is on the `main` branch.
#
# All work is supposed to happen in a worktree under `.claude/worktrees/<branch>`
# (see contribute/index.md and .claude/CLAUDE.md). Commits land on `main` only
# through an explicitly approved squash merge.
#
# Escape hatch: prefix the command with `ALLOW_MAIN_WRITE=1` to bypass this hook
# (e.g. the approved squash merge, or the documented exceptions such as editing
# CLAUDE.md / .gitignore / references.bib directly on main).

set -uo pipefail

input=$(cat)
command=$(printf '%s' "$input" | jq -r '.tool_input.command // ""')
cwd=$(printf '%s' "$input" | jq -r '.cwd // ""')

allow() { exit 0; }

deny() {
  jq -n --arg reason "$1" '{
    hookSpecificOutput: {
      hookEventName: "PreToolUse",
      permissionDecision: "deny",
      permissionDecisionReason: $reason
    }
  }'
  exit 0
}

# Explicit opt-out.
case "$command" in
  *ALLOW_MAIN_WRITE=1*) allow ;;
esac

# Subcommands that modify history, the index, or the remote.
guarded='commit|add|merge|rebase|reset|revert|cherry-pick|am|apply|restore|rm|mv|stash|push|clean'

# `git [-c k=v] [-C path] ... <subcommand>`
if ! printf '%s' "$command" |
  grep -Eq "(^|[^[:alnum:]_-])git([[:space:]]+-[^[:space:]]+([[:space:]]+[^[:space:]-][^[:space:]]*)?)*[[:space:]]+($guarded)([[:space:]]|$)"; then
  allow
fi

# Determine which repository the command targets: `git -C <path>` if given, else cwd.
target=$(printf '%s' "$command" | grep -oE '(^|[^[:alnum:]_-])git[[:space:]]+-C[[:space:]]+[^[:space:]]+' | head -n 1 | awk '{print $NF}')
target=${target:-.}
target=${target%\"}
target=${target#\"}
target=${target%\'}
target=${target#\'}

[ -n "$cwd" ] || allow
branch=$(cd "$cwd" 2>/dev/null && git -C "$target" rev-parse --abbrev-ref HEAD 2>/dev/null) || allow

if [ "$branch" = "main" ]; then
  deny "このリポジトリでは main ブランチ上で履歴・インデックスを変更する git 操作（commit・add・merge・push 等）は禁止されています．

作業は worktree で行ってください:
  git worktree add .claude/worktrees/<branch> -b <branch>
  cp -al .lake .claude/worktrees/<branch>/.lake
  rm -rf .claude/worktrees/<branch>/.lake/build

main への反映は，ユーザーの承認を得た上での squash マージのみです．
承認済みの操作や CLAUDE.md・.gitignore・references.bib など例外的な直接変更を commit する場合は，コマンド先頭に ALLOW_MAIN_WRITE=1 を付けて実行してください．"
fi

allow
