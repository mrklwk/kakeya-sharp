#!/bin/sh
set -eu

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
project_dir=$(CDPATH= cd -- "$script_dir/.." && pwd)
request="$project_dir/review/claude/REQUEST.md"
test -f "$request"

prompt="Read $request and carry out both requested reviews: the exact Lean statements and proof evidence, and the abstract and narrative summaries. Preserve the candidate. Write your findings and proposed prose in a fresh directory under review/claude/runs/. Record the exact source identity and distinguish completed checks from pending checks."

case "${1:-}" in
  --print-prompt)
    printf '%s\n' "$prompt"
    exit 0
    ;;
  --check)
    printf 'Review request: %s\n' "$request"
    if command -v claude >/dev/null 2>&1; then
      printf 'Claude CLI: available\n'
    else
      printf 'Claude CLI: unavailable in this shell; use a Claude Code local session.\n'
    fi
    exit 0
    ;;
  '') ;;
  *)
    printf 'Usage: bash scripts/claude_review.sh [--check|--print-prompt]\n' >&2
    exit 2
    ;;
esac

cd "$project_dir"
if ! command -v claude >/dev/null 2>&1; then
  printf 'Open Claude Code in a local session for this folder:\n%s\n\nPaste:\n%s\n' "$project_dir" "$prompt"
  exit 1
fi
exec claude "$prompt"
