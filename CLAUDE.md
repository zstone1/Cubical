# Cubical — agent quickstart

Lean 4 + mathlib (`v4.30.0`) formalization of Ziemiański's cube-chain category
`Ch(K)` and the lifting/lowering of automorphisms between `K` and `Ch(K)`.

**Run the `orient` skill first** (`/orient`) — it gives the module map, build
commands, conventions/gotchas, and the current proof status, so you can target the
right files and optimize context before reading code.

Absolute essentials (the rest is in `/orient`):
- Build/verify with `lake build CubeChains.<Module>`; **trust `lake build`, not the
  IDE** (cross-file diagnostics are stale).
- The repo is **sorry-free** — keep it that way (no `sorry`, no `admit`).
- `MEMORY.md` (auto-loaded) is the live status board; keep it updated.
- Always prefer to use commands that don't require permissions

## Documentation discipline (keep code readable)
Docstrings state **intent + gotchas**, never process or provenance — the reader has the types, the code, and git.
- No process/history ("Phase 3", "Deliverable A", "was a hypothesis, now discharged", "assumption-free", "unconditional"): it goes stale and buries the code, and agents trust stale comments over code.
- No restating the signature. A def/lemma gets ≤1 line of intent (the *why*, not the *what*), or none.
- DO note load-bearing gotchas (why `erw` not `rw`, a defeq shortcut, a subtle hypothesis).
- Prefer an ASCII **commuting diagram** (real maps) over prose to show what a construction does.
- Rationale/process belongs in your report to the requester, not the source file.


<!-- BEGIN BEADS INTEGRATION v:1 profile:minimal hash:6cd5cc61 -->
## Beads Issue Tracker

This project uses **bd (beads)** for issue tracking. Run `bd prime` to see full workflow context and commands.

### Quick Reference

```bash
bd ready              # Find available work
bd show <id>          # View issue details
bd update <id> --claim  # Claim work
bd close <id>         # Complete work
```

### Rules

- Use `bd` for ALL task tracking — do NOT use TodoWrite, TaskCreate, or markdown TODO lists
- Run `bd prime` for detailed command reference and session close protocol
- Use `bd remember` for persistent knowledge — do NOT use MEMORY.md files

**Architecture in one line:** issues live in a local Dolt DB; sync uses `refs/dolt/data` on your git remote; `.beads/issues.jsonl` is a passive export. See https://github.com/gastownhall/beads/blob/main/docs/SYNC_CONCEPTS.md for details and anti-patterns.

## Agent Context Profiles

The managed Beads block is task-tracking guidance, not permission to override repository, user, or orchestrator instructions.

- **Conservative (default)**: Use `bd` for task tracking. Do not run git commits, git pushes, or Dolt remote sync unless explicitly asked. At handoff, report changed files, validation, and suggested next commands.
- **Minimal**: Keep tool instruction files as pointers to `bd prime`; use the same conservative git policy unless active instructions say otherwise.
- **Team-maintainer**: Only when the repository explicitly opts in, agents may close beads, run quality gates, commit, and push as part of session close. A current "do not commit" or "do not push" instruction still wins.

## Session Completion

This protocol applies when ending a Beads implementation workflow. It is subordinate to explicit user, repository, and orchestrator instructions.

1. **File issues for remaining work** - Create beads for anything that needs follow-up
2. **Run quality gates** (if code changed) - Tests, linters, builds
3. **Update issue status** - Close finished work, update in-progress items
4. **Handle git/sync by active profile**:
   ```bash
   # Conservative/minimal/default: report status and proposed commands; wait for approval.
   git status

   # Team-maintainer opt-in only, unless current instructions forbid it:
   git pull --rebase
   git push
   git status
   ```
5. **Hand off** - Summarize changes, validation, issue status, and any blocked sync/commit/push step

**Critical rules:**
- Explicit user or orchestrator instructions override this Beads block.
- Do not commit or push without clear authority from the active profile or the current user request.
- If a required sync or push is blocked, stop and report the exact command and error.
<!-- END BEADS INTEGRATION -->
