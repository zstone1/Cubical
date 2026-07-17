# Cubical — agent quickstart

Lean 4 + mathlib (`v4.30.0`) formalization of the **concurrency braid groupoid** of a precubical
set: the executions of a cube chain `Ch(K)` made into a groupoid, and the theorem that it is the
(pure) braid group.

Start with `bd ready` (the board) and `ARCHITECTURE.md` (the map). Run `/orient` for
build conventions, the mathlib-reuse table, and the gotchas list.

Absolute essentials:
- Build/verify with `lake build CubeChains.<Module>`; **trust `lake build`, not the
  IDE** (cross-file diagnostics are stale).
- The repo is **sorry-free** — keep it that way (no `sorry`, no `admit`).
- Prefer commands that don't require permissions. Shell aliases may add `-i` and hang
  you: use `cp -f`, `mv -f`, `rm -f`, `apt-get -y`, `ssh -o BatchMode=yes`.

## Where things go

Every fact has exactly one home. Pick it by asking **who authors this, and would a
human review the diff?**

| kind of fact | home | example |
|---|---|---|
| status: what's done / next / blocked | **a bead** | "chambersConcat assoc is open" |
| durable knowledge that must survive a clone | **a pinned bead** | the landmines list (`Cubical-hic`) |
| a gotcha you paid for, convenience only | **`bd remember`** | `erw` not `rw`, and why |
| a rule humans decide and review | **this file** (git) | the `ε : Bool` convention |
| the mathematics | **prose** (`ARCHITECTURE.md`, the paper) | the proof structure |
| how the work went | **your reply to the requester** | anything else |

`bd remember` is a **local cache** — it lives in the gitignored Dolt DB and does *not*
travel with a clone. Anything that must survive `git clone` goes in a pinned bead (those
export to `.beads/issues.jsonl`) or in git. Every remembered fact is re-injected at the
start of every future session, so the bar is: *would you pay context for this, forever?*
Passes: "`equivWedgeCat` silently carries `NonSelfLinked`." Fails: "X is proved."

## Documentation discipline (keep code readable)

Docstrings state **intent + gotchas**. The reader has the types, the code, and git.

Three tests. They are mechanical — apply them, don't weigh them:
1. **Would this sentence become false when a bead closes?** Then it is not documentation.
   It is status. It goes in the bead.
2. **Does it have a tense** — "is now", "has been", "was previously", "remains"? Timeless
   facts don't need one. Rewrite it or cut it.
3. **Would it read as an argument that your work is good** — "unconditional",
   "assumption-free", "sorry-free", "now discharged", "Phase 3", "Deliverable A"? Cut it.
   The code is the argument. Say it in your reply to the requester instead, where it
   belongs and where it is *meant* to evaporate.

Budgets, not adjectives: **≤1 line of intent per declaration** (the *why*, never the
*what*); **≤10 lines per module docstring**. Need more? It's a bead, or it's the paper.

DO write: load-bearing gotchas (why `erw` not `rw`, a defeq shortcut, a subtle
hypothesis) and ASCII **commuting diagrams** of real maps. Those are why a reader is here.

Never point a tracked file at anything outside the repo. A `[[wikilink]]` into a private
memory directory is a dangling pointer for everyone but you.

When your task involves proving a lemma, prove the whole thing. Do not return early with a "risk assessment". Do not change the goal and say you've succeeded. Prove the fact, or establish why your approach is impossible.

Do not edit the README file. That's for human interaction only

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
