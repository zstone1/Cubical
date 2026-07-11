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
