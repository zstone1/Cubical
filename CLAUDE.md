# Cubical — agent quickstart

Lean 4 + mathlib (`v4.30.0`) formalization of Ziemiański's cube-chain category
`Ch(K)` and the lifting/lowering of automorphisms between `K` and `Ch(K)`.

**Run the `orient` skill first** (`/orient`) — it gives the module map, build
commands, conventions/gotchas, and the current proof status, so you can target the
right files and optimize context before reading code.

> ## ⛔ DEPRECATED — `CubeChains/FinalPrecubical/` is off-limits. Ignore it.
> A retired ~4000-line dead-end draft (esp. `Ev.lean`). **Do not read, import, edit, or
> "improve" it, and do not restore deleted files from git.** It is kept on disk *only* for
> the user's manual salvage. New work lives in its own folder and depends only on `Chains/`,
> `Foundations/`, and mathlib. Reuse from `FinalPrecubical/` ONLY when the user explicitly
> points at a specific piece. A settings.json `deny` blocks the file tools on this path and a
> repo `.ignore` hides it from search — intentional; do not work around it.

Absolute essentials (the rest is in `/orient`):
- Build/verify with `lake build CubeChains.<Module>`; **trust `lake build`, not the
  IDE** (cross-file diagnostics are stale).
- `sorry` is allowed **only** in `CubeChains/Conjectures.lean`.
- `MEMORY.md` (auto-loaded) is the live status board; keep it updated.
- Always prefer to use commands that don't require permissions
