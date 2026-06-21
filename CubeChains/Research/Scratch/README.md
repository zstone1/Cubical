# Research scratch — "which endofunctors does the cylinder construction induce?"

Scratch area for the investigation of `cylToPointedR` (RESULT 2). **Decoupled from the
green build**: nothing here is imported by the root `CubeChains.lean`, so `lake build
CubeChains` ignores it. Build a scratch module explicitly:

```
lake build CubeChains.Research.Scratch.<File>
```

## Ground rules (so agents don't step on each other)

- **One file per topic, listed below. Touch only your own files.** Do NOT edit the root
  `CubeChains.lean`, the main library, or another agent's scratch file.
- `sorry` is allowed here ONLY as an explicit `sorry -- TODO` scaffold marker. **A result is
  only "backed by Lean" if its module is sorry-free and `lake build` is green.** Never present
  a sorry-bearing statement as proven; label it a conjecture.
- Each topic ships TWO files: `Cyl<N>_<Topic>.lean` (the Lean) and `Cyl<N>_<Topic>.md`
  (the findings writeup: what was asked, what was proven, what's conjectured + evidence,
  what's open). Keep the `.md` self-contained.

## File ownership

| File stem | Topic |
|---|---|
| `Cyl1_Algebra`     | Converse of `pointedOfPaths`; non-surjectivity; monad/classical-CT structure |
| `Cyl2_Injectivity` | Fibers of the construction; universal property; constraints on the `x → F₀ x` maps |
| `Cyl3_Examples`    | Worked small examples + pathologies (realizability-style) |
| `Cyl4_Generation`  | Cylinders for generating homotopies; do K's homotopies generate all zigzags |
| `Cyl5_Altitude`    | Simplifications under NonSelfLinked + AdmitsAltitude |

## The construction (recap)

- `DPathGrpdR K := FreeGroupoid (RefineObj K.init K.final)` — the d-path homotopy groupoid.
- `pointedOfPaths (F₀ : C → FreeGroupoid C) (η : ∀ x, (of).obj x ⟶ F₀ x) :
  PointedEndofunctor (FreeGroupoid C)` — object-data → pointed endofunctor, naturality free
  by conjugation (`Cylinder/PointedFunctor.lean`).
- `cylToPointedObj c` = `pointedOfPaths` with
  `F₀ x = Rgrpd (Lgrpd⁻¹ x)` and `η x = counit.inv ≫ sweepR (Lgrpd⁻¹ x)`
  (`Cylinder/CylinderRefine.lean`).
- `cylToPointedR K : CylMapWeqR K ⥤ PointedEndofunctor (DPathGrpdR K)` — morphism map forced
  because the base is a groupoid (`pointedFunctorOfObj`).

## Key files to read
- `Cylinder/PointedFunctor.lean`, `Cylinder/CylinderRefine.lean`,
  `Cylinder/CylinderRefineCore.lean`, `Cylinder/CylinderSweep.lean`
- `Chains/Refine.lean` (`RefineObj`, `ChainRefine`), `Chains/Correspondence.lean` (thinness),
  `Foundations/Altitude.lean` (side conditions)
- `Testing/` (computable `FinBPSet` surrogate + `native_decide`) for examples.
