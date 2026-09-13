import CubeChains.Machinery.Cube.BoxMonoidal
import CubeChains.Precubical.Wedge.Wedge
import CubeChains.Precubical.Basic.Altitude

/-!
# Precubical/Chains/CubeNonSelfLinked — standard cubes are non-self-linked

`NonSelfLinked (□m)` asks that every cube map `(□m).cubeMap c` be pointwise injective.  On the
representable that map is precomposition by `c` (Yoneda), so the statement is exactly that
every `Box` morphism is monic — which substitution gives (`Box.mono`).
-/

open CategoryTheory Opposite

namespace CubeChain

open BPSet PrecubicalSet StdCube

/-- The cube map of the representable is precomposition (Yoneda). -/
theorem cubeMap_cube_app {m n k : ℕ} (c : (□m).cells n) (g : ▫k ⟶ ▫n) :
    ((□m).toPsh.cubeMap c)⟪k⟫ g = g ≫ c := by
  rw [PrecubicalSet.cubeMap, yonedaEquiv_symm_app_apply]; rfl

/-- **Standard cubes are non-self-linked**: precomposition by a box morphism is injective
because every box morphism is monic. -/
theorem cube_nonSelfLinked (m : ℕ) : (□m).NonSelfLinked := by
  intro n c k g₁ g₂ h
  rw [cubeMap_cube_app, cubeMap_cube_app] at h
  exact (cancel_mono c).mp h

end CubeChain
