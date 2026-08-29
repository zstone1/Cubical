import CubeChains.Testing.HTwo

/-!
# Testing/HTwoDeep — the degree-`5`/`6` end of `Testing/HTwo`

Rewrites never leave the source component, and relabelling directions acts transitively on the
components, so `Hom` out of **one** component determines all `24` — which is what puts degree `6`
(the top degree of an arrow of `Ch⋆(Hbp □⁴)`, hence of a relation) within reach.

Minutes per `#eval`.  Not built by `lake build CubeChains`.
-/

namespace CubeChains

/-- The distinct per-component degree-`d` hom counts — one entry means the localization looks the
same from every object. -/
def homHomogeneous (L : FinLoc) (d : ℕ) : List ℕ :=
  ((List.range (countDistinct (compsOf L).toList)).map fun c => (homData L d d [c]).2.1).eraseDups

#eval (countDistinct (compsOf (hStarLoc2 (SubCube.full 4))).toList,
       countDistinct (compsOf (hStarLoc2 (SubCube.boundary 4))).toList)     -- (576, 264)
#eval (homHomogeneous (hStarLoc (SubCube.full 4)) 3,
       homHomogeneous (hStarLoc (SubCube.boundary 4)) 3)                    -- ([156], [156])
#eval (homData (hStarLoc (SubCube.boundary 4)) 4 4 [0], homData (hStarLoc (SubCube.full 4)) 4 4 [0])
#eval (homData (hStarLoc (SubCube.boundary 4)) 5 5 [0], homData (hStarLoc (SubCube.full 4)) 5 5 [0])
#eval homData (hStarLoc (SubCube.boundary 4)) 6 6 [0]
#eval homData (hStarLoc (SubCube.full 4)) 6 6 [0]

end CubeChains
