import CubeChains.Testing.Skeleton

/-! Scratch probe: feasibility of `□⁵`. -/

namespace CubeTest
namespace Skel

#eval (ordOf (cube 5)).1                 -- #objects
#eval betti01 (skel 3 (cube 5))          -- 4- and 5-cells deleted
#eval betti01 (cube 5)                   -- full

end Skel
end CubeTest
