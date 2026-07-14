import CubeChains.Braid.Functor

/-!
# Braid/Characters — invariants of the braid functor, on the concurrency groupoid

Characters of `braidPhi K n : ConcGrpdN K n ⥤ BraidFib n`, read directly on the executions — no
Salvetti arrangement, no `salWind`.  Each is a homomorphism out of `Braid n` post-composed with `Φ`:

* the **event monodromy** `permHom ∘ Φ` — the `Sₙ`-shadow (`permHom_braidPhi`, `Braid/Functor`);
* the **writhe** `writheHom ∘ Φ` — the signed crossing count, here.

On a *loop* the writhe is the winding number: an alternating sum of the inversion counts of the
refinements around it (`writheHom` is a homomorphism, so `Φ` of a word is a product).  On a single
refinement it is exactly the number of event pairs it crosses.
-/

open CategoryTheory

namespace CubeChains

variable {K : BPSet} {n : ℕ}

/-- **The writhe character** of the braid functor: the signed crossing count of a 2-cell of the
concurrency groupoid. -/
noncomputable def braidWrithe (K : BPSet) (n : ℕ) :
    ConcGrpdN K n ⥤ SingleObj (Multiplicative ℤ) :=
  braidPhi K n ⋙ SingleObj.mapHom _ _ (writheHom n)

/-- On a refinement, the writhe is the **inversion count of its event permutation** — how many event
pairs it crosses. -/
@[simp] theorem braidWrithe_homMk {x y : ConcCatN K n} (f : x ⟶ y) :
    (braidWrithe K n).map (FreeGroupoid.homMk f)
      = Multiplicative.ofAdd ((permLen (evPerm f) : ℤ)) := by
  change (SingleObj.mapHom _ _ (writheHom n)).map ((braidPhi K n).map (FreeGroupoid.homMk f)) = _
  rw [braidPhi_homMk]
  exact writheHom_ofPerm (evPerm f)

end CubeChains
