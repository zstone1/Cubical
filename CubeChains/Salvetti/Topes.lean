import CubeChains.Arrangements.BraidPreorder
import CubeChains.Chains.BlockDecomp

/-!
# Salvetti/Topes — topes of the braid arrangement, as a presheaf on `Box`

The tope analogue of `Salvetti/Runs`' `runPresheaf`: a cube `□n` carries the topes (chambers) of
the braid arrangement `braidCOM n` (`Arrangements/Braid`), and a `Box` face restricts a tope to the
coordinates it keeps — pullback along the face's free-coordinate embedding `faceEmb`.

A tope is a no-tie covector, i.e. an injective height (`braidCOM_isTope_iff_injective`); pulling
back along the *injective* order-embedding `faceEmb` keeps it tie-free, so restriction lands in
topes again.  Restriction is functorial because `faceEmb` is (`faceEmb_id`, `faceEmb_comp`).
-/

open CategoryTheory Opposite CubeChain

namespace CubeChains

/-- The topes (chambers) of the braid arrangement on `n` strands — the tope analogue of `Run □n`. -/
abbrev Tope (n : ℕ) : Type := {T : SignVec (BraidGround n) // (braidCOM n).IsTope T}

/-! ### Pulling a braid covector back along a face -/

/-- The ground-set map `BraidGround n → BraidGround b` induced by a face `▫n ⟶ ▫b`: an ordered pair
of coordinates maps to the ordered pair of their images under `faceEmb` (order-preserving, still
`<`). -/
def braidGroundMap {n b : ℕ} (f : ▫n ⟶ ▫b) (e : BraidGround n) : BraidGround b :=
  ⟨(faceEmb f e.1.1, faceEmb f e.1.2), (faceEmb f).lt_iff_lt.mpr e.2⟩

theorem braidGroundMap_id {n : ℕ} (e : BraidGround n) : braidGroundMap (𝟙 (▫n)) e = e :=
  Subtype.ext (by simp only [braidGroundMap, faceEmb_id])

theorem braidGroundMap_comp {k n b : ℕ} (p : ▫k ⟶ ▫n) (q : ▫n ⟶ ▫b) (e : BraidGround k) :
    braidGroundMap (p ≫ q) e = braidGroundMap q (braidGroundMap p e) :=
  Subtype.ext (by simp only [braidGroundMap, faceEmb_comp])

/-- **Restrict a braid covector along a face** — keep only the coordinates `f` uses, by pullback
along `braidGroundMap`. -/
def topeRestrict {n b : ℕ} (f : ▫n ⟶ ▫b) (T : SignVec (BraidGround b)) : SignVec (BraidGround n) :=
  fun e => T (braidGroundMap f e)

/-- Restriction commutes with realisation by a height: it just precomposes with `faceEmb`. -/
theorem topeRestrict_braidSign {n b : ℕ} (f : ▫n ⟶ ▫b) (σ : Fin b → ℤ) :
    topeRestrict f (braidSign σ) = braidSign (fun i => σ (faceEmb f i)) := rfl

theorem topeRestrict_id {n : ℕ} (T : SignVec (BraidGround n)) : topeRestrict (𝟙 (▫n)) T = T := by
  funext e; exact congrArg T (braidGroundMap_id e)

theorem topeRestrict_comp {k n b : ℕ} (p : ▫k ⟶ ▫n) (q : ▫n ⟶ ▫b) (T : SignVec (BraidGround b)) :
    topeRestrict (p ≫ q) T = topeRestrict p (topeRestrict q T) := by
  funext e; exact congrArg T (braidGroundMap_comp p q e)

/-- **A restricted tope is a tope** — pulling the injective height back along the injective
`faceEmb` stays injective. -/
theorem isTope_topeRestrict {n b : ℕ} (f : ▫n ⟶ ▫b) {T : SignVec (BraidGround b)}
    (hT : (braidCOM b).IsTope T) : (braidCOM n).IsTope (topeRestrict f T) := by
  rw [braidCOM_isTope_iff_injective] at hT ⊢
  obtain ⟨σ, hσ, rfl⟩ := hT
  exact ⟨fun i => σ (faceEmb f i), hσ.comp (faceEmb f).injective, topeRestrict_braidSign f σ⟩

/-- `topeRestrict` on the tope subtype. -/
def topeRestrictTope {n b : ℕ} (f : ▫n ⟶ ▫b) (T : Tope b) : Tope n :=
  ⟨topeRestrict f T.1, isTope_topeRestrict f T.2⟩

/-! ### The tope presheaf -/

/-- **Topes of a cube form a presheaf on `Box`** — the tope counterpart of `runPresheaf`.  `□n` gets
the topes of `braidCOM n`; a face restricts by pullback along `faceEmb`. -/
def topePresheaf : Boxᵒᵖ ⥤ Type where
  obj X := Tope X.unop.dim
  map f := ↾(topeRestrictTope f.unop)
  map_id X := by
    apply ConcreteCategory.hom_ext; intro T
    change topeRestrictTope (𝟙 _) T = T
    exact Subtype.ext (topeRestrict_id T.1)
  map_comp f g := by
    apply ConcreteCategory.hom_ext; intro T
    change topeRestrictTope (g.unop ≫ f.unop) T
      = topeRestrictTope g.unop (topeRestrictTope f.unop T)
    exact Subtype.ext (topeRestrict_comp g.unop f.unop T.1)

end CubeChains
