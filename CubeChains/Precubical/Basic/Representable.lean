import CubeChains.Machinery.Cube.Box

/-!
# Precubical/Basic/Representable

The **cube Yoneda lemma**, on the nose: a cube map `▫n ⟶ ▫N` *is* a sign vector `Cell N n`,
because that is how `Box` is defined.  So `Box.sign` reads a map as a cell, `Box.ofSign` reads a
cell as a map, `cubeRepr` is `Equiv.refl`, and composition is substitution (`Box.sign_comp`).

What refers to the composition is the coface dictionary: facing a sign vector is precomposing
with a coface (`Box.ofSign_faceCell`), of which peeling the smallest fixed coordinate
(`Box.ofSign_peel`) is the instance every induction on cells uses.
-/

open CategoryTheory StdCube

namespace Box

/-- The sign vector of a cube map: the value on the free top cell. -/
def sign {X Y : Box} (f : X ⟶ Y) : Cell Y.dim X.dim := f

/-- The cube map classified by a sign vector.  The cell carries both dimensions as `ℕ`s, so the
objects never have to be supplied. -/
def ofSign {N n : ℕ} (c : Cell N n) : ▫n ⟶ ▫N := c

@[simp] theorem sign_ofSign {N n : ℕ} (c : Cell N n) : sign (ofSign c) = c := rfl

@[simp] theorem ofSign_sign {X Y : Box} (f : X ⟶ Y) : ofSign (sign f) = f := rfl

theorem hom_ext {X Y : Box} {f g : X ⟶ Y} (h : sign f = sign g) : f = g := h

@[simp] theorem sign_id (X : Box) : sign (𝟙 X) = topCell X.dim := rfl

/-- **Composition of cube maps is substitution** — the dictionary entry that makes every
sign-level computation downstream a `subst` computation. -/
theorem sign_comp {X Y Z : Box} (f : X ⟶ Y) (g : Y ⟶ Z) :
    sign (f ≫ g) = subst (sign g) (sign f) := rfl

/-- **Every cube map is monic**: a substituted cell remembers what was substituted, so the
cube is non-self-linked. -/
instance mono {X Y : Box} (f : X ⟶ Y) : Mono f where
  right_cancellation _ _ e := subst_injective (sign f) e

/-- **Cubes are rigid.**  `Box` is symmetry-free, so `▫n` has no endomorphism but the identity —
the convention that makes `(BPSet, ⊗)` unbraided and forces the braiding to be *created* by
the passage to executions. -/
theorem endo_eq_id {n : ℕ} (g : ▫n ⟶ ▫n) : g = 𝟙 ▫n := eq_topCell (sign g)

end Box

namespace StdCube

/-- **Representability of the standard cube** (cube Yoneda). -/
def cubeRepr (N n : ℕ) : (▫n ⟶ ▫N) ≃ Cell N n where
  toFun := Box.sign
  invFun := Box.ofSign
  left_inv _ := rfl
  right_inv _ := rfl

end StdCube

namespace PrecubicalSet

/-- The coface `□ⁿ ⟶ □ⁿ⁺¹` selecting the `(ε, i)`-face of the top cell. -/
def coface (ε : Bool) {n : ℕ} (i : Fin (n + 1)) : ▫n ⟶ ▫(n + 1) :=
  Box.ofSign (faceCell ε i (topCell (n + 1)))

end PrecubicalSet

namespace Box

/-- The sign vector of a coface is the corresponding face of the top cell. -/
@[simp] theorem sign_coface {k : ℕ} (ε : Bool) (i : Fin (k + 1)) :
    sign (PrecubicalSet.coface ε i) = faceCell ε i (topCell (k + 1)) := rfl

/-- **Precomposing with a coface faces the sign vector.**  The one law every face-level
computation on cubes reduces to. -/
theorem sign_coface_comp {N m : ℕ} (ε : Bool) (i : Fin (m + 1)) (x : ▫(m + 1) ⟶ ▫N) :
    sign (PrecubicalSet.coface ε i ≫ x) = faceCell ε i (sign x) := by
  rw [sign_comp, sign_coface, subst_faceCell, subst_topCell]

/-- **Facing a sign vector is precomposing with a coface.**  Every induction on cells peels
cofaces through this. -/
theorem ofSign_faceCell {N k : ℕ} (ε : Bool) (i : Fin (k + 1)) (a : Cell N (k + 1)) :
    ofSign (faceCell ε i a) = PrecubicalSet.coface ε i ≫ ofSign a :=
  hom_ext (by rw [sign_ofSign, sign_coface_comp, sign_ofSign])

/-- **Coface peeling.**  A non-top cell `c'` of `□ᴺ` factors its cube map through the
smallest-fixed-coordinate coface. -/
theorem ofSign_peel {N k : ℕ} (c' : Cell N k) (h : k < N) :
    ofSign c' = PrecubicalSet.coface (minFixedVal c' h) (minFixedIdx c' h)
      ≫ ofSign (freeMin c' h) :=
  (congrArg ofSign (face_freeMin c' h)).symm.trans (ofSign_faceCell _ _ _)

end Box

/-- **The coface relation in `Box`** — the dual of the precubical identity, living among the
*coface* box maps, whence the identity for every presheaf's face maps. -/
theorem PrecubicalSet.coface_coface (ε η : Bool) {n : ℕ} {i j : Fin (n + 1)} (hij : i ≤ j) :
    (coface ε i ≫ coface η j.succ : ▫n ⟶ ▫(n + 2))
      = coface η j ≫ coface ε i.castSucc := by
  refine Box.hom_ext ?_
  rw [Box.sign_coface_comp, Box.sign_coface_comp, Box.sign_coface, Box.sign_coface]
  exact face_face ε η hij (topCell (n + 2))

/-- **A `Box` morphism only lowers dimension**: `▫a ⟶ ▫b` forces `a ≤ b`, since a `b`-cube has no
cell of dimension above `b`. -/
theorem boxHom_dim_le {a b : ℕ} (f : ▫a ⟶ ▫b) : a ≤ b :=
  StdCube.cells_card_le (Box.sign f)
